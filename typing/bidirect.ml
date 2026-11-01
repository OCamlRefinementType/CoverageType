open Language
open Zutils
open Auxtyping
open Common
open HandlePred

type value_infer_mode = TopParam | PolyPredParam

let value_infer_mode = PolyPredParam
let ( let* ) x f = match x with Ok v -> f v | Error e -> Error e

let type_check_group (bctx : built_in_ctx) =
  let _find_in_ctx loc (rctx : rctx) (id : (Nt.t, string) typed) =
    let res = lookup_ctxs [ rctx.rty_ctx; bctx.builtin_ctx ] id.x in
    match res with
    | Some res ->
        let rty = fresh_name_rty res in
        let _, rty = instantiate_rty_by_nty [%here] rty id.ty in
        rty
    | None -> _die_with loc (spf "cannot find %s in type context" id.x)
  in
  let _id_type_infer loc (rctx : rctx) (id : (Nt.t, string) typed) : Nt.t rty =
    let rty = _find_in_ctx loc rctx id in
    (* NOTE: both over and under type will induce under type *)
    if is_base_rty rty then mk_eq_tvar_underrty id.x#:(erase_rty rty) else rty
  in
  let subtyping rctx (rty1, rty2) =
    pprint_typing_subtyping rctx (rty1, rty2);
    sub_rty rctx (rty1, rty2)
  in
  let rec value_type_infer (rctx : rctx) (v : (Nt.t, Nt.t value) typed) :
      (Nt.t rty, Nt.t rty value) typed type_result =
    let res =
      match v.x with
      | VVar id ->
          let () = if String.equal id.x "None" then _die [%here] in
          let rty = _id_type_infer [%here] rctx id in
          let res = Ok (VVar id.x#:rty)#:rty in
          if ZUtilsConfig.get_show_type_infer_variable_judgement () then
            pprint_typing_infer_value_after rctx (v, res);
          res
      | VConst U ->
          let res = Ok (VConst U)#:(mk_top_underrty Nt.unit_ty) in
          if ZUtilsConfig.get_show_type_infer_constant_judgement () then
            pprint_typing_infer_value_after rctx (v, res);
          res
      | VConst c ->
          let res = Ok (VConst c)#:(mk_eq_c_underrty c) in
          if ZUtilsConfig.get_show_type_infer_constant_judgement () then
            pprint_typing_infer_value_after rctx (v, res);
          res
      | VTuple vs ->
          let* vs =
            result_list_to_list_result @@ List.map (value_type_infer rctx) vs
          in
          let phis =
            List.mapi
              (fun idx x ->
                match x.ty with
                | RtyBase { ou = Under; cty = { phi; _ } } ->
                    let y =
                      mk_nth_lit [%here] (AVar default_v#:v.ty)#:v.ty idx
                    in
                    let phi = subst_prop_instance default_v y.x phi in
                    phi
                | _ -> _die_with [%here] "unimp")
              vs
          in
          let rty =
            RtyBase { ou = Under; cty = { nty = v.ty; phi = smart_and phis } }
          in
          let res = Ok (VTuple vs)#:rty in
          pprint_typing_infer_value_after rctx (v, res);
          res
      | VLam { lamarg; body } ->
          let nty = lamarg.ty in
          let res =
            if Nt.is_base_tp nty then
              match value_infer_mode with
              | PolyPredParam ->
                  let pred =
                    (Rename.unique_var "p")#:(Nt.construct_arr_tp
                                                ([ nty ], Nt.bool_ty))
                  in
                  let open Prop in
                  let phi =
                    Lit
                      (AAppOp (pred, [ tvar_to_lit default_v#:nty ]))#:Nt
                                                                       .bool_ty
                  in
                  let rty = cty_to_overrty { nty; phi } in
                  let lamarg = lamarg.x#:rty in
                  let rctx' = Rctx.add_pred rctx pred in
                  let rctx' = Rctx.add_var rctx' lamarg in
                  let* body = term_type_infer rctx' body in
                  let frty =
                    construct_poly_pred_rty
                      ([ pred ], construct_rty ([ lamarg ], body.ty))
                  in
                  Ok (VLam { lamarg; body })#:frty
              | TopParam ->
                  let lamarg = lamarg.x#:(mk_top_overrty nty) in
                  let* body = term_type_infer (Rctx.add_var rctx lamarg) body in
                  let frty = construct_rty ([ lamarg ], body.ty) in
                  Ok (VLam { lamarg; body })#:frty
            else _die_with [%here] "unimp"
          in
          pprint_typing_infer_value_after rctx (v, res);
          res
      | VFix { fixname; _ } -> (
          match Typectx.get_opt rctx.inv_ctx fixname.x with
          | None ->
              _die_with [%here]
                (spf "inductive invaraint of %s is missing" fixname.x)
          | Some rty ->
              let () =
                TypecheckerLog.typing @@ fun _ ->
                Pp.printf "@{<bold>inv:@} %s\n" (layout_rty rty)
              in
              value_type_check rctx v rty)
    in
    res
  and value_type_check (rctx : rctx) (v : (Nt.t, Nt.t value) typed)
      (rty : Nt.t rty) : (Nt.t rty, Nt.t rty value) typed type_result =
    let () = pprint_typing_check_value rctx (v, rty) in
    match (v.x, rty) with
    | _, RtyPolyType { pt; rty } ->
        value_type_check (Rctx.add_tvar rctx pt) v rty
    | _, RtyPolyPred { pred; rty } ->
        value_type_check (Rctx.add_pred rctx pred) v rty
    | VConst _, _ | VVar _, _ | VTuple _, _ ->
        let* e = value_type_infer rctx v in
        if subtyping rctx (e.ty, rty) then Ok e
        else (
          _warinning_subtyping_error [%here] (e.ty, rty);
          _warinning_typing_error [%here] (layout_typed_value v, rty);
          Error SubtypingFailure)
    | VLam { lamarg; body }, RtyArr { argrty; arg; retty } ->
        (* NOTE: unify the name of parameter type and lambda variable *)
        let retty = subst_rty_instance arg (AVar lamarg) retty in
        let lamarg = lamarg.x#:argrty in
        let rctx' = Rctx.add_var rctx lamarg in
        let* body = term_type_check rctx' body retty in
        Ok (VLam { lamarg; body })#:(RtyArr { argrty; arg; retty })
    | VLam _, _ -> _die [%here]
    | VFix { fixname; fixarg; body }, RtyArr { argrty; arg; retty } ->
        (* NOTE: we force the first argument to be the decreasing argument *)
        let measure_cty =
          match argrty with
          | RtyBase { ou = Over; cty } -> cty
          | _ ->
              _die_with [%here]
                "the first parameter of recursive function must be a \
                 decreasing base type"
        in
        let fixarg =
          fixarg #=> (fun t ->
          (* let () = *)
          (*   Printf.printf "%s =? %s\n" (Nt.layout t) (Nt.layout measure_cty.nty) *)
          (* in *)
          Nt.unify_two_types [%here] [] (t, measure_cty.nty))
        in
        (* NOTE: make sure the name of paramater of refinement type is different from the one in the implementation. *)
        (* let () = Printf.printf "fix retty %s\n" (layout_rty retty) in *)
        let arg, retty =
          if String.equal arg fixarg.x then
            let arg' = Rename.unique_var arg in
            (arg', subst_rty_instance arg (AVar arg'#:fixarg.ty) retty)
          else (arg, retty)
        in
        (* let () = Printf.printf "fix retty %s\n" (layout_rty retty) in *)
        let rty' =
          let phi = smart_add_to (mk_self_wf_dec fixarg) measure_cty.phi in
          let argrty = cty_to_overrty { nty = fixarg.ty; phi } in
          RtyArr { argrty; arg; retty }
        in
        (* let () = Printf.printf "fix rty' %s\n" (layout_rty rty') in *)
        let retty = subst_rty_instance arg (AVar fixarg) retty in
        let rctx' = Rctx.add_vars rctx [ fixarg.x#:argrty; fixname.x#:rty' ] in
        let rctx' =
          {
            rctx' with
            rec_bound =
              Some (fixname.x, { nty = fixarg.ty; phi = mk_self_wf_dec fixarg });
          }
        in
        let* body = term_type_check rctx' body retty in
        Ok
          (VFix { fixname = fixname.x#:rty; fixarg = fixarg.x#:argrty; body })#:rty
    | VFix _, _ -> _die [%here]
  and over_arrow_type_apply (_ : rctx) appf_rty
      (apparg : (Nt.t rty, Nt.t value) typed) : Nt.t rty type_result =
    let argrty, arg, retty = destruct_arr_rty [%here] appf_rty in
    let () =
      _assert [%here] "application basic type check"
        (Nt.equal_nt (erase_rty argrty) (erase_rty apparg.ty))
    in
    match argrty with
    | RtyBase { ou = Over; cty } ->
        let arglit = value_to_lit [%here] apparg.x in
        let retty = subst_rty_instance arg arglit retty in
        let tmp_rty =
          mk_unit_underrty (subst_prop_instance default_v arglit cty.phi)
        in
        let retty = exists_rty (Rename.fresh_var ())#:tmp_rty retty in
        Ok retty
    | _ -> _die [%here]
  and arrow_arrow_type_apply (rctx : rctx) appf_rty
      (apparg : (Nt.t rty, Nt.t value) typed) : Nt.t rty type_result =
    let argrty, arg, retty = destruct_arr_rty [%here] appf_rty in
    let () =
      let _nt1 = erase_rty argrty in
      let _nt2 = erase_rty apparg.ty in
      _assert [%here]
        (spf "application basic type check failed: %s != %s\n" (Nt.layout _nt1)
           (Nt.layout _nt2))
        (Nt.equal_nt _nt1 _nt2)
    in
    match argrty with
    | RtyArr _ ->
        if not (subtyping rctx (apparg.ty, argrty)) then (
          _warinning_subtyping_error [%here] (apparg.ty, argrty);
          _warinning_typing_error [%here]
            (layout_typed_value @@ (apparg#=>erase_rty), argrty);
          Error SubtypingFailure)
        else if is_free_rty arg retty then
          _die_with [%here]
            (spf "arrow typed variable cannot be refered (arg: %s) (retty: %s)"
               arg (layout_rty retty))
        else Ok retty
    | _ -> _die [%here]
  and term_type_infer (rctx : rctx) (e : (Nt.t, Nt.t term) typed) :
      (Nt.t rty, Nt.t rty term) typed type_result =
    match e.x with
    | CVal v ->
        let* v = value_type_infer rctx v in
        Ok (CVal v)#:v.ty
    | _ ->
        let () = pprint_typing_infer_term_before rctx e in
        let res =
          match e.x with
          | CVal _ -> _die [%here]
          | CErr ->
              _assert [%here]
                (spf "err can only has base type, not %s" (Nt.layout_nt e.ty))
                (Nt.is_base_tp e.ty);
              Ok CErr#:(mk_bot_underrty e.ty)
          | CRecord vs ->
              let fields, vs = List.split vs in
              let* vs =
                result_list_to_list_result
                @@ List.map (value_type_infer rctx) vs
              in
              let vs = List.combine fields vs in
              let self = default_v#:e.ty in
              let phis =
                List.map
                  (fun (x, v) ->
                    let cty = as_under_base_rty [%here] v.ty in
                    let lit = AField (lit_to_tlit (AVar self), x) in
                    let phi = subst_prop_instance default_v lit cty.phi in
                    phi)
                  vs
              in
              let cty = { nty = e.ty; phi = smart_and phis } in
              let rty = RtyBase { ou = Under; cty } in
              Ok (CRecord vs)#:rty
          | CField { rd; field } ->
              let lit = value_to_lit [%here] rd.x in
              let lit = (AField (lit_to_tlit lit, field))#:e.ty in
              let* rd = value_type_infer rctx rd in
              let rty = RtyBase { ou = Under; cty = mk_eq_lit_cty lit } in
              Ok (CField { rd; field })#:rty
          | CLetE { rhs; lhs; body } ->
              let* rhs' = term_type_infer rctx rhs in
              if not (non_emptiness_rty rctx rhs'.ty) then (
                _warinning_nonemptiness_error [%here] rhs'.ty;
                _warinning_typing_error [%here] (layout_term rhs.x, rhs'.ty);
                Error EmptyBranch)
              else
                let rhs = rhs' in
                let lhs = lhs.x#:rhs.ty in
                let rctx' = Rctx.add_var rctx lhs in
                let* body = term_type_infer rctx' body in
                let rty = Rctx.diff_exists_rty [%here] rctx' rctx body.ty in
                Ok (CLetE { rhs; lhs; body })#:rty
          (* (\* Lambda function to let binding *\) *)
          (* | CApp { appf = { x = VLam { lamarg; body }; _ }; apparg } -> *)
          (*     let apparg = value_type_infer rctx apparg in *)
          (*     let lamarg = lamarg.x#:apparg.ty in *)
          (*     let rctx' = Rctx.add_var rctx lamarg in *)
          (*     let* body = term_type_infer rctx' body in *)
          (*     let rty = Rctx.diff_exists_rty [%here] rctx' rctx body.ty in *)
          (*     let frty = *)
          (*       RtyArr { argrty = lamarg.ty; arg = lamarg.x; retty = rty } *)
          (*     in *)
          (*     let appf = (VLam { lamarg; body })#:frty in *)
          (*     Some (CApp { appf; apparg })#:rty *)
          | CApp { appf; apparg } ->
              (* let () = Printf.printf "Application : %s\n" (layout_term e.x) in *)
              let* appf = value_type_infer rctx appf in
              let* apparg' = value_type_infer rctx apparg in
              let poly_preds, appf_ty, apparg_rty =
                instantiate_poly_pred_rty rctx.pred_ctx appf.ty apparg'.ty
              in
              let rctx = Rctx.add_preds rctx poly_preds in
              (* Termination: a recursive call's argument must decrease. *)
              let* () =
                match (rctx.rec_bound, appf.x) with
                | Some (recname, bound_cty), VVar id
                  when String.equal id.x recname ->
                    let bound_rty = cty_to_overrty bound_cty in
                    if not (sub_rty_as_over rctx (apparg_rty, bound_rty)) then (
                      _warinning_subtyping_error [%here] (apparg_rty, bound_rty);
                      Error RecArgCheckFailure)
                    else Ok ()
                | _ -> Ok ()
              in
              (* let () = Printf.printf "appf_ty : %s\n" (layout_rty appf_ty) in *)
              let* retty =
                if is_over_arr_rty appf_ty then
                  over_arrow_type_apply rctx appf_ty apparg.x#:apparg_rty
                else if is_arr_arr_rty appf_ty then
                  arrow_arrow_type_apply rctx appf_ty apparg.x#:apparg_rty
                else
                  _die_with [%here]
                    (spf "cannot handle function type: %s\n"
                       (layout_rty appf_ty))
              in
              (* let () = Printf.printf "retty : %s\n" (layout_rty retty) in *)
              let retty =
                remove_redundant_poly_pred
                @@ construct_poly_pred_rty (poly_preds, retty)
              in
              (* let () = Printf.printf "retty : %s\n" (layout_rty retty) in *)
              Ok (CApp { appf; apparg = apparg' })#:retty
          | CAppOp { op; appopargs } ->
              let op =
                op.x#:(_find_in_ctx [%here] rctx op#->op_name_for_typectx)
              in
              (* let () = Printf.printf "op_ty : %s\n" (layout_rty op.ty) in *)
              let* appopargs =
                result_list_to_list_result
                @@ List.map
                     (fun v ->
                       let* v' = value_type_infer rctx v in
                       Ok (v, v'))
                     appopargs
              in
              let* retty =
                List.fold_left
                  (fun res (apparg, apparg') ->
                    let* rty = res in
                    over_arrow_type_apply rctx rty apparg.x#:apparg'.ty)
                  (Ok op.ty) appopargs
              in
              (* let () = Printf.printf "retty : %s\n" (layout_rty retty) in *)
              Ok (CAppOp { op; appopargs = List.map snd appopargs })#:retty
          | CMatch { matched; match_cases } ->
              (* NOTE: we drop unreachable cases *)
              let* match_cases =
                result_list_to_list_result
                @@ List.map (match_case_type_infer rctx matched) match_cases
              in
              let unioned_ty =
                union_rtys
                @@ List.map
                     (function CMatchcase { exp; _ } -> exp.ty)
                     match_cases
              in
              let* matched = value_type_infer rctx matched in
              Ok (CMatch { matched; match_cases })#:unioned_ty
          | CLetDeTuple { turhs; tulhs; body } ->
              let* turhs' = value_type_infer rctx turhs in
              let tmp = (Rename.fresh_var ())#:turhs.ty in
              let tulhs =
                List.mapi
                  (fun idx x ->
                    let lit = lit_to_tlit (AProj (tvar_to_lit tmp, idx)) in
                    let rty = mk_eq_lit_underrty lit in
                    x.x#:rty)
                  tulhs
              in
              let tmp = tmp.x#:turhs'.ty in
              let rctx' = Rctx.add_vars rctx (tmp :: tulhs) in
              let* body = term_type_infer rctx' body in
              let rty = Rctx.diff_exists_rty [%here] rctx' rctx body.ty in
              Ok (CLetDeTuple { turhs = turhs'; tulhs; body })#:rty
          (* | CLetE { rhs; lhs; body } -> *)
          (*     let* rhs = term_type_infer rctx rhs in *)
          (*     let lhs = lhs.x#:rhs.ty in *)
          (*     let rctx' = Rctx.add_var rctx lhs in *)
          (*     let* body = term_type_infer rctx' body in *)
          (*     Some *)
          (*       (CLetE { rhs; lhs; body })#:(Rctx.diff_exists_rty [%here] rctx' rctx *)
          (*                                      body.ty) *)
        in
        pprint_typing_infer_term_after rctx
          ( e,
            let* res = res in
            Ok res.ty );
        res
  and term_type_check (rctx : rctx) (e : (Nt.t, Nt.t term) typed)
      (rty : Nt.t rty) : (Nt.t rty, Nt.t rty term) typed type_result =
    match e.x with
    | CVal v ->
        let* v = value_type_check rctx v rty in
        Ok (CVal v)#:v.ty
    | _ -> (
        let () = pprint_typing_check_term rctx (e, rty) in
        match e.x with
        | CVal _ -> _die [%here]
        | CErr ->
            if sub_rty rctx (mk_bot_underrty (erase_rty rty), rty) then
              Ok CErr#:rty
            else Error SubtypingFailure
        | CLetDeTuple _ -> failwith "unimp"
        | CApp _ | CAppOp _ | CMatch _ | CLetE _ | CRecord _ | CField _ ->
            let* e' = term_type_infer rctx e in
            if sub_rty rctx (e'.ty, rty) then Ok e'.x#:rty
            else (
              _warinning_subtyping_error [%here] (e'.ty, rty);
              _warinning_typing_error [%here] (layout_typed_term e, rty);
              Error SubtypingFailure))
  (* | CLetE { rhs; lhs; body } -> *)
  (*     let* rhs = term_type_infer rctx rhs in *)
  (*     let rctx', lhs = Rctx.add_var rctx lhs.x #: rhs.ty in *)
  (*     let* body = term_type_check rctx' body rty in *)
  (*     Some (CLetE { rhs; lhs; body }) #: rty *)
  and match_case_type_infer (rctx : rctx) (matched : (Nt.t, Nt.t value) typed)
      (x : Nt.t match_case) : Nt.t rty match_case type_result =
    match x with
    | CMatchcase { constructor; args; exp } ->
        let constructor_rty =
          _find_in_ctx [%here] rctx constructor#->dt_name_for_typectx
        in
        (* let () = *)
        (*   Printf.printf "constructor.ty : %s\n" (layout_rty constructor_rty) *)
        (* in *)
        let args, retty =
          List.fold_left
            (fun (args, rty) x ->
              match rty with
              | RtyArr { argrty; arg; retty } ->
                  let retty = subst_rty_instance arg (AVar x) retty in
                  (args @ [ x.x#:(flip_rty argrty) ], retty)
              | _ -> _die [%here])
            ([], constructor_rty) args
        in
        let retty =
          match retty with
          | RtyBase { ou = Under; cty = { phi; _ } } ->
              let phi =
                subst_prop_instance default_v
                  (value_to_lit [%here] matched.x)
                  phi
              in
              RtyBase { ou = Under; cty = { nty = Nt.unit_ty; phi } }
          | _ -> _die_with [%here] (spf "retty %s" (layout_rty retty))
        in
        let rctx' =
          Rctx.add_vars rctx (args @ [ (Rename.fresh_var ())#:retty ])
        in
        let* exp' = term_type_infer rctx' exp in
        let exp' = exp'#=>(Rctx.diff_exists_rty [%here] rctx' rctx) in
        let () =
          pprint_typing_infer_match_case rctx constructor (exp, exp'.ty)
        in
        Ok
          (CMatchcase
             { constructor = constructor.x#:constructor_rty; args; exp = exp' })
  in
  (value_type_check, term_type_check)

(* A recursive call whose argument does not decrease fails the whole function. *)
let or_typecheck_failure = function Ok e -> Some e | Error _ -> None

let value_type_check bctx ctx (value, rty) =
  or_typecheck_failure @@ (fst @@ type_check_group bctx) ctx value rty

let term_type_check bctx ctx (value, rty) =
  or_typecheck_failure @@ (snd @@ type_check_group bctx) ctx value rty
