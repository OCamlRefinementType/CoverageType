open Language
open Zutils
open Sugar
open Auxtyping
open Common
open HandlePred

type value_infer_mode = TopParam | PolyPredParam

let value_infer_mode = PolyPredParam

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
      (Nt.t rty, Nt.t rty value) typed option =
    let res =
      match v.x with
      | VVar id ->
          let () = if String.equal id.x "None" then _die [%here] in
          let rty = _id_type_infer [%here] rctx id in
          Some (VVar id.x#:rty)#:rty
      | VConst U -> Some (VConst U)#:(mk_top_underrty Nt.unit_ty)
      | VConst c -> Some (VConst c)#:(mk_eq_c_underrty c)
      | VTuple vs ->
          let* vs =
            opt_list_to_list_opt @@ List.map (value_type_infer rctx) vs
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
          Some (VTuple vs)#:rty
      | VLam { lamarg; body } ->
          let nty = lamarg.ty in
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
                    (AAppOp (pred, [ tvar_to_lit default_v#:nty ]))#:Nt.bool_ty
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
                Some (VLam { lamarg; body })#:frty
            | TopParam ->
                let lamarg = lamarg.x#:(mk_top_overrty nty) in
                let* body = term_type_infer (Rctx.add_var rctx lamarg) body in
                let frty = construct_rty ([ lamarg ], body.ty) in
                Some (VLam { lamarg; body })#:frty
          else _die_with [%here] "unimp"
      | VFix { fixname; _ } -> (
          match Typectx.get_opt rctx.inv_ctx fixname.x with
          | None ->
              _die_with [%here]
                (spf "inductive invaraint of %s is missing" fixname.x)
          | Some rty ->
              let () = Pp.printf "@{<bold>inv:@} %s\n" (layout_rty rty) in
              value_type_check rctx v rty)
    in
    pprint_typing_infer_value_after rctx (v, res);
    res
  and value_type_check (rctx : rctx) (v : (Nt.t, Nt.t value) typed)
      (rty : Nt.t rty) : (Nt.t rty, Nt.t rty value) typed option =
    let () = pprint_typing_check_value rctx (v, rty) in
    match (v.x, rty) with
    | _, RtyPolyType { pt; rty } ->
        value_type_check (Rctx.add_tvar rctx pt) v rty
    | _, RtyPolyPred { pred; rty } ->
        value_type_check (Rctx.add_pred rctx pred) v rty
    | VConst _, _ | VVar _, _ | VTuple _, _ ->
        let* e = value_type_infer rctx v in
        if subtyping rctx (e.ty, rty) then Some e
        else (
          _warinning_subtyping_error [%here] (e.ty, rty);
          _warinning_typing_error [%here] (layout_typed_value v, rty);
          None)
    | VLam { lamarg; body }, RtyArr { argrty; arg; retty } ->
        (* NOTE: unify the name of parameter type and lambda variable *)
        let retty = subst_rty_instance arg (AVar lamarg) retty in
        let lamarg = lamarg.x#:argrty in
        let rctx' = Rctx.add_var rctx lamarg in
        let* body = term_type_check rctx' body retty in
        Some (VLam { lamarg; body })#:(RtyArr { argrty; arg; retty })
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
        let () = Printf.printf "fix retty %s\n" (layout_rty retty) in
        let arg, retty =
          if String.equal arg fixarg.x then
            let arg' = Rename.unique_var arg in
            (arg', subst_rty_instance arg (AVar arg'#:fixarg.ty) retty)
          else (arg, retty)
        in
        let () = Printf.printf "fix retty %s\n" (layout_rty retty) in
        let rty' =
          let phi = smart_add_to (mk_self_wf_dec fixarg) measure_cty.phi in
          let argrty = cty_to_overrty { nty = fixarg.ty; phi } in
          RtyArr { argrty; arg; retty }
        in
        let () = Printf.printf "fix rty' %s\n" (layout_rty rty') in
        let retty = subst_rty_instance arg (AVar fixarg) retty in
        let rctx' = Rctx.add_vars rctx [ fixarg.x#:argrty; fixname.x#:rty' ] in
        let* body = term_type_check rctx' body retty in
        Some
          (VFix { fixname = fixname.x#:rty; fixarg = fixarg.x#:argrty; body })#:rty
    | VFix _, _ -> _die [%here]
  and over_arrow_type_apply (rctx : rctx) appf_rty
      (apparg : (Nt.t rty, Nt.t value) typed) : Nt.t rty option =
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
        if not (non_emptiness_rty rctx tmp_rty) then (
          _warinning_nonemptiness_error [%here] argrty;
          _warinning_typing_error [%here] (layout_lit arglit, argrty);
          None)
        else
          let retty = exists_rty (Rename.fresh_var ())#:tmp_rty retty in
          Some retty
    | _ -> _die [%here]
  and arrow_arrow_type_apply (rctx : rctx) appf_rty
      (apparg : (Nt.t rty, Nt.t value) typed) : Nt.t rty option =
    let argrty, arg, retty = destruct_arr_rty [%here] appf_rty in
    let () =
      _assert [%here] "application basic type check"
        (Nt.equal_nt (erase_rty argrty) (erase_rty apparg.ty))
    in
    match argrty with
    | RtyArr _ ->
        if not (subtyping rctx (apparg.ty, argrty)) then (
          _warinning_subtyping_error [%here] (apparg.ty, argrty);
          _warinning_typing_error [%here]
            (layout_typed_value @@ (apparg#=>erase_rty), argrty);
          None)
        else if is_free_rty arg retty then (
          Printf.printf "%s\n" (layout_rty retty);
          _die_with [%here]
            (spf "arrow typed variable cannot be refered (%s)" arg))
        else Some retty
    | _ -> _die [%here]
  and term_type_infer (rctx : rctx) (e : (Nt.t, Nt.t term) typed) :
      (Nt.t rty, Nt.t rty term) typed option =
    let () = pprint_typing_infer_term_before rctx e in
    let res =
      match e.x with
      | CErr ->
          _assert [%here]
            (spf "err can only has base type, not %s" (Nt.layout_nt e.ty))
            (Nt.is_base_tp e.ty);
          Some CErr#:(mk_bot_underrty e.ty)
      | CVal v ->
          let* v = value_type_infer rctx v in
          Some (CVal v)#:v.ty
      | CRecord vs ->
          let fields, vs = List.split vs in
          let* vs =
            opt_list_to_list_opt @@ List.map (value_type_infer rctx) vs
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
          Some (CRecord vs)#:rty
      | CField { rd; field } ->
          let lit = value_to_lit [%here] rd.x in
          let lit = (AField (lit_to_tlit lit, field))#:e.ty in
          let* rd = value_type_infer rctx rd in
          let rty = RtyBase { ou = Under; cty = mk_eq_lit_cty lit } in
          Some (CField { rd; field })#:rty
      | CLetE { rhs; lhs; body } ->
          let* rhs = term_type_infer rctx rhs in
          let lhs = lhs.x#:rhs.ty in
          let rctx' = Rctx.add_var rctx lhs in
          let* body = term_type_infer rctx' body in
          let rty = Rctx.diff_exists_rty [%here] rctx' rctx body.ty in
          Some (CLetE { rhs; lhs; body })#:rty
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
          let rctx' = Rctx.add_preds rctx poly_preds in
          (* let () = Printf.printf "appf_ty : %s\n" (layout_rty appf_ty) in *)
          let* retty =
            if is_over_arr_rty appf_ty then
              over_arrow_type_apply rctx' appf_ty apparg.x#:apparg_rty
            else if is_arr_arr_rty appf_ty then
              arrow_arrow_type_apply rctx' appf_ty apparg.x#:apparg_rty
            else
              let () =
                Printf.printf "cannot handle function type: %s\n"
                  (layout_rty appf_ty)
              in
              _die [%here]
          in
          (* let () = Printf.printf "retty : %s\n" (layout_rty retty) in *)
          let retty =
            remove_redundant_poly_pred
            @@ construct_poly_pred_rty (poly_preds, retty)
          in
          (* let () = Printf.printf "retty : %s\n" (layout_rty retty) in *)
          Some (CApp { appf; apparg = apparg' })#:retty
      | CAppOp { op; appopargs } ->
          let op = op.x#:(_find_in_ctx [%here] rctx op#->op_name_for_typectx) in
          let () = Printf.printf "op_ty : %s\n" (layout_rty op.ty) in
          let* appopargs =
            opt_list_to_list_opt
            @@ List.map
                 (fun v ->
                   let* v' = value_type_infer rctx v in
                   Some (v, v'))
                 appopargs
          in
          let* retty =
            List.fold_left
              (fun res (apparg, apparg') ->
                let* rty = res in
                over_arrow_type_apply rctx rty apparg.x#:apparg'.ty)
              (Some op.ty) appopargs
          in
          let () = Printf.printf "retty : %s\n" (layout_rty retty) in
          Some (CAppOp { op; appopargs = List.map snd appopargs })#:retty
      | CMatch { matched; match_cases } ->
          (* NOTE: we drop unreachable cases *)
          let match_cases =
            List.filter_map (match_case_type_infer rctx matched) match_cases
          in
          let unioned_ty =
            union_rtys
            @@ List.map (function CMatchcase { exp; _ } -> exp.ty) match_cases
          in
          let* matched = value_type_infer rctx matched in
          Some (CMatch { matched; match_cases })#:unioned_ty
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
          Some (CLetDeTuple { turhs = turhs'; tulhs; body })#:rty
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
        Some res.ty );
    res
  and term_type_check (rctx : rctx) (e : (Nt.t, Nt.t term) typed)
      (rty : Nt.t rty) : (Nt.t rty, Nt.t rty term) typed option =
    let () = pprint_typing_check_term rctx (e, rty) in
    match e.x with
    | CErr -> Some CErr#:rty
    | CLetDeTuple _ -> failwith "unimp"
    | CVal v ->
        let* v = value_type_check rctx v rty in
        Some (CVal v)#:v.ty
    | CApp _ | CAppOp _ | CMatch _ | CLetE _ | CRecord _ | CField _ ->
        let* e' = term_type_infer rctx e in
        if sub_rty rctx (e'.ty, rty) then Some e'.x#:rty
        else (
          _warinning_subtyping_error [%here] (e'.ty, rty);
          _warinning_typing_error [%here] (layout_typed_term e, rty);
          None)
  (* | CLetE { rhs; lhs; body } -> *)
  (*     let* rhs = term_type_infer rctx rhs in *)
  (*     let rctx', lhs = Rctx.add_var rctx lhs.x #: rhs.ty in *)
  (*     let* body = term_type_check rctx' body rty in *)
  (*     Some (CLetE { rhs; lhs; body }) #: rty *)
  and match_case_type_infer (rctx : rctx) (matched : (Nt.t, Nt.t value) typed)
      (x : Nt.t match_case) : Nt.t rty match_case option =
    match x with
    | CMatchcase { constructor; args; exp } ->
        let constructor_rty =
          _find_in_ctx [%here] rctx constructor#->dt_name_for_typectx
        in
        let () =
          Printf.printf "constructor.ty : %s\n" (layout_rty constructor_rty)
        in
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
          | _ ->
              Printf.printf "retty: %s\n" (layout_rty retty);
              _die [%here]
        in
        let rctx' =
          Rctx.add_vars rctx (args @ [ (Rename.fresh_var ())#:retty ])
        in
        let* exp' = term_type_infer rctx' exp in
        let exp' = exp'#=>(Rctx.diff_exists_rty [%here] rctx' rctx) in
        let () =
          pprint_typing_infer_match_case rctx constructor (exp, exp'.ty)
        in
        Some
          (CMatchcase
             { constructor = constructor.x#:constructor_rty; args; exp = exp' })
  in
  (value_type_check, term_type_check)

let value_type_check bctx ctx (value, rty) =
  (fst @@ type_check_group bctx) ctx value rty

let term_type_check bctx ctx (value, rty) =
  (snd @@ type_check_group bctx) ctx value rty
