open Language
open Zutils
open Sugar
open Typectx
open Auxtyping

let _log = Myconfig._log_typing

let mk_self_wf_dec x =
  let open Prop in
  if Nt.equal_nt x.ty Nt.int_ty then
    let lt = "<"#:Nt.(construct_arr_tp ([ int_ty; int_ty ], bool_ty)) in
    lit_to_prop (AAppOp (lt, List.map tvar_to_lit [ default_v#:x.ty; x ]))
  else _failatwith [%here] "unimp"

module Rctx = struct
  type rctx = {
    tyvar_ctx : string list;
    pred_ctx : Nt.t ctx;
    rty_ctx : Nt.t rty ctx;
    inv_ctx : Nt.nt rty ctx;
  }

  let emp tyvar_ctx invs =
    { tyvar_ctx; pred_ctx = emp; rty_ctx = emp; inv_ctx = ctx_from_list invs }

  (* let to_ctx_g_v_pair ctx = *)
  (*   let rec aux (gctx, ctx) l = *)
  (*     match l with *)
  (*     | [] -> (gctx, ctx) *)
  (*     | x :: l -> *)
  (*         let gvars, rty = destruct_grty x.ty in *)
  (*         let gctx = Typectx.add_to_rights gctx gvars in *)
  (*         let ctx = Typectx.add_to_right ctx x.x#:rty in *)
  (*         aux (gctx, ctx) l *)
  (*   in *)
  (*   Typectx.(aux (emp, emp) ctx) *)

  let to_ctx { rty_ctx; _ } = rty_ctx
  (* let gctx, ctx = to_ctx_g_v_pair (Typectx.ctx_to_list ctx) in *)
  (* Typectx.concat gctx ctx *)

  let add_tvar rctx x =
    _assert [%here] "die" (not (List.exists (String.equal x) rctx.tyvar_ctx));
    { rctx with tyvar_ctx = rctx.tyvar_ctx @ [ x ] }

  let add_pred rctx x = { rctx with pred_ctx = add_to_right rctx.pred_ctx x }
  let add_preds res l = List.fold_left add_pred res l
  let add_var rctx x = { rctx with rty_ctx = add_to_right rctx.rty_ctx x }
  let add_vars res l = List.fold_left add_var res l

  (* let diff_exists_rty_opt ctx1 ctx2 rty = *)
  (*   let* ctx = subtract_opt (equal_rty Nt.equal_nt) ctx1 ctx2 in *)
  (*   let gvars, vars = map2 Typectx.ctx_to_list @@ to_ctx_g_v_pair ctx in *)
  (*   let _ = *)
  (*     _log @@ fun () -> *)
  (*     Pp.printf "exists [%s], [%s] into %s\n" (layout_rtyed_vars gvars) *)
  (*       (layout_rtyed_vars vars) (layout_rty rty) *)
  (*   in *)
  (*   Some (construct_grty gvars @@ exists_rtys vars rty) *)

  let diff_exists_rty_opt rctx1 rctx2 rty =
    _assert [%here] "die"
      (List.equal String.equal rctx1.tyvar_ctx rctx2.tyvar_ctx);
    let _ =
      _log @@ fun () ->
      Pp.printf "%s\n - \n%s\n"
        (Typectx.layout_ctx layout_rty rctx1.rty_ctx)
        (Typectx.layout_ctx layout_rty rctx2.rty_ctx)
    in
    let* vars =
      subtract_opt (equal_rty Nt.equal_nt) rctx1.rty_ctx rctx2.rty_ctx
    in
    let _ =
      _log @@ fun () ->
      Pp.printf "exists [%s] into %s\n" (layout_rtyed_vars vars)
        (layout_rty rty)
    in
    Some (exists_rtys vars rty)

  let diff_exists_rty loc ctx1 ctx2 rty =
    match diff_exists_rty_opt ctx1 ctx2 rty with
    | None -> _die loc
    | Some rty -> rty

  open Zdatatype

  let pprint { tyvar_ctx; pred_ctx; rty_ctx; inv_ctx } () =
    Pp.printf "@{<bold>Poly Vars:@} %s\n" (StrList.to_string tyvar_ctx);
    Pp.printf "@{<bold>Poly Preds:@} %s\n"
      (Typectx.layout_ctx Nt.layout pred_ctx);
    Pp.printf "@{<bold>Invariants:@}\n";
    Typectx.pprint_ctx layout_rty inv_ctx;
    Pp.printf "\n@{<bold>Refinement Type Ctx:@}\n";
    Typectx.pprint_ctx layout_rty rty_ctx;
    print_newline ()
end

open Rctx

let _warinning_subtyping_error loc (rty1, rty2) =
  _log @@ fun _ ->
  Pp.printf "@{<bold>Type Error at %s:@} %s <: %s\n" (pos_to_string loc)
    (layout_rty rty1) (layout_rty rty2)

let _warinning_nonemptiness_error loc rty1 =
  _log @@ fun _ ->
  Pp.printf "@{<bold>Type Error at %s:@} %s is empty type\n" (pos_to_string loc)
    (layout_rty rty1)

let _warinning_typing_error loc (str, rty) =
  _log @@ fun _ ->
  Pp.printf "@{<bold>Type Error at %s:@} %s : %s\n" (pos_to_string loc) str
    (layout_rty rty)

let pprint_typing_check_term rctx (e, ty) =
  _log @@ pprint_typing_check (pprint rctx) (layout_typed_term e, layout_rty ty)

let pprint_typing_infer_term_before rctx e =
  _log @@ pprint_typing_infer (pprint rctx) (layout_typed_term e, "??")

let layout_rty_opt res =
  match res with Some res -> layout_rty res | None -> "None"

let pprint_typing_infer_term_after rctx (e, ty) =
  _log
  @@ pprint_typing_infer (pprint rctx) (layout_typed_term e, layout_rty_opt ty)

let pprint_typing_check_value rctx (e, ty) =
  _log @@ pprint_typing_check (pprint rctx) (layout_typed_value e, layout_rty ty)

let pprint_typing_infer_value_before rctx e =
  _log @@ pprint_typing_infer (pprint rctx) (layout_typed_value e, "??")

let pprint_typing_infer_value_after rctx (e, res) =
  _log
  @@ pprint_typing_infer (pprint rctx)
       ( layout_typed_value e,
         match res with Some res -> layout_rty res.ty | None -> "None" )

let pprint_typing_subtyping rctx (rty1, rty2) =
  _log @@ pprint_subtyping (pprint rctx) (rty1, rty2)

let pprint_typing_infer_match_case rctx constr (e, rty) =
  (_log @@ fun _ -> Pp.printf "@{<bold>Infer from match case %s:@}\n" constr.x);
  _log @@ pprint_typing_infer (pprint rctx) (layout_typed_term e, layout_rty rty)

let rec lookup_ctxs ctxs id =
  match ctxs with
  | [] -> None
  | ctx :: ctxs -> (
      match get_opt ctx id with
      | Some res -> Some res
      | None -> lookup_ctxs ctxs id)

(** Debug *)
