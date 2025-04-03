include Ast
include Prop
include Frontend_opt
open Zutils
open Zdatatype

let layout_rtyed_var { x; ty } = spf "%s:%s" x (layout_rty ty)
let layout_rtyed_vars l = List.split_by_comma layout_rtyed_var l

let rec is_wf_rty (over_ctx, under_ctx) = function
  | RtyBase { ou = Over; _ } as rty -> is_close_rty (List.map fst over_ctx) rty
  | RtyBase { ou = Under; _ } as rty ->
      is_close_rty (List.map fst over_ctx @ List.map fst under_ctx) rty
  | RtyArr { arg; argrty; retty; _ } ->
      is_wf_rty (over_ctx, under_ctx) argrty
      && is_wf_rty (wf_ctx_add (over_ctx, under_ctx) arg#:argrty) retty
  | RtyPolyType { rty; _ } -> is_wf_rty (over_ctx, under_ctx) rty
  | RtyPolyPred { rty; _ } -> is_wf_rty (over_ctx, under_ctx) rty

and wf_ctx_add (over_ctx, under_ctx) { x; ty } =
  match ty with
  | RtyBase { ou = Over; cty } -> (over_ctx @ [ (x, cty) ], under_ctx)
  | RtyBase { ou = Under; cty } -> (over_ctx, under_ctx @ [ (x, cty) ])
  | RtyArr _ -> (over_ctx, under_ctx)
  | RtyPolyPred _ -> (over_ctx, under_ctx)
  | RtyPolyType _ ->
      let () = Printf.printf "poly type %s\n" (layout_rty ty) in
      _die_with [%here] (spf "poly type cannot be added into type context")

let build_wf_ctx (ctx : ('t rty, string) typed list) =
  List.fold_left wf_ctx_add ([], []) ctx

let instantiate_rty_by_nty loc rty nty =
  let open Nt in
  (* Printf.printf "try instantiate\n%s\nwith\n%s\n" (layout_rty rty) *)
  (*   (layout_nt nty); *)
  let subst_nt (id, t') t =
    let rec aux t =
      (* Printf.printf "subst [%s -> %s] in %s\n" id (layout_nt t') (show_nt t); *)
      match t with
      | Ty_unknown | Ty_any | Ty_uninter _ | Ty_enum _ -> t
      | Ty_var x ->
          (* Printf.printf "%s = %s --> %b\n" x id (streq x id); *)
          if streq x id then t' else t
      | Ty_poly (y, nt) ->
          if String.equal id y then Ty_poly (y, nt) else Ty_poly (y, aux nt)
      | Ty_arrow (t1, t2) -> Ty_arrow (aux t1, aux t2)
      | Ty_tuple xs -> Ty_tuple (List.map aux xs)
      | Ty_constructor (id, args) -> Ty_constructor (id, List.map aux args)
      | Ty_record l -> Ty_record (List.map (fun x -> x#=>aux) l)
    in
    aux t
  in
  let msubst_nt (m : t StrMap.t) =
    StrMap.fold (fun x ty -> subst_nt (x, ty)) m
  in
  (* let () = Printf.printf "erase rty: %s\n" (show_nt (erase_rty rty)) in *)
  (* let () = Printf.printf "erase rty: %s\n" (layout_nt (erase_rty rty)) in *)
  let pt, nty = Nt.lift_poly_tp nty in
  let pt', rty = lift_poly_rty rty in
  let bc, (_, _) =
    BoundConstraints.(add (empty (pt @ pt')) (nty, erase_rty rty))
  in
  let solution = type_unification StrMap.empty bc.cs in
  match solution with
  | None ->
      Printf.printf "cannot instantiate %s by %s\n" (layout_rty rty)
        (layout_nt nty);
      _die loc
  | Some sol ->
      Printf.printf "solution\n%s\n"
        (List.split_by_comma (fun (x, ty) -> spf "%s := %s" x (layout_nt ty))
        @@ StrMap.to_kv_list sol);
      let res = map_rty (msubst_nt sol) rty in
      Printf.printf "instantiated %s\n" (layout_rty res);
      (sol, construct_poly_rty (pt, res))
