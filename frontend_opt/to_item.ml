open Zutils
open OcamlParser
open Mutils
open Prop
open Parsetree
open Zdatatype
open Ast
open Sugar
open To_rty
open To_raw_term

let ocaml_structure_item_to_item structure =
  match structure.pstr_desc with
  | Pstr_primitive { pval_name; pval_type; pval_prim; pval_attributes; _ } ->
      let t = Nt.close_poly_nt [%here] (Nt.core_type_to_t pval_type) in
      Some
        (if String.equal pval_name.txt "method_predicates" then
           let mp = List.nth pval_prim 0 in
           MMethodPred mp#:t
         else
           match pval_attributes with
           | [ x ] when String.equal x.attr_name.txt "method_pred" ->
               MMethodPred pval_name.txt#:t
           | _ -> MValDecl pval_name.txt#:t)
  | Pstr_type (_, [ type_dec ]) -> Some (To_type_dec.of_ocamltypedec type_dec)
  | Pstr_value (flag, [ value_binding ]) ->
      Some
        (let name = Prop.typed_id_of_pattern value_binding.pvb_pat in
         let name, ty = (name.x, name.ty) in
         match value_binding.pvb_attributes with
         | [ x ] -> (
             match x.attr_name.txt with
             | "axiom" ->
                 MAxiom { name; prop = prop_of_expr value_binding.pvb_expr }
             | "assert" ->
                 MRty
                   {
                     is_assumption = false;
                     name;
                     rty = rty_of_expr value_binding.pvb_expr;
                   }
             | "library" | "assume" ->
                 MRty
                   {
                     is_assumption = true;
                     name;
                     rty = rty_of_expr value_binding.pvb_expr;
                   }
             | _ ->
                 _failatwith [%here]
                   "syntax error: non known rty kind, not axiom | assert | \
                    library")
         | [] ->
             let body = typed_raw_term_of_expr value_binding.pvb_expr in
             (* let () = Printf.printf "if_rec: %b\n" (get_if_rec flag) in *)
             (* let () = failwith "end" in *)
             let ty =
               if Nt.is_unkown ty then
                 Nt.close_poly_nt [%here] @@ __get_lam_term_ty [%here] body.x
               else ty
             in
             MFuncImpRaw
               { name = name#:ty; if_rec = get_if_rec flag; body = body.x#:ty }
         | _ -> _failatwith [%here] "wrong syntax")
  | Pstr_attribute _ -> None
  | _ ->
      let () =
        Printf.printf "%s\n" (Pprintast.string_of_structure [ structure ])
      in
      _failatwith [%here] "translate not a func_decl"

let ocaml_structure_to_items structure =
  List.filter_map ocaml_structure_item_to_item structure

let layout_item = function
  | MTyDecl _ as item -> To_type_dec.layout_type_dec item
  | MMethodPred x -> spf "val[@method_predicate] %s: %s" x.x @@ Nt.layout x.ty
  | MValDecl x -> spf "val %s: %s" x.x @@ Nt.layout x.ty
  | MAxiom { name; prop } -> spf "let[@axiom] %s = %s" name (layout_prop prop)
  | MFuncImpRaw { name; if_rec; body } ->
      spf "let %s%s = %s"
        (if if_rec then "rec " else "")
        name.x
        (layout_typed_raw_term body)
  | MFuncImp { name; if_rec; body } ->
      spf "let %s%s = %s"
        (if if_rec then "rec " else "")
        name.x
        (denormalize_term body |> layout_typed_raw_term)
  | MRty { is_assumption = false; name; rty } ->
      spf "let[@assert] %s = %s" name (layout_rty rty)
  | MRty { is_assumption = true; name; rty } ->
      spf "let[@library] %s = %s" name (layout_rty rty)

let layout_structure l = spf "%s\n" (List.split_by "\n" layout_item l)
