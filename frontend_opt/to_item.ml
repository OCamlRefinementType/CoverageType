open Zutils
open OcamlParser
open Oparse
open Mutils
open Prop
open Parsetree
open Zdatatype
open Ast
open Sugar
open To_rty
open To_raw_term
open Common

(* NOTE: The top level normal type need to be closed by Nt.close_poly_nt *)
let ocaml_structure_item_to_item structure =
  match structure.pstr_desc with
  | Pstr_primitive { pval_name; pval_type; pval_prim; pval_attributes; _ } ->
      let t = Nt.close_poly_nt [%here] (core_type_to_t pval_type) in
      Some
        (if String.equal pval_name.txt "method_predicates" then
           let mp = List.nth pval_prim 0 in
           MMethodPred mp#:t
         else
           match pval_attributes with
           | [ x ] when String.equal x.attr_name.txt "method_pred" ->
               MMethodPred pval_name.txt#:t
           | _ -> MValDecl pval_name.txt#:t)
  | Pstr_type (_, [ type_dec ]) -> To_type_dec.of_ocamltypedec type_dec
  | Pstr_value (flag, [ value_binding ]) ->
      Some
        (let name = Prop.typed_id_of_pattern value_binding.pvb_pat in
         let name, ty = (name.x, desugar_basic_coverage_monad name.ty) in
         match value_binding.pvb_attributes with
         | [ x ] -> (
             match x.attr_name.txt with
             | "axiom" ->
                 let tasks =
                   match x.attr_payload with
                   | PStr [] -> []
                   | PPat (pat, None) -> Prop.tuple_id_of_pattern pat
                   | _ -> _die [%here]
                 in
                 MAxiom
                   { name; tasks; prop = prop_of_expr value_binding.pvb_expr }
             | "assert" -> (
                 let rty = rty_of_expr value_binding.pvb_expr in
                 match x.attr_payload with
                 | PStr [] -> MRty { is_assumption = false; name; rty }
                 | PPat (pat, Some e) ->
                     let host_name = id_of_pattern pat in
                     let e = typed_raw_term_of_expr e in
                     let captured =
                       match raw_term_to_tuple raw_term_to_str_list e with
                       | [] -> mk_capture [] [] []
                       | [ a ] -> mk_capture a [] []
                       | [ a; b ] -> mk_capture a b []
                       | [ a; b; c ] -> mk_capture a b c
                       | _ -> _die [%here]
                     in
                     MLocalRty { host_name; name; captured; rty }
                 | PStr _ -> _die_with [%here] "Pstr"
                 | PSig _ -> _die_with [%here] "Psig"
                 | PTyp _ -> _die_with [%here] "PTyp"
                 | PPat _ -> _die_with [%here] "PPat")
             | "library" | "assume" ->
                 let rty = rty_of_expr value_binding.pvb_expr in
                 MRty { is_assumption = true; name; rty }
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
      let () = Printf.printf "%s\n" (string_of_structure [ structure ]) in
      _failatwith [%here] "translate not a func_decl"

let ocaml_structure_to_items structure =
  List.filter_map ocaml_structure_item_to_item structure

let layout_item = function
  | MTyDecl _ as item -> To_type_dec.layout_type_dec item
  | MMethodPred x -> spf "val[@method_predicate] %s: %s" x.x @@ Nt.layout x.ty
  | MValDecl x -> spf "val %s: %s" x.x @@ Nt.layout x.ty
  | MAxiom { name; prop; tasks } ->
      spf "let[@axiom ? (%s)] %s = %s" name (StrList.to_string tasks)
        (layout_prop prop)
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
  | MLocalRty { name; rty; _ } ->
      spf "let[@assert] %s = %s" name (layout_rty rty)

let layout_structure l = spf "%s\n" (List.split_by "\n" layout_item l)
