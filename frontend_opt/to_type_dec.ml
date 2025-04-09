open Zutils
open OcamlParser
open Prop
open Parsetree
open Zdatatype
open Ast
open Sugar
open Common

let constructor_declaration_of_ocaml { pcd_name; pcd_args; _ } =
  let argsty =
    match pcd_args with
    | Pcstr_tuple cts -> List.map core_type_to_t cts
    | _ -> failwith "unimp complex type decl"
  in
  { constr_name = pcd_name.txt; argsty }

let of_ocamltypedec { ptype_name; ptype_params; ptype_kind; ptype_manifest; _ }
    =
  if is_basic_coverage_monad ptype_name.txt then
    (* Coverage Monad Definition *)
    None
  else
    let type_params =
      List.map
        (fun (ct, (_, _)) ->
          match core_type_to_t ct with
          | Nt.Ty_var name -> name
          | _ -> _die [%here])
        ptype_params
    in
    let mk_decl type_decl =
      MTyDecl { type_name = ptype_name.txt; type_params; type_decl }
    in
    match (ptype_kind, ptype_manifest) with
    | Ptype_variant cds, None ->
        let cds =
          Decl_constructors (List.map constructor_declaration_of_ocaml cds)
        in
        Some (mk_decl cds)
    | Ptype_record lds, None ->
        let lds =
          List.map
            (fun ld -> ld.pld_name.txt#:(Nt.core_type_to_t ld.pld_type))
            lds
        in
        Some (mk_decl (Decl_record lds))
    | _ -> failwith "unimp complex type decl"

let constructor_declaration_to_ocaml { constr_name; argsty } =
  {
    pcd_name = Location.mknoloc constr_name;
    pcd_vars = [];
    pcd_args = Pcstr_tuple (List.map Nt.t_to_core_type argsty);
    pcd_res = None;
    pcd_loc = Location.none;
    pcd_attributes = [];
  }

let label_declaration_to_ocaml x =
  {
    pld_name = Location.mknoloc x.x;
    pld_mutable = Asttypes.Immutable;
    pld_type = Nt.t_to_core_type x.ty;
    pld_loc = Location.none;
    pld_attributes = [];
  }

let to_ocamltypedec = function
  | MTyDecl { type_name; type_params; type_decl } ->
      let ptype_params =
        List.map
          (fun t ->
            ( Nt.t_to_core_type (Nt.Ty_var t),
              (Asttypes.NoVariance, Asttypes.NoInjectivity) ))
          type_params
      in
      let ptype_kind =
        match type_decl with
        | Decl_constructors cds ->
            Ptype_variant (List.map constructor_declaration_to_ocaml cds)
        | Decl_record l -> Ptype_record (List.map label_declaration_to_ocaml l)
      in
      {
        ptype_name = Location.mknoloc type_name;
        ptype_params;
        ptype_cstrs = [];
        ptype_kind;
        ptype_manifest = None;
        ptype_attributes = [];
        ptype_loc = Location.none;
        ptype_private = Asttypes.Public;
      }
  | _ -> _die [%here]

let layout_ocaml es =
  Oparse.string_of_structure
  @@ List.map
       (fun e ->
         {
           pstr_desc = Pstr_type (Asttypes.Recursive, [ e ]);
           pstr_loc = Location.none;
         })
       es

let layout_type_dec e = layout_ocaml [ to_ocamltypedec e ]
