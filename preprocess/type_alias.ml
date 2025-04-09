open Language
open Zutils
open Zdatatype

let _log = Myconfig._log_preprocess

let inline_record { x; ty = args, record_ty } =
  let f ts =
    let m = StrMap.of_list @@ _safe_combine [%here] args ts in
    let record_ty = Nt.msubst_nt m record_ty in
    record_ty
  in
  Nt.subst_constructor_nt (x, f)

let self_inline l =
  let rec aux l =
    match l with
    | [] -> []
    | decl :: l ->
        let l =
          List.map
            (fun { x; ty = args, record_ty } ->
              { x; ty = (args, inline_record decl record_ty) })
            l
        in
        decl :: aux l
  in
  aux l

let item_mk_type_alias_ctx items =
  let f e =
    match e with
    | MTyDecl { type_name; type_params; type_decl = Decl_record fds } ->
        let record_type = Nt.mk_record (Some type_name) fds in
        [ type_name#:(type_params, record_type) ]
    | MTyDecl _ -> []
    | MValDecl _ -> []
    | MMethodPred _ -> []
    | MAxiom _ -> []
    | MRty _ -> []
    | MLocalRty _ -> []
    | MFuncImpRaw _ | MFuncImp _ -> _failatwith [%here] "not predefine"
  in
  let l = List.concat_map f items in
  self_inline l

let item_inline decls items =
  let minline = List.fold_right inline_record decls in
  let f e =
    match e with
    | MTyDecl { type_name; type_params; type_decl = Decl_constructors decls } ->
        let decls =
          List.map
            (fun { constr_name; argsty } ->
              { constr_name; argsty = List.map minline argsty })
            decls
        in
        let res =
          MTyDecl
            { type_name; type_params; type_decl = Decl_constructors decls }
        in
        Some res
    | MTyDecl { type_name; type_params; type_decl = Decl_record fds } ->
        (* if List.exists (fun x -> String.equal type_name x.x) decls then Some e *)
        (* else *)
        let fds = List.map (fun x -> x#=>minline) fds in
        let res =
          MTyDecl { type_name; type_params; type_decl = Decl_record fds }
        in
        Some res
    | MValDecl x -> Some (MValDecl x#=>minline)
    | MMethodPred x -> Some (MMethodPred x#=>minline)
    | MAxiom { name; tasks; prop } ->
        Some (MAxiom { name; tasks; prop = map_prop minline prop })
    | MLocalRty { host_name; name; rty; captured } ->
        let rty = map_rty minline rty in
        Some (MLocalRty { host_name; name; rty; captured })
    | MRty { is_assumption; name; rty } ->
        let rty = map_rty minline rty in
        Some (MRty { is_assumption; name; rty })
    | MFuncImpRaw { name; if_rec; body } ->
        let name = name#=>minline in
        let body = typed_map_raw_term minline body in
        Some (MFuncImpRaw { name; if_rec; body })
    | MFuncImp _ -> _failatwith [%here] "die"
  in
  List.filter_map f items

let%test "inline_alias" =
  let () =
    Myconfig.meta_config_path :=
      "/Users/zhezzhou/workspace/CoverageType/meta-config.json"
  in
  let test_file =
    "/Users/zhezzhou/workspace/CoverageType/data/inline_test/alias.ml"
  in
  let items =
    ocaml_structure_to_items
    @@ OcamlParser.Oparse.parse_imp_from_file ~sourcefile:test_file
  in
  let () = Pp.printf "@{<bold>Parse:@}\n%s\n" (layout_structure items) in
  let alias = item_mk_type_alias_ctx items in
  let items = item_inline alias items in
  let () = Pp.printf "@{<bold>Result:@}\n%s\n" (layout_structure items) in
  false
