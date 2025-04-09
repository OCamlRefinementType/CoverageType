include Basic_typing
include Normalization
open Language
open Zutils

let parse file =
  ocaml_structure_to_items
  @@ OcamlParser.Oparse.parse_imp_from_file ~sourcefile:file

let _ctxs = ref None
let _log = Myconfig._log_preprocess

let predefined_files =
  [ "basic_typing.ml"; "refinement_typing.ml"; "axioms.ml" ]

let load_ctxs () =
  match !_ctxs with
  | Some ctxs -> ctxs
  | None ->
      let prim_path = Myconfig.get_prim_path () in
      let items =
        List.concat_map
          (fun file -> parse (spf "%s/%s" prim_path.predefined_path file))
          predefined_files
      in
      let alias = Type_alias.item_mk_type_alias_ctx items in
      let items = Type_alias.item_inline alias items in
      let basic_ctx, items = struct_check Typectx.emp items in
      let builtin_ctx = struct_mk_rty_ctx items in
      let axioms = struct_mk_axiom_ctx items in
      let bctx = { builtin_ctx; cur_axiom_names = [] } in
      let bctx = axiom_add_to_rights bctx axioms in
      let res = (alias, basic_ctx, bctx) in
      _ctxs := Some res;
      res

let load_basic_ctx () =
  let _, basic_ctx, _ = load_ctxs () in
  basic_ctx

let load_bctx () =
  let _, _, bctx = load_ctxs () in
  bctx

let load_alias () =
  let alias, _, _ = load_ctxs () in
  alias

let preproress source_file =
  let items = parse source_file in
  let items' = Type_alias.item_inline (load_alias ()) items in
  let alias = Type_alias.item_mk_type_alias_ctx items' in
  let items' = Type_alias.item_inline alias items' in
  (* let () = Pp.printf "@{<bold>result:@}\n%s\n" (layout_structure items) in *)
  (* let () = Pp.printf "@{<bold>result:@}\n%s\n" (layout_structure items') in *)
  (* let () = _die [%here] in *)
  let _, code = struct_check (load_basic_ctx ()) items' in
  (* let () = Pp.printf "@{<bold>result:@}\n%s\n" (layout_structure code) in *)
  normalize_structure code
