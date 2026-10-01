open Zdatatype

(* An inline test's cwd is its stanza's build dir, e.g. [_build/default/test/fast],
   two levels below the project root. *)
let project_root = Filename.dirname (Filename.dirname (Sys.getcwd ()))

let run_test source_file =
  Statistic.clear ();
  Sys.chdir project_root;
  let cfg_root = Yojson.Safe.from_file "test/meta-config.json" in
  TypecheckerConfig.bootstrap cfg_root;
  let code = Preprocess.preprocess [ source_file ] in
  let _, passed, failed = Typing.struc_check (Preprocess.load_bctx ()) code in
  Printf.printf "passing: %s\n" (List.split_by_comma Fun.id passed);
  Printf.printf "failing: %s\n" (List.split_by_comma Fun.id failed)
