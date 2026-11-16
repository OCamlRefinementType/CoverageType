type prim_path = {
  data_type_decls : string option; [@default None]
  normal_typing : string;
  coverage_typing : string;
  axioms : string;
}
[@@deriving of_yojson { strict = true }]

type t = {
  prim_path : prim_path;
  log_tags : string list; [@default []]
  (* NOTE: after exists the constraints into the return type, the emptiness can be checked final stage;
   It may cause the more branch analysis. *)
  lazy_emptiness_check : bool; [@default false]
}
[@@deriving of_yojson { strict = true }]

include ConfigSection.Make (struct
  type nonrec t = t

  let name = "typechecker"
  let of_yojson = of_yojson
end)

(* Typechecking reads the zutils section too, so the pair is set together. *)
let bootstrap root =
  ZUtilsConfig.set (ZUtilsConfig.of_meta_config root);
  set (of_meta_config root)

let get_log_tags () = (get ()).log_tags
let lazy_emptiness_check () = (get ()).lazy_emptiness_check
