type prim_path = {
  data_type_decls : string option;
  normal_typing : string;
  coverage_typing : string;
  axioms : string;
}

type t = {
  prim_path : prim_path;
  log_tags : string list;
  lazy_emptiness_check : bool;
}

(* Populates the zutils + typechecker sections. *)
val bootstrap : Yojson.Safe.t -> unit
val get : unit -> t
val get_log_tags : unit -> string list
val lazy_emptiness_check : unit -> bool
