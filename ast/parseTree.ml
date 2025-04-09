open Zutils
open Prop
open Sexplib.Std

let _return = "return"
let _bind = "bind"
let _fmap = "fmap"

type 't value =
  | VConst of constant
  | VVar of (('t, string) typed[@free])
  | VLam of {
      lamarg : (('t, string) typed[@bound]);
      body : ('t, 't term) typed;
    }
  | VFix of {
      fixname : (('t, string) typed[@bound]);
      fixarg : (('t, string) typed[@bound]);
      body : ('t, 't term) typed;
    }
  | VTuple of ('t, 't value) typed list

and 't term =
  | CErr
  | CVal of ('t, 't value) typed
  | CRecord of (string * ('t, 't value) typed) list
  | CField of { rd : ('t, 't value) typed; field : string }
  | CLetE of {
      rhs : ('t, 't term) typed;
      lhs : (('t, string) typed[@bound]);
      body : ('t, 't term) typed;
    }
  | CLetDeTuple of {
      turhs : ('t, 't value) typed;
      tulhs : (('t, string) typed list[@bound]);
      body : ('t, 't term) typed;
    }
  | CApp of { appf : ('t, 't value) typed; apparg : ('t, 't value) typed }
  | CAppOp of { op : ('t, op) typed; appopargs : ('t, 't value) typed list }
  | CMatch of {
      matched : ('t, 't value) typed;
      match_cases : 't match_case list;
    }

and 't match_case =
  | CMatchcase of {
      constructor : ('t, string) typed;
      args : (('t, string) typed list[@bound]);
      exp : ('t, 't term) typed;
    }
[@@deriving eq, ord, show, sexp]

type 't raw_term =
  | Var of (('t, string) typed[@free])
  | Const of constant
  | Lam of {
      lamarg : (('t, string) typed[@bound]);
      lambody : ('t, 't raw_term) typed;
    }
  | Err
  | Let of {
      if_rec : bool;
      rhs : ('t, 't raw_term) typed;
      lhs : (('t, string) typed list[@bound]);
      letbody : ('t, 't raw_term) typed;
    }
  | App of ('t, 't raw_term) typed * ('t, 't raw_term) typed list
  | AppOp of ('t, op) typed * ('t, 't raw_term) typed list
  | Ifte of
      ('t, 't raw_term) typed
      * ('t, 't raw_term) typed
      * ('t, 't raw_term) typed
  | Tuple of ('t, 't raw_term) typed list
  | Record of (string * ('t, 't raw_term) typed) list
  | Field of ('t, 't raw_term) typed * string
  | Match of {
      matched : ('t, 't raw_term) typed;
      match_cases : 't raw_match_case list;
    }

and 't raw_match_case =
  | Matchcase of {
      constructor : ('t, string) typed;
      args : (('t, string) typed list[@bound]);
      exp : ('t, 't raw_term) typed;
    }
[@@deriving eq, ord, show, sexp]

type constructor_declaration = { constr_name : string; argsty : Nt.nt list }
[@@deriving eq, ord, show, sexp]

type type_decl =
  | Decl_constructors of constructor_declaration list
  | Decl_record of (Nt.nt, string) typed list
[@@deriving eq, ord, show, sexp]

(* NOTE: v is default variable *)
let default_v = "v"

type 't cty = { nty : Nt.nt; phi : 't prop } [@@deriving eq, ord, show, sexp]
type ou = Over | Under [@@deriving eq, ord, show, sexp]

type 't rty =
  | RtyBase of { ou : ou; cty : 't cty }
  | RtyArr of { argrty : 't rty; arg : (string[@bound]); retty : 't rty }
  | RtyPolyType of { pt : string; rty : 't rty }
  | RtyPolyPred of { pred : ('t, string) typed; rty : 't rty }
[@@deriving eq, ord, show, sexp]

type captured = {
  captured_ts : string list;
  captured_preds : string list;
  captured_vars : string list;
}
[@@deriving eq, ord, show, sexp]

type 't item =
  | MTyDecl of {
      type_name : string;
      type_params : string list;
      type_decl : type_decl;
    }
  | MValDecl of ('t, string) typed
  | MMethodPred of ('t, string) typed
  | MAxiom of { name : string; tasks : string list; prop : 't prop }
  | MFuncImpRaw of {
      name : ('t, string) typed;
      if_rec : bool;
      body : ('t, 't raw_term) typed;
    }
  | MFuncImp of {
      name : ('t, string) typed;
      if_rec : bool;
      body : ('t, 't term) typed;
    }
  | MRty of { is_assumption : bool; name : string; rty : 't rty }
  | MLocalRty of {
      host_name : string;
      captured : captured;
      name : string;
      rty : 't rty;
    }
[@@deriving eq, ord, show, sexp]

open Typectx

type built_in_ctx = {
  builtin_ctx : Nt.nt rty ctx;
  cur_axiom_names : string list;
}

type rctx = {
  task_name : string;
  tyvar_ctx : string list;
  pred_ctx : Nt.t ctx;
  rty_ctx : Nt.t rty ctx;
  inv_ctx : Nt.nt rty ctx;
}
