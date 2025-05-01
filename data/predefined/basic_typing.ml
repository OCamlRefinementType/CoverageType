(** Premitive type *)

type unit = TT
type bool = True | False
type 'a option = None | Some of 'a

type 'a tezosTree =
  | TezosLeaf of 'a
  | TezosNode1 of 'a * 'a tezosTree
  | TezosNode2 of 'a * 'a tezosTree * 'a tezosTree

(* NOTE: pair are builtin *)
(* val fst : 'a * 'b -> 'a *)
(* val snd : 'a * 'b -> 'b *)

(** Arithmatic operators *)

val ( == ) : 'a. 'a -> 'a -> bool
val ( != ) : 'a. 'a -> 'a -> bool
val ( < ) : int -> int -> bool
val ( <= ) : int -> int -> bool
val ( > ) : int -> int -> bool
val ( >= ) : int -> int -> bool
val ( + ) : int -> int -> int
val ( - ) : int -> int -> int
val ( mod ) : int -> int -> int
val not : bool -> bool
val ( && ) : bool -> bool -> bool
val ( || ) : bool -> bool -> bool
val char_to_int : char -> int
val char_is_digit : char -> bool
val char_le : char -> char -> bool

(** Builtin generators *)

val bool_gen : unit -> bool
val int_gen : unit -> int
val nat_gen : unit -> int
val int_range_inc : int -> int -> int
val int_range_inex : int -> int -> int
val increment : int -> int
val decrement : int -> int
val lt_eq_one : int -> bool
val gt_eq_int_gen : int -> int
val sizecheck : int -> bool
val subs : int -> int
val dummy : unit

(** Well-founded *)

val decreasing : 'a -> 'a -> bool

(** Datatypes and method predicates (needs to be stratificated) *)

(** string *)

(** string predicates *)

val string_len : string -> int

(** rational number *)

val rational_zero_one : int * int -> bool
val rational_zero_one_list : (int * int) list -> bool

(** priority *)

val wf_priority : priority -> bool
val is_high : priority -> bool
val is_medium : priority -> bool
val is_low : priority -> (int * int) list -> bool

(** tezosTree *)

val tezos_leaf : 'a tezosTree -> 'a -> bool
val tezos_node1 : 'a tezosTree -> 'a -> 'a tezosTree -> bool
val tezos_node2 : 'a tezosTree -> 'a -> 'a tezosTree -> 'a tezosTree -> bool

(** lists *)

type 'a list = Nil | Cons of 'a * 'a list

(** list predicates *)

val list_len : 'a list -> int
val list_nth_pred : 'a list -> int -> 'a -> bool
val hd : 'a list -> 'a -> bool
val tl : 'a list -> 'a list -> bool
val list_mem : 'a. 'a list -> 'a -> bool
val sorted : 'a list -> bool
val uniq : 'a list -> bool
val list_snd_mem : (int * 'a) list -> 'a -> bool (* for frequency *)
val list_swap : 'a list -> int -> int -> 'a list -> bool (* for shuffle *)
val list_same_mem : 'a list -> 'a list -> bool (* for shuffle *)
val list_concat : 'a list -> 'a list -> 'a list -> bool
val l2t_pre : 'a list -> 'a tezosTree -> bool
val list_index : 'a list -> int -> 'a -> bool (* for STLC *)

(** list to tree predicates *)

(** list functions *)

val list_length : 'a list -> int
val list_nth : 'a list -> int -> 'a

(** trees *)

type 'a tree = Leaf | Node of 'a * 'a tree * 'a tree

(** tree predicates *)

val depth : 'a tree -> int
val root : 'a tree -> 'a -> bool
val lch : 'a tree -> 'a tree -> bool
val rch : 'a tree -> 'a tree -> bool
val tree_mem : 'a tree -> 'a -> bool
val bst : 'a tree -> bool
val heap : 'a tree -> bool
val complete : 'a tree -> bool
val tree_num_node : 'a tree -> int

(** Stream *)

type 'a lazyty = Lazyty of 'a
type 'a stream = Streamnil | Streamlazycons of 'a * 'a stream lazyty

(** stream predicates *)

val forc : 'a stream lazyty -> 'a stream
val _forc : int -> int
val stream_len : 'a stream -> int
val stream_hd : 'a stream -> 'a -> bool
val stream_tl : 'a stream -> 'a stream -> bool

(** leftisthp *)

type 'a leftisthp =
  | Lhpleaf
  | Lhpnode of int * 'a * 'a leftisthp * 'a leftisthp

(** leftisthp predicates *)

val leftisthp_depth : 'a leftisthp -> int
val leftisthp_root : 'a leftisthp -> 'a -> bool
val leftisthp_rank : 'a leftisthp -> int -> bool
val leftisthp_lch : 'a leftisthp -> 'a leftisthp -> bool
val leftisthp_rch : 'a leftisthp -> 'a leftisthp -> bool

(** rbtree *)

type 'a rbtree = Rbtleaf | Rbtnode of bool * 'a rbtree * 'a * 'a rbtree

(** rbtree predicates *)

val num_black : 'a rbtree -> int
val rb_leaf : 'a rbtree -> bool
val rb_root : 'a rbtree -> 'a -> bool
val rb_root_color : 'a rbtree -> bool -> bool
val rb_lch : 'a rbtree -> 'a rbtree -> bool
val rb_rch : 'a rbtree -> 'a rbtree -> bool
val no_red_red : 'a rbtree -> bool

(** stlc *)

type stlc_ty = Stlc_ty_nat | Stlc_ty_arr of stlc_ty * stlc_ty

type stlc_term =
  | Stlc_const of int
  | Stlc_id of int
  | Stlc_app of stlc_term * stlc_term
  | Stlc_abs of stlc_ty * stlc_term

type stlc_measure = Measure of int * int

(** stlc predicates *)

val num_arr : stlc_ty -> int
val is_const : stlc_term -> bool
val is_var : stlc_term -> bool
val is_abs : stlc_term -> bool
val is_app : stlc_term -> bool
val typing : stlc_ty list -> stlc_term -> stlc_ty -> bool
val num_app : stlc_term -> int
val stlc_ty_nat : stlc_ty -> bool
val stlc_ty_arr1 : stlc_ty -> stlc_ty -> bool
val stlc_ty_arr2 : stlc_ty -> stlc_ty -> bool
val stlc_const : stlc_term -> int -> bool
val stlc_id : stlc_term -> int -> bool
val stlc_app1 : stlc_term -> stlc_term -> bool
val stlc_app2 : stlc_term -> stlc_term -> bool
val stlc_abs_ty : stlc_term -> stlc_ty -> bool
val stlc_abs_body : stlc_term -> stlc_term -> bool

val stlc_measure : stlc_ty -> int -> int -> bool
(** Aux functions *)

val sum_fst_int : (int * 'a) list -> int (* for frequency *)
val choose_by_fq : int list -> int (* for frequency *)
val char_of_int : int -> char
val swap : 'a list -> int -> int -> 'a list (* for shuffle *)
