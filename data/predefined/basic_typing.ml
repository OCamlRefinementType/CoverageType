(** Premitive type *)

type unit = TT
type bool = True | False
type 'a option = None | Some of 'a

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

(** Datatypes and method predicates (needs to be stratificated) *)

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
val list_repeat : 'a list -> bool (* for repeat *)

(** list functions *)

val list_length : 'a list -> int
val list_nth : 'a list -> int -> 'a

(** Aux functions *)

val sum_fst_int : (int * 'a) list -> int (* for frequency *)
val choose_by_fq : int list -> int (* for frequency *)
val char_of_int : int -> char
