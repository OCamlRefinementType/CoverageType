(** Premitive type *)

let[@library] TT = (true : [%v: unit]) [@under]
let[@library] True = (v : [%v: bool]) [@under]
let[@library] False = (not v : [%v: bool]) [@under]
let[@library] None = fun (a : baseType) -> (v == None : [%v: 'a option])

let[@library] Some =
 fun (a : baseType) ?r:(x = ((true : [%v: 'a]) [@over])) ->
  (v == Some x : [%v: 'a option])

(** Arithmatic operators *)

let[@library] ( == ) =
 fun ?r:(a : int) ?r:(b : int) -> (iff v (a == b) : [%v: bool])

let[@library] ( != ) =
 fun ?r:(a : int) ?r:(b : int) -> (iff v (a != b) : [%v: bool])

let[@library] ( < ) =
 fun ?r:(a : int) ?r:(b : int) -> (iff v (a < b) : [%v: bool])

let[@library] ( > ) =
 fun ?r:(a : int) ?r:(b : int) -> (iff v (a > b) : [%v: bool])

let[@library] ( <= ) =
 fun ?r:(a : int) ?r:(b : int) -> (iff v (a <= b) : [%v: bool])

let[@library] ( >= ) =
 fun ?r:(a : int) ?r:(b : int) -> (iff v (a >= b) : [%v: bool])

let[@library] ( + ) = fun ?r:(a : int) ?r:(b : int) -> (v == a + b : [%v: int])
let[@library] ( - ) = fun ?r:(a : int) ?r:(b : int) -> (v == a - b : [%v: int])

let[@library] ( mod ) =
 fun ?r:(a : int) ?r:(b : int) -> (v == a mod b : [%v: int])

(** Builtin generators *)

let[@library] bool_gen = M (true : [%v: bool])
let[@library] int_gen = M (true : [%v: int])
let[@library] nat_gen = M (0 <= v : [%v: int])

let[@library] int_range_inc =
  let a = ((true : [%v: int]) [@over]) in
  let b = ((a <= v : [%v: int]) [@over]) in
  ((a <= v && v <= b : [%v: int]) [@under])

let[@library] int_range_inex =
  let a = ((true : [%v: int]) [@over]) in
  let b = ((a <= v : [%v: int]) [@over]) in
  ((a <= v && v < b : [%v: int]) [@under])

let[@library] increment =
  let n = ((true : [%v: int]) [@over]) in
  ((v == n + 1 : [%v: int]) [@under])

let[@library] decrement =
  let n = ((true : [%v: int]) [@over]) in
  ((v == n - 1 : [%v: int]) [@under])

let[@library] lt_eq_one =
  let s = ((true : [%v: int]) [@over]) in
  (iff v (s <= 1) && iff (not v) (s > 1) : [%v: bool])

let[@library] gt_eq_int_gen =
  let x = ((true : [%v: int]) [@over]) in
  ((true : [%v: int]) [@under])

let[@library] sizecheck =
  let x = ((true : [%v: int]) [@over]) in
  (iff v (x == 0) && iff (not v) (x > 0) : [%v: bool])

let[@library] subs =
  let s = ((true : [%v: int]) [@over]) in
  ((v == s - 1 : [%v: int]) [@under])

let[@library] dummy = (true : [%v: unit])

(** Datatypes and method predicates (needs to be stratificated) *)

(** lists *)

let[@library] Nil = fun (a : baseType) -> (list_len v == 0 : [%v: 'a list])

let[@library] Cons =
 fun (a : baseType) ?r:(x : 'a) ?r:(xs : 'a list) ->
  (hd v x && tl v xs : [%v: 'a list])

let[@library] list_mem =
 fun (a : baseType) ?r:(xs : 'a list) ?r:(x : 'a) ->
  (v == list_mem xs x : [%v: bool])

let[@library] list_length =
 fun (a : baseType) ?r:(xs : 'a list) -> (v == list_len xs : [%v: int])

let[@library] list_nth =
 fun (a : baseType) ?r:(xs : 'a list)
     ?r:(idx = ((0 <= v && v < list_len xs : [%v: int]) [@over])) ->
  (list_nth_pred xs idx v : [%v: 'a])

(** Aux functions *)

(** For frequency *)

let[@library] sum_fst_int =
 fun (a : baseType) ?r:(xs : (int * 'a) list) -> (0 <= v : [%v: int])

let[@library] choose_by_fq =
 fun ?r:(xs : int list) -> (0 <= v && v < list_len xs : [%v: int])

let[@library] char_of_int =
 fun ?r:(x : int) -> (x == char_to_int v : [%v: char])
