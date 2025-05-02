val small_string : string gen
val frequency : int list -> (int -> 'a gen) -> 'a gen
val return : 'a -> 'a gen
val int_range : int -> int -> int gen
val string_size : int gen -> string gen
val ( >>= ) : 'a1 gen -> ('a1 -> 'a2 gen) -> 'a2 gen
val ( >|= ) : 'a1 gen -> ('a1 -> 'a2) -> 'a2 gen

let[@library] return (b1 : baseType) ?r:(x = ((true : [%v: 'b1]) [@over])) =
  M (v == x : [%v: 'b2])

let[@library] ( >>= ) (b1 : baseType) (b2 : baseType) (p1 : 'b1 -> bool)
    (p2 : 'b1 -> 'b2 -> bool) ?r:(_ = M (p1 v : [%v: 'b1]))
    ?r:(_ = fun ?r:(x = ((p1 v : [%v: 'b1]) [@over])) -> M (p2 x v : [%v: 'b2]))
    =
  M (fun ((x [@ex]) : 'b1) -> p1 x && p2 x v : [%v: 'b2])

let[@library] ( >|= ) (b1 : baseType) (b2 : baseType) (p1 : 'b1 -> bool)
    (p2 : 'b1 -> 'b2 -> bool) ?r:(_ = M (p1 v : [%v: 'b1]))
    ?r:(_ = fun ?r:(x = ((p1 v : [%v: 'b1]) [@over])) -> (p2 x v : [%v: 'b2])) =
  M (fun ((x [@ex]) : 'b1) -> p1 x && p2 x v : [%v: 'b2])

let[@library] int_range ?r:(a = ((true : [%v: int]) [@over]))
    ?r:(b = ((a <= v : [%v: int]) [@over])) =
  M (a <= v && v <= b : [%v: int])

let[@library] string_size (p1 : int -> bool) ?r:(_ = M (p1 v : [%v: int])) =
  M (fun ((x [@ex]) : int) -> p1 x && string_len v == x : [%v: string])

let[@library] frequency (b1 : baseType) (p1 : int -> 'b1 -> bool)
    ?r:(fq : int list)
    ?r:(_ =
        fun ?r:(x = ((0 <= v : [%v: int]) [@over])) -> M (p1 x v : [%v: 'b1])) =
  M (fun ((y [@ex]) : int) -> 0 <= y && y < list_len fq && p1 y v : [%v: 'b1])

type shell_header = { branch : Hash.t }
type operation = { shell : shell_header; proto : string }

let operation_proto_gen : string gen =
  let (len_gen : int gen) =
    frequency [ 9; 1 ] (fun (i : int) ->
        if i == 0 then return 0
        else if i == 1 then int_range 0 31
        else return Err)
  in
  string_size len_gen

let[@assert] operation_proto_gen = M (string_len v < 32 : [%v: string])

let operation_gen (block_hash_gen : Hash.t gen) : operation gen =
  block_hash_gen >>= fun (branch : Hash.t) ->
  operation_proto_gen >|= fun (proto : string) -> { shell = { branch }; proto }

let[@library] max_int = M (v == 2147483647 : [%v: int])

let[@library] small_list ?r:(_ = M (rational_zero_one v : [%v: int * int])) =
  M (rational_zero_one_list v && list_len v <= 100 : [%v: (int * int) list])

let[@library] oneofl (b1 : baseType) (p1 : 'b1 list -> bool)
    ?r:(l = ((p1 v : [%v: 'b1 list]) [@over])) =
  M (list_mem l v : [%v: 'b1])

let q_in_0_1 : (int * int) gen =
 fun () ->
  let (q : int) = int_range 1 (max_int ()) () in
  let (p : int) = int_range 0 q () in
  (p, q)

let[@assert] q_in_0_1 = M (rational_zero_one v : [%v: int * int])

type priority = High | Medium | Low of (int * int) list

let[@library] High = (is_high v : [%v: priority])
let[@library] Medium = (is_medium v : [%v: priority])

let[@library] Low =
 fun ?r:(l : (int * int) list) -> (is_low v l : [%v: priority])

let priority_gen : priority gen =
  oneofl [ High; Medium; Low [] ] >>= fun (top_prio_value : priority) ->
  match top_prio_value with
  | High -> return High
  | Medium -> return Medium
  | Low lowl ->
      small_list q_in_0_1 >|= fun (weights : (int * int) list) -> Low weights

let[@assert] priority_gen = M (wf_priority v : [%v: priority])
