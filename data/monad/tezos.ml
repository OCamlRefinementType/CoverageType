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

let[@library] int_bound ?r:(n = ((0 <= v : [%v: int]) [@over])) =
  M (0 <= v && v <= n : [%v: int])

let[@library] list_split_n (b1 : baseType) ?r:(xs : 'b1 list)
    ?r:(n = ((0 <= v && v <= list_len xs : [%v: int]) [@over])) =
  (list_concat (fst v) (snd v) xs : [%v: 'b1 list * 'b1 list])

let[@library] union (b1 : baseType) (p1 : 'b1 -> bool) (p2 : 'b1 -> bool)
    ?r:(_ = M (p1 v : [%v: 'b1])) ?r:(_ = M (p2 v : [%v: 'b1])) =
  M (p1 v || p2 v : [%v: 'b1])

let[@library] TezosLeaf =
 fun (a : baseType) ?r:(x : 'a) -> (tezos_leaf v x : [%v: 'a tezosTree])

let[@library] TezosNode1 =
 fun (a : baseType) ?r:(x : 'a) ?r:(t1 : 'a tezosTree) ->
  (tezos_node1 v x t1 : [%v: 'a tezosTree])

let[@library] TezosNode2 =
 fun (a : baseType) ?r:(x : 'a) ?r:(t1 : 'a tezosTree) ?r:(t2 : 'a tezosTree) ->
  (tezos_node2 v x t1 t2 : [%v: 'a tezosTree])

let rec tezos_tree_gen (blocks : 'a list) : 'a tezosTree option gen =
  match blocks with
  | [] -> return None
  | x :: xs ->
      if list_length xs == 0 then return (Some (TezosLeaf x))
      else
        let (g1 : 'a tezosTree option gen) =
          tezos_tree_gen xs >>= fun (sub : 'a tezosTree option) ->
          match sub with
          | None -> return (Some (TezosLeaf x))
          | Some subT -> return (Some (TezosNode1 (x, subT)))
        in
        let (g2 : 'a tezosTree option gen) =
          int_bound (list_length xs) >>= fun (n : int) ->
          let (left : 'a list), (right : 'a list) = list_split_n xs n in
          tezos_tree_gen left >>= fun (leftT : 'a tezosTree option) ->
          tezos_tree_gen right >>= fun (rightT : 'a tezosTree option) ->
          match leftT with
          | None -> (
              match rightT with
              | None -> return (Some (TezosLeaf x))
              | Some rt -> return (Some (TezosNode1 (x, rt))))
          | Some lt -> (
              match rightT with
              | None -> return (Some (TezosNode1 (x, lt)))
              | Some rt -> return (Some (TezosNode2 (x, lt, rt))))
        in
        union g1 g2

let[@assert] tezos_tree_gen (b1 : baseType) ?r:(blocks : 'b1 list) =
  M
    ((v == None && list_len blocks == 0) || fun ((vv [@ex]) : 'b1 tezosTree) ->
     v == Some vv && l2t_pre blocks vv
      : [%v: 'b1 tezosTree option])
