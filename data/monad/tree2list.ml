let[@library] fmap (b1 : baseType) (b2 : baseType) (p1 : 'b1 -> bool)
    (p2 : 'b1 -> 'b2 -> bool)
    ?r:(_ = fun ?r:(x = ((p1 v : [%v: 'b1]) [@over])) -> (p2 x v : [%v: 'b2]))
    ?r:(_ = M (p1 v : [%v: 'b1])) =
  M (fun ((x [@ex]) : 'b1) -> p1 x && p2 x v : [%v: 'b2])

let[@library] tree_num_node ?l:(tr = ((true : [%v: int tree]) [@over])) =
  (v == tree_num_node tr : [%v: int]) [@under]

let[@library] list_concat ?l:(l1 = ((true : [%v: int list]) [@over]))
    ?l:(l2 = ((true : [%v: int list]) [@over])) =
  (list_len v == list_len l1 + list_len l2 : [%v: int list]) [@under]

(* let rec flatten (n : int) (tr : int tree) : int list = *)
(*   match tr with *)
(*   | Leaf -> [] *)
(*   | Node (x, lt, rt) -> *)
(*       let (l1 : int list) = flatten 0 lt in *)
(*       let (l2 : int list) = flatten (n - 1) rt in *)
(*       x :: list_concat l1 l2 *)

let rec flatten (n : int) (tr : int tree) : int list =
  match tr with
  | Leaf -> []
  | Node (x, lt, rt) ->
      let (l2 : int list) = flatten (n - 1) rt in
      x :: l2

let[@assert] flatten ?l:(n = ((v >= 0 : [%v: int]) [@over]))
    ?l:(tr = ((n == tree_num_node v : [%v: int tree]) [@over])) =
  (list_len v == n : [%v: int list]) [@under]

(* let[@library] flatten ?l:(n = ((v >= 0 : [%v: int]) [@over])) *)
(*     ?l:(tr = ((tree_num_node v n : [%v: int tree]) [@under])) = *)
(*   (list_len v == n : [%v: int list]) [@under] *)

let list_gen (tree_gen : unit -> int tree) : unit -> int list =
  fmap
    (fun (tr : int tree) ->
      let (res : int list) = flatten (tree_num_node tr) tr in
      res)
    tree_gen

let[@assert] list_gen
    ?l:(u1 =
        fun ?l:(tmp1 = ((true : [%v: unit]) [@over])) ->
          ((true : [%v: int tree]) [@under])) =
 fun ?l:(tmp2 = ((true : [%v: unit]) [@over])) ->
  ((true : [%v: int list]) [@under])
