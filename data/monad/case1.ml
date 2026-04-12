val bind : (unit -> 'a) -> ('a -> unit -> 'b) -> unit -> 'b

let[@library] bind (b1 : baseType) (b2 : baseType) (p1 : 'b1 -> bool)
    (p2 : 'b1 -> 'b2 -> bool) ?r:(_ = M (p1 v : [%v: 'b1]))
    ?r:(_ = fun ?r:(x = ((p1 v : [%v: 'b1]) [@over])) -> M (p2 x v : [%v: 'b2]))
    =
  M (fun ((x [@ex]) : 'b1) -> p1 x && p2 x v : [%v: 'b2])

(* let union (g1 : unit -> int) (g2 : unit -> int) : unit -> int = *)
(*   let (x : bool) = bool_gen () in *)
(*   if x then g1 else g2 *)

(* let[@assert] union *)
(*     ?l:(u1 = *)
(*         fun ?l:(tmp1 = ((true : [%v: unit]) [@over])) -> *)
(*           ((v == 1 : [%v: int]) [@under])) *)
(*     ?l:(u2 = *)
(*         fun ?l:(tmp2 = ((true : [%v: unit]) [@over])) -> *)
(*           ((v == 2 : [%v: int]) [@under])) = *)
(*  fun ?l:(tmp2 = ((true : [%v: unit]) [@over])) -> *)
(*   ((v == 2 : [%v: int]) [@under]) *)

let union (g1 : unit -> int) (g2 : unit -> int) : unit -> int =
  bind bool_gen (fun (x : bool) -> if x then g1 else g2)

let[@assert] union
    ?l:(u1 =
        fun ?l:(tmp1 = ((true : [%v: unit]) [@over])) ->
          ((v == 1 : [%v: int]) [@under]))
    ?l:(u2 =
        fun ?l:(tmp2 = ((true : [%v: unit]) [@over])) ->
          ((v == 2 : [%v: int]) [@under])) =
 fun ?l:(tmp2 = ((true : [%v: unit]) [@over])) ->
  ((v == 2 : [%v: int]) [@under])
