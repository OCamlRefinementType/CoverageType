type 'a cm = unit -> 'a

let return (x : 'a) : 'a cm = fun () -> x
let bind (gen : 'a1 cm) (f : 'a1 -> 'a2 cm) : 'a2 cm = fun () -> f (gen ()) ()
let fmap (f : 'a1 -> 'a2) (gen : 'a1 cm) : 'a2 cm = fun () -> f (gen ())

let fmap2 (f : 'a -> 'b -> 'c) (gen1 : 'a cm) (gen2 : unit -> 'b) : 'c cm =
 fun () -> f (gen1 ()) (gen2 ())

let union (gen1 : 'a cm) (gen2 : 'a cm) : 'a cm =
  bind bool_gen (fun (x : bool) -> if x then gen1 else gen2)

let fix (f : int -> (int -> 'b cm) -> 'b cm) : int -> 'b cm =
  let rec aux (m : int) : 'b cm = f m aux in
  aux

let[@assert] return (b1 : poly) ?r:(x = ((true : [%v: 'b1]) [@over])) =
  M (v == x : [%v: 'b2])

let[@assert] bind (b1 : poly) (b2 : poly) (p1 : 'b1 -> bool)
    (p2 : 'b1 -> 'b2 -> bool) ?r:(_ = M (p1 v : [%v: 'b1]))
    ?r:(_ = fun ?r:(x = ((p1 v : [%v: 'b1]) [@over])) -> M (p2 x v : [%v: 'b2]))
    =
  M (fun ((x [@ex]) : 'b1) -> p1 x && p2 x v : [%v: 'b2])

let[@assert] fmap (b1 : poly) (b2 : poly) (p1 : 'b1 -> bool)
    (p2 : 'b1 -> 'b2 -> bool)
    ?r:(_ = fun ?r:(x = ((p1 v : [%v: 'b1]) [@over])) -> (p2 x v : [%v: 'b2]))
    ?r:(_ = M (p1 v : [%v: 'b1])) =
  M (fun ((x [@ex]) : 'b1) -> p1 x && p2 x v : [%v: 'b2])

let[@assert] fmap2 (b1 : poly) (b2 : poly) (b3 : poly) (p1 : 'b1 -> bool)
    (p2 : 'b2 -> bool) (p3 : 'b1 -> 'b2 -> 'b3 -> bool)
    ?r:(_ =
        fun ?r:(x = ((p1 v : [%v: 'b1]) [@over]))
          ?r:(y = ((p2 v : [%v: 'b2]) [@over]))
        -> (p3 x y v : [%v: 'b3])) ?r:(_ = M (p1 v : [%v: 'b1]))
    ?r:(_ = M (p2 v : [%v: 'b2])) =
  M
    (fun ((x [@ex]) : 'b1) ((y [@ex]) : 'b2) -> p1 x && p2 y && p3 x y v
      : [%v: 'b3])

let[@assert] union (b1 : poly) (p1 : 'b1 -> bool) (p2 : 'b1 -> bool)
    ?r:(_ = M (p1 v : [%v: 'b1])) ?r:(_ = M (p2 v : [%v: 'b1])) =
  M (p1 v || p2 v : [%v: 'b1])

let[@assert] fix (b1 : poly) (p1 : int -> 'b1 -> bool)
    ?r:(_ =
        fun ?r:(m = ((0 <= v : [%v: int]) [@over]))
          ?r:(_ =
              fun ?r:(n = ((0 <= v && v < m : [%v: int]) [@over])) ->
                M (p1 n v : [%v: 'b1]))
        -> M (p1 m v : [%v: 'b1])) =
 fun ?r:(x = ((0 <= v : [%v: int]) [@over])) -> M (p1 x v : [%v: 'b1])

let[@assert? fix when ([ b1 ], [ p1 ], [])] aux
    ?r:(m = ((0 <= v : [%v: int]) [@over])) =
  M (p1 m v : [%v: 'b1])

(* let prog : int cm = *)
(*   bind int_gen (fun (x : int) -> if x >= 0 then return x else return Err) *)

(* let[@assert] prog = M (v >= 0 : [%v: int]) *)
