let bind (gen : unit -> 'a1) (f : 'a1 -> unit -> 'a2) (u : unit) : 'a2 =
  f (gen ()) ()

let[@assert] bind (b1 : poly) (b2 : poly) (p1 : 'b1 -> bool)
    (p2 : 'b1 -> 'b2 -> bool) ?r:(tmp = M (p1 v : [%v: 'b1]))
    ?r:(tmp =
        fun ?r:(x = ((p1 v : [%v: 'b1]) [@over])) -> M (p2 x v : [%v: 'b2])) =
  M (fun ((x [@ex]) : 'b1) -> p1 x && p2 x v : [%v: 'b2])

let fmap (gen : unit -> 'a1) (f : 'a1 -> 'a2) (u : unit) : 'a2 = f (gen ())

let[@assert] fmap (b1 : poly) (b2 : poly) (p1 : 'b1 -> bool)
    (p2 : 'b1 -> 'b2 -> bool) ?r:(tmp = M (p1 v : [%v: 'b1]))
    ?r:(tmp = fun ?r:(x = ((p1 v : [%v: 'b1]) [@over])) -> (p2 x v : [%v: 'b2]))
    =
  M (fun ((x [@ex]) : 'b1) -> p1 x && p2 x v : [%v: 'b2])

let return (x : 'a) (u : unit) : 'a = x

let[@assert] return (b1 : poly) ?r:(x = ((true : [%v: 'b1]) [@over])) =
  M (v == x : [%v: 'b2])

let prog : unit -> int =
  bind int_gen (fun (x : int) -> if x >= 0 then return x else return Err)

let[@assert] prog = M (v >= 0 : [%v: int])
