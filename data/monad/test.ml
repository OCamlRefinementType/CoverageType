type 'a gen = unit -> 'a

(* Basic Monad Operators *)

let return (x : 'a) : 'a gen = fun () -> x

let bind (gen : 'a1 gen) (f : 'a1 -> 'a2 gen) : 'a2 gen =
 fun () -> f (gen ()) ()

let[@assert] return (b1 : baseType) ?r:(x = ((true : [%v: 'b1]) [@over])) =
  M (v == x : [%v: 'b1])
