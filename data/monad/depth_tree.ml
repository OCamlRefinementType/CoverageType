type 'a gen = unit -> 'a

(* Basic Monad Operators *)

let return (x : 'a) : 'a gen = fun () -> x

let bind (gen : 'a1 gen) (f : 'a1 -> 'a2 gen) : 'a2 gen =
 fun () -> f (gen ()) ()

let[@assert] return (b1 : baseType) ?r:(x = ((true : [%v: 'b1]) [@over])) =
  M (v == x : [%v: 'b2])

let[@assert] bind (b1 : baseType) (b2 : baseType) (p1 : 'b1 -> bool)
    (p2 : 'b1 -> 'b2 -> bool) ?r:(_ = M (p1 v : [%v: 'b1]))
    ?r:(_ = fun ?r:(x = ((p1 v : [%v: 'b1]) [@over])) -> M (p2 x v : [%v: 'b2]))
    =
  M (fun ((x [@ex]) : 'b1) -> p1 x && p2 x v : [%v: 'b2])

(* Monad Operators *)

let fmap (f : 'a1 -> 'a2) (gen : 'a1 gen) : 'a2 gen = fun () -> f (gen ())

let fmap2 (f : 'a -> 'b -> 'c) (gen1 : 'a gen) (gen2 : unit -> 'b) : 'c gen =
 fun () -> f (gen1 ()) (gen2 ())

let union (gen1 : 'a gen) (gen2 : 'a gen) : 'a gen =
  bind bool_gen (fun (x : bool) -> if x then gen1 else gen2)

let fix (f : int -> (int -> 'b gen) -> 'b gen) : int -> 'b gen =
  let rec aux (m : int) : 'b gen = f m aux in
  aux

let[@assert] fmap (b1 : baseType) (b2 : baseType) (p1 : 'b1 -> bool)
    (p2 : 'b1 -> 'b2 -> bool)
    ?r:(_ = fun ?r:(x = ((p1 v : [%v: 'b1]) [@over])) -> (p2 x v : [%v: 'b2]))
    ?r:(_ = M (p1 v : [%v: 'b1])) =
  M (fun ((x [@ex]) : 'b1) -> p1 x && p2 x v : [%v: 'b2])

let[@assert] fmap2 (b1 : baseType) (b2 : baseType) (b3 : baseType)
    (p1 : 'b1 -> bool) (p2 : 'b2 -> bool) (p3 : 'b1 -> 'b2 -> 'b3 -> bool)
    ?r:(_ =
        fun ?r:(x = ((p1 v : [%v: 'b1]) [@over]))
          ?r:(y = ((p2 v : [%v: 'b2]) [@over]))
        -> (p3 x y v : [%v: 'b3])) ?r:(_ = M (p1 v : [%v: 'b1]))
    ?r:(_ = M (p2 v : [%v: 'b2])) =
  M
    (fun ((x [@ex]) : 'b1) ((y [@ex]) : 'b2) -> p1 x && p2 y && p3 x y v
      : [%v: 'b3])

let[@assert] union (b1 : baseType) (p1 : 'b1 -> bool) (p2 : 'b1 -> bool)
    ?r:(_ = M (p1 v : [%v: 'b1])) ?r:(_ = M (p2 v : [%v: 'b1])) =
  M (p1 v || p2 v : [%v: 'b1])

let[@assert] fix (b1 : baseType) (p1 : int -> 'b1 -> bool)
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

(*  Basic generator varaints *)

let int_bound (n : int) : int gen =
  if n < 0 then return Err else fmap (fun (r : int) -> r mod (n + 1)) int_gen

let[@assert] int_bound ?r:(n = ((0 <= v : [%v: int]) [@over])) =
  M (0 <= v && v <= n : [%v: int])

let int_range (a : int) (b : int) : int gen =
  if b < a then return Err
  else fmap (fun (x : int) -> a + x) (int_bound (b - a))

let[@assert] int_range ?r:(a = ((true : [%v: int]) [@over]))
    ?r:(b = ((a <= v : [%v: int]) [@over])) =
  M (a <= v && v <= b : [%v: int])

let nat : int gen =
  bind (int_bound 10) (fun (p : int) ->
      if p < 5 then int_bound 10
      else if p < 8 then int_bound 100
      else if p < 9 then int_bound 1000
      else int_bound 10000)

let[@assert] nat = M (0 <= v && v <= 1000 : [%v: int])
let pair (g1 : 'a gen) (g2 : 'b gen) : ('a * 'b) gen = fun () -> (g1 (), g2 ())

let[@assert] pair (b1 : baseType) (b2 : baseType) (p1 : 'b1 -> bool)
    (p2 : 'b2 -> bool) ?r:(_ = M (p1 v : [%v: 'b1]))
    ?r:(_ = M (p2 v : [%v: 'b2])) =
  M (p1 (fst v) && p2 (snd v) : [%v: 'b1 * 'b2])

let option (g : 'a gen) : 'a option gen =
  fmap (fun (p : int) -> if p < 2 then None else Some (g ())) (int_bound 10)

let[@assert] option (b1 : baseType) (p1 : 'b1 -> bool)
    ?r:(_ = M (p1 v : [%v: 'b1])) =
  M
    (fun ((y [@ex]) : 'b1) -> v == None || (v == Some y && p1 y)
      : [%v: 'b1 option])

(* Others *)

(* Oneof *)

let oneof (l : int -> 'a gen) : 'a gen = fun () -> l (nat_gen ()) ()

let[@assert] oneof (b1 : baseType) (p1 : int -> 'b1 -> bool)
    ?r:(_ =
        fun ?r:(x = ((0 <= v : [%v: int]) [@over])) -> M (p1 x v : [%v: 'b1])) =
  M (fun ((x [@ex]) : int) -> 0 <= x && p1 x v : [%v: 'b1])

let nil_gen : int -> 'a gen = fun (i : int) () -> Err

let[@assert] nil_gen (b1 : baseType) =
 fun ?r:(x = ((0 <= v : [%v: int]) [@over])) -> M (false : [%v: 'b1])

let cons_gen (g : 'a gen) (l : int -> 'a gen) (i : int) : 'a gen =
  if i == 0 then g else l (i - 1)

let[@assert] cons_gen (b1 : baseType) (p1 : int -> 'b1 -> bool)
    (p2 : 'b1 -> bool) ?r:(_ = M (p2 v : [%v: 'b1]))
    ?r:(_ =
        fun ?r:(x = ((0 <= v : [%v: int]) [@over])) -> M (p1 x v : [%v: 'b1])) =
 fun ?r:(x = ((0 <= v : [%v: int]) [@over])) ->
  M ((x == 0 && p2 v) || (x > 0 && p1 (x - 1) v) : [%v: 'b1])

let oneofl (l : 'a list) : 'a gen =
  return (list_nth l (int_range 0 (list_length l - 1) ()))

let[@assert] oneofl (b1 : baseType) (p1 : 'b1 list -> bool)
    ?r:(l = ((p1 v : [%v: 'b1 list]) [@over])) =
  M (list_mem l v : [%v: 'b1])

(* Frequency *)

let rec frequencyl_aux (i : int) (m : int) (l : (int * 'a) list) (acc : int) :
    'a gen =
  match l with
  | [] -> return Err
  | tmp_pair :: rest ->
      let (n : int), (x : 'a) = tmp_pair in
      if bool_gen () then return x else frequencyl_aux (i - 1) m rest (acc + n)

let[@assert] frequencyl_aux (b1 : baseType)
    ?r:(i = ((0 <= v : [%v: int]) [@over]))
    ?r:(m = ((0 <= v : [%v: int]) [@over]))
    ?r:(l = ((i == list_len v : [%v: (int * 'b1) list]) [@over]))
    ?r:(acc = ((true : [%v: int]) [@over])) =
  M (list_snd_mem l v : [%v: 'b1])

let frequencyl (l : (int * 'a) list) : 'a gen =
  frequencyl_aux (list_length l) (sum_fst_int l) l 0

let[@assert] frequencyl (b1 : baseType)
    ?r:(l = ((true : [%v: (int * 'b1) list]) [@over])) =
  M (list_snd_mem l v : [%v: 'b1])

let frequency (fq : int list) (l : int -> 'a gen) : 'a gen =
 fun () -> l (choose_by_fq fq) ()

let[@assert] frequency (b1 : baseType) (p1 : int -> 'b1 -> bool)
    ?r:(fq : int list)
    ?r:(_ =
        fun ?r:(x = ((0 <= v : [%v: int]) [@over])) -> M (p1 x v : [%v: 'b1])) =
  M (fun ((x [@ex]) : int) -> 0 <= x && x < list_len fq && p1 x v : [%v: 'b1])
