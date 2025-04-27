val list_gen : int -> int list

let[@library] list_gen =
  let a = ((true : [%v: int]) [@over]) in
  ((list_len v == a : [%v: int list]) [@under])

let batchedq_gen (sizel : int) : int list * int list =
  let (sizer : int) = int_range_inc 0 sizel in
  let (l1 : int list) = list_gen sizel in
  let (l2 : int list) = list_gen sizer in
  (l1, l2)

let[@assert] batchedq_gen =
  let s = ((v >= 0 : [%v: int]) [@over]) in
  ((list_len (fst v) == s && list_len (snd v) < s
    : [%v: int list * int list])
    [@under])
