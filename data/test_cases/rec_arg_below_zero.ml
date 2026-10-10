let rec below_zero_gen (x : int) : int = below_zero_gen (x - 1)

let[@assert] below_zero_gen ?r:(x = ((true : [%v: int]) [@over])) =
  (v == 0 : [%v: int])
