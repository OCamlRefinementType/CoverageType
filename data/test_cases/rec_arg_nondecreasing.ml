let rec nondec_gen (s : int) : int list = if s == 0 then [] else nondec_gen s

let[@assert] nondec_gen ?r:(s = ((0 <= v : [%v: int]) [@over])) =
  (s == 0 && list_len v == 0 : [%v: int list])
