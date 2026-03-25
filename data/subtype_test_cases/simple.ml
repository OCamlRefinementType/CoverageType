let[@assert] rty1 =
  (v >= 0 : [%v: int]) [@under]

let[@assert] rty2 =
  (v >= 3 : [%v: int]) [@under]
