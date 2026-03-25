let[@assert] rty1 =
  (fun ((n [@exists]) : int) -> len v n && n >= 0 : [%v: int list]) [@under]

let[@assert] rty2 =
  (emp v : [%v: int list]) [@under]
