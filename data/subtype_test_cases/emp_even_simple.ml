let[@assert] rty1 =
  (fun ((n [@exists]) : int) ((k [@exists]) : int) -> len v n && n == (2 * k) : [%v: int list]) [@under]

let[@assert] rty2 =
  (emp v : [%v: int list]) [@under]
