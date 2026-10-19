let[@library] prefix ?l:(xs = ((true : [%v: int list]) [@over])) =
  (fun ((rest [@ex]) : int list) -> list_concat v rest xs
    : [%v: int list])
    [@under]

let rec loop (l : int list) : int list =
  match l with
  | [] -> []
  | x :: xs ->
      let (p : int list) = prefix l in
      loop p

let[@assert] loop ?r:(l = ((true : [%v: int list]) [@over])) =
  (list_len l == 0 && list_len v == 0 : [%v: int list])
