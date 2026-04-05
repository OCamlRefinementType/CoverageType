let rec sized_list_gen (s : int) : int list = Err

let[@assert] sized_list_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((true : [%v: int list]) [@under])
