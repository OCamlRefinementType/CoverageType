let rec repeated_list (n : int) : int list =
  if n = 0 then [] else 1 :: repeated_list (n - 1)

let[@assert] repeated_list ?r:(n = ((v >= 0 : [%v: int]) [@over])) =
  (list_len v == n
   && (list_len v > 0) #==> (fun (u : int) -> list_mem v u == (u == 1))
    : [%v: int list])
    [@under]
