let[@axiom] list_hd_no_emp (l : int list) (x : int) =
  (hd l x) #==> (not (emp l))

let[@axiom] list_len_geq_0 (l : int list) (n : int) = (len l n) #==> (n >= 0)
