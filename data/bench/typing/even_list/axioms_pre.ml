let[@axiom] list_positive_len_is_not_emp (l : int list) (n : int) =
  (len l n && n > 0) #==> (not (emp l))

let[@axiom] list_len_geq_0 = fun (l : (int list)) -> fun (n : int) -> ((len l n) #==> (n >= 0))
let[@axiom] list_no_emp_exists_hd = fun (l : (int list)) -> fun ((x [@ex]) : int) -> ((not (emp l)) #==> (hd l x))
let[@axiom] list_no_emp_exists_tl = fun (l : (int list)) -> fun ((l1 [@ex]) : (int list)) -> ((not (emp l)) #==> (tl l l1))
let[@axiom] list_tl_len_plus_1 = fun (l : (int list)) -> fun (l1 : (int list)) -> fun (n : int) -> ((tl l l1) #==> (iff (len l1 n) (len l (n + 1))))
