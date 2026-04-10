let[@axiom] list_len_geq_0 = fun (l : (int list)) -> fun (n : int) -> ((len l n) #==> (n >= 0))
let[@axiom] list_len_0_emp_iff = fun (l : (int list)) -> (iff (emp l) (len l 0))