let[@axiom] list_len_geq_0 (l : int list) (n : int) = (len l n) #==> (n >= 0)
let[@axiom] list_len_0_emp_iff = fun (l : (int list)) -> (iff (emp l) (len l 0))
let[@axiom] list_tl_len_plus_1 = fun (l : (int list)) (l1 : (int list)) (n : int) -> ((tl l l1) #==> (iff (len l1 n) (len l (n + 1))))
