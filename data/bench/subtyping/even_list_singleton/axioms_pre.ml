let[@axiom] list_len_0_emp = fun (l : (int list)) -> ((emp l) #==> (len l 0))
let[@axiom] list_emp_all_even = fun (l : (int list)) -> ((emp l) #==> (all_evens l))
let[@axiom] list_len_geq_0 (l : int list) (n : int) = (len l n) #==> (n >= 0)
let[@axiom] list_tl_len_plus_1 = fun (l : (int list)) (l1 : (int list)) (n : int) -> ((tl l l1) #==> (iff (len l1 n) (len l (n + 1))))
