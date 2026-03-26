let[@axiom] list_len_0_emp = fun (l : (int list)) -> ((emp l) #==> (len l 0))
let[@axiom] list_emp_all_even = fun (l : (int list)) -> ((emp l) #==> (all_evens l))