let[@axiom] list_emp_unique = fun (l : (int list)) -> ((emp l) #==> (uniq l))
let[@axiom] list_len_0_emp_iff = fun (l : (int list)) -> (iff (emp l) (len l 0))