let[@axiom] list_len_0_emp = fun (l : (int list)) -> ((emp l) #==> (len l 0))
let[@axiom] list_emp_unique = fun (l : (int list)) -> ((emp l) #==> (uniq l))