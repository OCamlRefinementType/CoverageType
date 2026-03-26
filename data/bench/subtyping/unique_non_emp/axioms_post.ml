let[@axiom] list_hd_no_emp = fun (l : (int list)) -> fun (x : int) -> ((hd l x) #==> (not (emp l)))
let[@axiom] list_len_geq_0 = fun (l : (int list)) -> fun (n : int) -> ((len l n) #==> (n >= 0))
let[@axiom] list_tl_len_plus_1 = fun (l : (int list)) (l1 : (int list)) (n : int) -> ((tl l l1) #==> (iff (len l1 n) (len l (n + 1))))
let[@axiom] list_tl_unique_parent = fun (l : (int list)) (l1 : (int list)) (n : int) -> (((uniq l1) && ((tl l l1) && ((hd l n) && (not (list_mem l1 n))))) #==> (uniq l))