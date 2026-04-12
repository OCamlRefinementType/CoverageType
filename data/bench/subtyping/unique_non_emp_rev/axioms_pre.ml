let[@axiom] list_no_emp_exists_tl (l : int list) ((l1 [@exists]) : int list) =
  (not (emp l)) #==> (tl l l1)

let[@axiom] list_no_emp_exists_hd (l : int list) ((x [@exists]) : int) =
  (not (emp l)) #==> (hd l x)

let[@axiom] list_len_geq_0 (l : int list) (n : int) = (len l n) #==> (n >= 0)
let[@axiom] list_tl_len_plus_1 = fun (l : (int list)) (l1 : (int list)) (n : int) -> ((tl l l1) #==> (iff (len l1 n) (len l (n + 1))))
