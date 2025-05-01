let[@library] type_eq ?r:(t1 : stlc_ty) ?r:(t2 : stlc_ty) =
  (v == (t1 == t2) : [%v: bool])

let[@library] stlc_ty_num_arr ?r:(t1 : stlc_ty) = (num_arr t1 == v : [%v: int])

let gen_const (a : unit) : stlc_term =
  let (n2 : int) = nat_gen () in
  Stlc_const n2

let[@assert] gen_const = M (is_const v : [%v: stlc_term])

let rec gen_type_size (size : int) : stlc_ty =
  if bool_gen () then Stlc_ty_nat
  else
    let (tau1 : stlc_ty) = gen_type_size (size - 1) in
    let (tau2 : stlc_ty) = gen_type_size (size - 1) in
    Stlc_ty_arr (tau1, tau2)

let[@assert] gen_type_size ?r:(s = ((v >= 0 : [%v: int]) [@over])) =
  (num_arr v <= s : [%v: stlc_ty])

let gen_type (a : unit) : stlc_ty = gen_type_size (nat_gen ())
let[@assert] gen_type = M (true : [%v: stlc_ty])

let rec vars_with_type_rev_index (gamma : stlc_ty list) (tau : stlc_ty) : int =
  match gamma with
  | [] -> Err
  | tau_hd :: gamma_rest ->
      if bool_gen () then vars_with_type_rev_index gamma_rest tau
      else if type_eq tau_hd tau then list_length gamma
      else Exn

let[@assert] vars_with_type_rev_index ?r:(gamma : stlc_ty list)
    ?r:(tau : stlc_ty) =
  (list_index gamma (list_len gamma - v) tau : [%v: int])

let rec vars_with_type (gamma : stlc_ty list) (tau : stlc_ty) : stlc_term =
  let (rev_id : int) = vars_with_type_rev_index gamma tau in
  Stlc_id (list_length gamma - rev_id)

let[@assert] vars_with_type ?r:(gamma : stlc_ty list) ?r:(tau : stlc_ty) =
  (typing gamma v tau && is_var v : [%v: stlc_term])

let rec gen_term_no_app (tau : stlc_ty) (gamma : stlc_ty list) : stlc_term =
  if bool_gen () then
    match tau with
    | Stlc_ty_nat -> gen_const ()
    | Stlc_ty_arr (tau1, tau2) ->
        Stlc_abs (tau1, gen_term_no_app tau2 (tau1 :: gamma))
  else vars_with_type gamma tau

let[@assert] gen_term_no_app ?r:(tau : stlc_ty) ?r:(gamma : stlc_ty list) =
  (typing gamma v tau && num_app v == 0 : [%v: stlc_term])

let[@library] calculate_measure ?r:(num : int) ?r:(tau : stlc_ty) =
  (stlc_measure tau num v : [%v: int])

let rec gen_term_size (measure : int) (num : int) (tau : stlc_ty)
    (gamma : stlc_ty list) : stlc_term =
  if num == 0 then gen_term_no_app tau gamma
  else if bool_gen () then
    let (arg_ty : stlc_ty) = gen_type () in
    let (num_app_func : int) = int_range_inex 0 num in
    let (num_app_arg : int) = int_range_inex 0 (num - num_app_func) in
    let (func_ty : stlc_ty) = Stlc_ty_arr (arg_ty, tau) in
    let (m1 : int) = calculate_measure num_app_func func_ty in
    let (func : stlc_term) = gen_term_size m1 num_app_func func_ty gamma in
    let (m2 : int) = calculate_measure num_app_arg arg_ty in
    let (arg : stlc_term) = gen_term_size m2 num_app_arg arg_ty gamma in
    Stlc_app (func, arg)
  else
    match tau with
    | Stlc_ty_nat -> Err
    | Stlc_ty_arr (tau1, tau2) ->
        let (m3 : int) = calculate_measure num tau2 in
        let (body : stlc_term) = gen_term_size m3 num tau2 (tau1 :: gamma) in
        Stlc_abs (tau1, body)

let[@assert] gen_term_size ?r:(measure : int)
    ?r:(num = ((v >= 0 : [%v: int]) [@over]))
    ?r:(tau = ((stlc_measure v num measure : [%v: stlc_ty]) [@over]))
    ?r:(gamma : stlc_ty list) =
  (typing gamma v tau && num_app v == num : [%v: stlc_term])
