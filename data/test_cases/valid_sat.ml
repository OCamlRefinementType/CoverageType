let[@valid] refl_valid = fun (x : int) -> x == x
let[@sat] refl_sat = fun (x : int) -> x == x
let[@valid] all_eq_invalid = fun (x : int list) (y : int list) -> x == y
let[@sat] all_eq_sat = fun (x : int list) (y : int list) -> x == y
let[@valid] not_refl_invalid = fun (x : int) -> x != x
let[@sat] not_refl_unsat = fun (x : int) -> x != x
