open Zutils
open Nt

let desugar_basic_coverage_monad =
  let rec aux rty =
    match rty with
    | Ty_var _ | Ty_any | Ty_unknown | Ty_uninter _ | Ty_enum _ -> rty
    | Ty_constructor (name, [ ty ]) when String.equal name "cm" ->
        construct_arr_tp ([ unit_ty ], ty)
    | Ty_constructor (name, tys) -> Ty_constructor (name, List.map aux tys)
    | Ty_record xs -> Ty_record (List.map (fun x -> x#=>aux) xs)
    | Ty_arrow (nt1, nt2) -> Ty_arrow (aux nt1, aux nt2)
    | Ty_tuple nts -> Ty_tuple (List.map aux nts)
    | Ty_poly (x, t) -> Ty_poly (x, aux t)
  in
  aux

let core_type_to_t ty = desugar_basic_coverage_monad @@ core_type_to_t ty
