open Language
open Zutils

let mk_self_wf_dec x =
  let open Prop in
  let v = tvar_to_lit default_v#:x.ty in
  if Nt.equal_nt x.ty Nt.int_ty then
    let cmp op = op#:Nt.(construct_arr_tp ([ int_ty; int_ty ], bool_ty)) in
    And
      [
        lit_to_prop (AAppOp (cmp "<", [ v; tvar_to_lit x ]));
        lit_to_prop (AAppOp (cmp ">=", [ v; (AC (I 0))#:Nt.int_ty ]));
      ]
  else
    let lt = "decreasing"#:Nt.(construct_arr_tp ([ x.ty; x.ty ], bool_ty)) in
    lit_to_prop (AAppOp (lt, [ v; tvar_to_lit x ]))
