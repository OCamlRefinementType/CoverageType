let[@library] return (b1 : baseType) ?r:(x : 'b1) = M (v == x : [%v: 'b1])

let[@library] ( >|= ) (b1 : baseType) (b2 : baseType) (p1 : 'b1 -> bool)
    (p2 : 'b1 -> 'b2 -> bool) ?r:(_ = M (p1 v : [%v: 'b1]))
    ?r:(_ = fun ?r:(x = ((p1 v : [%v: 'b1]) [@over])) -> (p2 x v : [%v: 'b2])) =
  M (fun ((x [@ex]) : 'b1) -> p1 x && p2 x v : [%v: 'b2])

let[@library] ( >>= ) (b1 : baseType) (b2 : baseType) (p1 : 'b1 -> bool)
    (p2 : 'b1 -> 'b2 -> bool) ?r:(_ = M (p1 v : [%v: 'b1]))
    ?r:(_ = fun ?r:(x = ((p1 v : [%v: 'b1]) [@over])) -> M (p2 x v : [%v: 'b2]))
    =
  M (fun ((x [@ex]) : 'b1) -> p1 x && p2 x v : [%v: 'b2])

let[@library] float_gen = M (true : [%v: float])
let[@library] bitvector_gen = M (true : [%v: Bitvector.t])
let[@library] string_gen = M (true : [%v: string])
let[@library] printable_gen = M (is_printable v : [%v: string])
let[@library] binop_gen = M (is_binop v : [%v: string])
let[@library] unop_gen = M (is_unop v : [%v: string])

let[@library] oneofl (b1 : baseType) ?r:(l : 'b1 list) =
  M (list_mem l v : [%v: 'b1])

let[@library] ( >+ ) (b1 : baseType) (p1 : 'b1 -> bool) (p2 : 'b1 -> bool)
    ?r:(_ = M (p1 v : [%v: 'b1])) ?r:(_ = M (p2 v : [%v: 'b1])) =
  M (p1 v || p2 v : [%v: 'b1])

let[@library] split2 ?r:(n = ((1 <= v : [%v: int]) [@over])) =
  M (fst v + snd v == n && 0 <= fst v && 0 <= snd v : [%v: int * int])

let[@library] split3 ?r:(n = ((1 <= v : [%v: int]) [@over])) =
  M
    (fst (fst v) + snd (fst v) + snd v == n
     && 0 <= fst (fst v)
     && 0 <= snd (fst v)
     && 0 <= snd v
      : [%v: (int * int) * int])

let[@library] list_size (b1 : baseType) (p1 : int -> bool) (p2 : 'b1 -> bool)
    ?r:(_ = M (p1 v : [%v: int])) ?r:(_ = M (p2 v : [%v: 'b1])) =
  M
    (p1 (list_len v) && fun ((x [@fa]) : 'b1) -> (list_mem v x)#==>(p2 x)
      : [%v: 'b1 list])

let[@library] int_bound ?r:(x : int) ?r:(n = ((x <= v : [%v: int]) [@over])) =
  M (x <= v && v <= n : [%v: 'b1])

let literal : literal gen =
  let (l_int : literal gen) = int_bound 0 1000 >|= fun (i : int) -> L_Int i in
  let (l_bool : literal gen) = bool_gen >|= fun (b : bool) -> L_Bool b in
  let (l_real : literal gen) = float_gen >|= fun (r : float) -> L_Real r in
  let (l_bv : literal gen) =
    list_size (int_bound 0 1000) (oneofl [ '0'; '1' ])
    >|= fun (bv : char list) -> L_BitVector bv
  in
  let (l_string : literal gen) =
    string_gen >|= fun (s : string) -> L_String s
  in
  l_int >+ l_bool >+ l_bv >+ l_real >+ l_string

let[@assert] literal = M (wf_literal v : [%v: literal])

(* let slices_gen (expr : int -> expr gen) (n : int) : slice list gen = *)
(*   let (slice_single : slice gen) = *)
(*     expr n >|= fun (e : expr) -> Slice_Single e *)
(*   in *)
(*   let (slice_range : slice gen) = *)
(*     if n < 1 then Err *)
(*     else *)
(*       split2 n >>= fun (n1n2 : int * int) -> *)
(*       let (n1 : int), (n2 : int) = n1n2 in *)
(*       expr n1 >>= fun (e1 : expr) -> *)
(*       expr n2 >|= fun (e2 : expr) -> Slice_Range (e1, e2) *)
(*   in *)
(*   let (slice_length : slice gen) = *)
(*     if n < 1 then Err *)
(*     else *)
(*       split2 n >>= fun (n1n2 : int * int) -> *)
(*       let (n1 : int), (n2 : int) = n1n2 in *)
(*       expr n1 >>= fun (e1 : expr) -> *)
(*       expr n2 >|= fun (e2 : expr) -> Slice_Length (e1, e2) *)
(*   in *)
(*   let (slice_star : slice gen) = *)
(*     if n < 1 then Err *)
(*     else *)
(*       split2 n >>= fun (n1n2 : int * int) -> *)
(*       let (n1 : int), (n2 : int) = n1n2 in *)
(*       expr n1 >>= fun (e1 : expr) -> *)
(*       expr n2 >|= fun (e2 : expr) -> Slice_Star (e1, e2) *)
(*   in *)
(*   let (slice : slice gen) = *)
(*     slice_single >+ slice_range >+ slice_length >+ slice_star *)
(*   in *)
(*   list_sized slice (n - 1) *)

(* let e_literal_gen : expr gen = literal >|= fun (l : literal) -> E_Literal l *)
(* let e_var_gen : expr gen = printable_gen >|= fun (s : string) -> E_Var s *)

(* let rec expr (n : int) : expr gen = *)
(*   if n < 0 then return Err *)
(*   else *)
(*     let (e_tuple : expr gen) = *)
(*       if n < 3 then return Err *)
(*       else list_size (expr (n - 1)) n >|= fun (li : expr list) -> E_Tuple li *)
(*     in *)
(*     let (e_binop : expr gen) = *)
(*       if n < 3 then return Err *)
(*       else *)
(*         split2 (n - 1) >>= fun (n1n2 : int * int) -> *)
(*         let (n1 : int), (n2 : int) = n1n2 in *)
(*         expr n1 >>= fun (e1 : expr) -> *)
(*         expr n2 >>= fun (e2 : expr) -> *)
(*         binop_gen >|= fun (op : string) -> E_Binop (op, e1, e2) *)
(*     in *)
(*     let (e_unop : expr gen) = *)
(*       if n < 1 then return Err *)
(*       else *)
(*         expr (n - 1) >>= fun (e : expr) -> *)
(*         binop_gen >|= fun (op : string) -> E_Unop (op, e) *)
(*     in *)
(*     let (e_cond : expr gen) = *)
(*       if n < 4 then return Err *)
(*       else *)
(*         split3 (n - 1) >>= fun (m1m2m3 : (int * int) * int) -> *)
(*         let (m1m2 : int * int), (m3 : int) = m1m2m3 in *)
(*         let (m1 : int), (m2 : int) = m1m2 in *)
(*         expr m1 >>= fun (e1 : expr) -> *)
(*         expr m2 >>= fun (e2 : expr) -> *)
(*         expr m3 >|= fun (e3 : expr) -> E_Cond (e1, e2, e3) *)
(*     in *)
(*     let (e_slice : expr gen) = *)
(*       if n < 2 then return Err *)
(*       else *)
(*         split2 (n - 1) >>= fun (k1k2 : int * int) -> *)
(*         let (k1 : int), (k2 : int) = k1k2 in *)
(*         expr k1 >>= fun (e1 : expr) -> *)
(*         slices_gen expr k2 >|= fun (slices : slice list) -> E_Slice (e1, slices) *)
(*     in *)
(*     e_literal_gen >+ e_var_gen >+ e_tuple >+ e_binop >+ e_unop >+ e_cond *)
(*     >+ e_slice *)

(* let[@assert] expr ?r:(n = ((0 <= v : [%v: int]) [@over])) = *)
(*   M (wf_expr v && expr_size v == n : [%v: expr]) *)
