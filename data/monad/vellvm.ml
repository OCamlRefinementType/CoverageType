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

let[@library] int_bound ?r:(n = ((0 <= v : [%v: int]) [@over])) =
  M (0 <= v && v <= n : [%v: int])

let[@library] oneofl (b1 : baseType) (p1 : 'b1 list -> bool)
    ?r:(l = ((p1 v : [%v: 'b1 list]) [@over])) =
  M (list_mem l v : [%v: 'b1])

let[@library] int_range ?r:(a : int) ?r:(b = ((a <= v : [%v: int]) [@over])) =
  M (a <= v && v <= b : [%v: int])

let[@library] list_size (b1 : baseType) (p1 : int -> bool) (p2 : 'b1 -> bool)
    ?r:(_ = M (p1 v : [%v: int])) ?r:(_ = M (p2 v : [%v: 'b1])) =
  M
    (p1 (list_len v) && fun ((x [@fa]) : 'b1) -> (list_mem v x)#==>(p2 x)
      : [%v: 'b1 list])

(* LLVM Int with size 1 *)
(* let g_i1 : dvalue gen = *)
(*   bool_gen >|= fun (x : bool) -> DVALUE_I (1, if x then 1 else 0) *)

(* let[@assert] g_i1 = M (dvalue_int_size v 1 : [%v: dvalue]) *)
(* let g_si8 : dvalue gen = int_range 0 255 >|= fun (x : int) -> DVALUE_I (8, x) *)
(* let[@assert] g_si8 = M (dvalue_int_size v 8 : [%v: dvalue]) *)
(* let g_si32 : dvalue gen = int_bound 10000 >|= fun (x : int) -> DVALUE_I (32, x) *)
(* let[@assert] g_si32 = M (dvalue_int_size v 32 : [%v: dvalue]) *)
(* let g_si64 : dvalue gen = int_bound 10000 >|= fun (x : int) -> DVALUE_I (64, x) *)
(* let[@assert] g_si64 = M (dvalue_int_size v 64 : [%v: dvalue]) *)

(* undefined symbolic values (uvalue) which is a subset of dvalue, see paper and note: https://github.com/vellvm/vellvm/blob/38b549eae8bbf1a66c32b99104a845690a40cf69/doc/intern/notes.org#L155 *)
let rec gen_uvalue (t : typ) : dvalue gen =
  match t with
  | TYPE_I i ->
      if i == 1 then
        oneofl [ true; false ] >|= fun (x : bool) ->
        DVALUE_I (1, if x then 1 else 0)
      else if i == 8 then int_range 0 255 >|= fun (x : int) -> DVALUE_I (8, x)
      else if i == 32 then int_bound 10000 >|= fun (x : int) -> DVALUE_I (32, x)
      else if i == 64 then int_bound 10000 >|= fun (x : int) -> DVALUE_I (64, x)
      else return Err
  | TYPE_Void -> return DVALUE_None
  | TYPE_Vector (sz, ty) ->
      let (list_ts : dvalue list gen) = list_size (return sz) (gen_uvalue ty) in
      list_ts >|= fun (l : dvalue list) -> DVALUE_Vector (t, l)
  | TYPE_Array (sz', ty') ->
      let (list_ts : dvalue list gen) =
        list_size (return sz') (gen_uvalue ty')
      in
      list_ts >|= fun (l : dvalue list) -> DVALUE_Array (t, l)
  | TYPE_Others -> return Err

let[@assert] gen_uvalue ?r:(ty : typ) = M (llvm_typing v ty : [%v: dvalue])
