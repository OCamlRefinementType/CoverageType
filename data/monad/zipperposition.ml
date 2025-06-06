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

let[@library] oneofl (b1 : baseType) (p1 : 'b1 list -> bool)
    ?r:(l = ((p1 v : [%v: 'b1 list]) [@over])) =
  M (list_mem l v : [%v: 'b1])

let[@library] frequencyl (b1 : baseType)
    ?r:(l = ((true : [%v: (int * 'b1) list]) [@over])) =
  M (list_snd_mem l v : [%v: 'b1])

let[@library] frequency (b1 : baseType) (p1 : int -> 'b1 -> bool)
    ?r:(fq : int list)
    ?r:(_ =
        fun ?r:(x = ((0 <= v : [%v: int]) [@over])) -> M (p1 x v : [%v: 'b1])) =
  M (fun ((x [@ex]) : int) -> 0 <= x && x < list_len fq && p1 x v : [%v: 'b1])

let[@library] fix (b1 : baseType) (p1 : int -> 'b1 -> bool)
    ?r:(_ =
        fun ?r:(m = ((0 <= v : [%v: int]) [@over]))
          ?r:(_ =
              fun ?r:(n = ((0 <= v && v < m : [%v: int]) [@over])) ->
                M (p1 n v : [%v: 'b1]))
        -> M (p1 m v : [%v: 'b1])) =
 fun ?r:(x = ((0 <= v : [%v: int]) [@over])) -> M (p1 x v : [%v: 'b1])

let[@library] int_bound ?r:(x : int) ?r:(n = ((x <= v : [%v: int]) [@over])) =
  M (x <= v && v <= n : [%v: 'b1])

let rec default_fuel (n : int) : pt_term gen =
  let (base : pt_term gen) =
    oneofl [ "a"; "b"; "c"; "d"; "e"; "x"; "y"; "z" ] >|= fun (s : string) ->
    PT_Var s
  in
  let (self : pt_term gen) = default_fuel (n - 1) in
  if n <= 0 then base
  else
    frequency [ 3; 1; 1; 1; 1; 1 ] (fun (k : int) ->
        if k == 0 then base
        else if k == 1 then
          self >>= fun (x1 : pt_term) ->
          self >|= fun (y1 : pt_term) -> PT_App (PT_Var "f", [ x1; y1 ])
        else if k == 2 then
          self >>= fun (x2 : pt_term) ->
          self >|= fun (y2 : pt_term) -> PT_App (PT_Var "sum", [ x2; y2 ])
        else if k == 3 then
          self >|= fun (x3 : pt_term) -> PT_App (PT_Var "g", [ x3 ])
        else if k == 4 then
          self >|= fun (x6 : pt_term) -> PT_App (PT_Var "h", [ x6 ])
        else
          self >>= fun (x4 : pt_term) ->
          self >>= fun (y4 : pt_term) ->
          self >|= fun (z4 : pt_term) -> PT_Ite (x4, y4, z4))

let[@assert] default_fuel ?r:(m = ((1 <= v : [%v: int]) [@over])) =
  M (wf_fol_pt_term v && pt_term_size v == m : [%v: pt_term])
