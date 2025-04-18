(** We always use 'a as poly type in the axioms *)

(** Axioms *)

let[@axiom] rational_zero_one =
 fun (v : int * int) ->
  (rational_zero_one v)#==>(0 <= fst v
                           && fst v <= snd v
                           && 1 <= snd v
                           && snd v <= 2147483647)

(** String *)

let[@axiom] string_len_geq_zero = fun (l : string) -> string_len l >= 0

let[@axiom] list_mem_has_nth =
 fun (l : 'a list) (v : 'a) ->
  (list_mem l v) #==> (fun ((idx [@ex]) : int) ->
  0 <= idx && idx < list_len l && list_nth_pred l idx v)

let[@axiom] list_snd_mem_none_when_len_0 =
 fun (l : (int * 'a) list) (v : 'a) ->
  (list_len l == 0)#==>(not (list_snd_mem l v))

let[@axiom] list_snd_mem_implies_len_gt_zero =
 fun (l : (int * 'a) list) (v : 'a) -> (list_snd_mem l v)#==>(list_len l > 0)

let[@axiom] list_len_gt_zero_implies_has_hd_tl =
 fun (l : 'a list) ->
  (list_len l > 0) #==> (fun ((hde [@ex]) : 'a) ((tle [@ex]) : 'a list) ->
  hd l hde && tl l tle)

let[@axiom] list_snd_mem_implies_snd_mem_hd_or_tl =
 fun (l : (int * 'a) list) (v : 'a) (hde : int * 'a) (tle : (int * 'a) list) ->
  (list_snd_mem l v && hd l hde && tl l tle)#==>(v == snd hde
                                                || list_snd_mem tle v)

let[@axiom] list_tl_len_minus_one =
 fun (l : 'a list) (tle : 'a list) ->
  (tl l tle)#==>(list_len l == 1 + list_len tle)

let[@axiom] list_hd_implies_len_gt_zero =
 fun (l : 'a list) (v : 'a) -> (hd l v)#==>(list_len l > 0)

let[@axiom] list_tl_implies_len_gt_zero =
 fun (l : 'a list) (tle : 'a list) -> (tl l tle)#==>(list_len l > 0)

let[@axiom] list_hd_is_mem =
 fun (l : 'a list) (v : 'a) -> (hd l v)#==>(list_mem l v)

let[@axiom] list_hd_unique =
 fun (l : 'a list) (x : 'a) (y : 'a) -> (hd l x && hd l y)#==>(x == y)

let[@axiom] list_tl_unique =
 fun (l : 'a list) (tle1 : 'a list) (tle2 : 'a list) ->
  (tl l tle1 && tl l tle2)#==>(tle1 == tle2)

let[@axiom] list_len_geq_zero = fun (l : 'a list) -> list_len l >= 0

let[@axiom] list_len_geq_zero_implies_list_ex =
 fun (n : int) -> (0 <= n) #==> (fun ((l [@ex]) : 'a list) -> list_len l == n)

let[@axiom] int_list_exists_0_9 =
 fun ((l0 [@ex]) : int list) ((l1 [@ex]) : int list) ((l2 [@ex]) : int list) ->
  tl l2 l1 && tl l1 l0 && list_len l0 == 0 && hd l1 1 && hd l2 9
