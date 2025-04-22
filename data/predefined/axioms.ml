(** We always use 'a as poly type in the axioms *)

(** Axioms *)

(** Rational *)

let[@axiom] rational_zero_one =
 fun (v : int * int) ->
  (rational_zero_one v)#==>(0 <= fst v
                           && fst v <= snd v
                           && 1 <= snd v
                           && snd v <= 2147483647)

(** Priority *)

let[@axiom] wf_priority =
 fun (v : priority) ->
  implies (wf_priority v) (fun ((x_17 [@exists]) : priority list) ->
      list_len x_17 == 0 && fun ((x_18 [@exists]) : (int * int) list) ->
      list_len x_18 == 0 && fun ((x_19 [@exists]) : priority) ->
      is_low x_19 x_18 && fun ((x_20 [@exists]) : priority list) ->
      hd x_20 x_19 && tl x_20 x_17
      && fun ((x_21 [@exists]) : priority) ->
      is_medium x_21 && fun ((x_22 [@exists]) : priority list) ->
      hd x_22 x_21 && tl x_22 x_20
      && fun ((x_23 [@exists]) : priority) ->
      is_high x_23 && fun ((x_24 [@exists]) : priority list) ->
      hd x_24 x_23 && tl x_24 x_22
      && fun ((x_44 [@exists]) : priority) ->
      list_mem x_24 x_44
      && ((is_high x_44 && is_high v)
         || (is_medium x_44 && is_medium v)
            && fun ((lowl [@exists]) : (int * int) list) ->
            is_low x_44 lowl && fun ((x_50 [@exists]) : (int * int) list) ->
            rational_zero_one_list x_50 && list_len x_50 <= 100 && is_low v x_50
         ))

(** Tezos *)

let[@axiom] tl_wf_decreasing =
 fun (l : 'a list) (ll : 'a list) -> (tl l ll)#==>(decreasing ll l)

let[@axiom] list_concat_wf_decreasing =
 fun (l : 'a list) (l1 : 'a list) (l2 : 'a list) ->
  (list_concat l1 l2 l)#==>(decreasing l1 l && decreasing l2 l)

let[@axiom] l2t_pre_singleton =
 fun (l : 'a list) (x : 'a) (xs : 'a list) (tr : 'a tezosTree) ->
  (l2t_pre l tr && hd l x && tl l xs)#==>(iff
                                            (list_len xs == 0)
                                            (tezos_leaf tr x))

let[@axiom] tezos =
 fun (blocks : 'a list) ->
  fun (v : 'a tezosTree) ->
   implies (l2t_pre blocks v) (fun ((x [@exists]) : 'a) ->
       fun ((xs [@exists]) : 'a list) ->
        hd blocks x && tl blocks xs
        && (list_len xs == 0
           || (fun ((x_127 [@exists]) : 'a tezosTree) ->
                l2t_pre xs x_127 && tezos_node1 v x x_127)
              && fun ((x_130 [@exists]) : int) ->
              0 <= list_len xs
              && 0 <= x_130
              && x_130 <= list_len xs
              && fun ((x_131 [@exists]) : 'a list * 'a list) ->
              0 <= x_130
              && x_130 <= list_len xs
              && list_concat (fst x_131) (snd x_131) xs
              && ( list_len (fst x_131) == 0
                 && ( (list_len (snd x_131) == 0 && tezos_leaf v x)
                    || fun ((x_133 [@exists]) : 'a tezosTree) ->
                      l2t_pre (snd x_131) x_133 && tezos_node1 v x x_133 )
                 || fun ((x_132 [@exists]) : 'a tezosTree) ->
                   l2t_pre (fst x_131) x_132
                   && ( (list_len (snd x_131) == 0 && tezos_node1 v x x_132)
                      || fun ((x_134 [@exists]) : 'a tezosTree) ->
                        l2t_pre (snd x_131) x_134 && tezos_node2 v x x_132 x_134
                      ) )))

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
