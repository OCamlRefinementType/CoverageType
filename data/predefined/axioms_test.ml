(* let[@axiom] list_len_geq_zero = fun (l : 'a list) -> list_len l >= 0 *)

(* let[@axiom] l2t_pre_empty = *)
(*  fun (blocks : 'a list) (vv : 'a tezosTree) -> *)
(*   (l2t_pre blocks vv)#==>(list_len blocks != 0) *)

let[@axiom] tl_wf_decreasing =
 fun (l : 'a list) (ll : 'a list) -> (tl l ll)#==>(decreasing ll l)

let[@axiom] list_concat_wf_decreasing =
 fun (l : 'a list) (l1 : 'a list) (l2 : 'a list) ->
  (list_concat l1 l2 l)#==>(decreasing l1 l && decreasing l2 l)

let[@axiom] tezos =
 fun (blocks : 'a list) ->
  fun (v : 'a tezosTree) ->
   implies (l2t_pre blocks v) (fun ((x [@exists]) : 'a) ->
       fun ((xs [@exists]) : 'a list) ->
        hd blocks x && tl blocks xs
        && ((list_len xs == 0 && tezos_leaf v x)
           || (not (list_len xs == 0))
              && ((list_len xs == 0 && tezos_leaf v x)
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
                            l2t_pre (snd x_131) x_133 && tezos_node1 v x x_133
                          )
                       || fun ((x_132 [@exists]) : 'a tezosTree) ->
                         l2t_pre (fst x_131) x_132
                         && ( list_len (snd x_131) == 0
                            && tezos_node1 v x x_132
                            || fun ((x_134 [@exists]) : 'a tezosTree) ->
                              l2t_pre (snd x_131) x_134
                              && tezos_node2 v x x_132 x_134 ) ))))
