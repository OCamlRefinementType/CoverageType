(* let[@axiom] ax1 = *)
(*  fun (n : int) -> *)
(*   implies (n >= 0) (fun (v : int tree) -> *)
(*       implies *)
(*         (n - 1 == treeNumNode v) *)
(*         (fun ((tr [@exists]) : int tree) -> *)
(*           n == treeNumNode tr && fun ((x [@exists]) : int) -> *)
(*           fun ((lt [@exists]) : int tree) -> root tr x && lch tr lt && rch tr v)) *)

(* let[@axiom] ax2 = *)
(*  fun (n : int) -> *)
(*   implies (n >= 0) (fun (v : int list) -> *)
(*       implies *)
(*         (listLen v == n) *)
(*         (fun ((tr [@exists]) : int tree) -> *)
(*           n == treeNumNode tr *)
(*           && ( (leaf tr && emp v) || fun ((x [@exists]) : int) -> *)
(*                fun ((lt [@exists]) : int tree) -> *)
(*                 fun ((rt [@exists]) : int tree) -> *)
(*                  root tr x && lch tr lt && rch tr rt *)
(*                  && fun ((x_0 [@exists]) : int) -> *)
(*                  x_0 == n - 1 && fun ((l2 [@exists]) : int list) -> *)
(*                  x_0 < n && x_0 >= 0 && listLen l2 == x_0 && hd v x && tl v l2 *)
(*              ))) *)

(* let[@axiom] ax3 = *)
(*  fun (v : int list) -> *)
(*   fun ((tr [@exists]) : int tree) -> *)
(*    treeNumNode tr == listLen v && listLen v >= 0 *)

(* let[@axiom] ax4 = fun (tr : int tree) -> treeNumNode tr >= 0 *)

let[@axiom] list_mem_has_nth =
 fun (l : 'a list) (v : 'a) ->
  (list_mem l v) #==> (fun ((idx [@ex]) : int) ->
  0 <= idx && idx < list_len l && list_nth_pred l idx v)

let[@axiom] list_snd_mem_none_when_len_0 =
 fun (l : (int * 'a) list) (v : 'a) ->
  (list_len l == 0)#==>(not (list_snd_mem l v))

let[@axiom? frequencyl] list_len_geq_0_pair =
 fun (l : (int * int) list) -> list_len l >= 0

(* let[@axiom? frequencyl_aux] list_len_has_hd_tl_pair = *)
(*  fun (l : (int * int) list) -> *)
(*   (list_len l > 0) *)
(*   #==> (fun ((x [@ex]) : int * int) ((xs [@ex]) : (int * int) list) -> *)
(*   hd l x && tl l xs && list_snd_mem l (snd x)) *)

let[@axiom? frequencyl_aux] frequencyl_aux =
 fun (i : int) ->
  implies (0 <= i) (fun (m : int) ->
      implies (0 <= m) (fun (l : (int * 'a) list) ->
          implies
            (i == list_len l)
            (fun (acc : int) ->
              implies (0 <= acc) (fun (v : 'a) ->
                  implies (list_snd_mem l v)
                    (fun ((tmp_pair [@exists]) : int * 'a) ->
                      fun ((rest [@exists]) : (int * 'a) list) ->
                       hd l tmp_pair && tl l rest
                       && fun ((tmp_78 [@exists]) : int * 'a) ->
                       tmp_78 == tmp_pair && fun ((n [@exists]) : int) ->
                       n == fst tmp_78 && fun ((x [@exists]) : 'a) ->
                       x == snd tmp_78 && fun ((x_39 [@exists]) : int) ->
                       x_39 == acc + n && fun ((x_40 [@exists]) : bool) ->
                       iff x_40 (m < x_39)
                       && ((x_40 && v == x)
                          || (not x_40) && fun ((x_41 [@exists]) : int) ->
                             x_41 == i - 1 && fun ((x_45 [@exists]) : int) ->
                             x_45 == acc + n
                             && 0 <= x_45
                             && x_41 == list_len rest
                             && 0 <= m && x_41 < i && 0 <= x_41
                             && list_snd_mem rest v))))))

(* let[@axiom] list_snd_mem_is_mem = *)
(*  fun (l : (int * 'a) list) (v : 'a) -> *)
(*   (list_snd_mem l v) #==> (fun ((ptmp [@ex]) : int * 'a) -> *)
(*   list_mem l ptmp && v == snd ptmp) *)

(* [v:'a | ∃tmp_pair, (∃rest, (hd l tmp_pair ∧ tl l rest ∧ (∃n, (n == (fst tmp_pair) ∧ (((m < acc + n) ∧ v == (snd tmp_pair)) ∨ (¬(m < acc + n) ∧ 0 <= (acc + n) ∧ p1 rest ∧ 0 <= m ∧ (i - 1) < i ∧ 0 <= (i - 1) ∧ list_snd_mem rest v))))))] *)
