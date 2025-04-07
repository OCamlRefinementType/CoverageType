(** We always use 'a as poly type in the axioms *)

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

let[@axiom] list_snd_mem_implies_len_gt_zero =
 fun (l : (int * 'a) list) (v : 'a) -> (list_snd_mem l v)#==>(list_len l > 0)

let[@axiom] list_len_gt_zero_implies_has_hd_tl =
 fun (l : (int * 'a) list) ->
  (list_len l > 0)
  #==> (fun ((hde [@ex]) : int * 'a) ((tle [@ex]) : (int * 'a) list) ->
  hd l hde && tl l tle)

let[@axiom] list_snd_mem_implies_snd_mem_hd_or_tl =
 fun (l : (int * 'a) list) (v : 'a) (hde : int * 'a) (tle : (int * 'a) list) ->
  (list_snd_mem l v && hd l hde && tl l tle)#==>(v == snd hde
                                                || list_snd_mem tle v)

let[@axiom] list_tl_len_minus_one =
 fun (l : (int * 'a) list) (tle : (int * 'a) list) ->
  (tl l tle)#==>(list_len l == 1 + list_len tle)
