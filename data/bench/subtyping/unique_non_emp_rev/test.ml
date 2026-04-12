let[@assert] rty1 =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun ((x1 [@exists]) : int) ((l1 [@exists]) : int list) ((s_15 [@exists]) : int) ->
     s > 0 && s_15 >= 0 && s_15 < s
     && s_15 == s - 1
     && len l1 s_15 && uniq l1
     && (not (list_mem l1 x1))
     && hd v x1 && tl v l1
    : [%v: int list])
    [@under]

let[@assert] rty2 =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun ((x2 [@exists]) : int) ((s_15 [@exists]) : int) ((l2 [@exists]) : int list) ->
     s > 0 && s_15 >= 0 && s_15 < s
     && s_15 == s - 1
     && len l2 s_15 && uniq l2
     && (not (list_mem l2 x2))
     && (not (emp v))
     && len v s && uniq v
    : [%v: int list])
    [@under]
