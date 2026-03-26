let[@assert] rty1 =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun ((x1 [@exists]) : int) ((s1 [@exists]) : int) ((l1 [@exists]) : int list) ->
     s > 0 && s1 >= 0 && s1 < s
     && s1 == s - 1
     && len l1 s1 && uniq l1
     && (not (list_mem l1 x1))
     && (not (emp v))
     && len v s && uniq v
    : [%v: int list])
    [@under]

let[@assert] rty2 =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun ((x2 [@exists]) : int) ((l2 [@exists]) : int list) ((s2 [@exists]) : int) ->
     s > 0 && s2 >= 0 && s2 < s
     && s2 == s - 1
     && len l2 s2 && uniq l2
     && (not (list_mem l2 x2))
     && hd v x2 && tl v l2
    : [%v: int list])
    [@under]
