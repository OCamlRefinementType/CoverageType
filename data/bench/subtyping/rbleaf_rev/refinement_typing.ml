let[@library] ( == ) =
  let a = ((true : [%v: int]) [@over]) in
  let b = ((true : [%v: int]) [@over]) in
  ((iff v (a == b) : [%v: bool]) [@under])

let[@library] ( != ) =
  let a = ((true : [%v: int]) [@over]) in
  let b = ((true : [%v: int]) [@over]) in
  ((iff v (a != b) : [%v: bool]) [@under])

let[@library] ( < ) =
  let a = ((true : [%v: int]) [@over]) in
  let b = ((true : [%v: int]) [@over]) in
  ((iff v (a < b) : [%v: bool]) [@under])

let[@library] ( > ) =
  let a = ((true : [%v: int]) [@over]) in
  let b = ((true : [%v: int]) [@over]) in
  ((iff v (a > b) : [%v: bool]) [@under])

let[@library] ( <= ) =
  let a = ((true : [%v: int]) [@over]) in
  let b = ((true : [%v: int]) [@over]) in
  ((iff v (a <= b) : [%v: bool]) [@under])

let[@library] ( >= ) =
  let a = ((true : [%v: int]) [@over]) in
  let b = ((true : [%v: int]) [@over]) in
  ((iff v (a >= b) : [%v: bool]) [@under])

let[@library] ( + ) =
  let a = ((true : [%v: int]) [@over]) in
  let b = ((true : [%v: int]) [@over]) in
  ((v == a + b : [%v: int]) [@under])

let[@library] ( - ) =
  let a = ((true : [%v: int]) [@over]) in
  let b = ((true : [%v: int]) [@over]) in
  ((v == a - b : [%v: int]) [@under])

let[@library] ( mod ) =
  let a = ((true : [%v: int]) [@over]) in
  let b = ((true : [%v: int]) [@over]) in
  ((v == a mod b : [%v: int]) [@under])

let[@library] True = (v : [%v: bool]) [@under]
let[@library] False = (not v : [%v: bool]) [@under]

let[@library] Rbtleaf = (rb_leaf v : [%v: int rbtree]) [@under]

let[@library] Rbtnode =
  let c = (true : [%v: bool]) [@over] in
  let lt = (true : [%v: int rbtree]) [@over] in
  let x = (true : [%v: int]) [@over] in
  let rt = (true : [%v: int rbtree]) [@over] in
  (rb_root_color v c && rb_root v x && rb_lch v lt && rb_rch v rt
    : [%v: int rbtree])
    [@under]
