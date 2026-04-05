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

let[@library] Leaf = (leaf v : [%v: int tree]) [@under]

let[@library] Node =
  let x = ((true : [%v: int]) [@over]) in
  let lt = ((true : [%v: int tree]) [@over]) in
  let rt = ((true : [%v: int tree]) [@over]) in
  ((root v x && lch v lt && rch v rt : [%v: int tree]) [@under])
