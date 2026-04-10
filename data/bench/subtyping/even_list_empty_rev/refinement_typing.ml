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

let[@library] Nil = (emp v : [%v: int list]) [@under]

let[@library] Cons =
  let x = ((true : [%v: int]) [@over]) in
  let xs = ((true : [%v: int list]) [@over]) in
  ((hd v x && tl v xs : [%v: int list]) [@under])
