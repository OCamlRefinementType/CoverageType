val stream_gen : int -> int stream

let[@library] stream_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((stream_len v == s : [%v: int stream]) [@under])

let bankersq_gen (lenf : int) : (int * int stream) * (int * int stream) =
  let (lenr : int) = int_range_inc 0 lenf in
  let (f : int stream) = stream_gen lenf in
  let (r : int stream) = stream_gen lenr in
  ((lenf, f), (lenr, r))

let[@assert] bankersq_gen =
  let s = ((v >= 0 : [%v: int]) [@over]) in
  (stream_len (snd (fst v)) == fst (fst v)
   && stream_len (snd (snd v)) == fst (snd v)
   && fst (snd v) < fst (fst v)
   && s == fst (fst v)
    : [%v: (int * int stream) * (int * int stream)])
