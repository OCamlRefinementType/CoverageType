# Polymorphic Coverage Types

We provide the main code of our tool, with the benchmark suites found in data/PLDI23 (the benchmarks of our PLDI23 conference paper *Covering All the Bases: Type-based Verification of Test Input Generators*) and data/monad (new case study). Each benchmark includes OCaml source code of generator annotated with coverage refinement types for verification (using `let[@assert]`).

For example, the unique list benchmark, located at `data/PLDI23/elrond/UniqueList.ml`, contains the following code:

```
let rec unique_list_gen (s : int) : int list =
  if s == 0 then []
  else
    let (l : int list) = unique_list_gen (s - 1) in
    let (x : int) = int_gen () in
    if list_mem l x then Err else x :: l

let[@assert] unique_list_gen ?r:(s = ((v >= 0 : [%v: int]) [@over])) =
  (list_len v == s && uniq v : [%v: int list]) [@under]
```

where `let unique_list_gen ...` defines the generator impementation and `let[@assert] unique_list_gen ...` specifies a coverage type `s:{v:int | v >= 0} -> [v: int list | list_len(v) = s /\ uniq(v)]`.
