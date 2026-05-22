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

# Testing

Currently, the testing suite is split into four groups:
  - `test/fast`, which are non-flaky tests that run relatively fast
  - `test/slow`, which are non-flaky tests that run a bit slow (>1s locally for me)
  - `test/flaky`, which are flaky tests which may or may not pass,
    depending on the exact local configuration
  - `test/monad`, which are the tests using some of the parametric and monadic features.
    Currently, they are not working, so they have been kept in a separate file for now.

Running `dune test test/fast -w` in a separate test window while developing
will run each test on any file change, which makes it easier to ensure that 
each change preserves the prior behavior of the type checker. The CI runs
`dune test test/fast test/slow`, which runs both the fast and slow test sets.
By default, the testing framework only shows the tests which failed.
