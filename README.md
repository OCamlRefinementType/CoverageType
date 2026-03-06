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

## Compiling CoverageType for Pasiv
Because of naming conflicts in the `rocq-runtime` library, building the project is a little more involved than it ideally should be.

We need to build Rocq from source from a custom fork that patches out the `rocq-runtime` naming issues. Since the Rocq fork is off of `master`, this also introduces a compilation error in `stdlib` v9.0.0 (the version on `opam`) and we also need to build *that* from source. In order to not pollute any external Rocq packages / versions, it's probably recommended to create a new `opam` switch first.
```bash
opam switch create rocq_fork 5.2.1
eval $(opam env)

git clone https://github.com/ky28059/rocq
cd rocq
git checkout use-wrapped-modules
opam install .

cd ..
git clone https://github.com/rocq-prover/stdlib
cd stdlib
make
make install
```
(If you're using VSCode for OCaml, install the LSP server here before other dependencies.)
```bash
opam install ocaml-lsp-server ocamlformat
```
The rest proceeds as usual; assuming `CoverageType` and `zutils` are cloned, simply `opam install .` to automatically pull in required dependencies (I've updated the `dune-project` files so that the listed dependencies are accurate):
```bash
cd ../zutils
git checkout pasiv
opam install .

cd ../CoverageType
git checkout jfp
opam install . --deps-only
```
(currently, the recompiled `rocq-runtime` doesn't automatically figure out where the standard library is; you can instead run
```bash
ky28059@ky28059:~/CoverageType$ rocq c -where
/home/ky28059/.opam/rocq_fork/lib/coq
```
to find the correct path and manually export
```bash
export ROCQLIB=/home/ky28059/.opam/rocq_fork/lib/coq
```
to fix this. I'm hopeful to fix this programmatically in the future.)

Afterwards, you can run
```bash
dune exec ./bin/main.exe subtype-check [path to subtype file]
```
to run a subtyping check.

### Customizing axioms / definitions
Currently, the files which CoverageType pulls axioms, type definitions, and refinement type definitions from are hard-coded in `./preprocess/preprocess.ml`; to customize axioms or typedefs these files can be overridden, or `preprocess.ml` can be edited to point to different files.

Note that if axioms or typedefs change, you may also want to edit the predefined proofs (for axioms) and definitions (for type predicates) that `zutils` generates in the Rocq file in case of an SMT failure. These are currently hard-coded in `../zutils/rocqParser/defs.ml`:
- `built_in_type_sigs` defines a list of custom type signatures (`list` and `option` are Rocq builtins, but other inductive types referenced by axioms or typedefs need to be defined here).
```rocq
Parameter tree : forall (a : Type), Type.
```
- `built_in_type_defs` defines the implementations for the types listed in `built_in_type_sigs`.
```rocq
Inductive tree' (a : Type) : Type :=
| Leaf : tree' a
| Node : a -> tree' a -> tree' a -> tree' a.
Definition tree := tree'.
```
- `built_in_defs` maps type predicates e.g.
```ocaml
val hd : 'a list -> 'a -> bool
```
into Rocq definitions e.g.
```rocq
Definition hd {a : Type} (l : list a) (n : a) : Prop :=
  match l with
  | nil => False
  | cons n' _ => n = n'
  end.
```
- `built_in_proofs` maps axioms e.g.
```ocaml
let[@axiom] list_emp_no_hd (l : int list) (x : int) =
  (emp l) #==> (not (hd l x))
```
into Rocq proofs e.g.
```rocq
Lemma list_emp_no_hd : forall (l : list Z), forall (x : Z), emp l -> ~hd l x.
Proof.
  intros [| x'] x H.
  - intros [].
  - contradiction. 
Qed.
```

For the simplest use case, adding to the latter two maps is optional;
- a typedef whose definition was not found in `built_in_defs` will simply be emitted as a `Parameter` without a body
- an axiom whose proof was not found in `built_in_proofs` will simply be `Admitted`

but populating the maps may help with proving new axioms in the `Axioms` module.
