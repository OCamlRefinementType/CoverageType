# Polymorphic Coverage Types

`Poirot` is a refinement-type checker for verifying that OCaml **test input
generators** cover the input space they're supposed to. It implements the
*coverage type* system from:

> **Polymorphic Coverage Types**, Zhe Zhou, Ashish Mishra, Benjamin Delaware,
> Suresh Jagannathan. (JFP 2026; extends the PLDI 2023 paper *Covering All the
> Bases: Type-Based Verification of Test Input Generators*.)
> https://jfp.episciences.org/en/articles/17755

A coverage type says what values an expression is **guaranteed** to
produce (a "must" property), which is the dual of an ordinary
refinement type's "may" guarantee. This lets you write an input
generator, annotate it with the shape of data you expect it to cover,
and have the checker statically verify that it actually does.

Benchmarks live in `data/PLDI23` (from the PLDI'23 paper) and
`data/monad` (monadic/combinator case studies), with
smaller/miscellaneous cases under `data/simple`, `data/test_cases`,
and `data/inline_test`.

## Quick start

You'll need an opam switch with OCaml 5.2.0 and dune >=
3.16. `zutils`, the one dependency not on the public opam repo, is
pinned automatically from `CoverageType.opam`'s `pin-depends`:

```bash
opam switch create coverage-type 5.2.0
opam install . --deps-only --with-test
dune build
```

(See `.github/workflows/build.yml` for the exact sequence CI runs.)

## Checking a benchmark

Each benchmark is a `.ml` file with a generator and a `let[@assert]`
declaration giving it a coverage type. For example,
`data/PLDI23/elrond/UniqueList.ml` declares:

```ocaml
let[@assert] unique_list_gen ?r:(s = ((v >= 0 : [%v: int]) [@over])) =
  (list_len v == s && uniq v : [%v: int list]) [@under]
```

This type annotation says that when applied to any non-negative
argument `s`, `unique_list_gen` will produce every list with exactly
`s` elements containing unique elements.

We can check that `unique_list_gen` satisfies this specification via
the following command:

```bash
dune exec bin/main.exe -- type-check data/PLDI23/elrond/UniqueList.ml
```

The tail of the output tells you whether it typechecks:

```
Task unique_list_gen, type check succeeded
Summary (total 1 tasks):
All tasks succeeded
Result: true
```

`type-check` exits with status 0 if every task succeeds and 1
otherwise, so it can be used directly in scripts.

Poirot also provides two additional commands, for answering more
tailored questions:

```bash
dune exec bin/main.exe -- print-source-code <file>   # show the parsed/desugared program
dune exec bin/main.exe -- subtype-check <file>       # check a `rty1 <: rty2` declared in <file>
```

## Running the test suite

Tests are split into four categories under `test/`:

- `test/fast` — non-flaky tests that run quickly; use this while developing
- `test/slow` — non-flaky tests that take longer (CI runs both fast and slow)
- `test/flaky` — may or may not pass depending on local configuration
- `test/monad` — monadic/parametric feature tests (currently not all passing)

```bash
dune test test/fast test/slow   # what CI runs
dune test test/fast -w          # watch mode: re-runs on every file change
```

## Debugging a failing typecheck

The output of the type checker is controlled by `meta-config.json` (or
`test/meta-config.json` for the test suite).  The file has two
relevant sections: `"zutils"` (the solver library) and `"typechecker"`
(Poirot itself), each with its own list of `log_tags`:

```json
{
    "zutils": {
        "log_tags": [],
        ...
    },
    "typechecker": {
        "log_tags": ["auxtyping", "preprocess", "typing", "result"],
        ...
    }
}
```

The most useful tag when a benchmark won't typecheck is `"auxtyping"`
(shown above): it prints every subtyping/non-emptiness query the
checker sends to the SMT solver, in both a human-readable form and as
a `let[@valid] tmp = ...` declaration. You can paste the latter into a
scratch file to futher explore the failing query.

Other tags for the `"typechecker"` section include:

- `"typing"`: the bidirectional typing derivation
- `"preprocess"`: desugaring and normalization
- `"result"`: per-task results and the final summary

The full list is in `typechecker_config/typecheckerLog.ml`. To quiet
the output, remove tags from the list; with an empty list you'll only
see the final `Result:` line.

## The type annotation syntax

Coverage types are written as OCaml attributes on top-level `let`
bindings:

| Attribute | Meaning |
|---|---|
| `[@assert]` | Asks the type checker to check the identified generator against the given coverage type |
| `[@assume]` / `[@library]` | Declares an assumed, _unchecked_ coverage type for a generator named by the `let`-bound identifier. This is typically used for library or primitive function |
| `[@axiom]` | Declares a fact that is assumed to hold when type checking. The associated `let`-bound identifier is simply a name for the axiom  |
| `[@valid]` / `[@sat]` | Asks the type checker whether a proposition is valid / satisfiable. The associated `let`-bound identifier is just a name, similiar to axioms. See `data/test_cases/valid_sat.ml` for examples |
| `[@over]` | Marks a qualifier as a standard ("may") refinement |
| `[@under]` | Marks a qualifier as a coverage ("must") type. This is the default when unmarked |
| `[%v: ty]` | Ascribes base type `ty` to the preceding qualifier, binding `v` |

`v` is a reserved name for a qualifier's bound variable, matching the
paper's `{v:b | φ}` notation.

## Repository layout

| Path | Contents |
|---|---|
| `ast/` | AST definitions, substitution, pretty-printing |
| `auxtyping/` | Subtyping, non-emptiness, and well-foundedness checking |
| `bin/` | CLI entry point (`main.ml`) |
| `data/` | Benchmarks: `PLDI23/`, `monad/`, `simple/`, `test_cases/`, `inline_test/`, and `predefined/` (shared axioms & library signatures every benchmark depends on) |
| `formalization/` | Rocq mechanization of the calculus and metatheory — see its own [README](formalization/README.md) |
| `frontend_opt/` | Parses the OCaml-attribute surface syntax into refinement types |
| `language/` | Shared language-level helpers (well-formedness of typing contexts, etc.) |
| `lib/` | Top-level `CoverageType` library stanza (dune only, no source files) |
| `preprocess/` | ANF/monadic-normal-form normalization, alias/type-context loading |
| `script/` | Python scripts that run various benchmarks and collate the results |
| `statistic/` | Collects per-function metrics during type checking |
| `test/` | Expect-tests, split into `fast`/`slow`/`flaky`/`monad` |
| `typechecker_config/` | Reads the `"typechecker"` section of `meta-config.json` and defines the log tags (see `typecheckerLog.ml`)|
| `typing/` | The bidirectional typing algorithm (`bidirect.ml`) |

### Tests 
Currently, the testing suite is split into three groups:
  - `test/fast`, which are tests that run relatively fast
  - `test/slow`, which are tests that run a bit slow (>1s locally for me)
  - `test/monad`, which are the tests using some of the parametric and monadic features.
    Currently, they are not working, so they have been kept in a separate file for now.

### Formalization
`formalization/` contains a Rocq mechanization of the core calculus, its
type system, and the soundness metatheory referenced in the paper. See
[`formalization/README.md`](formalization/README.md) for the file-by-file
breakdown.
