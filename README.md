# Polymorphic Coverage Types

`Poirot` is a refinement-type checker for verifying that OCaml **test input
generators** cover the input space they're supposed to. It implements the
*coverage type* system from:

> **Polymorphic Coverage Types**, Zhe Zhou, Ashish Mishra, Benjamin Delaware,
> Suresh Jagannathan. (JFP; extends the PLDI 2023 paper *Covering All the
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

You'll need an opam switch with OCaml 5.2.0 and dune >= 3.16 (CI
builds with dune 3.23). `zutils`, the one dependency not on the public
opam repo, is pinned automatically from `CoverageType.opam`'s
`pin-depends`:

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

This type annotation says that when applied to any non-zero argument
`s`, `unique_list_gen` will produce every list with exactly `s`
elements containing unique elements.

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
```

Poirot also provides two additional commands, for answering more
tailored questions:

```bash
dune exec bin/main.exe -- print-source-code <file>   # show the parsed/desugared program
dune exec bin/main.exe -- subtype-check <file>        # check a `rty1 <: rty2` declared in <file>
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

`meta-config.json` (or `test/meta-config.json` for the test suite)
controls what the checker prints, via `log_tags`. The most useful tag
when a benchmark won't typecheck is `"auxtyping"`: it prints every
subtyping/non-emptiness query the checker sends to the SMT solver, in
both a human-readable and a `let[@axiom]`-formatted form you can paste
into a scratch file to explore further.

```jsonc
"log_tags": [
    // ...
    "auxtyping",   // <- uncomment this
    // ...
],
```

Two things to note about this configuration file:

- This file is 'JSON plus `//`-style comments', with the comments
  being stripped before parsing. If you uncomment a tag, make sure to
  remove its trailing comma if its the last one; otherwise the config
  will fail to parse.

- Other useful tags:
  + `"typing"` (the bidirectional typing derivation),
  + `"preprocess"` (desugaring),
  + `"result"` (pass/fail summary only)

## The type annotation syntax

Coverage types are written as OCaml attributes on top-level `let`
bindings:

| Attribute | Meaning |
|---|---|
| `[@assert]` | Declares the coverage type to check a generator against |
| `[@library]` | Declares the (assumed, unchecked) type of a primitive/constructor |
| `[@axiom]` | Declares a fact about an uninterpreted predicate that is assumed to be true |
| `[@over]` | Marks a qualifier as a standard ("may") refinement |
| `[@under]` | Marks a qualifier as a coverage ("must") type. This is the default when unmarked |
| `[%v: ty]` | Ascribes base type `ty` to the preceding qualifier, binding `v` |

`v` is a reserved name for a qualifier's bound variable, matching the
paper's `{v:b | φ}` notation.

## Repository layout

| Path | Contents |
|---|---|
| `ast/` | AST definitions, substitution, pretty-printing |
| `frontend_opt/` | Parses the OCaml-attribute surface syntax into refinement types |
| `preprocess/` | ANF/monadic-normal-form normalization, alias/type-context loading |
| `language/` | Shared language-level helpers (well-formedness of typing contexts, etc.) |
| `typing/` | The bidirectional typing algorithm (`bidirect.ml`) |
| `auxtyping/` | Subtyping, non-emptiness, and well-foundedness checking |
| `bin/` | CLI entry point (`main.ml`) |
| `data/` | Benchmarks: `PLDI23/`, `monad/`, `simple/`, `test_cases/`, `inline_test/`, and `predefined/` (shared axioms & library signatures every benchmark depends on) |
| `test/` | Expect-tests, split into `fast`/`slow`/`flaky`/`monad` |
| `formalization/` | Rocq mechanization of the calculus and metatheory — see its own [README](formalization/README.md) |
| `script/`, `statistic/` | Benchmark-running and result-aggregation utilities |

## Active development

Besides `main`, the repo currently has three other branches: `jfp`,
`poly`, and `noGarr`. If you're picking up work on a specific
extension, check with a maintainer for which branch has the code you
want. `main` isn't necessarily where the latest work on any given
feature lives.

## Formalization

`formalization/` contains a Rocq mechanization of the core calculus, its
type system, and the soundness metatheory referenced in the paper. See
[`formalization/README.md`](formalization/README.md) for the file-by-file
breakdown.
