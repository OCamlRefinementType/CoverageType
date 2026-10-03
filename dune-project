(lang dune 3.16)

(name CoverageType)

(generate_opam_files true)

(source
 (github username/reponame))

(pin
 (package
  (name zutils))
 (url
  "git+https://github.com/OCamlRefinementType/zutils.git#b00108225b1a2e70c1ee858a1f547b7ace6cd7a5"))

(authors "Author Name")

(maintainers "Maintainer Name")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name CoverageType)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
  ocaml
  dune
  core
  core_unix
  ppx_optcomp
  ppx_compare
  ppx_sexp_conv
  ppx_inline_test
  ppx_assert
  ppx_deriving
  ppx_here
  ppx_deriving_yojson
  zutils
  (z3 (= 4.15.2))
  spectrum)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
