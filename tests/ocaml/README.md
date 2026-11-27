# `tests/ocaml`

This directory extracts selected CertiRocq test programs to OCaml, builds them
with both the bytecode and native OCaml compilers, and reports execution times.

Run it with:

```sh
dune test tests/ocaml
```

`tests.v` extracts the OCaml benchmark modules used by this directory. The
`vs_easy` and `vs_hard` wrappers are written so that the expensive VeriStar
computations remain deferred until the benchmark function is called, rather than
being evaluated at OCaml module initialization time.
