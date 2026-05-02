# `tests/ocaml`

This directory extracts selected CertiRocq test programs to OCaml, builds them
with both the bytecode and native OCaml compilers, and reports execution times.

Run from the top-level test driver with:

```sh
make -C tests ocaml
```

If you run this directory directly, build `tests/lib` first:

```sh
make -C tests lib
make -C tests/ocaml run
```

`tests.v` regenerates the OCaml benchmark modules used by this directory. The
`vs_easy` and `vs_hard` wrappers are written so that the expensive VeriStar
computations remain deferred until the benchmark function is called, rather than
being evaluated at OCaml module initialization time.
