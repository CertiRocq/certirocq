# Installing CertiRocq

These instructions build CertiRocq from source inside a dedicated
[opam](https://opam.ocaml.org) switch.

## Prerequisites

- opam 2.1 or later, initialized with `opam init`
  ([installation instructions](https://opam.ocaml.org/doc/Install.html))
- git, GNU make, Python 3 and a C compiler (clang). On macOS, these come with
  the Xcode Command Line Tools (`xcode-select --install`).
- GMP, used by the C runtime (`brew install gmp` on macOS).

## 1. Get the code

```console
$ git clone https://github.com/CertiRocq/certirocq.git
$ cd certirocq
```

## 2. Create an opam switch

Create a switch with OCaml 4.14 and add the Rocq package repository:

```console
$ opam switch create certirocq ocaml-base-compiler.4.14.2
$ eval $(opam env --switch=certirocq --set-switch)
$ opam repo add rocq-released https://rocq-prover.org/opam/released
```

Whenever you open a new terminal, run
`eval $(opam env --switch=certirocq --set-switch)` again to use this switch.

## 3. Pin MetaRocq

CertiRocq currently depends on a version of MetaRocq that has not been
released yet (the `9.1` branch). Pin MetaRocq to the commit that CertiRocq is
tested against:

```console
$ opam pin add --no-action -y git+https://github.com/MetaRocq/metarocq.git#c8cd46054518193103c3bb33aa6e15c7f489e72c
```

## 4. Install the dependencies

From the `certirocq/` directory, run:

```console
$ opam install --deps-only -y .
```

This builds Rocq 9.1, MetaRocq, CompCert, WasmCert and the other dependencies
from source, which takes about half an hour on a recent laptop. If opam reports missing system
packages (for example GMP), install them with your system package manager and
run the command again.

## 5. Build CertiRocq

CertiRocq is built with [dune](https://dune.build):

```console
$ dune build
```

This builds the theories, the CertiRocq plugin and its C runtime, the plugin
variant built with vanilla extraction, and the bootstrapped compiler and
checker under `bootstrap/`. To build only some of them, name their packages,
for example `dune build -p rocq-certirocq,rocq-certirocq-vanilla`. Building the
theories is by far the slowest step; dune runs as many jobs in parallel as the
machine has cores.

`make` and `make install` are shortcuts for `dune build` and `dune install`.

## Running the tests

```console
$ make test
```

This runs the tests of the bootstrapped compiler and checker (`dune test`),
then the regression suites under `tests/`. These use the packages as installed
in the build directory, `_build/install/default`; to run a single suite, point
`ROCQPATH` and `OCAMLPATH` there:

```console
$ ROCQPATH=$PWD/_build/install/default/lib/coq/user-contrib \
  OCAMLPATH=$PWD/_build/install/default/lib make -C tests programs
```

The Wasm tests under `tests/wasm/` additionally require `node` (the CI uses
Node.js 22) and `wabt`.

## Installing CertiRocq (optional)

You don't need this to work on CertiRocq. To install the theories and plugins
into the current switch, run:

```console
$ dune install
```

## Troubleshooting

**`Unable to locate library EImplementLazyForce with prefix MetaRocq.Erasure`**:
the switch has a released MetaRocq. Pin it as in step 3 and rerun
`opam install --deps-only -y .`.

**`Compiled library ... makes inconsistent assumptions over library ...`**:
some build files were compiled against older dependencies, for example
before upgrading MetaRocq. The build does not detect this by itself, so clean
everything and build again as in step 5:

```console
$ dune clean
```
