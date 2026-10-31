# Installing CertiRocq

These instructions build CertiRocq from source inside a dedicated
[opam](https://opam.ocaml.org) switch.

## Prerequisites

- opam 2.1 or later, initialized with `opam init`
  ([installation instructions](https://opam.ocaml.org/doc/Install.html))
- git, GNU make, Python 3 and a C compiler (clang). On macOS, these come with
  the Xcode Command Line Tools (`xcode-select --install`).

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

```console
$ ./configure.sh
$ make -j4        # libraries and theories
$ make plugin     # the CertiRocq plugin
$ make cplugin    # the plugin variant built with vanilla extraction
```

Building the theories is by far the slowest step. `-j4` runs four jobs in
parallel; adjust the number to your machine.

## Running the tests

The regression suites live under `tests/`. Run them all, or one suite at a
time:

```console
$ make -C tests all
$ make -C tests programs
```

All suites except `tests/ffi` use the plugin from your build directory.
`tests/ffi` uses the installed plugin, so it needs `make install` first (see
below). The Wasm tests under `tests/wasm/` additionally require `node` (the CI
uses Node.js 22) and `wabt`.

## Installing CertiRocq (optional)

You don't need this to work on CertiRocq. To install the theories and plugins
into the current switch, run:

```console
$ make install
```

This also builds the bootstrapped plugins under `bootstrap/`.

## Troubleshooting

**`Unable to locate library EImplementLazyForce with prefix MetaRocq.Erasure`**:
the switch has a released MetaRocq. Pin it as in step 3 and rerun
`opam install --deps-only -y .`.

**`Compiled library ... makes inconsistent assumptions over library ...`**:
some build files were compiled against older dependencies, for example
before upgrading MetaRocq. The build does not detect this by itself, so clean
everything and build again as in step 5:

```console
$ make clean
```
