# CertiRocq

<p align="center">
<img width="500" alt="CERTIROCQ_LOGO-logo-1" src="https://github.com/user-attachments/assets/bf3e20f3-7632-4e39-8dea-5871f28971cf" />
</p>

## Overview

[![build](https://github.com/CertiRocq/certirocq/actions/workflows/build.yml/badge.svg)](https://github.com/CertiRocq/certirocq/actions/workflows/build.yml)

![GitHub](https://img.shields.io/github/license/CertiRocq/certirocq)


CertiRocq is a compiler for Gallina, the specification language of the [Rocq Prover](https://rocq-prover.org). CertiRocq targets WebAssembly and Clight, a subset of the C language that can be compiled with any C compiler, including the [CompCert](http://compcert.org) verified compiler.

Large parts of the CertiRocq compiler have been verified whereas others are in the process of being verified.

## Documentation

The [CertiRocq Wiki](https://github.com/certirocq/certirocq/wiki) has instructions for using the [CertiRocq plugin](https://github.com/certirocq/certirocq/wiki/The-CertiRocq-plugin) to compile Gallina to C and interfacing with the generated C code.

You can also find some demos [here](https://github.com/CertiRocq/certirocq/blob/master/benchmarks/tests.v) and [here](https://github.com/CertiRocq/certirocq/blob/master/benchmarks/axioms/tests.v).

## Installation Instructions

See [INSTALL.md](INSTALL.md)  for installation instructions.

## Current Members

Yannick Forster, Joomy Korkut, Zoe Paraskevopoulou, and Matthieu Sozeau.

## Past Members and Contributors

Andrew Appel, Abhishek Anand, Anvay Grover, John Li, Greg Morrisett, Randy Pollack, Olivier Savary Belanger, Matthew Weaver

## License

CertiRocq is open source and distributed under the [MIT license](LICENSE.md).

## Directory structure

* `theories/` contains the sources of the compiler
* `plugin/` contains the CertiRocq plugin for Rocq
* `benchmarks/` contains the benchmark suite
* `glue/` contains the glue code generator
* `bootstrap/` contains the bootstrapped CertiRocq plugin for Rocq and
  a CertiRocq-compiled variant of MetaRocq's safe type checker.

Structure of the theories directory:

* `theories/common`: contains common code utilities 
* `theories/Compiler`: contains the toplevel CertiRocq pipeline
* `theories/LambdaBoxMut`: mutual inductive version of MetaRocq's LambdaBox erased language
* `theories/LambdaBoxLocal`: variant where deBruijn indices are represented using `N` instead of `nat`.
   The transformation from LambdaBoxMut let-binds the definitions in the environment to
   produce a closed term.
* `theories/LambdaANF` contains the λANF pipeline (and conversions -- direct and LambdaANF -- to λANF)
* `theories/Codegen` contains the C code generator.
* `theories/CodegenWasm` contains the Wasm code generator.


## Bugs 

We use github's [issue tracker](https://github.com/CertiRocq/certirocq/issues) to keep track of bugs and feature requests.
