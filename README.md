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

You can also find end-to-end examples in [tests/programs/tests.v](tests/programs/tests.v) and [tests/axioms/tests.v](tests/axioms/tests.v).

## Installation Instructions

See [INSTALL.md](INSTALL.md)  for installation instructions.

## Current Members

Yannick Forster, Joomy Korkut, Zoe Paraskevopoulou, and Matthieu Sozeau.

## Past Members and Contributors

Andrew Appel, Abhishek Anand, Anvay Grover, John Li, Greg Morrisett, Randy Pollack, Olivier Savary Belanger, Matthew Weaver

## License

CertiRocq is open source and distributed under the [MIT license](LICENSE.md).

## Directory structure

* `libraries/` contains shared Rocq utilities used throughout the development
* `theories/` contains the core compiler development and proofs
* `plugin/` contains the main CertiRocq plugin for Rocq, intended for regular use and built from the standard extraction pipeline
* `cplugin/` contains the vanilla-extraction variant of the CertiRocq plugin, used as the more conservative plugin variant and as the basis for bootstrapped tools
* `runtime/` contains the C runtime support and FFI helpers used by generated programs
* `tests/` contains demos, regression tests, and end-to-end test harnesses
* `bootstrap/` contains the bootstrapped CertiRocq plugin for Rocq and
  a CertiRocq-compiled variant of MetaRocq's safe type checker

Structure of the theories directory:

* `theories/common`: contains common utilities shared across the development
* `theories/LambdaBox_to_LambdaANF`: contains the translation from MetaRocq's erased LambdaBox language to CertiRocq's ANF IR
* `theories/LambdaANF`: contains the λANF IR, optimization pipeline, and proofs
* `theories/Compiler`: contains the top-level CertiRocq pipeline
* `theories/Codegen`: contains the Clight code generator
* `theories/CodegenWasm`: contains the Wasm code generator
* `theories/Glue`: contains glue-code generation support
* `theories/Extraction` and `theories/ExtractionVanilla`: contain the extraction entry points used to build the two plugin variants


## Bugs 

We use github's [issue tracker](https://github.com/CertiRocq/certirocq/issues) to keep track of bugs and feature requests.
