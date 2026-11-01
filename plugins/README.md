# CertiRocq Plugins

This directory contains the Rocq plugins used to expose CertiRocq commands:

* `plugin/`: the main plugin, built from the extraction of the compiler by
  `plugin/extraction.v`. It includes runtime primitive registration, GMP
  support, and the Wasm compilation path.
* `cplugin/`: the vanilla-extraction plugin, built from the extraction by
  `cplugin/extraction.v`. It is also used by the bootstrapped tools.
* `common/`: OCaml code shared by both plugin variants.

## Building

The plugins are built with dune, from the repository root:

```console
$ dune build -p rocq-certirocq,rocq-certirocq-vanilla
```

Each plugin's `dune` file extracts the compiler (`rocq.extraction`), builds the
OCaml library from the extracted code, the files of `static/` and of `common/`
and the `get_ordinal.c` stub of the runtime, and builds the Rocq theory that
loads it. The commands of `common/certirocq_commands.mlg` are included in each
plugin's `.mlg` file by `cpp`, which sets the name of the plugin.

## Loading

Load the main plugin with:

```coq
From CertiRocq.Plugin Require Import CertiRocq.
```

Load the vanilla plugin with:

```coq
From CertiRocq.VanillaPlugin Require Import CertiRocqVanilla.
```

## Maintaining the lists of extracted modules

dune needs to know the modules produced by each extraction, which are listed in
the `extracted_modules` field of each plugin's `dune` file. When the extracted
code changes, for example with a new dependency of the compiler, update the
lists with:

```console
$ dune build theories
$ plugins/update-extracted-modules.sh
```
