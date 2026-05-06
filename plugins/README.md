# CertiRocq Plugins

This directory contains the Rocq plugins used to expose CertiRocq commands:

* `plugin/`: the main plugin, built from `theories/Extraction/`. It includes
  runtime primitive registration, GMP support, and the Wasm compilation path.
* `cplugin/`: the vanilla-extraction plugin, built from
  `theories/ExtractionVanilla/`. It is also used by the bootstrapped tools.
* `common/`: OCaml code shared by both plugin variants.
* `manifests/`: the source of truth for generated plugin file lists.

## Building

From the repository root:

```console
$ make plugin
$ make cplugin
```

`make plugin` builds the main plugin from `plugins/plugin/`. `make cplugin`
builds the vanilla plugin from `plugins/cplugin/`.

## Loading

Load the main plugin with:

```coq
From CertiRocq.Plugin Require Import CertiRocq.
```

Load the vanilla plugin with:

```coq
From CertiRocq.VanillaPlugin Require Import CertiRocqVanilla.
```

## Maintaining File Lists

Do not edit these generated files directly:

* `plugins/plugin/_CoqProject`
* `plugins/plugin/certirocq_plugin.mlpack`
* `plugins/cplugin/_CoqProject`
* `plugins/cplugin/certirocq_vanilla_plugin.mlpack`

Instead, update `plugins/manifests/plugin-manifest` and run:

```console
$ make plugin-manifests
```

Use the `[coqproject]` section for hand-written plugin files: Rocq files, static
OCaml support files, frontend `.ml`/`.mli`/`.mlg` files, and metadata files.

Use the `[mlpack]` section for OCaml modules that must be packed into the plugin.
Order matters: list each module after the modules it depends on.

Lines without a suffix are shared by both plugins. Add ` :: plugin` or
` :: cplugin` for variant-specific entries.

Extracted `.ml` and `.mli` files are discovered automatically from each
variant's `extraction/` directory, so do not list them in `[coqproject]`. If a
new extracted module must be packed, add only its module name to `[mlpack]`.

Shared OCaml files in `plugins/common/` are not local `_CoqProject` sources. Add
explicit build rules for them in each affected `Makefile.local-late`, and add
their module names to `[mlpack]` if they are packed into the plugin.
