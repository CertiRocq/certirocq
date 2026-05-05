# CertiRocq Vanilla Plugin

This directory contains the vanilla-extraction variant of the CertiRocq
plugin for Rocq. It is built from `theories/ExtractionVanilla/` and is
used as the vanilla plugin variant and as the basis for the bootstrapped
tools under `bootstrap/`.

## What It Provides

This plugin supports the core CertiRocq commands for compiling,
running, inspecting, and evaluating Gallina definitions:

* `CertiRocq Compile <ref>`
* `CertiRocq Run <ref>`
* `CertiRocq Show IR <ref>`
* `CertiRocq Generate Glue [...]`
* `CertiRocq Eval <ref>`

Here `<ref>` denotes a Rocq global reference, typically the name of a
Gallina definition or constant.

Compared with the main plugin, this variant does not provide
`CertiRocq Compile Wasm` and does not export the GMP helper module.

## Building

From the repository root:

```console
$ make cplugin
```

This refreshes the extracted OCaml code from
`theories/ExtractionVanilla/` into `plugins/cplugin/extraction/` and then builds
the Rocq plugin.

## Loading

In Rocq, load the plugin with:

```coq
From CertiRocq.VanillaPlugin Require Import CertiRocqVanilla.
```

## Maintaining The Extracted Build

The file lists in `plugins/cplugin/_CoqProject` and
`plugins/cplugin/certirocq_vanilla_plugin.mlpack` are generated from
`plugins/manifests/`. The `_CoqProject` extraction entries are discovered from
`plugins/cplugin/extraction/`; the `.mlpack` order is maintained in the shared
manifest.

If a change to the extraction pipeline adds or removes generated modules, run:

```console
$ make plugin-manifests
```

Then rebuild with `make cplugin`.
