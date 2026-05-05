# CertiRocq Plugin

This directory contains the main CertiRocq plugin for Rocq. It packages
the compiler extracted from `theories/Extraction/` together with the
Rocq frontend and the registration modules for runtime primitives and GMP.

## What It Provides

This is the regular user-facing plugin. Its core commands include:

* `CertiRocq Compile <ref>`
* `CertiRocq Compile Wasm <ref>`
* `CertiRocq Run <ref>`
* `CertiRocq Show IR <ref>`
* `CertiRocq Generate Glue [...]`
* `CertiRocq Eval <ref>`

Here `<ref>` denotes a Rocq global reference, typically the name of a
Gallina definition or constant.

## Building

From the repository root:

```console
$ make plugin
```

This refreshes the extracted OCaml code from `theories/Extraction/` into
`plugins/plugin/extraction/` and then builds the Rocq plugin.

## Loading

In Rocq, load the plugin with:

```coq
From CertiRocq.Plugin Require Import CertiRocq.
```

## Maintaining The Extracted Build

The file lists in `plugins/plugin/_CoqProject` and
`plugins/plugin/certirocq_plugin.mlpack` are generated from
`plugins/manifests/`. The `_CoqProject` extraction entries are discovered from
`plugins/plugin/extraction/`; the `.mlpack` order is maintained in the shared
manifest.

If a change to the extraction pipeline adds or removes generated modules, run:

```console
$ make plugin-manifests
```

Then rebuild with `make plugin`.
