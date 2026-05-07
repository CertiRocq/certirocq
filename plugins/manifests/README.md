# Plugin Manifests

This directory is the source of truth for the generated plugin file lists:

* `plugins/plugin/_CoqProject`
* `plugins/plugin/certirocq_plugin.mlpack`
* `plugins/cplugin/_CoqProject`
* `plugins/cplugin/certirocq_vanilla_plugin.mlpack`

The shared manifest is `plugin-manifest`. Lines without a suffix are shared by
both plugin variants; lines ending in ` :: plugin` or ` :: cplugin` are
variant-specific.

The generated `_CoqProject` files also include the `.ml` and `.mli` files
discovered from each plugin's `extraction/` directory. These generated
extraction file names are not maintained in `plugin-manifest`. Shared OCaml
sources from `plugins/common/` are compiled by the plugin-specific
`Makefile.local-late` files, not listed as local `_CoqProject` entries.

The generator validates `.mlpack` entries against the modules available in the
plugin directory, `static/`, and `extraction/`, plus the common modules compiled
from `plugins/common/`.

Regenerate the checked-in files with:

```console
$ make plugin-manifests
```
