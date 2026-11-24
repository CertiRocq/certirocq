# opam overlay for Rocq 9.3

An opam repository with the three dependencies of CertiRocq that have no
release compatible with Rocq 9.3 yet. Each package is the released one, with
the same version number, and these changes:

- `coq-compcert.3.18`: accepts Rocq 9.3.
- `coq-menhirlib.20260209`: accepts Rocq 9.3, with the upstream fix of
  misplaced `Proof` commands (menhir commit 6dedce5d, not released yet).
- `coq-wasm.2.2.1`: accepts Rocq 9.3, with three proof fixes taken from the
  `rocq-master` branch of WasmCert, and requires dune < 3.24, as its
  `dune-project` uses the `coq` extension that dune 3.24 removed.

Register it before installing the dependencies (see `INSTALL.md`):

```console
$ opam repo add certirocq-overlay ./opam-overlay
```

The Nix overlays in `.nix/rocq-overlays` apply the same patch files. Remove a
package from here once a release of it supports Rocq 9.3.
