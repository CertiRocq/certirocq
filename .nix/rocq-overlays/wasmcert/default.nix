# The wasmcert package of nixpkgs, with the proof fixes that WasmCert 2.2.1
# needs to build with Rocq 9.3. They are taken from the rocq-master branch of
# WasmCert, and are not in a release yet.
{
  pkgs,
  callPackage,
  version ? null,
}:

(callPackage (pkgs.path + "/pkgs/development/rocq-modules/wasmcert") { inherit version; })
.overrideAttrs
  (o: {
    patches = (o.patches or [ ]) ++ [ ./rocq-9.3.patch ];
  })
