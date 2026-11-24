# The MenhirLib package of nixpkgs, with the upstream fix that makes it build
# with Rocq 9.3 (menhir commit 6dedce5d), which is not in a release yet.
{
  pkgs,
  callPackage,
  version ? null,
}:

(callPackage (pkgs.path + "/pkgs/development/rocq-modules/MenhirLib") { inherit version; })
.overrideAttrs
  (o: {
    patches = (o.patches or [ ]) ++ [ ./fix-proof-commands.patch ];
  })
