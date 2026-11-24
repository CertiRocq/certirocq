# The compcert package of nixpkgs, configured to accept Rocq 9.3: the configure
# script of CompCert 3.18 only accepts Rocq up to 9.2, although it builds with 9.3.
{
  pkgs,
  callPackage,
  version ? null,
}:

(callPackage (pkgs.path + "/pkgs/development/rocq-modules/compcert") { inherit version; })
.overrideAttrs
  (o: {
    configurePhase = "${o.configurePhase} -ignore-coq-version";
  })
