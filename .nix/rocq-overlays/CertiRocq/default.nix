{
  lib,
  pkgs,
  mkRocqDerivation,
  rocq-core,
  wasmcert,
  compcert,
  metarocq-erasure-plugin,
  metarocq-safechecker-plugin,
  ExtLib,
  version ? null,
}:

with lib;
let
  # The theories, the optimized plugin and its runtime, and the vanilla plugin
  packages = [ "rocq-certirocq" "rocq-certirocq-vanilla" ];
in
(mkRocqDerivation {
  pname = "CertiRocq";
  owner = "CertiRocq";
  repo = "certirocq";
  opam-name = "rocq-certirocq";
  useDune = true;
  mlPlugin = true;

  inherit version;
  releaseRev = v: "v${v}";

  propagatedBuildInputs = [
    # Used by the runtime, and by the programs compiled with its GMP bindings
    pkgs.gmp
    wasmcert
    compcert
    ExtLib
    metarocq-erasure-plugin
    metarocq-safechecker-plugin
  ];

  # The plugin invokes a C compiler to build the code it generates,
  # so dependents need one too.
  propagatedNativeBuildInputs = [
    pkgs.clang
  ];

  meta = {
    description = "CertiRocq";
    maintainers = with maintainers; [ womeier ];
    license = licenses.mit;
  };
}).overrideAttrs (o: {
  buildPhase = ''
    runHook preBuild
    dune build -p ${concatStringsSep "," packages} ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
    runHook postBuild
  '';
  installPhase = ''
    runHook preInstall
    dune install --prefix=$out --libdir $OCAMLFIND_DESTDIR ${concatStringsSep " " packages}
    mkdir $out/lib/coq/
    mv $OCAMLFIND_DESTDIR/coq $out/lib/coq/${rocq-core.rocq-version}
    runHook postInstall
  '';
})
