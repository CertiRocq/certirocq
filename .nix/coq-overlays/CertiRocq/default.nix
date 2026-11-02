{
  lib,
  pkgs,
  mkCoqDerivation,
  coq,
  wasmcert,
  coqprime,
  compcert,
  metarocq,
  ExtLib,
  version ? null,
}:

with lib;
let
  # The bootstrapped plugins and the CI files take no part in this build:
  # leave them out, so that changing them reuses the cached package.
  isSourceDir = v: isString v && hasPrefix "/" v;
  ignored = [ "bootstrap" ".github" ".nix" ];
  filtered = builtins.path {
    name = "source";
    path = version;
    filter = path: _: !elem (removePrefix "${version}/" path) ignored;
  };
in
mkCoqDerivation ({
  pname = "CertiRocq";
  mlPlugin = true;

  inherit version;
  releaseRev = v: "v${v}";

  nativeBuildInputs = [
    pkgs.clang
    pkgs.python3
  ];

  propagatedBuildInputs = [
    wasmcert
    coqprime
    compcert
    ExtLib
    metarocq
  ];

  patchPhase = ''
    patchShebangs ./configure.sh
    patchShebangs ./clean_extraction.sh
    patchShebangs ./make_plugin.sh
  '';

  configurePhase = ''
    ./configure.sh local
  '';

  buildPhase = ''
    runHook preBuild

    make
    make plugin
    make cplugin

    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall

    OUTDIR=$out/lib/coq/${coq.coq-version}/user-contrib

    DST=$OUTDIR/CertiRocq/Plugin/runtime make -C runtime install
    COQLIBINSTALL=$OUTDIR make -C theories install
    COQLIBINSTALL=$OUTDIR make -C libraries install
    COQLIBINSTALL=$OUTDIR COQPLUGININSTALL=$OCAMLFIND_DESTDIR make -C plugins/plugin install
    COQLIBINSTALL=$OUTDIR COQPLUGININSTALL=$OCAMLFIND_DESTDIR make -C plugins/cplugin install

    runHook postInstall
  '';

  meta = {
    description = "CertiRocq";
    maintainers = with maintainers; [ womeier ];
    license = licenses.mit;
  };
} // optionalAttrs (isSourceDir version) {
  src = filtered;
  # The bootstrap tests need the complete sources.
  passthru.fullSrc = version;
})
