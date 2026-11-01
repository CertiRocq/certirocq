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
mkRocqDerivation {
  pname = "CertiRocq";
  owner = "CertiRocq";
  repo = "certirocq";
  opam-name = "rocq-certirocq";
  mlPlugin = true;

  inherit version;
  releaseRev = v: "v${v}";

  nativeBuildInputs = [
    pkgs.python3
  ];

  # The plugin invokes a C compiler to build the code it generates,
  # so dependents need one too.
  propagatedNativeBuildInputs = [
    pkgs.clang
  ];

  propagatedBuildInputs = [
    wasmcert
    compcert
    ExtLib
    metarocq-erasure-plugin
    metarocq-safechecker-plugin
  ];

  postPatch = ''
    patchShebangs ./configure.sh
    patchShebangs ./clean_extraction.sh
    patchShebangs ./make_plugin.sh
  '';

  configurePhase = ''
    ./configure.sh local
  '';

  buildPhase = ''
    runHook preBuild

    make all
    make plugins

    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall

    OUTDIR=$out/lib/coq/${rocq-core.rocq-version}/user-contrib

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
}
