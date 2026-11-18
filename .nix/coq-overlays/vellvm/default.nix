{
  lib,
  mkCoqDerivation,
  coq,
  ExtLib,
  paco,
  ITree,
  flocq,
  equations,
  version ? null,
}:

mkCoqDerivation {
  pname = "vellvm";
  owner = "vellvm";
  repo = "vellvm";

  inherit version;
  # The LLVM backend needs Vellvm's current AST (CONV_Impure), which no
  # release contains yet. Same commit as the pin-depends of
  # rocq-certirocq.opam and the vellvm/ submodule.
  defaultVersion = "b63a28a0a36cbae73a454d99a97bb8171568343e";

  # Vellvm has no ML plugin of its own, but it loads Equations' plugin,
  # which Rocq 9 finds through findlib; mlPlugin puts findlib in the build.
  mlPlugin = true;

  propagatedBuildInputs = [
    ExtLib
    paco
    ITree
    flocq
    equations
  ];

  # Only the Rocq library, not the extracted interpreter. src/Makefile
  # forwards its targets to RocqMakefile with an unbounded -j, so the
  # generated makefile is called directly.
  buildPhase = ''
    runHook preBuild

    make -C src RocqMakefile
    make -C src -f RocqMakefile -j$NIX_BUILD_CORES

    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall

    make -C src -f RocqMakefile install \
      COQLIBINSTALL=$out/lib/coq/${coq.coq-version}/user-contrib

    runHook postInstall
  '';

  meta = {
    description = "Vellvm: verified semantics of LLVM IR";
    license = lib.licenses.mit;
  };
}
