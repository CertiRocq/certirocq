{
  lib,
  pkgs,
  mkRocqDerivation,
  rocq-core,
  wasmcert,
  compcert,
  metarocq-erasure,
  metarocq-safechecker,
  ExtLib,
  version ? null,
  # Whether to build and test the bootstrapped compiler and checker instead of the
  # packages (only in the bootstrap bundle of .nix/config.nix)
  bootstrap ? false,
}:

with lib;
let
  # The theories, the optimized plugin and its runtime, and the vanilla plugin
  packages = concatStringsSep "," [ "rocq-certirocq" "rocq-certirocq-vanilla" ];
  # With the bootstrapped compiler and checker, which are only built by the tests
  allPackages = concatStringsSep "," [
    "rocq-certirocq" "rocq-certirocq-vanilla" "rocq-certirocqc" "rocq-certirocqchk"
  ];
  # A dune command, printed in the log
  dune = args: ''
    ( set -x; dune ${args} --display=progress ''${enableParallelBuilding:+-j $NIX_BUILD_CORES} )
  '';
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
    metarocq-erasure
    metarocq-safechecker
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
  # With the bootstrap, only the theories of the compiler, without its proofs (the
  # default bundle builds them), the plugins and the runtime
  buildPhase = ''
    runHook preBuild
  '' + (if bootstrap then dune "build -p ${allPackages} @@compiler"
        else dune "build -p ${packages}") + ''
    runHook postBuild
  '';
  doCheck = true;
  # For the Wasm tests
  nativeCheckInputs = [ pkgs.nodejs_22 pkgs.python3 ];
  # The tests under tests/, or with the bootstrap those of the bootstrapped compiler
  # and checker (the default bundle runs the others), which dune runs with the plugins
  # of the build directory
  checkPhase = ''
    runHook preCheck
  '' + (if bootstrap then dune "build -p ${allPackages} @bootstrap/runtest"
        else dune "build -p ${packages} @runtest") + ''
    runHook postCheck
  '';
  # The bootstrap bundle only tests: there is nothing to install
  installPhase = ''
    runHook preInstall
  '' + (if bootstrap then ''
    mkdir -p $out
  '' else ''
    dune install --prefix=$out --libdir $OCAMLFIND_DESTDIR ${replaceStrings [","] [" "] packages}
    mkdir $out/lib/coq/
    mv $OCAMLFIND_DESTDIR/coq $out/lib/coq/${rocq-core.rocq-version}
  '') + ''
    runHook postInstall
  '';
})
