# Builds and tests the bootstrapped plugins (bootstrap/) against the
# CertiRocq package of the same sources, which the Nix CI already pushes to
# Cachix: only the bootstrap compilation itself runs here.
{
  lib,
  stdenv,
  pkgs,
  mkCoqDerivation,
  CertiRocq,
}:

with lib;
mkCoqDerivation {
  pname = "CertiRocq-bootstrap";
  mlPlugin = true;

  version = CertiRocq.fullSrc;

  nativeBuildInputs = [ pkgs.clang ] ++ optional stdenv.isLinux pkgs.gdb;

  buildInputs = [ CertiRocq ];

  # The _CoqProject files load the vanilla plugin from the source tree, which
  # is not built here: use the installed one instead.
  patchPhase = ''
    patchShebangs ./configure.sh
    sed -i '/plugins\/cplugin/d' bootstrap/certirocqc/_CoqProject bootstrap/certirocqchk/_CoqProject
  '';

  configurePhase = ''
    ./configure.sh global
  '';

  buildPhase = ''
    runHook preBuild

    make -C bootstrap all

    runHook postBuild
  '';

  # The tests load the plugins from the build tree rather than from an
  # installation: TESTCOQOPTS is empty in the global configuration.
  # On Linux, a failing test is run again under gdb to get a backtrace.
  doCheck = true;
  checkPhase = ''
    runHook preCheck

    status=0
    for plugin in certirocqc certirocqchk; do
      if ! make -C bootstrap/$plugin test TESTCOQOPTS='$(COQOPTS)'; then
        status=1
    ${optionalString stdenv.isLinux ''
        echo "bootstrap/$plugin: test failed, running it again under gdb"
        coqopts=$(make -s -C bootstrap/$plugin --eval 'print-coqopts: ; @echo $(COQOPTS)' print-coqopts)
        ( cd bootstrap/$plugin && ulimit -s unlimited
          gdb -batch -ex "set follow-fork-mode child" -ex "handle SIGSEGV stop" \
            -ex run -ex "bt 40" -ex "info threads" -ex "thread apply all bt 8" \
            -ex "info registers" -ex 'x/8i $pc' --args coqc $coqopts test.v ) || true
    ''}
      fi
    done
    [ $status = 0 ]

    runHook postCheck
  '';

  installPhase = ''
    runHook preInstall

    mkdir -p $out
    touch $out/tested

    runHook postInstall
  '';

  meta = {
    description = "Tests of the bootstrapped CertiRocq plugins";
    license = licenses.mit;
  };
}
