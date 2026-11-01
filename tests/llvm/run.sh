#!/usr/bin/env bash
# End-to-end tests of CertiRocq's LLVM backend against Rocq's own evaluation.
#
#   ./run.sh [-c] [-m MODE]... [TEST...]
#
# TEST is a test name (foo or foo.v) here, or a corpus program of
# ../llvm-corpus (c07, c07_ord_ge_251 or c07_ord_ge_251.v).  Default: every
# *.v here except SExp.v; with -c, every ../llvm-corpus/cNN_*.v instead.
# MODE (repeatable; default: plain final-gc asan):
#   plain     clang -O0 -g, run, compare stdout with Rocq's expected value
#   final-gc  same binary, CERTIROCQ_FINAL_GC=1: the result is rooted, one more
#             collection runs, and the moved result must print the same
#   asan      clang -O0 -g -fsanitize=address,undefined (the emitted functions
#             get the sanitize_address attribute so ASan instruments them too)
#   valgrind  plain binary under valgrind --error-exitcode=1 (if installed)
#   O2        clang -O2 (optimised emitted code), compare
#   checked   like plain, but linked with runtime/gc_stack_checked.c instead of
#             gc_stack.c: every collection checks the runtime contract
#             (../llvm-corpus/CONTRACT.md); a violation aborts with
#             "certirocq-contract: VIOLATION [<Rocq clause>] PRE|POST ..."
#   checked-small  checked, with a 2^LOG_NURSERY-word nursery (default 13)
#             instead of gc_stack.h's 2^16: many more collections and root
#             checks.  A chunk bigger than the nursery is a [room] VIOLATION, so
#             LOG_NURSERY must cover the largest chunk (c14: 6000 words -> 13)
#   asan-checked   asan + checked
# Every binary is also linked with runtime/prim_int63.c (PrimInt63 programs).
# All tests and modes are run; the exit status is 1 if any of them failed,
# except for the expected failures listed in XFAIL (default: c07 c13 c15, see
# ../llvm-corpus/README.md), which are reported as "... (XFAIL)" or "XPASS".
#
# Outcome of one test in one mode:
#   ok (gc_calls=N) | MISMATCH | VIOLATION [clause] PRE|POST | ABORT(reason)
#   | ASAN(kind) | UBSAN | TIMEOUT | CRASH(SIGxxx) | EXIT-rc
#   | TOO-FEW-GCS (checked modes: fewer than CERTIROCQ_CHECK_MIN_GC collections)
# Full stderr (violation text, ASan report, checker summary): _build/foo.MODE.stderr
#
# For each test foo.v (which defines [prog] and says
# [CertiRocq Compile LLVM prog.]):
#   1. rocq c foo.v with the locally built plugin     -> _build/foo.ll
#   2. Rocq computes the expected S-expression:
#        Redirect "..." Eval vm_compute in (to_sexp prog)   -> _build/foo.expected
#   3. clang prelude.ll foo.ll llvm_main.c gc_stack.c prim_int63.c -> _build/foo[.MODE]
#   4. run, compare stdout with _build/foo.expected; GC count and final
#      alloc/limit (llvm_main.c's stderr) are logged to _build/foo.MODE.stderr.
# A corpus program cNN_x.v has no CertiRocq command: it is copied to
# _build/corpus/cNN_x.v with "From CertiRocq.Plugin Require Import CertiRocq."
# and "CertiRocq Compile LLVM prog." appended (logical path
# CertiRocq.LLVMCorpus).  Its expected value is [to_sexp prog] if SExp.v has
# instances for prog's type, else the "EXPECTED:" line of its header; if both
# exist and disagree, the SExp value is used and a NOTE is printed.  In the
# checked modes corpus programs run with CERTIROCQ_CHECK_MIN_GC=1 (they are
# meant to collect), except those in NOGC (default c00 c06 c12: they test
# Ecase dispatch / PrimInt63 ops and allocate less than one nursery).
#
# Environment: SWITCH (opam switch, default the current one), CLANG (default clang),
# TIMEOUT (seconds per run, default 300), CERTIROCQ_STACK_MB (see llvm_main.c),
# LOG_NURSERY (checked-small, default 12), XFAIL (expected failures).

set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
SWITCH="${SWITCH:-$(opam switch show)}"
CLANG="${CLANG:-clang}"
TIMEOUT="${TIMEOUT:-300}"
LOG_NURSERY="${LOG_NURSERY:-13}"
XFAIL="${XFAIL-c07 c13 c15}"
NOGC="${NOGC-c00 c06 c12}"
B="$HERE/_build"
CORPUS="$ROOT/tests/llvm-corpus"
mkdir -p "$B" "$B/corpus"

MODES=()
USE_CORPUS=0
while getopts "cm:" opt; do
  case $opt in
    c) USE_CORPUS=1 ;;
    m) MODES+=("$OPTARG") ;;
    *) echo "usage: $0 [-c] [-m MODE]... [TEST...]" >&2; exit 2 ;;
  esac
done
shift $((OPTIND - 1))
[ ${#MODES[@]} -eq 0 ] && MODES=(plain final-gc asan)

if [ $# -eq 0 ]; then
  if [ $USE_CORPUS -eq 1 ]; then
    set -- $(cd "$CORPUS" && ls c[0-9][0-9]_*.v | sed 's/\.v$//')
  else
    set -- $(cd "$HERE" && ls *.v | grep -v '^SExp\.v$' | sed 's/\.v$//')
  fi
fi

rocq() { # (OCaml 4.14 runs on the C stack: big corpus terms need ulimit -s)
  (cd "$HERE" && { ulimit -s unlimited 2>/dev/null || ulimit -s 1048576 2>/dev/null; true; } && OCAMLPATH="$ROOT/plugins/plugin${OCAMLPATH:+:$OCAMLPATH}" \
     opam exec --switch="$SWITCH" -- rocq c \
       -Q "$ROOT/plugins/plugin" CertiRocq.Plugin -Q "$HERE" CertiRocq.LLVMTests \
       -Q "$B/corpus" CertiRocq.LLVMCorpus "$@")
}

RT="$ROOT/runtime"
CFLAGS_COMMON=(-g -I "$RT" -Wno-override-module -Wl,--wrap=garbage_collect -lpthread)

build() { # name mode -> binary path on stdout
  local n=$1 mode=$2 out="$B/$1.$2" ll="$B/$1.full.ll"
  local gc=("$RT/gc_stack.c") opt=-O0 san=() src="$B/$1.full.ll"
  case $mode in plain|final-gc|valgrind) out="$B/$n.plain" ;; esac
  if [ "$out" = "$B/$n.plain" ] && [ -x "$out" ] && [ "$out" -nt "$ll" ]; then
    echo "$out"; return 0
  fi
  case $mode in
    plain|final-gc|valgrind) ;;
    O2) opt=-O2 ;;
    checked) gc=("$RT/gc_stack_checked.c") ;;
    checked-small)
      gc=(-DCERTIROCQ_LOG_NURSERY_SIZE="$LOG_NURSERY" "$RT/gc_stack_checked.c") ;;
    asan|asan-checked)
      [ $mode = asan-checked ] && gc=("$RT/gc_stack_checked.c")
      sed -E 's/^(define .*\)) \{$/\1 sanitize_address {/' "$ll" > "$B/$n.$mode.ll"
      src="$B/$n.$mode.ll"
      san=(-fsanitize=address,undefined -fno-omit-frame-pointer) ;;
    *) echo "unknown mode $mode" >&2; return 1 ;;
  esac
  $CLANG $opt "${san[@]}" "${CFLAGS_COMMON[@]}" "$src" "$HERE/llvm_main.c" \
    "${gc[@]}" "$RT/prim_int63.c" -o "$out" > "$B/$n.$mode.clang.log" 2>&1 || return 1
  echo "$out"
}

# Classify a failed run from its exit status and stderr.
classify() { # rc stderr-file
  local rc=$1 err=$2 v
  if v=$(grep -m1 -o 'certirocq-contract: VIOLATION \[.*\] [A-Z_]* (gc call #[0-9]*)' "$err"); then
    echo "VIOLATION${v#certirocq-contract: VIOLATION}"
  elif grep -q 'Nursery is too small' "$err"; then echo "ABORT(Nursery is too small, exit $rc)"
  elif v=$(grep -m1 -o 'ERROR: AddressSanitizer: [a-z-]*' "$err"); then
    echo "ASAN(${v#ERROR: AddressSanitizer: })"
  elif grep -q 'runtime error:' "$err"; then echo "UBSAN"
  elif grep -q 'certirocq-contract: FAIL' "$err"; then echo "TOO-FEW-GCS"
  elif [ "$rc" -eq 124 ]; then echo "TIMEOUT"
  elif [ "$rc" -gt 128 ]; then echo "CRASH(SIG$(kill -l $((rc - 128)) 2>/dev/null || echo $((rc - 128))))"
  else echo "EXIT-$rc"
  fi
}

run_mode() { # name mode -> 0 pass / 1 fail
  local n=$1 mode=$2 bin exp="$B/$1.expected" got="$B/$1.$2.out" err="$B/$1.$2.stderr"
  local min_gc=0 x
  case $n in c[0-9][0-9]_*) min_gc=1 ;; esac
  for x in $NOGC; do case $n in "$x"|"$x"_*) min_gc=0 ;; esac; done
  bin=$(build "$n" "$mode") || { echo "BUILD-FAIL(_build/$n.$mode.clang.log)"; return 1; }
  case $mode in
    final-gc) CERTIROCQ_FINAL_GC=1 timeout "$TIMEOUT" "$bin" > "$got" 2> "$err" ;;
    asan|asan-checked)
          CERTIROCQ_CHECK_MIN_GC=$min_gc \
          ASAN_OPTIONS="detect_leaks=0:abort_on_error=0:halt_on_error=1" \
          UBSAN_OPTIONS="print_stacktrace=1:halt_on_error=1" \
          timeout "$TIMEOUT" "$bin" > "$got" 2> "$err" ;;
    valgrind) timeout "$TIMEOUT" valgrind -q --error-exitcode=99 --main-stacksize=67108864 \
          "$bin" > "$got" 2> "$err" ;;
    checked|checked-small)
          CERTIROCQ_CHECK_MIN_GC=$min_gc timeout "$TIMEOUT" "$bin" > "$got" 2> "$err" ;;
    *) timeout "$TIMEOUT" "$bin" > "$got" 2> "$err" ;;
  esac
  local rc=$?
  [ $rc -ne 0 ] && { classify $rc "$err"; return 1; }
  if [ "$mode" = final-gc ]; then
    { cat "$exp"; cat "$exp"; } | cmp -s - "$got" || { echo "MISMATCH"; return 1; }
  else
    cmp -s "$exp" "$got" || { echo "MISMATCH"; return 1; }
  fi
  echo "ok ($(grep -o 'gc_calls=[0-9]*' "$err" | tail -1))"
}

# Copy corpus program $1 (cNN_x) to _build/corpus, adding the compile command.
wrap_corpus() {
  { cat "$CORPUS/$1.v"
    printf '\nFrom CertiRocq.Plugin Require Import CertiRocq.\nCertiRocq Compile LLVM prog.\n'
  } > "$B/corpus/$1.v"
}

# PrimInt63 operations ([Eprim], outside the theorem) are calls of the C
# runtime's prim_int63_* functions, which the emitted module does not declare
# (prelude.ll is just the statement's runtime_prelude).  Declare every such
# callee with the types of its call site.
prim_decls() { # emitted .ll -> declarations of the C runtime's primitives it calls
  grep -o 'call  *[a-z0-9]\+  *@prim_[A-Za-z0-9_]*([^)]*)' "$1" \
    | sed -E 's/^call +([a-z0-9]+) +(@[A-Za-z0-9_]+)\((.*)\)$/\2 \1 \3/' \
    | sort -u -k1,1 \
    | while read -r name ret args; do
        printf 'declare %s %s(%s)\n' "$ret" "$name" \
          "$(printf '%s' "$args" | sed -E 's/(ptr|i[0-9]+|double) +[^,]+/\1/g')"
      done
}

# The helper library with the expected-value printers.
rocq SExp.v || { echo "SExp.v failed to compile"; exit 1; }

FAILS=0
for t in "$@"; do
  n="${t%.v}"
  corpus=0
  if [ ! -f "$HERE/$n.v" ]; then
    c=$(cd "$CORPUS" && ls "$n".v "$n"_*.v 2>/dev/null | head -1)
    [ -z "$c" ] && { echo "$n: no such test"; FAILS=$((FAILS+1)); continue; }
    n="${c%.v}"; corpus=1
  fi
  xfail=0
  for x in $XFAIL; do case $n in "$x"|"$x"_*) xfail=1 ;; esac; done
  printf '%-22s' "$n"
  # 1. compile with the plugin
  if [ $corpus -eq 1 ]; then
    wrap_corpus "$n"; src="$B/corpus/$n.v"; lib=LLVMCorpus
  else
    src="$n.v"; lib=LLVMTests
  fi
  if ! rocq "$src" > "$B/$n.rocq.log" 2>&1; then
    echo " ROCQ-FAIL (see _build/$n.rocq.log)"; FAILS=$((FAILS+1)); continue
  fi
  mv -f "$HERE/CertiRocq.$lib.$n.prog.ll" "$B/$n.ll"
  { cat "$HERE/prelude.ll"; prim_decls "$B/$n.ll"; cat "$B/$n.ll"; } > "$B/$n.full.ll"
  # 2. expected value, computed by Rocq (corpus: else the EXPECTED: line)
  cat > "$B/expect_$n.v" <<EOR
From Stdlib Require Import String.
From CertiRocq.$lib Require Import $n.
From CertiRocq.LLVMTests Require Import SExp.
Open Scope string_scope.
Redirect "$B/$n.expected" Eval vm_compute in (to_sexp $n.prog).
EOR
  # (a missing SExp instance leaves an evar: "= ?SExp ..." instead of a string)
  if rocq "$B/expect_$n.v" > "$B/$n.expect.log" 2>&1 &&
     grep -q '^ *= "' "$B/$n.expected.out"; then
    # "     = \"...\"%string\n     : string"  ->  ...
    tr -d '\n' < "$B/$n.expected.out" | sed -E 's/^[^"]*"//; s/"[^"]*$//' > "$B/$n.expected"
    echo >> "$B/$n.expected"
    from_sexp=1
  elif [ $corpus -eq 1 ]; then
    from_sexp=0
  else
    echo " EXPECT-FAIL (see _build/$n.expect.log)"; FAILS=$((FAILS+1)); continue
  fi
  if [ $corpus -eq 1 ]; then
    line=$(grep -m1 -o 'EXPECTED: .*' "$CORPUS/$n.v" | sed -E 's/^EXPECTED: //; s/ *\*\) *$//')
    if [ $from_sexp -eq 0 ]; then
      printf '%s\n' "$line" > "$B/$n.expected"
    elif [ "$line" != "$(cat "$B/$n.expected")" ]; then
      printf ' NOTE(EXPECTED: line says "%s", SExp says "%s")' "$line" "$(cat "$B/$n.expected")"
    fi
  fi
  # 3./4. build, run, compare in every mode
  for m in "${MODES[@]}"; do
    if [ "$m" = valgrind ] && ! command -v valgrind > /dev/null; then
      printf ' %s: skipped(no valgrind)' "$m"; continue
    fi
    r=$(run_mode "$n" "$m"); rc=$?
    if [ $xfail -eq 1 ]; then
      if [ $rc -ne 0 ]; then r="$r (XFAIL)"; rc=0; else r="$r XPASS"; fi
    fi
    printf ' %s: %s' "$m" "$r"
    [ $rc -ne 0 ] && FAILS=$((FAILS+1))
  done
  echo
done
find "$HERE" -maxdepth 1 \( -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' -o -name '.*.aux' \) -delete 2>/dev/null
find "$B" \( -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' -o -name '.*.aux' \) -delete 2>/dev/null
if [ $FAILS -ne 0 ]; then echo "$FAILS FAILURE(S)"; exit 1; fi
echo "ALL PASSED"
