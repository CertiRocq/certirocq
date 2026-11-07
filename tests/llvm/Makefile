# End-to-end tests of the LLVM backend (CertiRocq Compile LLVM).
#
# Prerequisites (from the repository root, in an opam switch with the
# dependencies of rocq-certirocq.opam, Vellvm included):
#   make theories/Makefile libraries/Makefile
#   make -C libraries -j24
#   make -C theories -j24 Extraction/extraction.vo
#   make runtime plugins/plugin/Makefile && bash ./make_plugin.sh plugin
# The plugin is used in place (OCAMLPATH=../../plugins/plugin), not installed.
#
#   make            plain, final-gc and asan modes on every test
#   make all-modes  additionally O2 and valgrind (skipped if not installed)
#   make checked    every test in checked and asan-checked modes: linked with
#                   runtime/gc_stack_checked.c instead of gc_stack.c, which
#                   checks the runtime contract (../llvm-corpus/CONTRACT.md) at
#                   every collection and aborts with
#                   "certirocq-contract: VIOLATION [<clause>] PRE|POST ..."
#   make corpus     the stress corpus ../llvm-corpus/cNN_*.v in checked and
#                   asan modes (CERTIROCQ_CHECK_MIN_GC=1 except c00/c06/c12);
#                   c07, c13, c15 are expected failures (XFAIL)
#   make stress     tests and corpus in checked-small mode: checked with a
#                   2^LOG_NURSERY-word nursery (default 13, vs. 2^16)
#   make TESTS="peano mutual" MODES="-m plain"
#   make TESTS="c07 c15" MODES="-m checked"   (corpus programs by prefix)
#   make clean
# Modes (run.sh -m): plain final-gc asan valgrind O2 checked checked-small
# asan-checked.  Outcomes and the latest results: RESULTS.md.  Checked runs
# hash the whole reachable heap at every GC, so they are slow (minutes for
# the GC-heavy tests); raise TIMEOUT (seconds, default 300) if needed.
#
# Adding a test: create foo.v here with
#
#   From CertiRocq.Plugin Require Import CertiRocq.
#   From CertiRocq.LLVMTests Require Import SExp.
#   Definition prog : T := ... .
#   CertiRocq Compile LLVM prog.
#
# The definition must be called [prog] (run.sh picks up
# CertiRocq.LLVMTests.foo.prog.ll and evaluates [to_sexp foo.prog]).  T needs
# an [SExp T] instance: SExp.v has unit, bool, nat, positive, N, list, prod,
# option; for a new inductive, add an instance in foo.v giving each
# constructor's CertiRocq ordinal (nullary and non-nullary constructors are
# numbered separately, in declaration order) and its non-parameter fields,
# e.g. match_arms.v.  The result must be first-order data (no functions).
# run.sh compiles foo.v, has Rocq compute the expected S-expression
# (vm_compute), links foo.ll with prelude.ll, llvm_main.c and
# runtime/gc_stack.c (+ prim_int63.c), runs it and compares.  Logs and
# artefacts: _build/.
#
# Corpus programs (../llvm-corpus/cNN_*.v) carry no CertiRocq command and
# usually no SExp instance: run.sh copies each to _build/corpus/ with the
# compile command appended, and compares against to_sexp prog when SExp.v can
# print prog's type, else against the "EXPECTED:" line of the file header.

SWITCH ?= $(shell opam switch show)
TESTS ?=
MODES ?=

TIMEOUT ?= 3600

.PHONY: test all-modes checked corpus stress clean
test:
	SWITCH=$(SWITCH) ./run.sh $(MODES) $(TESTS)

all-modes:
	SWITCH=$(SWITCH) ./run.sh -m plain -m final-gc -m asan -m O2 -m valgrind $(TESTS)

checked:
	SWITCH=$(SWITCH) TIMEOUT=$(TIMEOUT) ./run.sh -m checked -m asan-checked $(TESTS)

corpus:
	SWITCH=$(SWITCH) TIMEOUT=$(TIMEOUT) ./run.sh -c -m checked -m asan $(TESTS)

stress:
	SWITCH=$(SWITCH) TIMEOUT=$(TIMEOUT) ./run.sh -m checked-small $(TESTS)
	SWITCH=$(SWITCH) TIMEOUT=$(TIMEOUT) ./run.sh -c -m checked-small $(TESTS)

clean:
	rm -rf _build CertiRocq.LLVMTests.*.ll CertiRocq.LLVMCorpus.*.ll *.vo *.vos *.vok *.glob .*.aux
