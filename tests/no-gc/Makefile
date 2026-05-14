COQOPTS = -R ../../plugins/plugin CertiRocq.Plugin -I ../../plugins/plugin -R ./ CertiRocq.Tests
CCOMPILER ?= gcc
INCLUDE = ../../runtime
WARN_OPTS = -w -Wno-everything

TESTS = no_gc_bool no_gc_list no_gc_closure
BOOL_TESTS = no_gc_bool
LIST_TESTS = no_gc_list
NAT_TESTS = no_gc_closure
CFILES = $(TESTS:%=CertiRocq.Tests.tests.%.c)
RUNTIME = $(INCLUDE)/certirocq_runtime.c $(INCLUDE)/certirocq_no_gc.c
CFLAGS = $(WARN_OPTS) -O2 -fomit-frame-pointer -I$(INCLUDE)

default: run

.PHONY: compile exec clean run

$(CFILES): tests.v
	rocq c $(COQOPTS) $<

compile: $(CFILES)

$(BOOL_TESTS): %: CertiRocq.Tests.tests.%.c main_bool.c $(RUNTIME)
	$(CCOMPILER) -o $@ $(CFLAGS) main_bool.c $(RUNTIME) $<

$(LIST_TESTS): %: CertiRocq.Tests.tests.%.c main_list.c $(RUNTIME)
	$(CCOMPILER) -o $@ $(CFLAGS) main_list.c $(RUNTIME) $<

$(NAT_TESTS): %: CertiRocq.Tests.tests.%.c main_nat.c $(RUNTIME)
	$(CCOMPILER) -o $@ $(CFLAGS) main_nat.c $(RUNTIME) $<

exec: $(TESTS)

run: run.sh exec
	sh $<

clean:
	rm -f ./*.*.c
	rm -f ./*.*.h
	rm -f ./*.vo
	rm -f ./*.vok
	rm -f ./*.vos
	rm -f ./*.glob
	rm -f ./.tests.aux
	rm -f $(TESTS)
