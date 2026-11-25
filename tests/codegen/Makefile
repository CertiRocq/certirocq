include ../config.mk
COQOPTS = $(PLUGINOPTS) -R ./ CertiRocq.Tests
CCOMPILER ?= gcc
WARN_OPTS = -w -Wno-everything

TESTS=$(shell cat TESTS)
CALLS=$(filter calls_%, $(TESTS))
PRIMS=$(filter prims_%, $(TESTS))
CFILES=$(patsubst %, CertiRocq.Tests.tests.%.c, $(TESTS)) glue.c
PRIM_SRC=$(INCLUDE)/prim_int63.c $(INCLUDE)/prim_floats.c $(INCLUDE)/prim_string.c
TEST_RECIPE=$(CCOMPILER) -o $@ $(WARN_OPTS) -O2 -fomit-frame-pointer -I$(INCLUDE) main.c glue.c $(INCLUDE)/gc_stack.c

default: run

.PHONY: compile exec clean run

clean:
	rm -f ./*.*.c
	rm -f ./*.*.h
	rm -f ./*.vo
	rm -f ./*.vok
	rm -f ./*.vos
	rm -f ./*.glob
	rm -f $(TESTS)
	rm -f glue.*

compile: tests.v
	rocq c $(COQOPTS) tests.v

$(CFILES): compile

$(CALLS): %: CertiRocq.Tests.tests.%.c glue.c main.c
	$(TEST_RECIPE) $<

$(PRIMS): %: CertiRocq.Tests.tests.%.c glue.c main.c
	$(TEST_RECIPE) $(PRIM_SRC) $<

exec: $(TESTS)

run: run.sh exec
	sh $<
