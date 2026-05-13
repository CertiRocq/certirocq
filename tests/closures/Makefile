COQOPTS = -R ../../plugins/plugin CertiRocq.Plugin -I ../../plugins/plugin -R ./ CertiRocq.Tests
CCOMPILER ?= gcc
INCLUDE = ../../runtime
WARN_OPTS = -w -Wno-everything

TESTS=$(shell cat TESTS)
CFILES=$(patsubst %, CertiRocq.Tests.tests.%.c, $(TESTS)) glue.c

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

$(TESTS): %: CertiRocq.Tests.tests.%.c glue.c print.c
	$(CCOMPILER) -o $@ $(WARN_OPTS) -O2 -fomit-frame-pointer -I$(INCLUDE) main.c $(INCLUDE)/gc/gc.c $^

exec: $(TESTS)

run: run.sh exec
	sh $<
