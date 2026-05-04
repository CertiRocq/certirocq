COQOPTS = -R ../../plugins/plugin CertiRocq.Plugin -I ../../plugins/plugin -R ./ CertiRocq.Tests -R ../lib CertiRocq.Tests.lib
CCOMPILER?=gcc
INCLUDE=../../runtime
WARN_OPTS=-w -Wno-everything

# Names of the tests
TESTS=$(shell cat TESTS)
# Names of the generated C files
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

fibn: CertiRocq.Tests.tests.fibn.c glue.c int63.c
	$(CCOMPILER) -o $@ $(WARN_OPTS) -O2 -fomit-frame-pointer -I$(INCLUDE) main.c $(INCLUDE)/gc_stack.c $^

print_lst: CertiRocq.Tests.tests.print_lst.c glue.c print.c
	$(CCOMPILER) -o $@ $(WARN_OPTS) -O2 -fomit-frame-pointer -I$(INCLUDE) main.c $(INCLUDE)/gc_stack.c $^

list_sum_int63: CertiRocq.Tests.tests.list_sum_int63.c glue.c int63.c
	$(CCOMPILER) -o $@ $(WARN_OPTS) -O2 -fomit-frame-pointer -I$(INCLUDE) main.c $(INCLUDE)/gc_stack.c $^

list_sum_int63_tinfo: CertiRocq.Tests.tests.list_sum_int63_tinfo.c glue.c int63_tinfo.c
	$(CCOMPILER) -o $@ $(WARN_OPTS) -O2 -fomit-frame-pointer -I$(INCLUDE) main.c $(INCLUDE)/gc_stack.c $^

exec: $(TESTS)

run: run.sh exec
	sh $<
