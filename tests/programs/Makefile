COQOPTS = -R ../../plugins/plugin CertiRocq.Plugin -I ../../plugins/plugin -R ./ CertiRocq.Tests -R ../lib CertiRocq.Tests.lib
CCOMPILER?=gcc
INCLUDE=../../runtime
WARN_OPTS=-w -Wno-everything

# Names of the tests
TESTS=$(shell cat TESTS)
CPS_TESTS=$(shell cat CPS_TESTS)
TEST_PREQS=%_main.c glue_%.c $(INCLUDE)/certirocq_runtime.c $(INCLUDE)/gc/gc.c
TEST_RECIPE=$(CCOMPILER) -o $@ $(WARN_OPTS) -O2 -fomit-frame-pointer -I$(INCLUDE) $^

# Names of the generated glue code files
GLUE=$(TESTS:%=glue_%.c) $(TESTS:%=glue_%.h)

# Names of the generated C files
OPTS=default O0
TESTS_OPTS=$(foreach TEST,$(TESTS),$(OPTS:%=$(TEST)_%))
CPS_TESTS_OPTS=$(CPS_TESTS:%=%_cps)
CFILES=$(TESTS_OPTS:%=CertiRocq.Tests.tests.%.c) $(CPS_TESTS_OPTS:%=CertiRocq.Tests.tests.%.c)

default: run
all: lib exec run

.PHONY: all default clean cleanexec lib cleanlib run $(TESTS)

exec: $(TESTS) $(CPS_TESTS_OPTS)

clean: cleanexec
	rm -f ./*.*.c
	rm -f ./*.*.h
	rm -f ./*.vo
	rm -f ./*.vok
	rm -f ./*.vos
	rm -f ./*.glob
	rm -f ./glue_*.*
	rm -f ./CertiRocq.Tests.tests.*.c

cleanexec:
	rm -f ./*_default
	rm -f ./*_O0
	rm -f ./*_cps
	rm -f ./*_opt
	rm -f ./*_opt[1-5]

lib/Makefile:
	cd ../lib; coq_makefile -f _CoqProject -o Makefile

lib: ../lib/Makefile
	$(MAKE) -C ../lib

cleanlib:
	$(MAKE) clean -C ../lib

$(GLUE) $(CFILES): tests.v
	rocq c $(COQOPTS) $<

%_default: $(TEST_PREQS) CertiRocq.Tests.tests.%_default.c ; $(TEST_RECIPE)
%_O0:      $(TEST_PREQS) CertiRocq.Tests.tests.%_O0.c      ; $(TEST_RECIPE)
%_cps:     $(TEST_PREQS) CertiRocq.Tests.tests.%_cps.c     ; $(TEST_RECIPE)
$(TESTS):%: %_default %_O0

run: run.sh exec
	sh $<
