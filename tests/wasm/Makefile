COQOPTS = -R ../../plugin CertiRocq.Plugin -I ../../plugin -R ./ CertiRocq.Tests -R ../lib CertiRocq.Tests.lib

# Names of the tests
TESTS=$(shell cat TESTS)

# Name of generated webassembly files
WASMFILES=$(patsubst %, CertiRocq.Tests.tests.%.wasm, $(TESTS))

OS=$(shell uname)
STACKSIZE=$(if $(filter Linux,$(OS)),unlimited,65532)

.PHONY: all default clean lib cleanlib
.PHONY: tests primitive_unit_tests
.PHONY: run run_tests run_primitive_unit_tests

all: run_tests run_primitive_unit_tests

$(WASMFILES): tests

lib/Makefile:
	cd ../lib; coq_makefile -f _CoqProject -o Makefile

lib: lib/Makefile
	$(MAKE) -C ../lib

cleanlib:
	$(MAKE) clean -C ../lib

tests: tests.v lib
	ulimit -s $(STACKSIZE) && coqc $(COQOPTS) $<

primitive_unit_tests: uint63_unit_tests.v lib
	coqc -quiet $(COQOPTS) $<

run: run_tests run_primitive_unit_tests

run_tests: $(WASMFILES)
	ulimit -s $(STACKSIZE) && ./run_wasm_tests.py

run_primitive_unit_tests: primitive_unit_tests
	node --stack-size=10000000 js/run_uint63_unit_tests.js

clean:
	rm -f *.wat *.wasm *.cwasm *.tests.*.js *.ir
	rm -f *.vo *.vos *.vok *.glob
