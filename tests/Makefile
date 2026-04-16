DIRS=lib axioms ffi ocaml programs wasm
CLEAN_DIRS=$(addprefix clean,$(DIRS))

.PHONY: all clean $(DIRS) $(CLEAN_DIRS)

all: $(DIRS)

lib/Makefile:
	cd lib; coq_makefile -f _CoqProject -o Makefile

lib: lib/Makefile
	$(MAKE) -C $@

ffi/Makefile:
	cd ffi; rocq makefile -f _RocqProject -o Makefile; mkdir _build

ffi: ffi/Makefile
	$(MAKE) -C $@

axioms ocaml programs wasm: lib
	$(MAKE) -C $@ run

$(CLEAN_DIRS): clean%:
	$(MAKE) -C $* clean

clean: $(CLEAN_DIRS)
