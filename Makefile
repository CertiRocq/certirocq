# CertiRocq is built with dune (see dune-project); these targets are shortcuts.

.PHONY: all install test clean

all:
	dune build

install:
	dune install

# The bootstrapped compiler and checker are tested by dune test. The other tests are
# run with the packages as installed in the build directory, and with the largest
# stack allowed, as some test programs recurse deeply.
INSTALLED = $(CURDIR)/_build/install/default/lib

test:
	dune build @install
	dune test
	ulimit -Ss "$$(ulimit -Hs)" && \
	ROCQPATH=$(INSTALLED)/coq/user-contrib$${ROCQPATH:+:$$ROCQPATH} \
	  OCAMLPATH=$(INSTALLED)$${OCAMLPATH:+:$$OCAMLPATH} $(MAKE) -C tests

clean:
	dune clean
