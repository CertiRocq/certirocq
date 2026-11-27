# CertiRocq is built with dune (see dune-project); these targets are shortcuts.

.PHONY: all compiler install test clean

all:
	dune build --display=short

# The compiler part of theories/, the plugins and the runtime, without the proofs
compiler:
	dune build @@compiler --display=short

install:
	dune install

# The tests under tests/ and those of the bootstrapped compiler and checker, which use
# the plugins from the build directory, without installing them
test:
	dune test --display=short

clean:
	dune clean
