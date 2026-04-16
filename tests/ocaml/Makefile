COQOPTS = -R ../../plugin CertiRocq.Plugin -I ../../plugin -R ../lib CertiRocq.Tests.lib
CCOMPILER=gcc

# Names of the tests
TESTS=$(shell cat TESTS)
# Names of the generated cfiles
MLFILES=$(patsubst %,%.ml, $(TESTS))
MLIFILES=$(patsubst %,%.mli, $(TESTS))
CMOFILES=$(patsubst %,%.cmo, $(TESTS))
CMXFILES=$(patsubst %,%.cmx, $(TESTS))

default: tests run
all: tests run

.PHONY: tests run clean cleanml

$(MLFILES): tests
$(CMOFILES): $(TESTS)
$(CMXFILES): $(TESTS)
exec: $(TESTS)


clean:
	rm -f ./*.cmi
	rm -f ./*.cmo
	rm -f ./*.cmx
	rm -f ./*.cma
	rm -f ./*.o
	rm -f $(TESTS)
	rm -f main mainopt
	rm -f ./*.vo ./*.vos ./*.vok

cleanml :
	rm -f $(MLFILES) $(MLIFILES)


$(TESTS): $(MLFILES)
	ocamlc -c $@.mli
	ocamlc -c $@.ml
	ocamlopt -c $@.mli
	ocamlopt -c $@.ml

main: $(CMOFILES) $(CMXFILES)
	ocamlc -c main.ml
	ocamlopt -c main.ml
	ocamlc -o main unix.cma $(CMOFILES) main.cmo 
	ocamlopt -o mainopt unix.cmxa $(CMXFILES) main.cmx

tests: tests.v
	coqc $(COQOPTS) tests.v

run: main mainopt
	./main 10
	./mainopt 10
