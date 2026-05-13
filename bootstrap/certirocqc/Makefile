# clang compiler 
CCOMPILER := $(shell { command -v clang-11 || command -v clang || command -v gcc; } 2>/dev/null)
# clang options
CCOMPILEROPTS = -fPIC -fomit-frame-pointer -g -c -I . -I $(RUNTIME_DIR) -I 20 20 12 61 79 80 81 98 701 33 100 204 250 395 398 399 400RUNTIME_DIR)/gc -I $(RUNTIME_DIR)/lib -I ${OCAMLLIB} -w -Wno-everything -O2
UNAME=$(shell uname -s)
ifeq '$(UNAME)' 'Darwin'
  SED= $(shell which gsed)
  ifeq '$(SED)' ''
   $(error "Must have gsed installed on MacOS, try e.g. brew install gsed")
  endif
else
SED=`which gsed || which sed`
endif

# CompCert compiler
CCOMPCOMPILER := $(CCOMPILER)
# $(shell { command -v ccomp; } 2>/dev/null)
# ccomp options
CCOMPCOMPILEROPTS = $(CCOMPILEROPTS)
# -g -c -I . -I $(RUNTIME_DIR) -I ${OCAMLLIB} -w -flongdouble -O2

-include ../../Makefile.conf

ifeq '$(CERTIROCQ_CONFIG)' 'local'
  ifeq ($(shell which cygpath 2>/dev/null),)
  OCAMLPATH := $(shell pwd)/../../plugins/cplugin/:$(OCAMLPATH)
  else
  OCAMLPATH := $(shell cygpath -m `pwd`)/../../plugins/cplugin/;$(OCAMLPATH)
  endif
  export OCAMLPATH

  COQOPTS = -Q ../../theories/Codegen CertiRocq.Codegen -Q ../../libraries CertiRocq.Libraries \
	-Q ../../theories/LambdaANF CertiRocq.LambdaANF \
	-Q ../../theories/LambdaBox_to_LambdaANF CertiRocq.LambdaBox_to_LambdaANF \
	-Q ../../theories/CodegenWasm CertiRocq.CodegenWasm \
	-Q ../../theories/Compiler CertiRocq.Compiler -Q ../../theories/common CertiRocq.Common \
	-Q ../../theories/Glue CertiRocq.Glue \
	-Q ../../plugins/plugin CertiRocq.Plugin \
	-I ../../plugins/plugin \
	-Q ../../plugins/cplugin CertiRocq.VanillaPlugin \
	-I ../../plugins/cplugin \
	-Q theories CertiRocq.CertiRocqC \
	-I .

  TESTCOQOPTS = $(COQOPTS)
  CERTIROCQ_PIPELINE_DEPS = ../../theories/Compiler/pipeline.vo
else
 ifeq '$(CERTIROCQ_CONFIG)' 'global'
  COQOPTS = -I . -Q theories CertiRocq.CertiRocqC
  TESTCOQOPTS = 
  CERTIROCQ_PIPELINE_DEPS =
 else
  $(error "Must first set CERTIROCQ_CONFIG by running ./configure.sh")
 endif
endif

PKGS = -package rocq-runtime,rocq-runtime.clib,rocq-runtime.config,rocq-runtime.engine,rocq-runtime.gramlib,rocq-runtime.interp,rocq-runtime.kernel,rocq-runtime.lib,rocq-runtime.library,rocq-runtime.toplevel,rocq-runtime.vernac,rocq-runtime.plugins.ltac
COQLIB = $(shell coqc -where)
COQLIBINSTALL = $(COQLIB)/user-contrib/CertiRocq/CertiRocqC
OCAMLLIB = $(shell ocamlc -where)
OCAMLOPTS = -package rocq-metarocq-template-ocaml.plugin -open Metarocq_template_plugin -package rocq-certirocq-vanilla.plugin -open Certirocq_vanilla_plugin \
	-I . -thread -rectypes -w +a-4-9-27-41-42-44-45-48-58-67-68   -safe-string -strict-sequence -w -33  -w -34  -w -32  -w -39  -w -20  -w -60  
GENCFILES = glue.c CertiRocq.CertiRocqC.CertiRocqC.certirocqc.c
CFILES = certirocqc_wrapper.c $(GENCFILES)

RUNTIME_DIR = ../../runtime
RUNTIME_FILES = $(RUNTIME_DIR)/gc/gc.o $(RUNTIME_DIR)/lib/prim_floats.o ${RUNTIME_DIR}/lib/prim_string.o $(RUNTIME_DIR)/lib/prim_int63.o $(RUNTIME_DIR)/lib/rocq_c_ffi.o

VFILES = theories/Loader.v theories/PrimInt63.v theories/PrimFloats.v theories/CertiRocqC.v

.PHONY: runtime certirocqc

all: plugin

plugin: theories/compile.vo certirocqc

runtime: $(RUNTIME_FILES:.o=.c)
	cd $(RUNTIME_DIR) && $(MAKE)

Makefile.certirocqc: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.certirocqc

certirocqc: runtime Makefile.certirocqc certirocqc_plugin.cmxs
	$(MAKE) -f Makefile.certirocqc

test: test.vo

test.vo: test.v
	mkdir -p tests
	ulimit -a
	ulimit -H -a
	echo coqc $(TESTCOQOPTS) test.v
	ulimit -Ss unlimited && ulimit -s unlimited && coqc $(TESTCOQOPTS) test.v

clean: Makefile.certirocqc
	make -f Makefile.certirocqc clean
	rm -f *.cm* *.o *.vo theories/*.vo

theories/CertiRocqC.vo: theories/CertiRocqC.v $(CERTIROCQ_PIPELINE_DEPS)
	coqc $(COQOPTS) $<

theories/compile.v: theories/CertiRocqC.vo

theories/compile.vo CertiRocq.CertiRocqC.compile.certirocqc.c &: theories/compile.v theories/CertiRocqC.vo $(CERTIROCQ_PIPELINE_DEPS)
	coqc $(COQOPTS) $<

g_certirocqc.ml: g_certirocqc.mlg certirocqc.cmx certirocqc_plugin_wrapper.cmx
	coqpp $<

certirocqc.cmx: certirocqc_plugin_wrapper.cmx

.PRECIOUS: $(GENCFILES)

$(GENCFILES:%.c=%.o): %.o: %.c
	$(SED) -f unicode.sed -i $<
	$(CCOMPCOMPILER) $(CCOMPCOMPILEROPTS) -o $@ $<

certirocqc_wrapper.o: %.o: %.c
	$(SED) -f unicode.sed -i $<
	$(CCOMPILER) $(CCOMPILEROPTS) -o $@ $<

certirocqc_plugin.cmx: certirocqc_plugin_wrapper.cmx certirocqc.cmx g_certirocqc.cmx
	ocamlfind opt $(OCAMLOPTS) -pack -o $@ $+

certirocqc_plugin.cmxa: certirocqc_plugin.cmx
	ocamlfind opt -linkall $(OCAMLOPTS) -a -o $@ $<

certirocqc_plugin.cmxs: certirocqc_plugin.cmxa $(CFILES:.c=.o) $(RUNTIME_FILES)
	ocamlfind ocamlopt $(OCAMLOPTS) -shared -o $@ $+

.PRECIOUS: %.cmi
%.cmi: %.mli
	ocamlfind opt $(PKGS) $(OCAMLOPTS) -for-pack Certirocqc_plugin $<

%.cmx: %.ml	%.cmi
	ocamlfind opt -c $(PKGS) $(OCAMLOPTS) -for-pack Certirocqc_plugin -o $@ $<

install: theories/compile.vo certirocqc_plugin.cmxs
	install -d "$(COQLIBINSTALL)"
	install -m 0644 theories/CertiRocqC.v theories/CertiRocqC.vo theories/compile.v theories/compile.vo certirocqc_plugin.cmx* "$(COQLIBINSTALL)"
	make -f Makefile.certirocqc install
	ocamlfind install -add rocq-certirocqc certirocqc_plugin.cmx* certirocqc_plugin.cmi

.PHONY: plugin test

.NOTPARALLEL:
