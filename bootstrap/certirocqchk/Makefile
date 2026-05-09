CCOMPILER := $(shell { command -v clang-11 || command -v clang; } 2>/dev/null)

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
	-Q . CertiRocq.CertiRocqCheck \
	-I .
  TESTCOQOPTS = $(COQOPTS)
  CERTIROCQ_VANILLA_PLUGIN_DEPS = \
	../../plugins/cplugin/certirocq_vanilla_plugin.cmi \
	../../plugins/cplugin/certirocq_vanilla_plugin.cmx \
	../../plugins/cplugin/certirocq_vanilla_plugin.cmxa \
	../../plugins/cplugin/certirocq_vanilla_plugin.cmxs
else
  COQOPTS = -I . -Q . CertiRocq.CertiRocqCheck
  TESTCOQOPTS = 
  CERTIROCQ_VANILLA_PLUGIN_DEPS =
endif

PKGS = -package rocq-runtime,rocq-runtime.clib,rocq-runtime.config,rocq-runtime.engine,rocq-runtime.gramlib,rocq-runtime.interp,rocq-runtime.kernel,rocq-runtime.lib,rocq-runtime.library,rocq-runtime.toplevel,rocq-runtime.vernac,rocq-runtime.plugins.ltac
COQLIB = $(shell coqc -where)
COQLIBINSTALL = $(COQLIB)/user-contrib/CertiRocq/CertiRocqCheck
OCAMLLIB = $(shell ocamlc -where)
OCAMLOPTS = -package rocq-metarocq-template-ocaml.plugin -open Metarocq_template_plugin -package rocq-certirocq-vanilla.plugin -open Certirocq_vanilla_plugin \
	-I . -thread -rectypes -w +a-4-9-27-41-42-44-45-48-58-67-68   -safe-string -strict-sequence -w -33  -w -34  -w -32  -w -39  -w -20  -w -60  -w -8
GENCFILES = glue.c CertiRocq.CertiRocqCheck.compile.certirocqchk.c
CFILES = certirocqchk_wrapper.c ${GENCFILES}

RUNTIME_DIR = ../../runtime
RUNTIME_FILES = ${RUNTIME_DIR}/gc_stack.o ${RUNTIME_DIR}/prim_floats.o ${RUNTIME_DIR}/prim_string.o ${RUNTIME_DIR}/prim_int63.o ${RUNTIME_DIR}/rocq_ffi.o

CCOMPILEROPTS = -fPIC -g -c -I . -I ${RUNTIME_DIR} -I ${OCAMLLIB} -w -Wno-everything -O2
# ccomp: CCOMPILEROPTS = -g -c -I . -I ${OCAMLLIB} -O2

.PHONY: certirocqchk
.PRECIOUS: $(GENCFILES)

plugin: compile.vo certirocqchk

test: test.vo

test.vo: test.v
	ulimit -Ss 65500 && coqc ${TESTCOQOPTS} test.v

clean: 
	make -f Makefile.certirocqchk clean
	rm -f *.cm* *.o *.vo

Makefile.certirocqchk: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.certirocqchk

certirocqchk: Makefile.certirocqchk certirocqchk_plugin.cmxs
	$(MAKE) -f Makefile.certirocqchk

compile.vo ${GENCFILES} &: compile.v
	coqc ${COQOPTS} $<

%.o: %.c
	$(CCOMPILER) $(CCOMPILEROPTS) -o $@ $<

certirocqchk_plugin.cmxs: certirocqchk_plugin.cmxa ${CFILES:.c=.o} ${RUNTIME_FILES}
	ocamlfind opt ${OCAMLOPTS} -shared -o $@ $+

certirocqchk_plugin.cmx: certirocqchk_plugin_wrapper.cmx certirocqchk.cmx g_certirocqchk.cmx
	ocamlfind opt ${OCAMLOPTS} -pack -o $@ $+

certirocqchk_plugin.cmxa: certirocqchk_plugin.cmx
	ocamlfind opt -linkall ${OCAMLOPTS} -a -o $@ $<

g_certirocqchk.ml: g_certirocqchk.mlg certirocqchk.cmx certirocqchk_plugin_wrapper.cmx
	coqpp $<

certirocqchk_wrapper.c: compile.vo

certirocqchk_plugin_wrapper.cmx: certirocqchk_wrapper.o

certirocqchk.cmx: certirocqchk_plugin_wrapper.cmx certirocqchk_plugin_wrapper.cmi

# %.mli: %.ml
# 	[ -f "$@" ] || ocamlfind opt ${PKGS} ${OCAMLOPTS} -for-pack Certirocqchk_plugin -i $< > $@

%.cmi: %.mli $(CERTIROCQ_VANILLA_PLUGIN_DEPS)
	ocamlfind opt ${PKGS} ${OCAMLOPTS} -for-pack Certirocqchk_plugin $<

%.cmx: %.ml	%.cmi $(CERTIROCQ_VANILLA_PLUGIN_DEPS)
	ocamlfind opt -c ${PKGS} ${OCAMLOPTS} -for-pack Certirocqchk_plugin -o $@ $<

install: Loader.vo certirocqchk_plugin.cmxs
	install -d "$(COQLIBINSTALL)"
	install -m 0644 Loader.v Loader.vo certirocqchk_plugin.cmx* "$(COQLIBINSTALL)"
	make -f Makefile.certirocqchk install
	ocamlfind install -add rocq-certirocqchk certirocqchk_plugin.cmx* certirocqchk_plugin.cmi

.PHONY: plugin test

.NOTPARALLEL:
