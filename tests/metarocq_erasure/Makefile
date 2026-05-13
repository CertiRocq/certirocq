PKGS = -package rocq-runtime,rocq-runtime.plugins.ltac,rocq-metarocq-template-ocaml,rocq-certirocqc
LINKOPTS = -linkpkg -dontlink str,unix,dynlink,threads,zarith
OCAMLOPTS = -open Metarocq_template_plugin -I . -thread -rectypes -w +a-4-9-27-41-42-44-45-48-58-67-68   -safe-string -strict-sequence -w -33  -w -34  -w -32  -w -39  -w -20  -w -60  -w -8
GENCFILES = glue.CertiRocq.Tests.metacoq_erasure.metacoq_erasure.metacoq_erasure.c \
		CertiRocq.Tests.metacoq_erasure.metacoq_erasure.metacoq_erasure.c
CFILES = certirocq_erasure.c ${GENCFILES} print.c
COPTS = -g -I ../../_opam/lib/ocaml -I . -I ../../runtime -I ../../runtime/gc -I ../../runtime/lib
# ffi.CertiRocq.Tests.metacoq_erasure.metacoq_erasure.QuoteFFI.c
COQOPTS = -Q ../../theories/Codegen CertiRocq.Codegen -Q ../../libraries CertiRocq.Libraries \
	-Q ../../theories/LambdaANF CertiRocq.LambdaANF -Q ../../theories/LambdaBoxLocal CertiRocq.LambdaBoxLocal \
	-Q ../../theories/Compiler CertiRocq.Compiler -Q ../../theories/common CertiRocq.Common \
	-Q ../../theories/LambdaBoxMut CertiRocq.LambdaBoxMut -Q .. CertiRocq.Tests \
        -R ../../plugins/plugin CertiRocq.Plugin -I ../../plugins/plugin

RUNTIME_DIR = ../../runtime
RUNTIME_FILES = ${RUNTIME_DIR}/gc/gc.o ${RUNTIME_DIR}/lib/prim_floats.o ${RUNTIME_DIR}/lib/prim_int63.o

plugin: metarocq_erasure.vo Loader.vo

test: test.vo

test.vo: plugin test.v
	rocq c -I . -Q . CertiRocq.Tests.metarocq_erasure test.v

clean: 
	rm *.cm*

Loader.vo: Loader.v install
	rocq c -I . -Q . CertiRocq.Tests.metarocq_erasure Loader.v

metarocq_erasure.vo: metarocq_erasure.v
	rocq c ${COQOPTS} $<

%.o: %.c
	gcc ${COPTS} -c -Wno-everything -O2 -fomit-frame-pointer -o $@ $<

certirocq_erasure_plugin.cmxs: certirocq_erasure_plugin.cmxa ${CFILES:.c=.o} ${RUNTIME_FILES}
	ocamlfind opt ${OCAMLOPTS} ${LINKOPTS} -shared -linkall -o $@ $+

certirocq_erasure_plugin.cmx: certiRocqErase.cmx g_safe_erasure.cmx
	ocamlfind opt ${PKGS} ${OCAMLOPTS} -pack -o $@ $+

certirocq_erasure_plugin.cmxa: certirocq_erasure_plugin.cmx
	ocamlfind opt ${OCAMLOPTS} -a -o $@ $<

g_safe_erasure.ml: g_safe_erasure.mlg certiRocqErase.cmx
	coqpp $<

# g_safe_erasure.mli: g_safe_erasure.ml
# ocamlfind opt ${PKGS} ${OCAMLOPTS} -for-pack Certirocq_erasure_plugin -i $< > $@

%.cmi: %.mli
	ocamlfind opt ${PKGS} ${OCAMLOPTS} -for-pack Certirocq_erasure_plugin $<

%.cmx: %.ml %.cmi
	ocamlfind opt -c ${PKGS} ${OCAMLOPTS} -for-pack Certirocq_erasure_plugin $<

install: certirocq_erasure_plugin.cmxa certirocq_erasure_plugin.cmxs certirocq_erasure_plugin.cmx
	ocamlfind remove rocq-certirocq-bootstrapped-erasure
	ocamlfind install rocq-certirocq-bootstrapped-erasure META $+

.PHONY: plugin test
