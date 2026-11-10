SRC = gc_stack.c certirocq_run_main.c rocq_c_ffi.c rocq_ffi.c prim_int63.c prim_floats.c prim_string.c get_ordinal.c certirocq_gmp.c
HEADERS = m.h config.h values.h gc_stack.h certirocq_run_main.h rocq_c_ffi.h rocq_ffi.h prim_int63.h prim_floats.h prim_string.h get_ordinal.h certirocq_gmp.h
LINKOPTS = -linkpkg -dontlink str,unix,dynlink,threads,zarith

TARGETS = ${SRC:.c=.o}
COQLIB = `coqc -where`
COQLIBINSTALL ?= $(if $(DESTDIR),$(DESTDIR)/)${COQLIB}/user-contrib
INSTALLDIR = ${COQLIBINSTALL}/CertiRocq/Plugin/runtime

all: ${TARGETS}

%.o: %.c
	$(CC) -I /opt/homebrew/include -I . -I `ocamlc -where` -fPIC -O2 -g -c -o $@ $+

install: all
	install -d "${INSTALLDIR}"
	install -m 0644 ${HEADERS} "${INSTALLDIR}"
	install -m 0644 ${SRC} "${INSTALLDIR}"
	install -m 0644 ${TARGETS} "${INSTALLDIR}"

clean:
	rm -f *.o
