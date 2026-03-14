SRC = gc_stack.c certirocq_run_main.c rocq_c_ffi.c rocq_ffi.c prim_int63.c prim_floats.c prim_string.c get_ordinal.c certirocq_gmp.c
HEADERS = m.h config.h values.h gc_stack.h certirocq_run_main.h rocq_c_ffi.h rocq_ffi.h prim_int63.h prim_floats.h prim_string.h get_ordinal.h certirocq_gmp.h
LINKOPTS = -linkpkg -dontlink str,unix,dynlink,threads,zarith

TARGETS = ${SRC:.c=.o}
COQLIB = `coqc -where`
DST ?= ${COQLIB}/user-contrib/CertiRocq/Plugin/runtime

all: ${TARGETS}

%.o: %.c
	gcc -I /opt/homebrew/include -I . -I `ocamlc -where` -fPIC -g -c -o $@ $+

install: all
	install -d ${DST}
	install -m 0644 ${HEADERS} ${DST}
	install -m 0644 ${SRC} ${DST}
	install -m 0644 ${TARGETS} ${DST}

clean:
	rm -f *.o
