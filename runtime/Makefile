CC = gcc
COQC = coqc
OCAMLC = ocamlc

CFLAGS ?= -fPIC -O2 -g
SYSTEM_INCLUDE_DIRS ?= /opt/homebrew/include
CPPFLAGS += $(SYSTEM_INCLUDE_DIRS:%=-I%) -I . -I $(shell $(OCAMLC) -where)

COQLIB = $(shell $(COQC) -where)
DST ?= $(COQLIB)/user-contrib/CertiRocq/Plugin/runtime

# Generated programs share this OCaml-compatible value layout and runtime ABI.
RUNTIME_CORE_HEADERS = m.h config.h values.h certirocq_runtime.h

# Current GC/thread interface used directly by generated code.
RUNTIME_GC_SRC = gc_stack.c
RUNTIME_GC_HEADERS = gc_stack.h

# Optional executable driver used by CertiRocq Compile when it builds and runs C.
RUNTIME_DRIVER_SRC = certirocq_run_main.c
RUNTIME_DRIVER_HEADERS =

# Rocq message FFI for standalone C and dynamically loaded plugins.
RUNTIME_FFI_SRC = rocq_c_ffi.c rocq_ffi.c
RUNTIME_FFI_HEADERS = rocq_c_ffi.h rocq_ffi.h

# Primitive-library support installed for Extract Constants Include Library.
RUNTIME_PRIMITIVE_SRC = prim_int63.c prim_floats.c prim_string.c certirocq_gmp.c
RUNTIME_PRIMITIVE_HEADERS = prim_int63.h prim_floats.h prim_string.h certirocq_gmp.h

# Helper linked into the Rocq plugins themselves.
RUNTIME_PLUGIN_HELPER_SRC = get_ordinal.c
RUNTIME_PLUGIN_HELPER_HEADERS = get_ordinal.h

RUNTIME_SRC = \
	$(RUNTIME_GC_SRC) \
	$(RUNTIME_DRIVER_SRC) \
	$(RUNTIME_FFI_SRC) \
	$(RUNTIME_PRIMITIVE_SRC) \
	$(RUNTIME_PLUGIN_HELPER_SRC)

RUNTIME_HEADERS = \
	$(RUNTIME_CORE_HEADERS) \
	$(RUNTIME_GC_HEADERS) \
	$(RUNTIME_DRIVER_HEADERS) \
	$(RUNTIME_FFI_HEADERS) \
	$(RUNTIME_PRIMITIVE_HEADERS) \
	$(RUNTIME_PLUGIN_HELPER_HEADERS)

RUNTIME_OBJECTS = $(RUNTIME_SRC:.c=.o)

# Compatibility aliases for callers that already refer to these names.
SRC = $(RUNTIME_SRC)
HEADERS = $(RUNTIME_HEADERS)
TARGETS = $(RUNTIME_OBJECTS)

.PHONY: all install clean

all: $(RUNTIME_OBJECTS)

%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c -o $@ $<

install: all
	install -d $(DST)
	install -m 0644 $(RUNTIME_HEADERS) $(DST)
	install -m 0644 $(RUNTIME_SRC) $(DST)
	install -m 0644 $(RUNTIME_OBJECTS) $(DST)

clean:
	rm -f *.o
