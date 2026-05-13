CC = gcc
COQC = coqc
OCAMLC = ocamlc

CFLAGS ?= -fPIC -O2 -g
SYSTEM_INCLUDE_DIRS ?= /opt/homebrew/include
RUNTIME_INCLUDE_DIRS = . gc lib driver
CPPFLAGS += $(RUNTIME_INCLUDE_DIRS:%=-I%) $(SYSTEM_INCLUDE_DIRS:%=-I%) -I $(shell $(OCAMLC) -where)

COQLIB = $(shell $(COQC) -where)
DST ?= $(COQLIB)/user-contrib/CertiRocq/Plugin/runtime

# Generated programs share this OCaml-compatible value layout and runtime ABI.
RUNTIME_CORE_SRC = certirocq_runtime.c
RUNTIME_CORE_HEADERS = m.h config.h values.h certirocq_runtime.h

# Current GC/thread interface used directly by generated code.
RUNTIME_GC_SRC = gc/gc.c
RUNTIME_GC_HEADERS = gc/gc.h

# Optional executable driver used by CertiRocq Compile when it builds and runs C.
RUNTIME_DRIVER_SRC = driver/certirocq_run_main.c
RUNTIME_DRIVER_HEADERS =

# Rocq message FFI for standalone C and dynamically loaded plugins.
RUNTIME_FFI_SRC = lib/rocq_c_ffi.c lib/rocq_ffi.c
RUNTIME_FFI_HEADERS = lib/rocq_c_ffi.h lib/rocq_ffi.h

# Primitive-library support installed for Extract Constants Include Library.
RUNTIME_PRIMITIVE_SRC = lib/prim_int63.c lib/prim_floats.c lib/prim_string.c lib/certirocq_gmp.c
RUNTIME_PRIMITIVE_HEADERS = lib/prim_int63.h lib/prim_floats.h lib/prim_string.h lib/certirocq_gmp.h

# Helper linked into the Rocq plugins themselves.
RUNTIME_PLUGIN_HELPER_SRC = lib/get_ordinal.c
RUNTIME_PLUGIN_HELPER_HEADERS = lib/get_ordinal.h

RUNTIME_SRC = \
	$(RUNTIME_CORE_SRC) \
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
RUNTIME_GC_OBJECTS = $(RUNTIME_GC_SRC:.c=.o)
RUNTIME_DRIVER_OBJECTS = $(RUNTIME_DRIVER_SRC:.c=.o)
RUNTIME_LIB_SRC = $(RUNTIME_FFI_SRC) $(RUNTIME_PRIMITIVE_SRC) $(RUNTIME_PLUGIN_HELPER_SRC)
RUNTIME_LIB_HEADERS = $(RUNTIME_FFI_HEADERS) $(RUNTIME_PRIMITIVE_HEADERS) $(RUNTIME_PLUGIN_HELPER_HEADERS)
RUNTIME_LIB_OBJECTS = $(RUNTIME_LIB_SRC:.c=.o)

# Compatibility aliases for callers that already refer to these names.
SRC = $(RUNTIME_SRC)
HEADERS = $(RUNTIME_HEADERS)
TARGETS = $(RUNTIME_OBJECTS)

.PHONY: all install clean

all: $(RUNTIME_OBJECTS)

%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c -o $@ $<

install: all
	install -d $(DST) $(DST)/gc $(DST)/lib $(DST)/driver
	install -m 0644 $(RUNTIME_CORE_HEADERS) $(RUNTIME_CORE_SRC) $(RUNTIME_CORE_SRC:.c=.o) $(DST)
	install -m 0644 $(RUNTIME_DRIVER_SRC) $(RUNTIME_DRIVER_OBJECTS) $(DST)/driver
	install -m 0644 $(RUNTIME_GC_HEADERS) $(RUNTIME_GC_SRC) $(RUNTIME_GC_OBJECTS) $(DST)/gc
	install -m 0644 $(RUNTIME_LIB_HEADERS) $(RUNTIME_LIB_SRC) $(RUNTIME_LIB_OBJECTS) $(DST)/lib

clean:
	rm -f $(RUNTIME_OBJECTS)
