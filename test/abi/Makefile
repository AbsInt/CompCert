include ../../Makefile.config

CCOMP=../../ccomp -stdlib ../../runtime
CCOMPFLAGS=
CFLAGS=-O -Wno-overflow -Wno-constant-conversion

TESTS=fixed.compcert fixed.cc2compcert fixed.compcert2cc \
     vararg.compcert vararg.cc2compcert vararg.compcert2cc \
     struct.compcert struct.cc2compcert struct.compcert2cc

all: $(TESTS)

all_s: fixed_def_compcert.s fixed_use_compcert.s \
       vararg_def_compcert.s vararg_use_compcert.s \
       struct_def_compcert.s struct_use_compcert.s

test:
	@set -e; for t in $(TESTS); do \
          SIMU='$(SIMU)' ARCH=$(ARCH) MODEL=$(MODEL) ABI=$(ABI) SYSTEM=$(SYSTEM) ./Runtest $$t; \
         done

generator.exe: generator.ml
	ocamlopt -g -o $@ generator.ml

clean::
	rm -f generator.exe *.cm[iox]

fixed_decl.h: generator.exe
	./generator.exe -rnd 500 -o fixed

fixed_def.c fixed_use.c: fixed_decl.h

clean::
	rm -f fixed_decl.h fixed_def.c fixed_use.c

vararg_decl.h: generator.exe
	./generator.exe -vararg -rnd 500 -o vararg

vararg_def.c vararg_use.c: vararg_decl.h

clean::
	rm -f vararg_decl.h vararg_def.c vararg_use.c

struct_decl.h: generator.exe
	./generator.exe -structs -o struct

struct_def.c struct_use.c: struct_decl.h

clean::
	rm -f struct_decl.h struct_def.c struct_use.c

struct%.o: CCOMPFLAGS += -fstruct-passing -dclight

%_compcert.o: %.c
	$(CCOMP) $(CCOMPFLAGS) -c -o $@ $*.c
%_cc.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $*.c

%_compcert.s: %.c
	$(CCOMP) -S -o $@ $*.c
%_cc.s: %.c
	$(CC) $(CFLAGS) -S -o $@ $*.c

%.compcert: %_def_compcert.o %_use_compcert.o
	$(CCOMP) -o $@ $*_def_compcert.o $*_use_compcert.o

%.cc2compcert: %_def_compcert.o %_use_cc.o
	$(CCOMP) -o $@ $*_def_compcert.o $*_use_cc.o

%.compcert2cc: %_def_cc.o %_use_compcert.o
	$(CCOMP) -o $@ $*_def_cc.o $*_use_compcert.o

clean::
	rm -f *.[os] *.compcert *.cc2compcert *.compcert2cc *.light.c

