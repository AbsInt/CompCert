include ../../Makefile.config

CCOMP=../../ccomp -stdlib ../../runtime
CCOMPFLAGS=
CFLAGS=-O -Wno-overflow -Wno-constant-conversion

TESTS=fixed.compcert fixed.cc2compcert fixed.compcert2cc \
     vararg.compcert vararg.cc2compcert vararg.compcert2cc \
     struct.compcert struct.cc2compcert struct.compcert2cc

DIFFTESTS=layout.compcert layout.cc \
          staticlayout.compcert staticlayout.cc

all: $(TESTS) $(DIFFTESTS)

all_s: fixed_def_compcert.s fixed_use_compcert.s \
       vararg_def_compcert.s vararg_use_compcert.s \
       struct_def_compcert.s struct_use_compcert.s

test:
	@set -e; for t in $(TESTS); do \
          SIMU='$(SIMU)' ARCH=$(ARCH) MODEL=$(MODEL) ABI=$(ABI) SYSTEM=$(SYSTEM) ./Runtest $$t; \
         done
	@set -e; for t in layout staticlayout; do \
	  $(SIMU) ./$$t.compcert > _compcert.log; \
	  $(SIMU) ./$$t.cc > _cc.log; \
	 if diff -a -u  _cc.log  _compcert.log; \
         then echo "$$t: CompCert and $CC agree"; rm _*.log; \
	 else echo "$$t: CompCert and $CC DISAGREE"; exit 2; fi; \
         done

generator.exe: generator.ml
	ocamlopt -g -o $@ generator.ml

genlayout.exe: genlayout.ml
	ocamlopt -g -o $@ genlayout.ml

clean::
	rm -f generator.exe genlayout.exe *.cm[iox]

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

ifeq ($(ARCH),arm)
GENLAYOUT_OPTIONS += -stable
endif
ifeq ($(ARCH),aarch64)
GENLAYOUT_OPTIONS += -stable
endif

layout.h: genlayout.exe
	./genlayout.exe $(GENLAYOUT_OPTIONS) > layout.h

struct%.o: CCOMPFLAGS += -fstruct-passing -dclight

%_compcert.o: %.c
	$(CCOMP) $(CCOMPFLAGS) -c -o $@ $*.c
%_cc.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $*.c

%_compcert.s: %.c
	$(CCOMP) -S -o $@ $*.c
%_cc.s: %.c
	$(CC) $(CFLAGS) -S -o $@ $*.c

layout.compcert: layout.c layout.h
	$(CCOMP) $(CCOMPFLAGS) -o $@ layout.c
layout.cc: layout.c layout.h
	$(CC) $(CFLAGS) -o $@ layout.c

staticlayout.compcert: staticlayout.c layout.h
	$(CCOMP) $(CCOMPFLAGS) -o $@ staticlayout.c
staticlayout.cc: staticlayout.c layout.h
	$(CC) $(CFLAGS) -o $@ staticlayout.c

%.compcert: %_def_compcert.o %_use_compcert.o
	$(CCOMP) -o $@ $*_def_compcert.o $*_use_compcert.o

%.compcert: %_def_compcert.o %_use_compcert.o
	$(CCOMP) -o $@ $*_def_compcert.o $*_use_compcert.o

%.cc2compcert: %_def_compcert.o %_use_cc.o
	$(CCOMP) -o $@ $*_def_compcert.o $*_use_cc.o

%.compcert2cc: %_def_cc.o %_use_compcert.o
	$(CCOMP) -o $@ $*_def_cc.o $*_use_compcert.o

clean::
	rm -f *.[os] *.compcert *.cc2compcert *.compcert2cc *.light.c

