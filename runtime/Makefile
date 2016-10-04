include ../Makefile.config

CFLAGS=-O1 -g -Wall

ifeq ($(ARCH),ia32)
ifeq ($(MODEL),64)
ARCH=x86_64
endif
endif

ifeq ($(ARCH),x86_64)
OBJS=i64_dtou.o i64_utod.o i64_utof.o vararg.o
else
OBJS=i64_dtos.o i64_dtou.o i64_sar.o i64_sdiv.o i64_shl.o \
  i64_shr.o i64_smod.o i64_stod.o i64_stof.o \
  i64_udivmod.o i64_udiv.o i64_umod.o i64_utod.o i64_utof.o \
  i64_smulh.o i64_umulh.o \
  vararg.o
endif

LIB=libcompcert.a

INCLUDES=include/float.h include/stdarg.h include/stdbool.h \
  include/stddef.h include/varargs.h include/stdalign.h \
  include/stdnoreturn.h

VPATH=$(ARCH)

ifeq ($(ARCH),powerpc)
ifeq ($(MODEL),ppc64)
VPATH=powerpc/ppc64 $(ARCH)
else ifeq ($(MODEL),e5500)
VPATH=powerpc/ppc64 $(ARCH)
endif
endif

ifeq ($(strip $(HAS_RUNTIME_LIB)),true)
all: $(LIB)
else
all:
endif

$(LIB): $(OBJS)
	rm -f $(LIB)
	ar rcs $(LIB) $(OBJS)

%.o: %.s
	$(CASMRUNTIME) -o $@ $^

%.o: %.S
	$(CASMRUNTIME) -DMODEL_$(MODEL) -DABI_$(ABI) -DENDIANNESS_$(ENDIANNESS) -DSYS_$(SYSTEM) -o $@ $^

clean::
	rm -f *.o $(LIB)

ifeq ($(strip $(HAS_RUNTIME_LIB)),true)
install::
	install -d $(LIBDIR)
	install -m 0644 $(LIB) $(LIBDIR)
else
install::
endif

ifeq ($(strip $(HAS_STANDARD_HEADERS)),true)
install::
	install -d $(LIBDIR)/include
	install -m 0644 $(INCLUDES) $(LIBDIR)/include
else
install::
endif

test/test_int64: test/test_int64.c $(LIB)
	$(CC) -g -o $@ test/test_int64.c $(LIB)

clean::
	rm -f test/test_int64

.PHONY: test

test: FORCE test/test_int64
	test/test_int64

FORCE:
