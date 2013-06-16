include ../Makefile.config

CFLAGS=-O1 -g -Wall
INCLUDES=
OBJS=i64_dtos.o i64_dtou.o i64_sar.o i64_sdiv.o i64_shl.o \
  i64_shr.o i64_smod.o i64_stod.o i64_stof.o \
  i64_udivmod.o i64_udiv.o i64_umod.o i64_utod.o i64_utof.o
LIB=libcompcert.a

ifeq ($(strip $(HAS_RUNTIME_LIB)),true)
all: $(LIB) $(INCLUDES)
else
all:
endif

$(LIB): $(OBJS)
	rm -f $(LIB)
	ar rcs $(LIB) $(OBJS)

%.o: $(ARCH)/%.s
	$(CASMRUNTIME) -o $@ $^

%.o: $(ARCH)/%.S
	$(CASMRUNTIME) -DVARIANT_$(VARIANT) -DSYS_$(SYSTEM) -o $@ $^

clean::
	rm -f *.o $(LIB)

ifeq ($(strip $(HAS_RUNTIME_LIB)),true)
install:
	install -d $(LIBDIR)
	install -c $(LIB) $(INCLUDES) $(LIBDIR)
else
install:
endif

test/test_int64: test/test_int64.c $(LIB)
	$(CC) -o $@ test/test_int64.c $(LIB)

clean::
	rm -f test/test_int64

.PHONY: test

test: FORCE test/test_int64
	test/test_int64

FORCE:
