include ../Makefile.config

CFLAGS=-O1 -g -Wall
INCLUDES=
OBJS=int64.o
LIB=libcompcert.a

all: $(LIB) $(INCLUDES)

$(LIB): $(OBJS)
	rm -f $(LIB)
	ar rcs $(LIB) $(OBJS)

%.o: $(ARCH)/%.s
	$(CASM) $^

clean::
	rm -f *.o $(LIB)

install:
	install -d $(LIBDIR)
	install -c $(LIB) $(INCLUDES) $(LIBDIR)

test/test_int64: test/test_int64.c $(LIB)
	$(CC) -o $@ test/test_int64.c $(LIB)

clean::
	rm -f test/test_int64

.PHONY: test

test: FORCE test/test_int64
	test/test_int64

FORCE:
