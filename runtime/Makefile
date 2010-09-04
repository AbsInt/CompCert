include ../Makefile.config

CFLAGS=-O1 -g -Wall
OBJS=stdio.o
LIB=libcompcert.a
INCLUDES=stdio.h

ifeq ($(strip $(NEED_STDLIB_WRAPPER)),true)
all: $(LIB) $(INCLUDES)
else
all:
endif

$(LIB): $(OBJS)
	rm -f $(LIB)
	ar rcs $(LIB) $(OBJS)

clean:
	rm -f *.o $(LIB)

ifeq ($(strip $(NEED_STDLIB_WRAPPER)),true)
install:
	install -d $(LIBDIR)
	install -c $(LIB) $(INCLUDES) $(LIBDIR)
else
install:
endif
