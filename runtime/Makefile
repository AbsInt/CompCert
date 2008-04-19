include ../Makefile.config

CFLAGS=-O1 -g -Wall
OBJS=stdio.o calloc.o
LIB=libcompcert.a
INCLUDES=stdio.h

$(LIB): $(OBJS)
	rm -f $(LIB)
	ar rcs $(LIB) $(OBJS)

stdio.o: stdio.h

clean:
	rm -f *.o $(LIB)

install:
	install -d $(LIBDIR)
	install -c $(LIB) $(INCLUDES) $(LIBDIR)
