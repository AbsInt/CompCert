CFLAGS=-arch ppc -O1 -g -Wall
#CFLAGS=-O1 -g -Wall
OBJS=stdio.o calloc.o
LIB=libcompcert.a

$(LIB): $(OBJS)
	rm -f $(LIB)
	ar rcs $(LIB) $(OBJS)

stdio.o: stdio.h

clean:
	rm -f *.o $(LIB)
