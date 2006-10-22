CFLAGS=-arch ppc -O1 -g -Wall
OBJS=compcert_stdio.o
LIB=libcompcert.a

$(LIB): $(OBJS)
	ar rcs $(LIB) $(OBJS)

compcert_stdio.o: compcert_stdio.h
