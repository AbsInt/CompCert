include ../Makefile.config

CFLAGS=-O1 -g -Wall
INCLUDES=
OBJS=
LIB=libcompcert.a

ifeq ($(strip $(HAS_RUNTIME_LIB)),true)
all: $(LIB) $(INCLUDES)
else
all:
endif

$(LIB): $(OBJS)
	rm -f $(LIB)
	ar rcs $(LIB) $(OBJS)

clean:
	rm -f *.o $(LIB)

ifeq ($(strip $(HAS_RUNTIME_LIB)),true)
install:
	install -d $(LIBDIR)
	install -c $(LIB) $(INCLUDES) $(LIBDIR)
else
install:
endif
