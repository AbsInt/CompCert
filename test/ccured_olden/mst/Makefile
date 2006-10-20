# /* For copyright information, see olden_v1.0/COPYRIGHT */

BINARY		= mst.exe
PROGS		= main makegraph hash args ssplain

OLDENHOME	= /tmp/olden

ifdef _MSVC
CC    = cl
DEF   = /D
CONLY = /c
OBJOUT = /Fo
EXEOUT = /Fe
OBJ   = .obj

OPTFLAGS	= /Ox
LIBS = 

else

CC		= gcc -arch ppc
CCOMP=../../../../ccomp
CCOMPFLAGS=-dump-c
DEF   = -D
CONLY = -c
OBJOUT= -o
EXEOUT= -o

OBJ		= .o

OPTFLAGS	= -g -Wall -O3

LIBS		= 
LIBPATH		= 
endif

SRC		= .c
ASM		= .s
EXTRA_CDEFS	= $(DEF)I_TIME $(DEF)I_SYS_TIME $(DEF)ULTRIX
CDEFS		= $(DEF)PLAIN $(DEF)SS_PLAIN
SRCS		= $(addsuffix $(SRC),$(PROGS))
OBJS		= $(addsuffix $(OBJ),$(PROGS))
ASMS		= $(addsuffix $(ASM),$(PROGS))

all_s: $(PROGS:%=%.s)

all: $(PROGS:%=%.compcert)

all_gcc: $(PROGS:%=%.gcc)

%.compcert: %.s
	$(CC) $(CFLAGS) $(LDFALGS) $(OPTFLAGS) -o $*.compcert $*.s $(LIBS)

%.s: %.c ../../../../ccomp
	$(CCOMP) $(CCOMPFLAGS) $*.c

%.gcc: %.c
	$(CC) $(CFLAGS) $(LDFALGS) $(OPTFLAGS) -o $*.gcc $*.c $(LIBS)

clean:
	rm -f $(BINARY) $(OBJS) $(OBJS) *~ *infer.c *cured.c *cil.c *_comb.c *.i *.light.c

