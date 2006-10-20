# /* For copyright information, see olden_v1.0/COPYRIGHT */

BINARY		= voronoi.exe
PROGS		= newvor vector output args ssplain trusted_voronoi

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
CCOMP=../../../ccomp
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
# sm: ??
ifdef _MSVC
CDEFS		= $(DEF)PLAIN $(DEF)SS_PLAIN $(DEF)OLDEN
else
CDEFS		= $(DEF)PLAIN $(DEF)OLDEN
endif
SRCS		= $(addsuffix $(SRC),$(FILES))
OBJS		= $(addsuffix $(OBJ),$(FILES))
ASMS		= $(addsuffix $(ASM),$(FILES))

all_s: $(PROGS:%=%.s)

all: $(PROGS:%=%.compcert)

all_gcc: $(PROGS:%=%.gcc)

%.compcert: %.s
	$(CC) $(CFLAGS) $(LDFALGS) $(OPTFLAGS) -o $*.compcert $*.s $(LIBS)

%.s: %.c ../../../../ccomp
	$(CCOMP) $(CCOMPFLAGS)  $(CDEFS) $(EXTRA_CDEFS)  $(MY_CDEFS) $*.c

%.gcc: %.c
	$(CC) $(CFLAGS) $(LDFALGS) $(OPTFLAGS) -o $*.gcc $*.c $(LIBS)

#$(BINARY):	$(OBJS)
#	$(CC) $(LDFALGS) $(OPTFLAGS) $(EXEOUT)$@ $(OBJS) $(LIBPATH) $(LIBS)

#%$(OBJ) : %$(SRC)
#	$(CC) $(CDEFS) $(EXTRA_CDEFS) $(MY_CDEFS) $(OPTFLAGS) $(CONLY) $<

clean:
	rm -f $(BINARY) $(OBJS) *~ 

