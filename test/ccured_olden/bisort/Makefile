# /* For copyright information, see olden_v1.0/COPYRIGHT */

BINARY		= bisort.exe
PROGS		= bitonic args ssplain

ifdef _MSVC
CC		= cl

SRC		= .c
OBJ		= .obj
ASM		= .s

EXTRA_CDEFS	= /DI_TIME /DI_SYS_TIME /DULTRIX
CDEFS		= /DPLAIN /DSS_PLAIN
OPTFLAGS	= /Ox

LIBS		= 
LIBPATH		= 
else
CC		= gcc -arch ppc          # MacOS X
#CC=gcc                                  # other systems
CCOMP=../../../../ccomp
CCOMPFLAGS=-dump-c

SRC		= .c
OBJ		= .o
ASM		= .s

EXTRA_CDEFS	= -DI_TIME -DI_SYS_TIME -DULTRIX
CDEFS		= -DPLAIN -DSS_PLAIN
OPTFLAGS	= -g -Wall -O3

LIBS		=                        # MacOS X
# LIBS		= -lm
LIBPATH		= 
endif

SRCS		= $(addsuffix $(SRC),$(PROGS))
OBJS		= $(addsuffix $(OBJ),$(PROGS))
ASMS		= $(addsuffix $(ASM),$(PROGS))

#defaulttarget: $(BINARY)

#$(BINARY):	$(OBJS)
#	$(CC) $(LDFALGS) $(OPTFLAGS) -o $@ $(OBJS) $(LIBPATH) $(LIBS)

#$(SRC)$(OBJ):
#	$(CC) $(CDEFS) $(EXTRA_CDEFS) $(MY_CDEFS) $(OPTFLAGS) -c $<

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
	rm -f $(BINARY) $(OBJS)  $(ASMS) *~ *.light.c *.cil.*

