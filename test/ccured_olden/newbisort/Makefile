# /* For copyright information, see olden_v1.0/COPYRIGHT */

BINARY		= bisort
PROGS		= bitonic args ssplain

CC		= gcc -arch ppc
CCOMP=../../../ccomp
CCOMPFLAGS=-dump-c

SRC		= .c
OBJ		= .o
ASM		= .s
SRCS		= $(addsuffix $(SRC),$(PROGS))
OBJS		= $(addsuffix $(OBJ),$(PROGS))
ASMS		= $(addsuffix $(ASM),$(PROGS))
INCDIRS		= /usr/include 

EXTRA_CDEFS	= -DI_TIME -DI_SYS_TIME -DULTRIX
CDEFS		= -DPLAIN -DSS_PLAIN #-I$(OLDENHOME)/common
OPTFLAGS	= -g -Wall -O3

LIBS		= -lc -lgcc -lm
LIBPATH		= 

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
	$(CCOMP) $(CCOMPFLAGS)  $(CDEFS) $(EXTRA_CDEFS) $*.c

%.gcc: %.c
	$(CC) $(CFLAGS) $(LDFALGS) $(OPTFLAGS) -o $*.gcc $*.c $(LIBS)

clean:
	rm -f $(BINARY) $(OBJS) *~  $(ASMS) *.light.c

