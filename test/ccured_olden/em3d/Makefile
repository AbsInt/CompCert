# /* For copyright information, see olden_v1.0/COPYRIGHT */

BINARY		= em3d.exe
BINARYCCOMP	= em3d.exe.compcert
PROGS		= main em3d make_graph util args ssplain


OLDENHOME	= /tmp/olden

CC		= gcc -arch ppc
CCOMP		= ../../../ccomp
CCOMPFLAGS=-dump-c

SRC		= .c
OBJ		= .o
ASM		= .s
SRCS		= $(addsuffix $(SRC),$(PROGS))
OBJS		= $(addsuffix $(OBJ),$(PROGS))
ASMS		= $(addsuffix $(ASM),$(PROGS))
INCDIRS		= /usr/include 

EXTRA_CDEFS	= -DI_TIME -DI_SYS_TIME -DULTRIX
CDEFS		= -DPLAIN -DSS_PLAIN -DSS_RAND #-I$(OLDENHOME)/common
OPTFLAGS	= -g -Wall -O3

LIBS		= 
LIBPATH		= 

#$(BINARY):	$(OBJS)
#	$(CC) $(LDFALGS) $(OPTFLAGS) -o $@ $(OBJS) $(LIBPATH) $(LIBS)

all_s: $(PROGS:%=%.s)

all: $(PROGS:%=%.compcert)

all_gcc: $(PROGS:%=%.gcc)

%.compcert: %.s
	$(CC) $(CFLAGS) $(LDFALGS) $(OPTFLAGS) -o $*.compcert $*.s $(LIBS)

%.s: %.c ../../../../ccomp
	$(CCOMP) $(CCOMPFLAGS) $*.c

%.gcc: %.c
	$(CC) $(CFLAGS) $(LDFALGS) $(OPTFLAGS) -o $*.gcc $*.c $(LIBS)



#$(BINARYCCOMP):	$(OBJSCCOMP)
#	$(CC) $(LDFALGS) $(OPTFLAGS) -o $@ $(OBJSCCOMP) $(LIBPATH) $(LIBS)

#$(OBJCCOMP):
#	$(CCOMP) $(CDEFS) $(EXTRA_CDEFS) $(MY_CDEFS) $(OPTFLAGS) -c $<

$(SRC)$(OBJ):
	$(CC) $(CDEFS) $(EXTRA_CDEFS) $(MY_CDEFS) $(OPTFLAGS) -c $<

clean:
	rm -f $(BINARY) $(BINARYCCOMP) $(OBJS) $(ASMS) *~ *.light.c *.cil.* 

links:
	/bin/rm -f ssplain.[hc]
	ln -s $(OLDENHOME)/common/ssplain.h
	ln -s $(OLDENHOME)/common/ssplain.c
