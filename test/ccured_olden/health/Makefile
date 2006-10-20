# /* For copyright information, see olden_v1.0/COPYRIGHT */

BINARY		= health.exe
PROGS		= health poisson list args ssplain

# ------- msvc ------
ifdef _MSVC
CC		= cl

CFLAGS		=
CONLY           = /c
SRC		= .c
OBJ		= .obj
ASM		= .s
EXEOUT          = /Fe

EXTRA_CDEFS	= /DI_TIME /DI_SYS_TIME /DULTRIX
CDEFS		= /DPLAIN /DSS_PLAIN
ifdef _DEBUG
OPTFLAGS        = /Zi /MLd
else
OPTFLAGS	= /Ox
endif

LIBS		= 
LIBPATH		= 

# ------- gcc ------
else
CC		= gcc -arch ppc
CCOMP=../../../../ccomp
CCOMPFLAGS=-dump-c

CFLAGS		= -O3
CONLY           = -c
SRC		= .c
OBJ		= .gcc
OBJCCOMP	= .compcert
ASM		= .s

EXTRA_CDEFS	= -DI_TIME -DI_SYS_TIME -DULTRIX
CDEFS		= -DPLAIN -DSS_PLAIN
OPTFLAGS	= -g -Wall -O3
EXEOUT          = -gcc

LIBS		= 
LIBPATH		= 
endif

# ------- common --------

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
	rm -f $(BINARY) *.o *~ *.s *.light.c *.cil.* *.compcert



