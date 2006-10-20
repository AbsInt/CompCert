# /* For copyright information, see olden_v1.01/COPYRIGHT */
.KEEP_STATE:
SRCS     = main.c maketree.c

OLDEN_DIR=/u/ac/carlisle/olden_v1.01
RCC = $(OLDEN_DIR)/mcc/sparc/backend/mcc
CPP = gcc -E -U__GNUC__ -D_NO_LONGLONG
#CPPFLAGS = -DVERIFY_AFFINITIES 
CPPFLAGS = 
#LIBFLAGS = "CPPFLAGS=-DPROF"
#LIBFLAGS = "CPPFLAGS=-DVISUALIZE" "VFLAG=-v"
LIBFLAGS =
#PFLAG = -p
PFLAG =
PLIBOBJS    = plain.o plain2.o
LIBOBJS     = libolden.a
OBJS     = $(SRCS:%.c=%.o)  args.o
ROBJS    = $(SRCS:%.c=%.r.o) args.o
LIBLINK     = $(LIBOBJS:%=$(OLDEN_DIR)/runtime/%)
RLIBLINK    = $(PLIBOBJS:%=$(OLDEN_DIR)/runtime/%)
INCDIRS     = /usr/include $(OLDEN_DIR)/runtime
NODELIBS =
LIBDIRS     =

CC    = cc
#sm: CFLAGS      =
CFLAGS      = -O2


# sm:
PLAIN=1
all: defaulttarget

ifdef PLAIN
ifdef _MSVC
EXTOBJ = .obj
OBJOUT = /Fo
EXEOUT = /Fe
CFLAGS = /DPLAIN
CONLY  = /c
CC     = cl
else
EXTOBJ = .o
OBJOUT = -o
EXEOUT = -o
CFLAGS += -DPLAIN
CONLY  = -c
CC     = gcc -arch ppc
CCOMP=../../../../ccomp
CCOMPFLAGS=-dump-c

endif

OBJS = maketree$(EXTOBJ) main$(EXTOBJ)

%.obj : %.c
	$(CC) $(CONLY) $(CFLAGS) $< $(OBJOUT)$@


defaulttarget: $(OBJS)
	$(CC) $(CFLAGS) $(OBJS) $(EXEOUT)perimeter.exe
endif

perm: $(OBJS) target
	/usr/bin/cmmd-ld \
	-comp $(CC) $(OBJS) $(LIBLINK) -v -o /scratch1/carlisle/perm   \
	$(LIBDIRS:%=-L%) $(NODELIBS:%=-l%)

plain: $(ROBJS) target
	/usr/bin/cmmd-ld \
	-comp $(CC) $(ROBJS) $(RLIBLINK) -v -o /scratch1/carlisle/plainperm   \
	$(LIBDIRS:%=-L%) $(NODELIBS:%=-l%)

ifndef PLAIN
args.s: args.c
	/lib/cpp $(CPPFLAGS) $(INCDIRS:%=-I%) args.c | $(RCC) > args.s
endif

%.s:    %.c
	$(CPP) -DFUTURES  $(CPPFLAGS) $(INCDIRS:%=-I%) $< | $(RCC) $(PFLAG) -n -m -k > $*.s


%.p.s:    %.c
	/lib/cpp -DPLAIN $(CPPFLAGS) $(INCDIRS:%=-I%) $< | $(RCC) -f > $*.p.s

%.o:	%.s
	$(CC) $(CFLAGS) -c $<


%.r.o:	%.p.s
	$(CC) $(CFLAGS) -c $< -o $*.r.o

target: 
	cd $(OLDEN_DIR)/runtime; make $(LIBFLAGS)

clean:
	rm -f $(TARGET) $(OBJS) *.exe *.o *.obj *~ .make.state .nse_depinfo *.s *.light.c


