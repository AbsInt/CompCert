
CC		= gcc -arch ppc
CCOMP=../../../../ccomp
CCOMPFLAGS=-dump-c

CFLAGS		= $(EXTRA_CFLAGS)
#CFLAGS		= -O2
LDFLAGS         = $(EXTRA_LDFLAGS)

CFLAGS += -DPLAIN

ifdef _MSVC
  # ...
else
  MATH = -lm
  CFLAGS += -g -ffloat-store
  LDFLAGS += -g -ffloat-store
endif

PROGS = compute build main

#defaulttarget: $(OBJS)
#	$(CC) $(LDFLAGS) $(OBJS) $(EXTRA_LIBS) -o power.exe $(MATH)

all_s: $(PROGS:%=%.s)

all: $(PROGS:%=%.compcert)

all_gcc: $(PROGS:%=%.gcc)

%.compcert: %.s
	$(CC) $(LDFALGS)  -o $*.compcert $*.s 

%.s: %.c ../../../../ccomp
	$(CCOMP) $(CCOMPFLAGS) $*.c

%.gcc: %.c
	$(CC) $(CFLAGS) $(LDFALGS) $(OPTFLAGS) -o $*.gcc $*.c 

clean:
	rm -f $(TARGET) $(OBJS) *~ *.obj *.o *.exe .make.state .nse_depinfo *.light.c *.s *.compcert
