CCOMP=../../ccomp
FLAGS=-S
CPP=cpp -P
CC=gcc
CFLAGS=-arch ppc -g
ASFLAGS=-arch ppc
VPATH=../harness ../lib

PROGS=fib integr qsort fft sha1 aes almabench manyargs lists \
  stopcopy marksweep

all_s: $(PROGS:%=%.s)

all: $(PROGS)

$(PROGS:%=%.s): $(CCOMP)

fib: fib.o mainfib.o
	$(CC) $(CFLAGS) -o fib fib.o mainfib.o
clean::
	rm -f fib

integr: integr.o mainintegr.o
	$(CC) $(CFLAGS) -o integr integr.o mainintegr.o
clean::
	rm -f integr

qsort: qsort.o mainqsort.o
	$(CC) $(CFLAGS) -o qsort qsort.o mainqsort.o
clean::
	rm -f qsort

fft: fft.o mainfft.o
	$(CC) $(CFLAGS) -o fft fft.o mainfft.o -lm
clean::
	rm -f fft

sha1: sha1.o mainsha1.o
	$(CC) $(CFLAGS) -o sha1 sha1.o mainsha1.o
clean::
	rm -f sha1 sha1.cm

aes: aes.o mainaes.o
	$(CC) $(CFLAGS) -o aes aes.o mainaes.o
clean::
	rm -f aes aes.cm

almabench: almabench.o mainalmabench.o
	$(CC) $(CFLAGS) -o almabench almabench.o mainalmabench.o -lm
clean::
	rm -f almabench almabench.cm

manyargs: manyargs.o mainmanyargs.o
	$(CC) $(CFLAGS) -o manyargs manyargs.o mainmanyargs.o
clean::
	rm -f manyargs

lists: lists.o mainlists.o
	$(CC) $(CFLAGS) -o lists lists.o mainlists.o -L../../runtime -lcompcert
clean::
	rm -f lists

stopcopy: stopcopy.o maingc.o
	$(CC) $(CFLAGS) -o stopcopy stopcopy.o maingc.o
clean::
	rm -f stopcopy

marksweep: marksweep.o maingc.o marksweepcheck.o
	$(CC) $(CFLAGS) -o marksweep marksweep.o maingc.o marksweepcheck.o
clean::
	rm -f marksweep

switchtbl: switchtbl.o mainswitchtbl.o
	$(CC) $(CFLAGS) -o switchtbl switchtbl.o mainswitchtbl.o
clean::
	rm -f switchtbl

.SUFFIXES:

.SUFFIXES: .cmp .cm .s .o .c .S

.cmp.s:
	$(CPP) $*.cmp > $*.cm
	$(CCOMP) $(FLAGS) $*.cm

.cm.s:
	$(CCOMP) $(FLAGS) $*.cm

.c.o:
	$(CC) $(CFLAGS) -c $<

.s.o:
	$(AS) $(ASFLAGS) -o $*.o $<

.S.o:
	$(AS) $(ASFLAGS) -o $*.o $<

.SECONDARY: $(PROGS:%=%.s)

clean::
	rm -f *.s *.o *~
