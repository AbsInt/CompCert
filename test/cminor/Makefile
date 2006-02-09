CCOMP=../../ccomp
CPP=cpp -P
CC=gcc
CFLAGS=-g
VPATH=../harness ../lib

PROGS=fib integr qsort fft sha1 aes almabench manyargs

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

fft: fft.o mainfft.o staticlib.o
	$(CC) $(CFLAGS) -o fft fft.o mainfft.o staticlib.o -lm
clean::
	rm -f fft

sha1: sha1.o mainsha1.o staticlib.o
	$(CC) $(CFLAGS) -o sha1 sha1.o mainsha1.o staticlib.o
clean::
	rm -f sha1 sha1.cm

aes: aes.o mainaes.o
	$(CC) $(CFLAGS) -o aes aes.o mainaes.o
clean::
	rm -f aes aes.cm

almabench: almabench.o mainalmabench.o staticlib.o
	$(CC) $(CFLAGS) -o almabench almabench.o mainalmabench.o staticlib.o -lm
clean::
	rm -f almabench almabench.cm

manyargs: manyargs.o mainmanyargs.o
	$(CC) $(CFLAGS) -o manyargs manyargs.o mainmanyargs.o
clean::
	rm -f manyargs

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

clean::
	rm -f *.s *.o *~
