CC=gcc
CFLAGS=-O2 -Wall

VPATH=../harness ../lib

PROGS=fib integr qsort fft sha1 aes almabench

all: $(PROGS)

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

clean::
	rm -f *.s *.o *~
