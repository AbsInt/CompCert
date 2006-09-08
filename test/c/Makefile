CC=gcc
CFLAGS=-O2 -Wall
CCOMP=../../ccomp
CCOMPFLAGS=-dump-c

PROGS=fib integr qsort fft sha1 aes almabench

all_s: $(PROGS:%=%.s)

all: $(PROGS)

%: %.s
	$(CC) $(CFLAGS) -o $* $*.s

%.s: %.c ../../ccomp
	$(CCOMP) $(CCOMPFLAGS) $*.c

clean:
	rm -f $(PROGS)
	rm -f *.clight *.s *.o *~ 
