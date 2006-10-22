CCOMP=../../ccomp
CCOMPFLAGS=-dump-c -I../lib

CC=gcc -arch ppc

CFLAGS=-O1 -Wall

LIBS=

TIME=xtime -o /dev/null -mintime 1.0     # Xavier's hack
#TIME=time >/dev/null                    # Otherwise

PROGS=fib integr qsort fft sha1 aes almabench lists \
  binarytrees fannkuch knucleotide mandelbrot nbody \
  nsieve nsievebits spectral

all_s: $(PROGS:%=%.s)

all: $(PROGS:%=%.compcert)

all_gcc: $(PROGS:%=%.gcc)

%.compcert: %.s
	$(CC) $(CFLAGS) -o $*.compcert $*.s ../lib/libcompcert.a $(LIBS)

%.s: %.c ../../ccomp
	$(CCOMP) $(CCOMPFLAGS) $*.c

%.gcc: %.c
	$(CC) $(CFLAGS) -o $*.gcc $*.c $(LIBS)

test_compcert:
	@for i in $(PROGS); do \
	   if ./$$i.compcert | cmp -s - Results/$$i; \
           then echo "$$i: passed"; \
           else echo "$$i: FAILED"; \
	   fi; \
         done

test_gcc:
	@for i in $(PROGS); do \
	   if ./$$i.gcc | cmp -s - Results/$$i; \
           then echo "$$i: passed"; \
           else echo "$$i: FAILED"; \
	   fi; \
         done

time_gcc:
	@for i in $(PROGS); do \
	   echo -n "$$i: "; $(TIME) ./$$i.gcc; \
         done

clean:
	rm -f *.compcert *.gcc
	rm -f *.light.c *.s *.o *~ 
