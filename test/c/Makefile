include ../../Makefile.config

CCOMP=../../ccomp
CCOMPFLAGS=-stdlib ../../runtime -fmadd -dc -dclight -dasm

CFLAGS=-O1 -Wall

LIBS=$(LIBMATH)

TIME=xtime -o /dev/null -mintime 1.0     # Xavier's hack
#TIME=time >/dev/null                    # Otherwise

PROGS=fib integr qsort fft sha1 aes almabench lists \
  binarytrees fannkuch knucleotide mandelbrot nbody \
  nsieve nsievebits spectral vmach \
  bisect chomp perlin

all_s: $(PROGS:%=%.s)

all: $(PROGS:%=%.compcert)

all_gcc: $(PROGS:%=%.gcc)

%.compcert: %.c $(CCOMP)
	$(CCOMP) $(CCOMPFLAGS) -o $*.compcert $*.c $(LIBS)

%.s: %.c $(CCOMP)
	$(CCOMP) $(CCOMPFLAGS) -S $*.c

%.gcc: %.c
	$(CC) $(CFLAGS) -o $*.gcc $*.c $(LIBS)

test:
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

bench_gcc:
	@for i in $(PROGS); do \
	   echo -n "$$i: "; $(TIME) ./$$i.gcc; \
         done

bench:
	@for i in $(PROGS); do \
	   echo -n "$$i: "; $(TIME) ./$$i.compcert; \
         done

clean:
	rm -f *.compcert *.gcc
	rm -f *.light.c *.compcert.c *.s *.o *~ 
