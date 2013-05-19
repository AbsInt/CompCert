include ../../Makefile.config

CCOMP=../../ccomp
CCOMPFLAGS=-stdlib ../../runtime -dc -dclight -dasm

CFLAGS=-O1 -Wall

LIBS=$(LIBMATH)

TIME=xtime -o /dev/null -mintime 2.0     # Xavier's hack
#TIME=time >/dev/null                    # Otherwise

PROGS=fib integr qsort fft fftsp fftw sha1 sha3 aes almabench \
  lists binarytrees fannkuch knucleotide mandelbrot nbody \
  nsieve nsievebits spectral vmach \
  bisect chomp perlin siphash24

all: $(PROGS:%=%.compcert)

all_s: $(PROGS:%=%.s)

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
	rm -f *.light.c *.parsed.c *.s *.o *~ 
