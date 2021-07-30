include ../../Makefile.config

ifeq ($(wildcard ../../$(ARCH)_$(BITSIZE)),)
ARCHDIRS=$(ARCH)
else
ARCHDIRS=$(ARCH)_$(BITSIZE) $(ARCH)
endif
RECDIRS := lib common $(ARCHDIRS) cfrontend  exportcsyntax
COQINCLUDES := $(foreach d, $(RECDIRS), -R ../../$(d) compcert.$(d))
ifeq ($(LIBRARY_FLOCQ),local)
COQINCLUDES += -R ../../flocq Flocq
endif


CSYNTAXGEN=../../csyntaxgen
COQC=coqc

# Regression tests in the current directory
SRC=$(wildcard *.c)
# From ../c
SRC+=aes.c almabench.c binarytrees.c bisect.c chomp.c fannkuch.c fft.c \
  fftsp.c fftw.c fib.c integr.c knucleotide.c lists.c mandelbrot.c \
  nbody.c nsievebits.c nsieve.c perlin.c qsort.c sha1.c sha3.c \
  siphash24.c spectral.c vmach.c
# From ../raytracer
SRC+=arrays.c eval.c gmllexer.c gmlparser.c intersect.c light.c main.c \
  matrix.c memory.c object.c render.c simplify.c surface.c vector.c

CFLAGS=-DSYSTEM_$(SYSTEM)

aes.vo almabench.vo binarytrees.vo bisect.vo chomp.vo: CFLAGS += -short-idents

fft.vo fftsp.vo fftw.vo fib.vo integr.vo knucleotide.vo: CFLAGS += -short-idents

all: $(SRC:.c=.vo)

test:

%.v: %.c
	$(CSYNTAXGEN) $(CFLAGS) -o $@ $<

%.v: ../c/%.c
	$(CSYNTAXGEN) $(CFLAGS) -o $@ $<

%.v: ../raytracer/%.c
	$(CSYNTAXGEN) -I../raytracer -fall $(CFLAGS) -o $@ $<

%.vo: %.v
	$(COQC) $(COQINCLUDES) -noglob $<

.SECONDARY: $(SRC:.c=.v)

clean:
	rm -f *.v *.vo* .*.aux
