include ../../Makefile.config

ifeq ($(wildcard ../../$(ARCH)_$(BITSIZE)),)
ARCHDIRS=$(ARCH)
else
ARCHDIRS=$(ARCH)_$(BITSIZE) $(ARCH)
endif
RECDIRS := lib common $(ARCHDIRS) cfrontend  exportclight
COQINCLUDES := $(foreach d, $(RECDIRS), -R ../../$(d) compcert.$(d))
ifeq ($(LIBRARY_FLOCQ),local)
COQINCLUDES += -R ../../flocq Flocq
endif


CLIGHTGEN=../../clightgen
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

fft.vo fftsp.vo fftw.vo fib.vo integr.vo knucleotide.vo: CFLAGS += -short-idents -normalize

qsort.vo sha1.vo sha3.vo siphash24.vo spectral.vo vmach.vo: CFLAGS += -normalize

all: $(SRC:.c=.vo)

test:

%.v: %.c
	$(CLIGHTGEN) $(CFLAGS) -o $@ $<

%.v: ../c/%.c
	$(CLIGHTGEN) $(CFLAGS) -o $@ $<

%.v: ../raytracer/%.c
	$(CLIGHTGEN) -I../raytracer -fall $(CFLAGS) -o $@ $<

%.vo: %.v
	$(COQC) $(COQINCLUDES) -noglob $<

.SECONDARY: $(SRC:.c=.v)

clean:
	rm -f *.v *.vo* .*.aux
