#######################################################################
#                                                                     #
#              The Compcert verified compiler                         #
#                                                                     #
#        François Pottier, INRIA Paris-Rocquencourt                   #
#                                                                     #
#  Copyright Institut National de Recherche en Informatique et en     #
#  Automatique.  All rights reserved.  This file is distributed       #
#  under the terms of the INRIA Non-Commercial License Agreement.     #
#                                                                     #
#######################################################################

.PHONY: all clean

SOURCES := $(wildcard *.c)
TARGETS := \
  $(patsubst %.c,%.ccomp.err,$(SOURCES)) \
  $(patsubst %.c,%.gcc.err,$(SOURCES)) \
  $(patsubst %.c,%.clang.err,$(SOURCES))

CCOMP   := ../../../ccomp
GCC     := gcc
CLANG   := clang

all: $(TARGETS)

clean:
	@ rm -f *.err *~

%.ccomp.err: %.c $(CCOMP)
	@ echo $(CCOMP) -c $<
	@ if $(CCOMP) -c $< 2>$@ ; then \
	  echo "UNEXPECTED SUCCESS: $(CCOMP) -c $< SUCCEEDED!" ; \
	fi
	@ if grep "unknown syntax error" $@ ; then \
	  echo "UNKNOWN SYNTAX ERROR!" ; \
	fi

%.gcc.err: %.c
	@ echo $(GCC) -c $<
	@ if $(GCC) -c $< 2>$@ ; then \
	  echo "UNEXPECTED SUCCESS: $(GCC) -c $< SUCCEEDED!" ; \
	fi

%.clang.err: %.c
	@ echo $(CLANG) -c $<
	@ if $(CLANG) -c $< 2>$@ ; then \
	  echo "UNEXPECTED SUCCESS: $(CLANG) -c $< SUCCEEDED!" ; \
	fi

