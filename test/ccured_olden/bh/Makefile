##############################################################################
# MAKEFILE: compile tree-code program.                                       #
#                                                                            #
# Copyright (c) 1993, Joshua E. Barnes, Honolulu, HI.                        #
# It's free because it's yours.                                              #
##############################################################################

# Compiler flags for development on SGI; not used on other systems.
# single version: CFLAGS = -fullwarn -woff 269,302 -prototypes -O -float
# double version: CFLAGS = -DDOUBLEPREC -fullwarn -woff 269,302 -prototypes -O

# Standard compiler flags.  Double precision is the default because not
# all available systems seem to have single-precision square root.
#sm: orig: CFLAGS = -DDOUBLEPREC -O
CFLAGS = -DDOUBLEPREC -O3
LDFLAGS = -O3

# CompCert
CCOMP=../../../ccomp
CCOMPFLAGS=-dump-c

CC=gcc -arch ppc                         # MacOS X
#CC=gcc                                  # other systems

CFLAGS=-O1 -Wall

LIBS=                                    # MacOS X

# Build a treecode.
code.exe.compcert: code.compcert io.compcert load.compcert grav.compcert util.compcert getparam.compcert trusted_bh.compcert
	$(CCOMP) $(LDFLAGS) -o code.exe.compcert code.compcert io.compcert load.compcert grav.compcert\
		util.o getparam.compcert trusted_bh.compcert $(EXTRA_LIBS)

code.compcert: code.c defs.h code.h stdinc.h
	$(CCOMP) $(CCOMPFLAGS)  code.c

io.compcert: io.c defs.h stdinc.h
	$(CCOMP) $(CCOMPFLAGS)  io.c

load.compcert: load.c defs.h stdinc.h
	$(CCOMP) $(CCOMPFLAGS)  load.c

grav.compcert: grav.c defs.h stdinc.h
	$(CCOMP) $(CCOMPFLAGS) -grav.c

code.exe: code.o io.o load.o grav.o util.o getparam.o trusted_bh.o
	$(CC) $(LDFLAGS) -o code.exe code.o io.o load.o grav.o\
		util.o getparam.o trusted_bh.o -lm $(EXTRA_LIBS)

code.o: code.c defs.h code.h stdinc.h
	$(CC) $(CFLAGS) -c code.c

io.o: io.c defs.h stdinc.h
	$(CC) $(CFLAGS) -c io.c

load.o: load.c defs.h stdinc.h
	$(CC) $(CFLAGS) -c load.c

grav.o: grav.c defs.h stdinc.h
	$(CC) $(CFLAGS) -c grav.c

#  Utility routines etc.

util.o: util.c stdinc.h
	$(CC) $(CFLAGS) util.c

util.compcert: util.c stdinc.h
	$(CCOMP) $(CCOMPFLAGS) util.c

# Added to help boxing
trusted_bh.o: trusted_bh.c stdinc.h
	$(CC) $(CFLAGS) -c trusted_bh.c

getparam.o: getparam.c stdinc.h
	$(CC) $(CFLAGS) -c getparam.c

trusted_bh.compcert: trusted_bh.c stdinc.h
	$(CCOMP) $(CCOMPFLAGS) trusted_bh.c

getparam.compcert: getparam.c stdinc.h
	$(CCOMP) $(CCOMPFLAGS) getparam.c

clean: 
	rm -f *.o *.lib *.exe *.obj *~ *cil.c *_comb.c *infer.c *cured.c *.i *cured*optim.c
