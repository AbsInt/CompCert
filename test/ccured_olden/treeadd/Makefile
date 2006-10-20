# /* For copyright information, see olden_v1.0/COPYRIGHT */

BINARY		= treeadd.exe
FILES		= par-alloc node args ssplain


OLDENHOME	= /tmp/olden

CC		= gcc

SRC		= .c
OBJ		= .o
ASM		= .s
SRCS		= $(addsuffix $(SRC),$(FILES))
OBJS		= $(addsuffix $(OBJ),$(FILES))
ASMS		= $(addsuffix $(ASM),$(FILES))
INCDIRS		= /usr/include 

EXTRA_CDEFS	= -DI_TIME -DI_SYS_TIME -DULTRIX
CDEFS		= -DPLAIN -DSS_PLAIN #-I$(OLDENHOME)/common
OPTFLAGS	= -g -Wall -O3

LIBS		= -lm
LIBPATH		= 

$(BINARY):	$(OBJS)
	$(CC) $(LDFALGS) $(OPTFLAGS) -o $@ $(OBJS) $(LIBPATH) $(LIBS)

$(SRC)$(OBJ):
	$(CC) $(CDEFS) $(EXTRA_CDEFS) $(MY_CDEFS) $(OPTFLAGS) -c $<

clean:
	rm -f $(BINARY) $(OBJS)  $(ASMS) *~ *.light.c 

links:
	/bin/rm -f ssplain.[hc]
	ln -s $(OLDENHOME)/common/ssplain.h
	ln -s $(OLDENHOME)/common/ssplain.c
