CC    = gcc

#CFLAGS      =
CFLAGS      = -O2

# sm
PLAIN=1
all: defaulttarget

ifdef PLAIN
ifdef _MSVC
EXTOBJ = .obj
OBJOUT = /Fo
EXEOUT = /Fe
CFLAGS = /DPLAIN
CONLY  = /c
CC     = cl
else
EXTOBJ = .o
OBJOUT = -o
EXEOUT = -o
CFLAGS += -DPLAIN
CONLY  = -c
CC     = gcc
MATH   = -lm
endif

MYOBJS = tsp$(EXTOBJ) build$(EXTOBJ) main$(EXTOBJ)

%$(EXTOBJ) : %.c
	$(CC) $(CONLY) $(CFLAGS) $< $(OBJOUT)$@


defaulttarget: $(MYOBJS)
	$(CC) $(CFLAGS) $(MYOBJS) $(EXTRA_LIBS) $(EXEOUT)tsp.exe $(MATH)
endif



clean:
	rm -f $(TARGET) $(OBJS) *.o *.obj *.exe *~ .make.state .nse_depinfo



