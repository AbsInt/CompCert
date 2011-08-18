CC=../../ccomp 
CFLAGS=-U__GNUC__ -stdlib ../../runtime -dclight -dasm
LIBS=
TIME=xtime -o /dev/null -mintime 1.0

EXE=arcode lzw lzss

COMMON_OBJS=optlist.o bitfile.o

all: $(EXE)

ARCODE_OBJS=$(COMMON_OBJS) arcode.o armain.o

arcode: $(ARCODE_OBJS)
	$(CC) $(CFLAGS) -o $@ $(ARCODE_OBJS) $(LIBS)

LZW_OBJS=$(COMMON_OBJS) lzwencode.o lzwdecode.o lzwmain.o

lzw: $(LZW_OBJS)
	$(CC) $(CFLAGS) -o $@ $(LZW_OBJS) $(LIBS)

LZSS_OBJS=$(COMMON_OBJS) lzvars.o lzhash.o lzencode.o lzdecode.o lzssmain.o

lzss: $(LZSS_OBJS)
	$(CC) $(CFLAGS) -o $@ $(LZSS_OBJS) $(LIBS)

TESTFILE:=$(firstword $(wildcard /usr/share/dict/words) ./lzss)
TESTCOMPR=/tmp/testcompr.out
TESTEXPND=/tmp/testexpnd.out

test:
	rm -f $(TESTCOMPR) $(TESTEXPND)
	@echo "Test data: $(TESTFILE)"
	@for i in $(EXE); do \
          echo "$$i: compression..."; \
          ./$$i -c -i $(TESTFILE) -o $(TESTCOMPR); \
          echo "$$i: decompression..."; \
          ./$$i -d -i $(TESTCOMPR) -o $(TESTEXPND); \
          if cmp $(TESTFILE) $(TESTEXPND); \
          then echo "$$i: passed"; \
          else echo "$$i: FAILED"; \
          fi; \
        done
	rm -f $(TESTCOMPR) $(TESTEXPND)

bench:
	rm -f $(TESTCOMPR)
	@for i in $(EXE); do \
          echo -n "$$i "; \
          $(TIME) sh -c "./$$i -c -i $(TESTFILE) -o $(TESTCOMPR) && ./$$i -d -i $(TESTCOMPR) -o /dev/null"; \
         done
	rm -f $(TESTCOMPR)

include .depend

clean:
	rm -f *.o *.light.c *.s $(EXE)

depend:
	gcc -MM *.c > .depend
