CC=../../ccomp 
CFLAGS=-U__GNUC__ -stdlib ../../runtime -dclight -dasm
LIBS=

OBJS=memory.o gmllexer.o gmlparser.o eval.o \
  arrays.o vector.o matrix.o object.o intersect.o surface.o light.o \
  simplify.o render.o main.o

render: $(OBJS)
	$(CC) $(CFLAGS) -o render $(OBJS) $(LIBS)

clean:
	rm -f *.o *.light.c *.s *.ppm render

include .depend

depend:
	gcc -MM *.c > .depend

gcc0:
	$(MAKE) clean
	$(MAKE) CC=gcc CFLAGS="-O0 -Wall"
	mv render render.gcc0
	$(MAKE) clean

gcc1:
	$(MAKE) clean
	$(MAKE) CC=gcc CFLAGS="-O1 -Wall"
	mv render render.gcc1
	$(MAKE) clean

gcc2:
	$(MAKE) clean
	$(MAKE) CC=gcc CFLAGS="-O2 -Wall"
	mv render render.gcc2
	$(MAKE) clean

gcc3:
	$(MAKE) clean
	$(MAKE) CC=gcc CFLAGS="-O3 -Wall"
	mv render render.gcc3
	$(MAKE) clean

