include ../../Makefile.config

CC=../../ccomp 
CFLAGS=$(CCOMPOPTS) -stdlib ../../runtime -dparse -dclight -dasm -fstruct-return
LIBS=$(LIBMATH)
TIME=ocaml unix.cma ../../tools/xtime.ml -mintime 2.0 -minruns 4

OBJS=memory.o gmllexer.o gmlparser.o eval.o \
  arrays.o vector.o matrix.o object.o intersect.o surface.o light.o \
  simplify.o render.o main.o

all: render

render: $(OBJS)
	$(CC) $(CFLAGS) -o render $(OBJS) $(LIBS)

clean:
	rm -f *.o *.parsed.c *.light.c *.s *.sdump *.ppm render

include .depend

depend:
	gcc -MM *.c > .depend

test:
	$(SIMU) ./render < kal.gml
	@if cmp kal.ppm Results/kal.ppm; \
        then echo "raytracer: passed"; \
        else echo "raytracer: FAILED"; exit 2; \
        fi

bench:
	@$(TIME) -name raytracer -- sh -c './render < kal.gml'
