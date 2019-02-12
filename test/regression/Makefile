include ../../Makefile.config

CCOMP=../../ccomp
CCOMPFLAGS=$(CCOMPOPTS) -stdlib ../../runtime \
 -dparse -dc -dclight -dasm -fall \
 -DARCH_$(ARCH) -DMODEL_$(MODEL)
INTERPFLAGS=-stdlib ../../runtime -interp -quiet -fall
LIBS=$(LIBMATH)

# Can run, both in compiled mode and in interpreter mode,
# and have reference output in Results

TESTS=int32 int64 floats floats-basics \
  expr1 expr6 funptr2 initializers initializers2 initializers3 \
  volatile1 volatile2 volatile3 volatile4 \
  funct3 expr5 struct7 struct8 struct11 struct12 casts1 casts2 char1 \
  sizeof1 sizeof2 binops bool for1 for2 switch switch2 compound \
  decl1 interop1 bitfields9 ptrs3 \
  parsing krfun

# Can run, but only in compiled mode, and have reference output in Results

TESTS_COMP=attribs1 bitfields1 bitfields2 bitfields3 bitfields4 \
  bitfields5 bitfields6 bitfields7 bitfields8 \
  builtins-$(ARCH) packedstruct1 packedstruct2 alignas \
  varargs1 varargs2 varargs3 sections alias aligned

# Can run, both in compiled mode and in interpreter mode,
# but produce processor-dependent results, so no reference output in Results

TESTS_DIFF=NaNs

# Other tests: should compile to .s without errors (but expect warnings)

EXTRAS=annot1 commaprec expr2 expr3 expr4 extern1 funct2 funptr1 \
  pragmas ptrs1 ptrs2 struct1 struct2 struct3 \
  struct4 struct5 struct6 struct9 struct10 types1 seqops \
  singlefloats emptydecl extasm

# Test known to fail
FAILURES=funct1

all: $(TESTS:%=%.compcert) $(TESTS_COMP:%=%.compcert) $(TESTS_DIFF:%=%.compcert) $(EXTRAS:%=%.s)

all_s: $(TESTS:%=%.s) $(TESTS_COMP:%=%.s) $(TESTS_DIFF:%=%.s) $(EXTRAS:%=%.s)

interop1.compcert: interop1.c
	$(CC) -DCC_SIDE -c -o interop1n.o interop1.c
	$(CCOMP) $(CCOMPFLAGS) -DCOMPCERT_SIDE -o interop1.compcert interop1.c interop1n.o $(LIBS)

interop1.s: interop1.c
	$(CCOMP) $(CCOMPFLAGS) -S interop1.c

%.compcert: %.c
	$(CCOMP) $(CCOMPFLAGS) -o $*.compcert $*.c $(LIBS)

%.s: %.c
	$(CCOMP) $(CCOMPFLAGS) -S $*.c

clean:
	rm -f *.compcert
	rm -f *.parsed.c *.compcert.c *.light.c *.s *.o *.sdump *~ 

test:
	@echo "----------- Compiled tests -------------"
	@set -e; for i in $(TESTS) $(TESTS_COMP); do \
	   SIMU='$(SIMU)' ./Runtest $$i ./$$i.compcert; \
         done
	@echo "----------- Interpreted tests -------------"
	@set -e; for i in $(TESTS); do \
           SIMU='' INTERP=1 ./Runtest $$i $(CCOMP) $(INTERPFLAGS) $$i.c; \
         done
	@for i in $(TESTS_DIFF); do \
           if $(CCOMP) -fall -interp -quiet $$i.c > _cinterp.log; then \
             if $(SIMU) ./$$i.compcert | cmp -s _cinterp.log -; \
             then echo "$$i: compiler and interpreter agree"; \
             else echo "$$i: compiler and interpreter DISAGREE"; \
             fi; \
           else \
             echo "$$i: interpreter undefined behavior"; \
           fi; \
           rm -f _cinterp.log; \
         done

bench:

