OCAMLC=ocamlc -g
OCAMLOPT=ocamlopt -g
OCAMLLEX=ocamllex
OCAMLYACC=ocamlyacc -v
OCAMLDEP=ocamldep
OCAMLMKLIB=ocamlmklib

LIBDIR=`$(OCAMLC) -where`/cparser

INTFS=C.mli

SRCS=Errors.ml Cabs.ml Cabshelper.ml Parse_aux.ml Parser.ml Lexer.ml \
  Machine.ml \
  Env.ml Cprint.ml Cutil.ml Ceval.ml \
  Builtins.ml GCC.ml \
  Cleanup.ml Elab.ml Rename.ml \
  Transform.ml \
  Unblock.ml SimplExpr.ml AddCasts.ml StructByValue.ml StructAssign.ml \
  Bitfields.ml PackedStructs.ml SimplVolatile.ml \
  Parse.ml

COBJS=uint64.o
BOBJS=$(SRCS:.ml=.cmo)
NOBJS=$(SRCS:.ml=.cmx)
IOBJS=$(INTFS:.mli=.cmi)

all: cparser.cma cparser.cmxa cparser cparser.byte

install:
	mkdir -p $(LIBDIR)
	cp -p Cparser.cmi cparser.cma cparser.cmxa cparser.a libcparser.a dllcparser.so $(LIBDIR)

cparser: $(COBJS) $(NOBJS) Main.cmx
	$(OCAMLOPT) -o cparser str.cmxa $(COBJS) $(NOBJS) Main.cmx

clean::
	rm -f cparser

cparser.byte: $(COBJS) $(BOBJS) Main.cmo
	$(OCAMLC) -custom -o cparser.byte str.cma $(COBJS) $(BOBJS) Main.cmo

clean::
	rm -f cparser.byte

cparser.cma libcparser.a: uint64.o Cparser.cmo 
	$(OCAMLMKLIB) -o cparser uint64.o Cparser.cmo

cparser.cmxa: uint64.o Cparser.cmx
	$(OCAMLMKLIB) -o cparser uint64.o Cparser.cmx

Cparser.cmo Cparser.cmi: $(IOBJS) $(BOBJS)
	$(OCAMLC) -pack -o Cparser.cmo $(IOBJS) $(BOBJS)

Cparser.cmx: $(IOBJS) $(NOBJS)
	$(OCAMLOPT) -pack -o Cparser.cmx $(IOBJS) $(NOBJS)

Parser.ml Parser.mli: Parser.mly
	$(OCAMLYACC) Parser.mly

clean::
	rm -f Parser.ml Parser.mli Parser.output

beforedepend:: Parser.ml Parser.mli

Lexer.ml: Lexer.mll
	$(OCAMLLEX) Lexer.mll

clean::
	rm -f Lexer.ml

beforedepend:: Lexer.ml

.SUFFIXES: .ml .mli .cmi .cmo .cmx

.mli.cmi:
	$(OCAMLC) -c $*.mli
.ml.cmo:
	$(OCAMLC) -c $*.ml
.ml.cmx:
	$(OCAMLOPT) -c -for-pack Cparser $*.ml
.c.o:
	$(OCAMLC) -c $*.c

clean::
	rm -f *.cm? *.cmxa *.o *.so *.a

depend: beforedepend
	$(OCAMLDEP) *.mli *.ml > .depend

include .depend
