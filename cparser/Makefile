OCAMLC=ocamlc -g
OCAMLOPT=ocamlopt -g
OCAMLLEX=ocamllex
OCAMLYACC=ocamlyacc -v
OCAMLDEP=ocamldep
OCAMLMKLIB=ocamlmklib

LIBDIR=`$(OCAMLC) -where`/cparser

INTFS=C.mli

SRCS=Cerrors.ml Cabs.ml Cabshelper.ml Parse_aux.ml Parser.ml Lexer.ml \
  Machine.ml \
  Env.ml Cprint.ml Cutil.ml Ceval.ml \
  Builtins.ml GCC.ml \
  Cleanup.ml Elab.ml Rename.ml \
  Transform.ml \
  Unblock.ml StructReturn.ml \
  Bitfields.ml PackedStructs.ml \
  Parse.ml

BOBJS=$(SRCS:.ml=.cmo)
NOBJS=$(SRCS:.ml=.cmx)
IOBJS=$(INTFS:.mli=.cmi)

all: cparser.cma cparser.cmxa cparser cparser.byte

install:
	mkdir -p $(LIBDIR)
	cp -p Cparser.cmi cparser.cma cparser.cmxa cparser.a $(LIBDIR)

cparser: $(NOBJS) Main.cmx
	$(OCAMLOPT) -o cparser str.cmxa $(COBJS) $(NOBJS) Main.cmx

clean::
	rm -f cparser

cparser.byte: $(COBJS) $(BOBJS) Main.cmo
	$(OCAMLC) -custom -o cparser.byte str.cma $(COBJS) $(BOBJS) Main.cmo

clean::
	rm -f cparser.byte

cparser.cma: Cparser.cmo 
	$(OCAMLC) -a -o cparser.cma Cparser.cmo

cparser.cmxa: Cparser.cmx
	$(OCAMLOPT) -a -o cparser.cmxa Cparser.cmx

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
