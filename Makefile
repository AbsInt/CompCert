COQC=coqc $(INCLUDES)
COQDEP=coqdep $(INCLUDES)
COQDOC=coqdoc

INCLUDES=-I lib -I backend -I cfrontend

# Files in lib/

LIB=Coqlib.v Maps.v Sets.v union_find.v Inclusion.v Lattice.v Ordered.v \
  Iteration.v Integers.v Floats.v Parmov.v

# Files in backend/

BACKEND=AST.v Values.v Mem.v Events.v Globalenvs.v \
  Op.v Cminor.v \
  Cmconstr.v Cmconstrproof.v \
  Csharpminor.v Cminorgen.v Cminorgenproof.v \
  Registers.v RTL.v \
  RTLgen.v RTLgenproof1.v RTLgenproof.v \
  RTLtyping.v \
  Kildall.v \
  Constprop.v Constpropproof.v \
  CSE.v CSEproof.v \
  Locations.v Conventions.v LTL.v LTLtyping.v \
  InterfGraph.v Coloring.v Coloringproof.v \
  Parallelmove.v Allocation.v \
  Allocproof.v Alloctyping.v \
  Tunneling.v Tunnelingproof.v Tunnelingtyping.v \
  Linear.v Lineartyping.v \
  Linearize.v Linearizeproof.v Linearizetyping.v \
  Mach.v Machabstr.v Machtyping.v \
  Stacking.v Stackingproof.v Stackingtyping.v \
  Machabstr2mach.v \
  PPC.v PPCgen.v PPCgenproof1.v PPCgenproof.v \
  Main.v

# Files in cfrontend/

CFRONTEND=Csyntax.v Csem.v Ctyping.v Cshmgen.v \
  Cshmgenproof1.v Cshmgenproof2.v Cshmgenproof3.v 

# All source files

FILES=$(LIB:%=lib/%) $(BACKEND:%=backend/%) $(CFRONTEND:%=cfrontend/%)

FLATFILES=$(LIB) $(BACKEND) $(CFRONTEND)

proof: $(FILES:.v=.vo)

all:
	$(MAKE) proof
	$(MAKE) -C extraction extraction
	$(MAKE) -C extraction depend
	$(MAKE) -C extraction

documentation:
	$(COQDOC) --html -d doc $(FLATFILES:%.v=--glob-from doc/%.glob) $(FILES)
	doc/removeproofs doc/lib.*.html doc/backend.*.html

latexdoc:
	$(COQDOC) --latex -o doc/doc.tex -g $(FILES)

.SUFFIXES: .v .vo

.v.vo:
	@rm -f doc/glob/$(*F).glob
	$(COQC) -dump-glob doc/$(*F).glob $*.v

depend:
	$(COQDEP) $(FILES) > .depend

clean:
	rm -f */*.vo *~ */*~
	rm -f doc/lib.*.html doc/backend.*.html doc/*.glob
	$(MAKE) -C extraction clean
	$(MAKE) -C test/cminor clean

include .depend

