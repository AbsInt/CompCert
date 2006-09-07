COQC=coqc $(INCLUDES)
COQDEP=coqdep $(INCLUDES)
COQDOC=coqdoc
CILDISTRIB=cil-1.3.5.tar.gz

INCLUDES=-I lib -I common -I backend -I cfrontend

# Files in lib/

LIB=Coqlib.v Maps.v Sets.v union_find.v Inclusion.v Lattice.v Ordered.v \
  Iteration.v Integers.v Floats.v Parmov.v

# Files in common/

COMMON=AST.v Events.v Globalenvs.v Mem.v Values.v Main.v

# Files in backend/

BACKEND=\
  Op.v Cminor.v \
  Cmconstr.v Cmconstrproof.v \
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
  PPC.v PPCgen.v PPCgenproof1.v PPCgenproof.v

# Files in cfrontend/

CFRONTEND=Csyntax.v Csem.v Ctyping.v Cshmgen.v \
  Cshmgenproof1.v Cshmgenproof2.v Cshmgenproof3.v \
  Csharpminor.v Cminorgen.v Cminorgenproof.v

# All source files

FILES=$(LIB:%=lib/%) $(COMMON:%=common/%) $(BACKEND:%=backend/%) $(CFRONTEND:%=cfrontend/%)

FLATFILES=$(LIB) $(BACKEND) $(CFRONTEND)

proof: $(FILES:.v=.vo)

all:
	$(MAKE) proof
	$(MAKE) cil
	$(MAKE) -C extraction extraction
	$(MAKE) -C extraction depend
	$(MAKE) -C extraction

cil:
	tar xzf $(CILDISTRIB)
	for i in cil.patch/*; do patch -p1 < $$i; done
	cd cil; ./configure
	$(MAKE) -C cil

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

