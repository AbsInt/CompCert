#######################################################################
#                                                                     #
#              The Compcert verified compiler                         #
#                                                                     #
#          Xavier Leroy, INRIA Paris-Rocquencourt                     #
#                                                                     #
#  Copyright Institut National de Recherche en Informatique et en     #
#  Automatique.  All rights reserved.  This file is distributed       #
#  under the terms of the INRIA Non-Commercial License Agreement.     #
#                                                                     #
#######################################################################

include Makefile.config

COQC=coqc $(INCLUDES)
COQDEP=coqdep $(INCLUDES)
COQDOC=coqdoc

INCLUDES=-I lib -I common -I backend -I cfrontend

# Files in lib/

LIB=Coqlib.v Maps.v Lattice.v Ordered.v \
  Iteration.v Integers.v Floats.v Parmov.v

# Files in common/

COMMON=Errors.v AST.v Events.v Globalenvs.v Mem.v Values.v \
  Smallstep.v Switch.v Main.v Complements.v

# Files in backend/

BACKEND=\
  Cminor.v Op.v CminorSel.v \
  Selection.v Selectionproof.v \
  Registers.v RTL.v \
  RTLgen.v RTLgenspec.v RTLgenproof.v \
  RTLtyping.v \
  Kildall.v \
  Constprop.v Constpropproof.v \
  CSE.v CSEproof.v \
  Locations.v Conventions.v LTL.v LTLtyping.v \
  InterfGraph.v Coloring.v Coloringproof.v \
  Allocation.v Allocproof.v Alloctyping.v \
  Tunneling.v Tunnelingproof.v Tunnelingtyping.v \
  LTLin.v LTLintyping.v \
  Linearize.v Linearizeproof.v Linearizetyping.v \
  Linear.v Lineartyping.v \
  Parallelmove.v Reload.v Reloadproof.v Reloadtyping.v \
  Mach.v Machabstr.v Machtyping.v \
  Bounds.v Stacking.v Stackingproof.v Stackingtyping.v \
  Machconcr.v Machabstr2concr.v \
  PPC.v PPCgen.v PPCgenretaddr.v PPCgenproof1.v PPCgenproof.v

# Files in cfrontend/

CFRONTEND=Csyntax.v Csem.v Ctyping.v Cshmgen.v \
  Cshmgenproof1.v Cshmgenproof2.v Cshmgenproof3.v \
  Csharpminor.v Cminorgen.v Cminorgenproof.v

# All source files

FILES=$(LIB:%=lib/%) $(COMMON:%=common/%) $(BACKEND:%=backend/%) $(CFRONTEND:%=cfrontend/%)

FLATFILES=$(LIB) $(COMMON) $(BACKEND) $(CFRONTEND)

proof: $(FILES:.v=.vo)

all:
	$(MAKE) proof
	$(MAKE) -C cil
	$(MAKE) -C extraction extraction
	$(MAKE) -C extraction depend
	$(MAKE) -C extraction
	$(MAKE) -C runtime

documentation:
	@ln -f $(FILES) doc/
	@mkdir -p doc/html
	cd doc; $(COQDOC) --html -d html \
          $(FLATFILES:%.v=--glob-from %.glob) $(FLATFILES)
	@cd doc; rm -f $(FLATFILES)
	cp doc/coqdoc.css doc/html/coqdoc.css
	doc/removeproofs doc/html/*.html

latexdoc:
	cd doc; $(COQDOC) --latex -o doc/doc.tex -g $(FILES)

.SUFFIXES: .v .vo

.v.vo:
	@rm -f doc/glob/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

depend:
	$(COQDEP) $(FILES) > .depend

install:
	$(MAKE) -C extraction install
	$(MAKE) -C runtime install

clean:
	rm -f */*.vo *~ */*~
	rm -rf doc/html doc/*.glob
	$(MAKE) -C extraction clean
	$(MAKE) -C runtime clean
	$(MAKE) -C test/cminor clean
	$(MAKE) -C test/c clean

distclean:
	$(MAKE) clean
	rm -rf cil
	rm -f Makefile.config

include .depend

