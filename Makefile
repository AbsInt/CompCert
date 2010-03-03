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

DIRS=lib common $(ARCH)/$(VARIANT) $(ARCH) backend cfrontend driver

INCLUDES=$(patsubst %,-I %, $(DIRS))

COQC=coqc $(INCLUDES)
COQDEP=coqdep $(INCLUDES)
COQDOC=coqdoc
COQEXEC=coqtop $(INCLUDES) -batch -load-vernac-source

OCAMLBUILD=ocamlbuild
OCB_OPTIONS=\
  -no-hygiene \
  -no-links \
  -I extraction $(INCLUDES)

VPATH=$(DIRS)
GPATH=$(DIRS)

# General-purpose libraries (in lib/)

LIB=Coqlib.v Maps.v Lattice.v Ordered.v \
  Iteration.v Integers.v Floats.v Parmov.v UnionFind.v

# Parts common to the front-ends and the back-end (in common/)

COMMON=Errors.v AST.v Events.v Globalenvs.v Mem.v Values.v \
  Smallstep.v Determinism.v Switch.v

# Back-end modules (in backend/, $(ARCH)/, $(ARCH)/$(VARIANT))

BACKEND=\
  Cminor.v Op.v CminorSel.v \
  SelectOp.v Selection.v SelectOpproof.v Selectionproof.v \
  Registers.v RTL.v \
  RTLgen.v RTLgenspec.v RTLgenproof.v \
  Tailcall.v Tailcallproof.v \
  RTLtyping.v \
  Kildall.v \
  ConstpropOp.v Constprop.v ConstpropOpproof.v Constpropproof.v \
  CSE.v CSEproof.v \
  Machregs.v Locations.v Conventions.v LTL.v LTLtyping.v \
  InterfGraph.v Coloring.v Coloringproof.v \
  Allocation.v Allocproof.v Alloctyping.v \
  Tunneling.v Tunnelingproof.v Tunnelingtyping.v \
  LTLin.v LTLintyping.v \
  Linearize.v Linearizeproof.v Linearizetyping.v \
  Linear.v Lineartyping.v \
  Parallelmove.v Reload.v Reloadproof.v Reloadtyping.v \
  Mach.v Machabstr.v Machtyping.v \
  Bounds.v Stacklayout.v Stacking.v Stackingproof.v Stackingtyping.v \
  Machconcr.v Machabstr2concr.v \
  Asm.v Asmgen.v Asmgenretaddr.v Asmgenproof1.v Asmgenproof.v

# C front-end modules (in cfrontend/)

CFRONTEND=Csyntax.v Csem.v Ctyping.v Cshmgen.v \
  Cshmgenproof1.v Cshmgenproof2.v Cshmgenproof3.v \
  Csharpminor.v Cminorgen.v Cminorgenproof.v

# Putting everything together (in driver/)

DRIVER=Compiler.v Complements.v

# All source files

FILES=$(LIB) $(COMMON) $(BACKEND) $(CFRONTEND) $(DRIVER)

proof: $(FILES:.v=.vo)

extraction:
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/extraction.v
	cd extraction && ./fixextract

ccomp: driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.native \
        && rm -f ccomp && ln -s _build/driver/Driver.native ccomp

ccomp.prof: driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.p.native \
        && rm -f ccomp.prof && ln -s _build/driver/Driver.p.native ccomp.prof

ccomp.byte: driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.d.byte \
        && rm -f ccomp.byte && ln -s _build/driver/Driver.d.byte ccomp.byte

runtime:
	$(MAKE) -C runtime

.PHONY: proof extraction cil ccomp ccomp.prof ccomp.byte runtime

all:
	$(MAKE) proof
	$(MAKE) extraction
	$(MAKE) ccomp
	$(MAKE) runtime

documentation: doc/removeproofs documentation-link
	@mkdir -p doc/html
	cd doc; $(COQDOC) --html -d html \
          $(FILES:%.v=--glob-from %.glob) $(FILES)
	@cd doc; rm -f $(FILES)
	cp doc/coqdoc.css doc/html/coqdoc.css
	doc/removeproofs doc/html/*.html

documentation-link: $(FILES)
	@ln -f $^ doc/

doc/removeproofs: doc/removeproofs.ml
	ocamlopt -o doc/removeproofs doc/removeproofs.ml

doc/removeproofs.ml: doc/removeproofs.mll
	ocamllex doc/removeproofs.mll

latexdoc:
	cd doc; $(COQDOC) --latex -o doc/doc.tex -g $(FILES)

.SUFFIXES: .v .vo

.v.vo:
	@rm -f doc/glob/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

driver/Configuration.ml: Makefile.config
	(echo 'let stdlib_path = "$(LIBDIR)"'; \
         echo 'let prepro = "$(CPREPRO)"'; \
         echo 'let asm = "$(CASM)"'; \
         echo 'let linker = "$(CLINKER)"'; \
         echo 'let arch = "$(ARCH)"'; \
         echo 'let variant = "$(VARIANT)"'; \
         echo 'let system = "$(SYSTEM)"') \
        > driver/Configuration.ml

depend:
	$(COQDEP) $(patsubst %, %/*.v, $(DIRS)) \
        | sed -e 's|$(ARCH)/$(VARIANT)/|$$(ARCH)/$$(VARIANT)/|g' \
              -e 's|$(ARCH)/|$$(ARCH)/|g' \
        > .depend

install:
	install -d $(BINDIR)
	install ./ccomp $(BINDIR)
	$(MAKE) -C runtime install

clean:
	rm -f $(patsubst %, %/*.vo, $(DIRS))
	rm -f ccomp ccomp.byte
	rm -rf _build
	rm -rf doc/html doc/*.glob
	rm -f doc/removeproofs.ml doc/removeproofs
	rm -f driver/Configuration.ml
	rm -f extraction/*.ml extraction/*.mli
	$(MAKE) -C runtime clean
	$(MAKE) -C test/cminor clean
	$(MAKE) -C test/c clean

distclean:
	$(MAKE) clean
	rm -f Makefile.config

include .depend

FORCE:
