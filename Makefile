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

DIRS=lib common $(ARCH)/$(VARIANT) $(ARCH) backend cfrontend driver \
  flocq/Core flocq/Prop flocq/Calc flocq/Appli

INCLUDES=$(patsubst %,-I %, $(DIRS))

COQC=/usr/local/bin/coqc -q $(INCLUDES)
COQDEP=/usr/local/bin/coqdep $(INCLUDES)
COQDOC=/usr/local/bin/coqdoc
COQEXEC=/usr/local/bin/coqtop $(INCLUDES) -batch -load-vernac-source
COQCHK=coqchk $(INCLUDES)

OCAMLBUILD=ocamlbuild
OCB_OPTIONS=\
  -j 2 \
  -no-hygiene \
  -no-links \
  -I extraction -I cparser $(INCLUDES)
OCB_OPTIONS_CHECKLINK=\
  $(OCB_OPTIONS) \
  -I checklink \
  -use-ocamlfind

VPATH=$(DIRS)
GPATH=$(DIRS)

# Flocq
FLOCQ_CORE=Fcore_float_prop.v Fcore_Zaux.v Fcore_rnd_ne.v Fcore_FTZ.v \
  Fcore_FLT.v Fcore_defs.v Fcore_Raux.v Fcore_ulp.v Fcore_rnd.v Fcore_FLX.v \
  Fcore_FIX.v Fcore_digits.v Fcore_generic_fmt.v Fcore.v
FLOCQ_PROP=Fprop_Sterbenz.v Fprop_mult_error.v Fprop_relative.v \
  Fprop_div_sqrt_error.v Fprop_plus_error.v
FLOCQ_CALC=Fcalc_ops.v Fcalc_bracket.v Fcalc_sqrt.v Fcalc_div.v Fcalc_round.v \
  Fcalc_digits.v
FLOCQ_APPLI=Fappli_IEEE_bits.v Fappli_IEEE.v
FLOCQ=$(FLOCQ_CORE) $(FLOCQ_PROP) $(FLOCQ_CALC) $(FLOCQ_APPLI)

# General-purpose libraries (in lib/)

LIB=Axioms.v Coqlib.v Intv.v Maps.v Heaps.v Lattice.v Ordered.v \
  Iteration.v Integers.v Floats.v Parmov.v UnionFind.v Wfsimpl.v \
  Postorder.v

# Parts common to the front-ends and the back-end (in common/)

COMMON=Errors.v AST.v Events.v Globalenvs.v Memdata.v Memtype.v Memory.v \
  Values.v Smallstep.v Behaviors.v Switch.v Determinism.v

# Back-end modules (in backend/, $(ARCH)/, $(ARCH)/$(VARIANT))

BACKEND=\
  Cminor.v Op.v CminorSel.v \
  SelectOp.v Selection.v SelectOpproof.v Selectionproof.v \
  Registers.v RTL.v \
  RTLgen.v RTLgenspec.v RTLgenproof.v \
  Tailcall.v Tailcallproof.v \
  Inlining.v Inliningspec.v Inliningproof.v \
  Renumber.v Renumberproof.v \
  RTLtyping.v \
  Kildall.v \
  ConstpropOp.v Constprop.v ConstpropOpproof.v Constpropproof.v \
  CombineOp.v CSE.v CombineOpproof.v CSEproof.v \
  Machregs.v Locations.v Conventions1.v Conventions.v LTL.v LTLtyping.v \
  InterfGraph.v Coloring.v Coloringproof.v \
  Allocation.v Allocproof.v Alloctyping.v \
  Tunneling.v Tunnelingproof.v Tunnelingtyping.v \
  LTLin.v LTLintyping.v \
  Linearize.v Linearizeproof.v Linearizetyping.v \
  CleanupLabels.v CleanupLabelsproof.v CleanupLabelstyping.v \
  Linear.v Lineartyping.v \
  Parallelmove.v Reload.v Reloadproof.v Reloadtyping.v \
  RRE.v RREproof.v RREtyping.v \
  Mach.v Machtyping.v \
  Bounds.v Stacklayout.v Stacking.v Stackingproof.v Stackingtyping.v \
  Machsem.v \
  Asm.v Asmgen.v Asmgenretaddr.v Asmgenproof1.v Asmgenproof.v 

# C front-end modules (in cfrontend/)

CFRONTEND=Csyntax.v Csem.v Cstrategy.v Cexec.v \
  Initializers.v Initializersproof.v \
  SimplExpr.v SimplExprspec.v SimplExprproof.v \
  Clight.v Cshmgen.v Cshmgenproof.v  \
  Csharpminor.v Cminorgen.v Cminorgenproof.v

# Putting everything together (in driver/)

DRIVER=Compiler.v Complements.v

# All source files

FILES=$(LIB) $(COMMON) $(BACKEND) $(CFRONTEND) $(DRIVER) $(FLOCQ)

# Symbolic links vs. copy

ifneq (,$(findstring CYGWIN,$(shell uname -s)))
SLN=cp
else
SLN=ln -s
endif

proof: $(FILES:.v=.vo)

extraction:
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/extraction.v

ccomp: driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.native \
        && rm -f ccomp && $(SLN) _build/driver/Driver.native ccomp

ccomp.prof: driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.p.native \
        && rm -f ccomp.prof && $(SLN) _build/driver/Driver.p.native ccomp.prof

ccomp.byte: driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.d.byte \
        && rm -f ccomp.byte && $(SLN) _build/driver/Driver.d.byte ccomp.byte

runtime:
	$(MAKE) -C runtime

cchecklink: driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS_CHECKLINK) Validator.native \
        && rm -f cchecklink && $(SLN) _build/checklink/Validator.native cchecklink

cchecklink.byte: driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS_CHECKLINK) Validator.d.byte \
        && rm -f cchecklink.byte && $(SLN) _build/checklink/Validator.d.byte cchecklink.byte

.PHONY: proof extraction cil ccomp ccomp.prof ccomp.byte runtime cchecklink cchecklink.byte

all:
	$(MAKE) proof
	$(MAKE) extraction
	$(MAKE) ccomp
	$(MAKE) runtime
ifeq ($(CCHECKLINK),true)
	$(MAKE) cchecklink
endif

documentation: doc/coq2html $(FILES)
	mkdir -p doc/html
	rm -f doc/html/*.html
	doc/coq2html -o 'doc/html/%.html' doc/*.glob \
          $(filter-out doc/coq2html, $^)
	cp doc/coq2html.css doc/coq2html.js doc/html/

doc/coq2html: doc/coq2html.ml
	ocamlopt -o doc/coq2html str.cmxa doc/coq2html.ml

doc/coq2html.ml: doc/coq2html.mll
	ocamllex doc/coq2html.mll

tools/ndfun: tools/ndfun.ml
	ocamlopt -o tools/ndfun str.cmxa tools/ndfun.ml

latexdoc:
	cd doc; $(COQDOC) --latex -o doc/doc.tex -g $(FILES)

%.vo: %.v
	@rm -f doc/glob/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

%.v: %.vp tools/ndfun
	@rm -f $*.v
	@echo "Preprocessing $*.vp"
	@tools/ndfun $*.vp > $*.v || { rm -f $*.v; exit 2; }
	@chmod -w $*.v

driver/Configuration.ml: Makefile.config VERSION
	(echo let stdlib_path = "\"$(LIBDIR)\""; \
         echo let prepro = "\"$(CPREPRO)\""; \
         echo let asm = "\"$(CASM)\""; \
         echo let linker = "\"$(CLINKER)\""; \
         echo let arch = "\"$(ARCH)\""; \
         echo let variant = "\"$(VARIANT)\""; \
         echo let system = "\"$(SYSTEM)\""; \
         echo let need_stdlib_wrapper = $(NEED_STDLIB_WRAPPER); \
         version=`cat VERSION`; \
         echo let version = "\"$$version\"") \
        > driver/Configuration.ml

depend: $(FILES)
	$(COQDEP) $^ \
        | sed -e 's|$(ARCH)/$(VARIANT)/|$$(ARCH)/$$(VARIANT)/|g' \
              -e 's|$(ARCH)/|$$(ARCH)/|g' \
        > .depend

install:
	install -d $(BINDIR)
	install ./ccomp $(BINDIR)
ifeq ($(CCHECKLINK),true)
	install ./cchecklink $(BINDIR)
endif
	$(MAKE) -C runtime install

clean:
	rm -f $(patsubst %, %/*.vo, $(DIRS))
	rm -f ccomp ccomp.byte cchecklink cchecklink.byte
	rm -rf _build
	rm -rf doc/html doc/*.glob
	rm -f doc/coq2html.ml doc/coq2html
	rm -f driver/Configuration.ml
	rm -f extraction/*.ml extraction/*.mli
	rm -f tools/ndfun
	$(MAKE) -C runtime clean
	$(MAKE) -C test/cminor clean
	$(MAKE) -C test/c clean

distclean:
	$(MAKE) clean
	rm -f Makefile.config

check-admitted: $(FILES)
	@grep -w 'admit\|Admitted\|ADMITTED' $^ || echo "Nothing admitted."

# Problems with coqchk:
#   Integers.one_bits_range takes forever to check
#   Mach#<>#instruction causes a failure
check-proof: $(FILES)
	$(COQCHK) -admit Integers Complements

include .depend

FORCE:
