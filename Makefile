#######################################################################
#                                                                     #
#              The Compcert verified compiler                         #
#                                                                     #
#          Xavier Leroy, INRIA Paris-Rocquencourt                     #
#                                                                     #
#  Copyright Institut National de Recherche en Informatique et en     #
#  Automatique.  All rights reserved.  This file is distributed       #
#  under the terms of the GNU General Public License as published by  #
#  the Free Software Foundation, either version 2 of the License, or  #
#  (at your option) any later version.  This file is also distributed #
#  under the terms of the INRIA Non-Commercial License Agreement.     #
#                                                                     #
#######################################################################

include Makefile.config

DIRS=lib common $(ARCH)/$(VARIANT) $(ARCH) backend cfrontend driver \
  flocq/Core flocq/Prop flocq/Calc flocq/Appli exportclight

RECDIRS=lib common backend cfrontend driver flocq exportclight

COQINCLUDES=$(foreach d, $(RECDIRS), -R $(d) -as compcert.$(d)) \
  -I $(ARCH)/$(VARIANT) -as compcert.$(ARCH).$(VARIANT) \
  -I $(ARCH) -as compcert.$(ARCH)

CAMLINCLUDES=$(patsubst %,-I %, $(DIRS)) -I extraction -I cparser

COQC=coqc -q $(COQINCLUDES)
COQDEP=coqdep $(COQINCLUDES)
COQDOC=coqdoc
COQEXEC=coqtop $(COQINCLUDES) -batch -load-vernac-source
COQCHK=coqchk $(COQINCLUDES)

OCAMLBUILD=ocamlbuild
OCB_OPTIONS=\
  -j 2 \
  -no-hygiene \
  -no-links \
  $(CAMLINCLUDES)
OCB_OPTIONS_CHECKLINK=\
  $(OCB_OPTIONS) \
  -I checklink \
  -use-ocamlfind
OCB_OPTIONS_CLIGHTGEN=\
  $(OCB_OPTIONS) \
  -I exportclight

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
  Postorder.v FSetAVLplus.v

# Parts common to the front-ends and the back-end (in common/)

COMMON=Errors.v AST.v Events.v Globalenvs.v Memdata.v Memtype.v Memory.v \
  Values.v Smallstep.v Behaviors.v Switch.v Determinism.v Subtyping.v

# Back-end modules (in backend/, $(ARCH)/, $(ARCH)/$(VARIANT))

BACKEND=\
  Cminor.v Op.v CminorSel.v \
  SelectOp.v SelectLong.v Selection.v \
  SelectOpproof.v SelectLongproof.v Selectionproof.v \
  Registers.v RTL.v \
  RTLgen.v RTLgenspec.v RTLgenproof.v \
  Tailcall.v Tailcallproof.v \
  Inlining.v Inliningspec.v Inliningproof.v \
  Renumber.v Renumberproof.v \
  RTLtyping.v \
  Kildall.v Liveness.v \
  ConstpropOp.v Constprop.v ConstpropOpproof.v Constpropproof.v \
  CombineOp.v CSE.v CombineOpproof.v CSEproof.v \
  Machregs.v Locations.v Conventions1.v Conventions.v LTL.v \
  Allocation.v Allocproof.v \
  Tunneling.v Tunnelingproof.v \
  Linear.v Lineartyping.v \
  Linearize.v Linearizeproof.v \
  CleanupLabels.v CleanupLabelsproof.v \
  Mach.v \
  Bounds.v Stacklayout.v Stacking.v Stackingproof.v \
  Asm.v Asmgen.v Asmgenproof0.v Asmgenproof1.v Asmgenproof.v

# C front-end modules (in cfrontend/)

CFRONTEND=Ctypes.v Cop.v Csyntax.v Csem.v Cstrategy.v Cexec.v \
  Initializers.v Initializersproof.v \
  SimplExpr.v SimplExprspec.v SimplExprproof.v \
  Clight.v ClightBigstep.v SimplLocals.v SimplLocalsproof.v \
  Cshmgen.v Cshmgenproof.v \
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

all:
	$(MAKE) proof
	$(MAKE) extraction
	$(MAKE) ccomp
ifeq ($(HAS_RUNTIME_LIB),true)
	$(MAKE) runtime
endif
ifeq ($(CCHECKLINK),true)
	$(MAKE) cchecklink
endif

proof: $(FILES:.v=.vo)

extraction: extraction/STAMP

extraction/STAMP: $(FILES:.v=.vo) extraction/extraction.v
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/extraction.v
	touch extraction/STAMP

ccomp: extraction/STAMP driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.native \
        && rm -f ccomp && $(SLN) _build/driver/Driver.native ccomp

ccomp.prof: extraction/STAMP driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.p.native \
        && rm -f ccomp.prof && $(SLN) _build/driver/Driver.p.native ccomp.prof

ccomp.byte: extraction/STAMP driver/Configuration.ml
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

clightgen: extraction/STAMP driver/Configuration.ml exportclight/Clightdefs.vo
	$(OCAMLBUILD) $(OCB_OPTIONS_CLIGHTGEN) Clightgen.native \
        && rm -f clightgen && $(SLN) _build/exportclight/Clightgen.native clightgen

clightgen.byte: extraction/STAMP driver/Configuration.ml exportclight/Clightdefs.vo
	$(OCAMLBUILD) $(OCB_OPTIONS_CLIGHTGEN) Clightgen.d.byte \
        && rm -f clightgen.byte && $(SLN) _build/exportclight/Clightgen.d.byte clightgen.byte

.PHONY: proof extraction ccomp ccomp.prof ccomp.byte runtime cchecklink cchecklink.byte clightgen clightgen.byte

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
         echo let has_runtime_lib = $(HAS_RUNTIME_LIB); \
         echo let asm_supports_cfi = $(ASM_SUPPORTS_CFI); \
         version=`cat VERSION`; \
         echo let version = "\"$$version\"") \
        > driver/Configuration.ml

depend: $(FILES) exportclight/Clightdefs.v
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
ifeq ($(HAS_RUNTIME_LIB),true)
	$(MAKE) -C runtime install
endif

clean:
	rm -f $(patsubst %, %/*.vo, $(DIRS))
	rm -f ccomp ccomp.byte cchecklink cchecklink.byte clightgen clightgen.byte
	rm -rf _build
	rm -rf doc/html doc/*.glob
	rm -f doc/coq2html.ml doc/coq2html
	rm -f driver/Configuration.ml
	rm -f extraction/STAMP extraction/*.ml extraction/*.mli
	rm -f tools/ndfun
	$(MAKE) -C runtime clean
	$(MAKE) -C test clean

distclean:
	$(MAKE) clean
	rm -f Makefile.config

check-admitted: $(FILES)
	@grep -w 'admit\|Admitted\|ADMITTED' $^ || echo "Nothing admitted."

# Problems with coqchk (coq 8.4.pl2):
# Integers.Int.Z_mod_modulus_range takes forever to check
# Floats.Float.double_of_bits_of_double takes forever to check
# AST.external_function gives "Failure: impredicative Type inductive type"
# Asm.instruction gives "Failure: impredicative Type inductive type"
# Mach.instruction gives "Failure: impredicative Type inductive type"
# UnionFind.UF.elt gives "Anomaly: Uncaught exception Reduction.NotConvertible"

check-proof: $(FILES)
	$(COQCHK) -admit Integers -admit Floats -admit AST -admit Asm -admit Mach -admit UnionFind Complements 

print-includes:
	@echo $(COQINCLUDES)

include .depend

FORCE:
