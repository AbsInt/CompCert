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

DIRS=lib common $(ARCH) backend cfrontend driver debug\
  flocq/Core flocq/Prop flocq/Calc flocq/Appli exportclight \
  cparser cparser/validator

RECDIRS=lib common $(ARCH) backend cfrontend driver flocq exportclight cparser

COQINCLUDES=$(foreach d, $(RECDIRS), -R $(d) compcert.$(d))

COQC="$(COQBIN)coqc" -q $(COQINCLUDES)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQDOC="$(COQBIN)coqdoc"
COQEXEC="$(COQBIN)coqtop" $(COQINCLUDES) -batch -load-vernac-source
COQCHK="$(COQBIN)coqchk" $(COQINCLUDES)
MENHIR=menhir
CP=cp

VPATH=$(DIRS)
GPATH=$(DIRS)

# Flocq

FLOCQ=\
  Fcore_Raux.v Fcore_Zaux.v Fcore_defs.v Fcore_digits.v                     \
  Fcore_float_prop.v Fcore_FIX.v Fcore_FLT.v Fcore_FLX.v                    \
  Fcore_FTZ.v Fcore_generic_fmt.v Fcore_rnd.v Fcore_rnd_ne.v                \
  Fcore_ulp.v Fcore.v                                                       \
  Fcalc_bracket.v Fcalc_digits.v Fcalc_div.v Fcalc_ops.v                    \
  Fcalc_round.v Fcalc_sqrt.v                                                \
  Fprop_div_sqrt_error.v Fprop_mult_error.v Fprop_plus_error.v              \
  Fprop_relative.v Fprop_Sterbenz.v                                         \
  Fappli_rnd_odd.v Fappli_double_round.v Fappli_IEEE.v Fappli_IEEE_bits.v

# General-purpose libraries (in lib/)

VLIB=Axioms.v Coqlib.v Intv.v Maps.v Heaps.v Lattice.v Ordered.v \
  Iteration.v Integers.v Archi.v Fappli_IEEE_extra.v Floats.v \
  Parmov.v UnionFind.v Wfsimpl.v \
  Postorder.v FSetAVLplus.v IntvSets.v Decidableplus.v

# Parts common to the front-ends and the back-end (in common/)

COMMON=Errors.v AST.v Linking.v \
  Events.v Globalenvs.v Memdata.v Memtype.v Memory.v \
  Values.v Smallstep.v Behaviors.v Switch.v Determinism.v Unityping.v \
  Separation.v

# Back-end modules (in backend/, $(ARCH)/)

BACKEND=\
  Cminor.v Op.v CminorSel.v \
  SelectOp.v SelectDiv.v SelectLong.v Selection.v \
  SelectOpproof.v SelectDivproof.v SelectLongproof.v Selectionproof.v \
  Registers.v RTL.v \
  RTLgen.v RTLgenspec.v RTLgenproof.v \
  Tailcall.v Tailcallproof.v \
  Inlining.v Inliningspec.v Inliningproof.v \
  Renumber.v Renumberproof.v \
  RTLtyping.v \
  Kildall.v Liveness.v \
  ValueDomain.v ValueAOp.v ValueAnalysis.v \
  ConstpropOp.v Constprop.v ConstpropOpproof.v Constpropproof.v \
  CSEdomain.v CombineOp.v CSE.v CombineOpproof.v CSEproof.v \
  NeedDomain.v NeedOp.v Deadcode.v Deadcodeproof.v \
  Unusedglob.v Unusedglobproof.v \
  Machregs.v Locations.v Conventions1.v Conventions.v LTL.v \
  Allocation.v Allocproof.v \
  Tunneling.v Tunnelingproof.v \
  Linear.v Lineartyping.v \
  Linearize.v Linearizeproof.v \
  CleanupLabels.v CleanupLabelsproof.v \
  Debugvar.v Debugvarproof.v \
  Mach.v \
  Bounds.v Stacklayout.v Stacking.v Stackingproof.v \
  Asm.v Asmgen.v Asmgenproof0.v Asmgenproof1.v Asmgenproof.v

# C front-end modules (in cfrontend/)

CFRONTEND=Ctypes.v Cop.v Csyntax.v Csem.v Ctyping.v Cstrategy.v Cexec.v \
  Initializers.v Initializersproof.v \
  SimplExpr.v SimplExprspec.v SimplExprproof.v \
  Clight.v ClightBigstep.v SimplLocals.v SimplLocalsproof.v \
  Cshmgen.v Cshmgenproof.v \
  Csharpminor.v Cminorgen.v Cminorgenproof.v

# LR(1) parser validator

PARSERVALIDATOR=Alphabet.v Interpreter_complete.v Interpreter.v \
  Validator_complete.v Automaton.v Interpreter_correct.v Main.v \
  Validator_safe.v Grammar.v Interpreter_safe.v Tuples.v

# Parser

PARSER=Cabs.v Parser.v

# Putting everything together (in driver/)

DRIVER=Compopts.v Compiler.v Complements.v

# All source files

FILES=$(VLIB) $(COMMON) $(BACKEND) $(CFRONTEND) $(DRIVER) $(FLOCQ) \
  $(PARSERVALIDATOR) $(PARSER)

all:
	$(MAKE) proof
	$(MAKE) extraction
	$(MAKE) ccomp
ifeq ($(HAS_RUNTIME_LIB),true)
	$(MAKE) runtime
endif
ifeq ($(CLIGHTGEN),true)
	$(MAKE) clightgen
endif


proof: $(FILES:.v=.vo)

extraction: extraction/STAMP

extraction/STAMP: $(FILES:.v=.vo) extraction/extraction.v $(ARCH)/extractionMachdep.v
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/extraction.v
	touch extraction/STAMP

.depend.extr: extraction/STAMP tools/modorder driver/Version.ml
	$(MAKE) -f Makefile.extr depend

ccomp: .depend.extr compcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr ccomp
ccomp.byte: .depend.extr compcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr ccomp.byte

clightgen: .depend.extr compcert.ini exportclight/Clightdefs.vo driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr clightgen
clightgen.byte: .depend.extr compcert.ini exportclight/Clightdefs.vo driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr clightgen.byte

runtime:
	$(MAKE) -C runtime

FORCE:

.PHONY: proof extraction runtime FORCE

documentation: doc/coq2html $(FILES)
	mkdir -p doc/html
	rm -f doc/html/*.html
	doc/coq2html -o 'doc/html/%.html' doc/*.glob \
          $(filter-out doc/coq2html cparser/Parser.v, $^)
	cp doc/coq2html.css doc/coq2html.js doc/html/

doc/coq2html: doc/coq2html.ml
	ocamlopt -w +a-29 -o doc/coq2html str.cmxa doc/coq2html.ml

doc/coq2html.ml: doc/coq2html.mll
	ocamllex -q doc/coq2html.mll

tools/ndfun: tools/ndfun.ml
	ocamlopt -o tools/ndfun str.cmxa tools/ndfun.ml
tools/modorder: tools/modorder.ml
	ocamlopt -o tools/modorder str.cmxa tools/modorder.ml

latexdoc:
	cd doc; $(COQDOC) --latex -o doc/doc.tex -g $(FILES)

%.vo: %.v
	@rm -f doc/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

%.v: %.vp tools/ndfun
	@rm -f $*.v
	@echo "Preprocessing $*.vp"
	@tools/ndfun $*.vp > $*.v || { rm -f $*.v; exit 2; }
	@chmod -w $*.v

compcert.ini: Makefile.config
	(echo "stdlib_path=$(LIBDIR)"; \
         echo "prepro=$(CPREPRO)"; \
         echo "linker=$(CLINKER)"; \
         echo "asm=$(CASM)"; \
	 echo "prepro_options=$(CPREPRO_OPTIONS)";\
	 echo "asm_options=$(CASM_OPTIONS)";\
	 echo "linker_options=$(CLINKER_OPTIONS)";\
         echo "arch=$(ARCH)"; \
         echo "model=$(MODEL)"; \
         echo "abi=$(ABI)"; \
         echo "system=$(SYSTEM)"; \
         echo "has_runtime_lib=$(HAS_RUNTIME_LIB)"; \
         echo "has_standard_headers=$(HAS_STANDARD_HEADERS)"; \
         echo "asm_supports_cfi=$(ASM_SUPPORTS_CFI)"; \
         echo "struct_passing_style=$(STRUCT_PASSING)"; \
         echo "struct_return_style=$(STRUCT_RETURN)";) \
        > compcert.ini

driver/Version.ml: VERSION
	cat VERSION \
	| sed -e 's|\(.*\)=\(.*\)|let \1 = \"\2\"|g' \
	>driver/Version.ml

cparser/Parser.v: cparser/Parser.vy
	$(MENHIR) --coq cparser/Parser.vy

depend: $(FILES) exportclight/Clightdefs.v
	$(COQDEP) $^ \
        | sed -e 's|$(ARCH)/|$$(ARCH)/|g' \
        > .depend

install:
	install -d $(BINDIR)
	install -m 0755 ./ccomp $(BINDIR)
	install -d $(SHAREDIR)
	install -m 0644 ./compcert.ini $(SHAREDIR)
	$(MAKE) -C runtime install
ifeq ($(CLIGHTGEN),true)
	install -m 0755 ./clightgen $(BINDIR)
endif

clean:
	rm -f $(patsubst %, %/*.vo, $(DIRS))
	rm -rf doc/html doc/*.glob
	rm -f doc/coq2html.ml doc/coq2html doc/*.cm? doc/*.o
	rm -f driver/Version.ml
	rm -f compcert.ini
	rm -f extraction/STAMP extraction/*.ml extraction/*.mli .depend.extr
	rm -f tools/ndfun tools/modorder tools/*.cm? tools/*.o
	rm -f $(ARCH)/ConstpropOp.v $(ARCH)/SelectOp.v backend/SelectDiv.v backend/SelectLong.v
	$(MAKE) -f Makefile.extr clean
	$(MAKE) -C runtime clean
	$(MAKE) -C test clean

distclean:
	$(MAKE) clean
	rm -f Makefile.config

check-admitted: $(FILES)
	@grep -w 'admit\|Admitted\|ADMITTED' $^ || echo "Nothing admitted."

# Problems with coqchk (coq 8.5pl1):
# Integers.Int.Z_mod_modulus_range takes forever to check
# compcert.lib.Floats.Float.of_longu_from_words takes forever to check
# compcert.backend.SelectDivproof.divs_mul_shift_2 takes forever to check

check-proof: $(FILES)
	$(COQCHK) -admit Integers -admit Floats -admit SelectDivproof Complements

print-includes:
	@echo $(COQINCLUDES)

include .depend

FORCE:
