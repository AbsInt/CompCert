#######################################################################
#                                                                     #
#              The Compcert verified compiler                         #
#                                                                     #
#          Xavier Leroy, INRIA Paris-Rocquencourt                     #
#                                                                     #
#  Copyright Institut National de Recherche en Informatique et en     #
#  Automatique.  All rights reserved.  This file is distributed       #
#  under the terms of the GNU Lesser General Public License as        #
#  published by the Free Software Foundation, either version 2.1 of   #
#  the License, or (at your option) any later version.                #
#  This file is also distributed under the terms of the               #
#  INRIA Non-Commercial License Agreement.                            #
#                                                                     #
#######################################################################

include Makefile.config
include VERSION

BUILDVERSION ?= $(version)
BUILDNR ?= $(buildnr)
TAG ?= $(tag)
BRANCH ?= $(branch)

ifeq ($(wildcard $(ARCH)_$(BITSIZE)),)
ARCHDIRS=$(ARCH)
else
ARCHDIRS=$(ARCH)_$(BITSIZE) $(ARCH)
endif

DIRS := lib common $(ARCHDIRS) backend cfrontend driver export cparser

COQINCLUDES := $(foreach d, $(DIRS), -R $(d) compcert.$(d))

ifeq ($(LIBRARY_FLOCQ),local)
DIRS += flocq/Core flocq/Prop flocq/Calc flocq/IEEE754
COQINCLUDES += -R flocq Flocq
endif

ifeq ($(LIBRARY_MENHIRLIB),local)
DIRS += MenhirLib
COQINCLUDES += -R MenhirLib MenhirLib
endif

# Notes on silenced Coq warnings:
#
# unused-pattern-matching-variable:
#    warning introduced in 8.13
#    the code rewrite that avoids the warning is not desirable
# deprecated-ident-entry:
#    warning introduced in 8.13
#    suggested change (use `name` instead of `ident`) supported since 8.13
# deprecated-instance-without-locality:
#    warning introduced in 8.14
#    triggered by Menhir-generated files, to be solved upstream in Menhir
# opaque-let:
#    warning introduced in 8.18, addressed in the main CompCert files,
#    still triggered by Flocq, to be solved upstream

COQCOPTS ?= \
  -w -unused-pattern-matching-variable \
  -w -deprecated-ident-entry

cparser/Parser.vo: COQCOPTS += -w -deprecated-instance-without-locality
flocq/IEEE754/Bits.vo: COQCOPTS += -w -opaque-let

ifneq ($(INSTALL_COQDEV),true)
# Disable costly generation of .cmx files, which are not used locally
  COQCOPTS += -w -deprecated-native-compiler-option -native-compiler no
endif

ifneq (,$(TIMING))
  # does this coq version support -time-file ? (Coq >= 8.18)
  ifeq (,$(shell "$(COQBIN)coqc" -time-file /dev/null 2>&1))
    COQCOPTS += -time-file $<.timing
  endif
endif

ifneq (,$(PROFILING))
  # does this coq version dupport -profile ? (Coq >= 8.19)
  ifeq (,$(shell "$(COQBIN)coqc" -profile /dev/null 2>&1))
    COQCOPTS += -profile $<.prof.json
    PROFILE_ZIP = gzip -f $<.prof.json
  else
  endif
endif
PROFILE_ZIP ?= true

COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQDOC="$(COQBIN)coqdoc"
COQEXEC="$(COQBIN)coqtop" $(COQINCLUDES) -batch -load-vernac-source
COQCHK="$(COQBIN)coqchk" $(COQINCLUDES)
MENHIR=menhir
CP=cp

VPATH=$(DIRS)
GPATH=$(DIRS)

# Flocq

ifeq ($(LIBRARY_FLOCQ),local)
FLOCQ=\
  Raux.v Zaux.v Defs.v Digits.v Float_prop.v FIX.v FLT.v FLX.v FTZ.v \
  Generic_fmt.v Round_pred.v Round_NE.v Ulp.v Core.v \
  Bracket.v Div.v Operations.v Plus.v Round.v Sqrt.v \
  Div_sqrt_error.v Mult_error.v Plus_error.v \
  Relative.v Sterbenz.v Round_odd.v Double_rounding.v \
  BinarySingleNaN.v Binary.v Bits.v
else
FLOCQ=
endif

# General-purpose libraries (in lib/)

VLIB=Axioms.v Coqlib.v Intv.v Maps.v Heaps.v Lattice.v Ordered.v \
  Iteration.v Zbits.v Integers.v Archi.v IEEE754_extra.v Floats.v \
  Parmov.v UnionFind.v Wfsimpl.v \
  Postorder.v FSetAVLplus.v IntvSets.v Decidableplus.v BoolEqual.v

# Parts common to the front-ends and the back-end (in common/)

COMMON=Errors.v AST.v Linking.v \
  Events.v Globalenvs.v Memdata.v Memtype.v Memory.v \
  Values.v Smallstep.v Behaviors.v Switch.v Determinism.v Unityping.v \
  Separation.v Builtins0.v Builtins1.v Builtins.v

# Back-end modules (in backend/, $(ARCH)/)

BACKEND=\
  Cminor.v Cminortyping.v Op.v CminorSel.v \
  SelectOp.v SelectDiv.v SplitLong.v SelectLong.v Selection.v \
  SelectOpproof.v SelectDivproof.v SplitLongproof.v \
  SelectLongproof.v Selectionproof.v \
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

# Parser

PARSER=Cabs.v Parser.v

# MenhirLib

ifeq ($(LIBRARY_MENHIRLIB),local)
MENHIRLIB=Alphabet.v Automaton.v Grammar.v Interpreter_complete.v \
  Interpreter_correct.v Interpreter.v Main.v Validator_complete.v \
  Validator_safe.v Validator_classes.v
else
MENHIRLIB=
endif

# Putting everything together (in driver/)

DRIVER=Compopts.v Compiler.v Complements.v

# Library for .v files generated by clightgen

ifeq ($(CLIGHTGEN),true)
EXPORTLIB=Ctypesdefs.v Clightdefs.v Csyntaxdefs.v
else
EXPORTLIB=
endif

# All source files

FILES=$(VLIB) $(COMMON) $(BACKEND) $(CFRONTEND) $(DRIVER) $(FLOCQ) \
  $(MENHIRLIB) $(PARSER) $(EXPORTLIB)

# Generated source files

GENERATED=\
  $(ARCH)/ConstpropOp.v $(ARCH)/SelectOp.v $(ARCH)/SelectLong.v \
  backend/SelectDiv.v backend/SplitLong.v \
  cparser/Parser.v

all:
	@test -f .depend || $(MAKE) depend
	$(MAKE) proof
	$(MAKE) extraction
	$(MAKE) ccomp
ifeq ($(HAS_RUNTIME_LIB),true)
	$(MAKE) runtime
endif
ifeq ($(CLIGHTGEN),true)
	$(MAKE) clightgen
endif
ifeq ($(INSTALL_COQDEV),true)
	$(MAKE) compcert.config
endif

proof: $(FILES:.v=.vo)

# Turn off some warnings for Flocq and Menhirlib
# These warnings can only be addressed upstream

flocq/%.vo: COQCOPTS+=-w -deprecated-syntactic-definition
MenhirLib/%.vo: COQCOPTS+=-w -deprecated-syntactic-definition

extraction: extraction/STAMP

extraction/STAMP: $(FILES:.v=.vo) extraction/extraction.v $(ARCH)/extractionMachdep.v
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/extraction.v
	@if grep 'AXIOM TO BE REALIZED' extraction/*.ml; then \
            echo "An error occured during extraction to OCaml code."; \
            echo "Check the versions of Flocq and MenhirLib used."; \
            exit 2; \
         fi
	touch extraction/STAMP

.depend.extr: extraction/STAMP tools/modorder driver/Version.ml
	$(MAKE) -f Makefile.extr depend

ccomp: .depend.extr compcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr ccomp
ccomp.byte: .depend.extr compcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr ccomp.byte

clightgen: .depend.extr compcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr clightgen
clightgen.byte: .depend.extr compcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr clightgen.byte

runtime:
	$(MAKE) -C runtime

FORCE:

.PHONY: proof extraction runtime FORCE

documentation: $(FILES)
	mkdir -p doc/html
	rm -f doc/html/*.html
	coq2html -d doc/html/ -base compcert -short-names doc/*.glob \
          $(filter-out doc/coq2html cparser/Parser.v, $^)

tools/ndfun: tools/ndfun.ml
ifeq ($(OCAML_NATIVE_COMP),true)
	ocamlopt -o tools/ndfun -I +str str.cmxa tools/ndfun.ml
else
	ocamlc -o tools/ndfun -I +str str.cma tools/ndfun.ml
endif

tools/modorder: tools/modorder.ml
ifeq ($(OCAML_NATIVE_COMP),true)
	ocamlopt -o tools/modorder -I +str str.cmxa tools/modorder.ml
else
	ocamlc -o tools/modorder -I +str str.cma tools/modorder.ml
endif

latexdoc:
	cd doc; $(COQDOC) --latex -o doc/doc.tex -g $(FILES)

%.vo: %.v
	@rm -f doc/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v
	@$(PROFILE_ZIP)

%.v: %.vp tools/ndfun
	@rm -f $*.v
	@echo "Preprocessing $*.vp"
	@tools/ndfun $*.vp > $*.v || { rm -f $*.v; exit 2; }
	@chmod a-w $*.v

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
         echo "endianness=$(ENDIANNESS)"; \
         echo "system=$(SYSTEM)"; \
         echo "has_runtime_lib=$(HAS_RUNTIME_LIB)"; \
         echo "has_standard_headers=$(HAS_STANDARD_HEADERS)"; \
         echo "asm_supports_cfi=$(ASM_SUPPORTS_CFI)"; \
	 echo "response_file_style=$(RESPONSEFILE)";) \
        > compcert.ini

compcert.config: Makefile.config
	(echo "# CompCert configuration parameters"; \
        echo "COMPCERT_ARCH=$(ARCH)"; \
        echo "COMPCERT_MODEL=$(MODEL)"; \
        echo "COMPCERT_ABI=$(ABI)"; \
        echo "COMPCERT_ENDIANNESS=$(ENDIANNESS)"; \
        echo "COMPCERT_BITSIZE=$(BITSIZE)"; \
        echo "COMPCERT_SYSTEM=$(SYSTEM)"; \
        echo "COMPCERT_VERSION=$(BUILDVERSION)"; \
        echo "COMPCERT_BUILDNR=$(BUILDNR)"; \
        echo "COMPCERT_TAG=$(TAG)"; \
        echo "COMPCERT_BRANCH=$(BRANCH)" \
        ) > compcert.config

driver/Version.ml: VERSION
	(echo 'let version = "$(BUILDVERSION)"'; \
         echo 'let buildnr = "$(BUILDNR)"'; \
         echo 'let tag = "$(TAG)"'; \
         echo 'let branch = "$(BRANCH)"') > driver/Version.ml

cparser/Parser.v: cparser/Parser.vy
	@rm -f $@
	$(MENHIR) --coq --coq-no-version-check cparser/Parser.vy
	@chmod a-w $@

depend: $(GENERATED) depend1

depend1: $(FILES) export/Clightdefs.v
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend

install:
	install -d $(DESTDIR)$(BINDIR)
	install -m 0755 ./ccomp $(DESTDIR)$(BINDIR)
	install -d $(DESTDIR)$(SHAREDIR)
	install -m 0644 ./compcert.ini $(DESTDIR)$(SHAREDIR)
	install -d $(DESTDIR)$(MANDIR)/man1
	install -m 0644 ./doc/ccomp.1 $(DESTDIR)$(MANDIR)/man1
	$(MAKE) -C runtime install
ifeq ($(CLIGHTGEN),true)
	install -m 0755 ./clightgen $(DESTDIR)$(BINDIR)
endif
ifeq ($(INSTALL_COQDEV),true)
	install -d $(DESTDIR)$(COQDEVDIR)
	for d in $(DIRS); do \
          set -e; \
          install -d $(DESTDIR)$(COQDEVDIR)/$$d; \
          install -m 0644 $$d/*.vo $(DESTDIR)$(COQDEVDIR)/$$d/; \
          if test -d $$d/.coq-native; then \
            install -d $(DESTDIR)$(COQDEVDIR)/$$d/.coq-native; \
            install -m 0644 $$d/.coq-native/* $(DESTDIR)$(COQDEVDIR)/$$d/.coq-native/; \
          fi \
	done
	install -m 0644 ./VERSION $(DESTDIR)$(COQDEVDIR)
	install -m 0644 ./compcert.config $(DESTDIR)$(COQDEVDIR)
	@(echo "To use, pass the following to coq_makefile or add the following to _CoqProject:"; echo "-R $(COQDEVDIR) compcert") > $(DESTDIR)$(COQDEVDIR)/README
endif


clean:
	rm -f $(patsubst %, %/*.vo*, $(DIRS))
	rm -f $(patsubst %, %/.*.aux, $(DIRS))
	rm -rf $(patsubst %, %/.coq-native, $(DIRS))
	rm -rf doc/html doc/*.glob
	rm -f driver/Version.ml
	rm -f compcert.ini compcert.config
	rm -f extraction/STAMP extraction/*.ml extraction/*.mli .depend.extr
	rm -f tools/ndfun tools/modorder tools/*.cm? tools/*.o
	rm -f $(GENERATED) .depend
	rm -f .lia.cache
	$(MAKE) -f Makefile.extr clean
	$(MAKE) -C runtime clean

distclean:
	$(MAKE) clean
	rm -f Makefile.config

check-admitted: $(FILES)
	@if grep -w 'admit\|Admitted\|ADMITTED' $^; \
         then exit 2; else echo "Nothing admitted."; fi

check-leftovers: $(FILES)
	@if grep -w '^Check\|^Print\|^Search' $^; \
         then exit 2; else echo "No leftover interactive commands."; fi

check-proof: $(FILES)
	$(COQCHK) compcert.driver.Complements

print-includes:
	@echo $(COQINCLUDES)

CoqProject:
	@echo $(COQINCLUDES) > _CoqProject

-include .depend

FORCE:
