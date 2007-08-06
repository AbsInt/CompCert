include ../Makefile.config

FILES=\
  Datatypes.ml Logic.ml Wf.ml Peano.ml Specif.ml Compare_dec.ml EqNat.ml \
  Bool.ml CList.ml Sumbool.ml Setoid.ml BinPos.ml BinNat.ml BinInt.ml \
  ZArith_dec.ml Zeven.ml Zmax.ml Zmisc.ml Zbool.ml Zpower.ml Zdiv.ml \
  Ascii.ml CString.ml \
  OrderedType.ml FSetInterface.ml FSetFacts.ml FSetList.ml \
  CInt.ml FSetAVL.ml \
  Coqlib.ml Maps.ml Ordered.ml Errors.ml AST.ml Iteration.ml Integers.ml \
  ../caml/Camlcoq.ml ../caml/Floataux.ml Floats.ml Parmov.ml Values.ml \
  Mem.ml Globalenvs.ml \
  Csyntax.ml Ctyping.ml Cminor.ml Csharpminor.ml Cshmgen.ml \
  Cminorgen.ml \
  Op.ml CminorSel.ml \
  Selection.ml \
  Registers.ml RTL.ml \
  Switch.ml ../caml/RTLgenaux.ml RTLgen.ml \
  Locations.ml Conventions.ml \
  ../caml/RTLtypingaux.ml RTLtyping.ml \
  Lattice.ml Kildall.ml \
  Constprop.ml CSE.ml \
  LTL.ml LTLin.ml \
  InterfGraph.ml ../caml/Coloringaux.ml Coloring.ml \
  Allocation.ml  \
  Tunneling.ml Linear.ml Linearize.ml \
  Parallelmove.ml Reload.ml \
  Mach.ml Bounds.ml Stacking.ml \
  PPC.ml PPCgen.ml \
  Main.ml \
  ../caml/Cil2Csyntax.ml \
  ../caml/CMparser.ml ../caml/CMlexer.ml ../caml/CMtypecheck.ml \
  ../caml/PrintCsyntax.ml ../caml/PrintPPC.ml \
  ../caml/Configuration.ml ../caml/Driver.ml

EXTRACTEDFILES:=$(filter-out ../caml/%, $(FILES))
GENFILES:=$(EXTRACTEDFILES) $(EXTRACTEDFILES:.ml=.mli)

CAMLINCL=-I ../caml -I ../cil/obj/$(ARCHOS)
OCAMLC=ocamlc -g $(CAMLINCL)
OCAMLOPT=ocamlopt $(CAMLINCL)
OCAMLDEP=ocamldep $(CAMLINCL)
OCAMLLIBS=unix.cma str.cma cil.cma

COQINCL=-I ../lib -I ../common -I ../backend -I ../cfrontend
COQEXEC=coqtop $(COQINCL) -batch -load-vernac-source

executables: ../ccomp ../ccomp.byt

../ccomp.byt: $(FILES:.ml=.cmo)
	$(OCAMLC) -o ../ccomp.byt $(OCAMLLIBS) $(FILES:.ml=.cmo)
clean::
	rm -f ../ccomp.byt

../ccomp: $(FILES:.ml=.cmx)
	$(OCAMLOPT) -o ../ccomp $(OCAMLLIBS:.cma=.cmxa) $(FILES:.ml=.cmx)
clean::
	rm -f ../ccomp

extraction:
	@rm -f $(GENFILES)
	$(COQEXEC) extraction.v
	@echo "Fixing file names..."
	@mv list.ml CList.ml
	@mv list.mli CList.mli
	@mv string.ml CString.ml
	@mv string.mli CString.mli
	@mv int.ml CInt.ml
	@mv int.mli CInt.mli
	@for i in $(GENFILES); do \
          j=`./uncapitalize $$i`; \
          test -f $$i || (test -f $$j && mv $$j $$i); \
         done
	@echo "Conversion List -> CList, String -> CString, Int -> CInt..."
	@./convert $(GENFILES)
	@echo "Patching files..."
	@for i in *.patch; do patch < $$i; done

../caml/CMparser.ml ../caml/CMparser.mli: ../caml/CMparser.mly
	ocamlyacc -v ../caml/CMparser.mly

beforedepend:: ../caml/CMparser.ml ../caml/CMparser.mli
clean::
	rm -f ../caml/CMparser.ml ../caml/CMparser.mli ../caml/CMparser.output

../caml/CMlexer.ml: ../caml/CMlexer.mll
	ocamllex ../caml/CMlexer.mll

beforedepend:: ../caml/CMlexer.ml
clean::
	rm -f ../caml/CMlexer.ml

../caml/Configuration.ml: ../Makefile.config
	echo 'let stdlib_path = "$(LIBDIR)"' > ../caml/Configuration.ml

beforedepend:: ../caml/Configuration.ml
clean::
	rm -f ../caml/Configuration.ml

.SUFFIXES: .ml .mli .cmo .cmi .cmx

.mli.cmi:
	$(OCAMLC) -c $*.mli
.ml.cmo:
	$(OCAMLC) -c $*.ml
.ml.cmx:
	$(OCAMLOPT) -c $*.ml

clean::
	rm -f $(GENFILES)
	rm -f *.cm? *.o
	cd ../caml && rm -f *.cm? *.o

depend: beforedepend
	$(OCAMLDEP) ../caml/*.mli ../caml/*.ml *.mli *.ml > .depend

install:
	install -d $(BINDIR)
	install ../ccomp ../ccomp.byt $(BINDIR)

include .depend


