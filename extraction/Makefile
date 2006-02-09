FILES=\
  Datatypes.ml Logic.ml Wf.ml Peano.ml Specif.ml Compare_dec.ml \
  Bool.ml List.ml Sumbool.ml BinPos.ml BinNat.ml BinInt.ml \
  ZArith_dec.ml Zeven.ml Zmin.ml Zmisc.ml Zbool.ml Zpower.ml Zdiv.ml \
  FSetInterface.ml FSetBridge.ml FSetList.ml FSetAVL.ml \
  Coqlib.ml Maps.ml Sets.ml union_find.ml AST.ml Integers.ml \
  ../caml/Camlcoq.ml ../caml/Floataux.ml Floats.ml Values.ml \
  Mem.ml Globalenvs.ml \
  Op.ml Cminor.ml Cmconstr.ml \
  Csharpminor.ml Cminorgen.ml \
  Registers.ml RTL.ml \
  ../caml/RTLgenaux.ml RTLgen.ml \
  RTLtyping.ml \
  Lattice.ml Kildall.ml \
  Constprop.ml CSE.ml \
  Locations.ml Conventions.ml LTL.ml \
  Ordered.ml InterfGraph.ml ../caml/Coloringaux.ml Coloring.ml \
  Parallelmove.ml Allocation.ml  \
  Tunneling.ml Linear.ml Lineartyping.ml Linearize.ml \
  Mach.ml Stacking.ml \
  PPC.ml PPCgen.ml \
  Main.ml \
  ../caml/CMparser.ml ../caml/CMlexer.ml \
  ../caml/PrintPPC.ml ../caml/Main2.ml

EXTRACTEDFILES:=$(filter-out ../caml/%, $(FILES))
GENFILES:=$(EXTRACTEDFILES) $(EXTRACTEDFILES:.ml=.mli)

CAMLINCL=-I ../caml
OCAMLC=ocamlc -g $(CAMLINCL)
OCAMLOPT=ocamlopt $(CAMLINCL)
OCAMLDEP=ocamldep $(CAMLINCL)

COQINCL=-I ../lib -I ../backend
COQEXEC=coqtop $(COQINCL) -batch -load-vernac-source

../ccomp: $(FILES:.ml=.cmo)
	$(OCAMLC) -o ../ccomp $(FILES:.ml=.cmo)
clean::
	rm -f ../ccomp

../ccomp.opt: Pack.cmx
	$(OCAMLOPT) -o ../ccomp.opt Pack.cmx
clean::
	rm -f ../ccomp.opt

Pack.cmx: $(FILES:.ml=.cmx)
	$(OCAMLOPT) -pack -o Pack.cmx $(FILES:.ml=.cmx)

extraction:
	@rm -f $(GENFILES)
	$(COQEXEC) extraction.v
	@echo "Fixing file names..."
	@for i in $(GENFILES); do \
          j=`./uncapitalize $$i`; \
          test -f $$i || (test -f $$j && mv $$j $$i); \
         done
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

include .depend


