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

include ../Makefile.config

DIRS=lib common $(ARCH)/$(VARIANT) $(ARCH) backend cfrontend driver

COQINCL=$(patsubst %,-I ../%,$(DIRS))
COQEXEC=coqtop $(COQINCL) -batch -load-vernac-source

all: Configuration.ml extraction

extraction:
	rm -f [:lower:]*.mli [:lower:]*.ml
	$(COQEXEC) extraction.v
	@echo "Fixing file names..."
	@mv list.ml CoqList.ml
	@mv list.mli CoqList.mli
	@mv string.ml CoqString.ml
	@mv string.mli CoqString.mli
	@mv int.ml CoqInt.ml
	@mv int.mli CoqInt.mli
	@echo "Conversion List -> CoqList, String -> CoqString, Int -> CoqInt..."
	@./convert *.mli *.ml
	@echo "Patching files..."
	@for i in *.patch; do patch < $$i; done

Configuration.ml: ../Makefile.config
	(echo 'let stdlib_path = "$(LIBDIR)"'; \
         echo 'let prepro = "$(CPREPRO)"'; \
         echo 'let asm = "$(CASM)"'; \
         echo 'let linker = "$(CLINKER)"'; \
         echo 'let arch = "$(ARCH)"'; \
         echo 'let variant = "$(VARIANT)"') \
        > Configuration.ml

clean:
	rm -f *.mli *.ml
