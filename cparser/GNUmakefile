#######################################################################
#                                                                     #
#              The Compcert verified compiler                         #
#                                                                     #
#        François Pottier, INRIA Paris-Rocquencourt                   #
#                                                                     #
#  Copyright Institut National de Recherche en Informatique et en     #
#  Automatique.  All rights reserved.  This file is distributed       #
#  under the terms of the INRIA Non-Commercial License Agreement.     #
#                                                                     #
#######################################################################

# This is a development Makefile.
# It is meant to be used by developers who wish to modify the pre_parser.

# A collection of erroneous input sentences (and accompanying error messages)
# for the pre_parser is stored in the file handcrafted.messages.

# After a modification to the pre_parser, one must ensure that this collection of
# erroneous input sentences remains correct, irredundant, and complete. By this,
# we mean:
# - every input sentence in the collection leads to an error (on its last token);
# - every state where an error can occur is reached by some input sentence in the
#   collection;
# - every state where an error can occur is reached by at most one input sentence
#   in the collection.

# These properties are checked by [make correct] and [make complete] below.
# [make correct] is cheap and is performed automatically when CompCert is
# compiled. [make complete] is expensive and must be called explicitly.

# After a modification to the pre_parser, one should also reconstruct the
# auto-generated comments in handcrafted.messages. This is done by calling
# [make update].

# Finally, after a modification to the pre_parser, one should ensure that every
# error message remains meaningful. Indeed, an error message should not be
# specific of the example sentence that causes this error; it should reflect all
# possible sentences that cause an error in this state. One must look at the
# description of the error state (which is part of the auto-generated comments)
# and decide, based on this description, whether the error message seems
# appropriate.

# If you wish to play with one input sentence and see how the automaton behaves,
# use [make interpret] or [make interpret_error].

# If you wish to translate the database of erroneous input sentences to concrete
# syntax, so as to be able to run a C compiler on these sentences, use [make
# concrete].

# ------------------------------------------------------------------------------

# Make sure we use the same Menhir setup as the main CompCert Makefiles.

include ../Makefile.menhir

# Be more verbose about the automaton.

FLAGS    := $(MENHIR_FLAGS) -v -la 2

# So, here is our basic Menhir command.

COMMAND  := $(MENHIR) $(MENHIR_MODE) pre_parser.mly $(FLAGS)

# And this is the database of messages.

DATABASE := handcrafted.messages

# We use (GNU) cut when de-lexing examples sentences.

CUT       = $(shell if command -v gcut >/dev/null ; then echo gcut ; else echo cut ; fi)

# ------------------------------------------------------------------------------

# Working with the error message database.

.PHONY: nothing correct complete update

nothing:
	@ echo "If you wish to compile CompCert, please run \"make\" one level up."
	@ echo "If you wish to work on the pre-parser, please read GNUmakefile."

# Checking correctness and irredundancy is done via --compile-errors.
# This entry is also called from [Makefile.extr] to compile the message
# database down to OCaml code.
# This also produces a description of the automaton in pre_parser.automaton
# and a description of the conflicts (if any) in pre_parser.conflicts.
correct:
	@ $(COMMAND) --compile-errors $(DATABASE) > pre_parser_messages.ml && \
	    echo "OK. The set of erroneous inputs is correct and irredundant."

# Checking completeness is done by first generating a complete list of
# erroneous sentences (in pre_parser.messages), then comparing the two
# .messages files for inclusion.
complete:
# Re-generate the list of error messages. This takes time (about 25 seconds).
	@ $(COMMAND) --list-errors >pre_parser.messages
	@ echo "Number of error sentences that involve spurious reductions:"
	@ grep WARNING pre_parser.messages | wc -l
# Check $(DATABASE) for completeness.
# We assume pre_parser.messages is up-to-date.
	@ $(COMMAND) --compare-errors pre_parser.messages --compare-errors $(DATABASE) && \
	    echo "OK. The set of erroneous inputs is complete."

update:
# Update the auto-comments in $(DATABASE).
	@ mv -f $(DATABASE) $(DATABASE).bak
	@ if ! $(COMMAND) --update-errors $(DATABASE).bak > $(DATABASE) ; then \
	  cp $(DATABASE).bak $(DATABASE) ; \
	fi
	@ echo "The auto-generated comments in $(DATABASE) have been re-generated."

# ------------------------------------------------------------------------------

# Trying out an input sentence.

# [make interpret] waits for you to interactively type an input sentence,
# in symbolic syntax (e.g. ALIGNAS LPAREN TYPEDEF_NAME INT). It runs the
# automaton on this sentence in --trace mode.

# [make interpret_error] is analogous, but expects the sentence to cause
# an error at the last token, and displays in what state the error takes
# place.

.PHONY: interpret interpret_error

interpret:
# Interpret one sentence (interactive).
	@ $(COMMAND) --trace --interpret

interpret_error:
# Interpret one error sentence (interactive).
	@ $(COMMAND) --interpret-error

# ------------------------------------------------------------------------------

# Translating the database of erroneous input sentences to concrete syntax.

# [make concrete] destroys and re-creates the C files in tests/generated/.
# Once this is done, run [make -C tests/generated] to submit these C files
# to CompCert, clang and gcc.

.PHONY: concrete

# First, we translate $(DATABASE) to a text file which contains just the
# erroneous input sentences, nothing else (no comments, no blank lines).
%.messages.raw: %.messages
	@ $(COMMAND) --echo-errors $< > $@

# We compile deLexer.ml to native code, because running it as an ocaml script
# is way too slow. This little utility translates symbolic tokens to their
# concrete C syntax, e.g., EQ is translated to = and so on.
deLexer: deLexer.ml
	@ ocamlopt -o $@ str.cmxa $<

concrete: $(DATABASE).raw deLexer
# Destroy the C files in tests/generated.
	@ rm -f tests/generated/*.c
# Read $(DATABASE).raw, line by line.
# For each sentence, create a new C file.
# A sentence takes the form "<start symbol>: SYMBOLS...".
# We cut the start symbol away,
# and translate the rest to concrete C syntax using the deLexer.
# We declare a type name "t", which the de-lexer uses as a type name.
	@ f=0 ; \
	while read -r line ; do \
	  filename=`printf "tests/generated/parser_%03d.c" $$f` ; \
	  rm -f $$filename ; \
	  echo "typedef int t;" >> $$filename ; \
	  echo "$$line" \
	    | $(CUT) -f 2- -d " " \
	    | ./deLexer \
	    >> $$filename ; \
	  f=$$((f+1)) ; \
	done < $<

# ------------------------------------------------------------------------------

# Cleaning up.

clean:
	rm -f pre_parser.automaton
	rm -f pre_parser.conflicts
	rm -f pre_parser.messages
	rm -f $(DATABASE).raw $(DATABASE).bak
	rm -f deLexer
