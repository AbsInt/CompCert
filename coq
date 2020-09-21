#!/bin/sh
# Start coqide with the right options
# Use the Makefile to rebuild dependencies if needed
# Recompile the modified file after coqide editing

make -q ${1}o || {
  make -n ${1}o | grep -v "\\b${1}\\b" | \
  (while read cmd; do
    sh -c "$cmd" || exit 2
   done)
}

"${COQBIN}coqide" -async-proofs off $1 && make ${1}o
