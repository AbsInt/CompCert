#!/bin/sh
# Start rocqide/coqide with the right options
# Use the Makefile to rebuild dependencies if needed
# Recompile the modified file after coqide editing

make -q ${1}o || {
  make -n ${1}o | grep -v "\\b${1}\\b" | \
  (while read cmd; do
    sh -c "$cmd" || exit 2
   done)
}

if command -v "${COQBIN}rocqide" >/dev/null 2>&1; then
  cmd="${COQBIN}rocqide"
elif command -v "${COQBIN}coqide" >/dev/null 2>&1; then
  cmd="${COQBIN}coqide"
else
  echo "Cannot find rocqide / coqide" >&2
  exit 2
fi

"$cmd" -async-proofs off $1 && make ${1}o
