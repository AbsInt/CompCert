#!/bin/sh
# Start coqide with the right -I options
# Use the Makefile to rebuild dependencies if needed
# Recompile the modified file after coqide editing

ARCH=`sed -n -e 's/^ARCH=//p' Makefile.config`
VARIANT=`sed -n -e 's/^VARIANT=//p' Makefile.config`

make -q ${1}o || {
  make -n ${1}o | grep -v "\\b${1}\\b" | \
  (while read cmd; do
    sh -c "$cmd" || exit 2
   done)
}

coqide -I lib -I common -I $ARCH/$VARIANT -I $ARCH -I backend -I cfrontend -I flocq -I flocq/Appli -I flocq/Calc -I flocq/Core -I flocq/Prop $1 \
&& make ${1}o
