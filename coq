#!/bin/sh
# Start coqide with the right -I options

ARCH=`sed -n -e 's/^ARCH=//p' Makefile.config`
VARIANT=`sed -n -e 's/^VARIANT=//p' Makefile.config`

coqide -I lib -I common -I $ARCH/$VARIANT -I $ARCH -I backend -I cfrontend $1 && make ${1}o
