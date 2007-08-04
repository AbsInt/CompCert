#!/bin/sh
# Start coqide with the right -I options

coqide -I lib -I common -I backend -I cfrontend $1 && make ${1}o
