#!/bin/sh
# Start coqide with the right -I options

exec coqide -I lib -I common -I backend -I cfrontend "$@"
