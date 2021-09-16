# The clightgen tool


## Overview
"clightgen" is an experimental tool that transforms C source files
into Clight abstract syntax, pretty-printed in Coq format in .v files.
These generated .v files can be loaded in a Coq session for
interactive verification, typically.


## How to build

Change to the top-level CompCert directory and issue
```
   make clightgen
```

## Usage
```
   clightgen [options] <C source files>
```
For each source file `src.c`, its Clight abstract syntax is generated
in `src.v`.

The options recognized are a subset of those of the CompCert compiler ccomp
(see [user's manual](http://compcert.inria.fr/man/manual003.html) for full documentation):
```
   -I<dir>     search <dir> for include files
   -D<symbol>  define preprocessor macro
   -U<symbol>  undefine preprocessor macro
   -Wp,<opts>  pass options to C preprocessor
   -f<feature> activate emulation of the given C feature
```
