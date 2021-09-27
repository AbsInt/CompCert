# The clightgen tool

## Overview

`clightgen` is an experimental tool that transforms C source files
into Clight abstract syntax or Csyntax abstract syntax, pretty-printed
in Coq format inside `.v` files.

These generated `.v` files can be loaded in a Coq session for
interactive verification, for example using the
[VST](https://vst.cs.princeton.edu/) toolchain.

## How to build

Configure CompCert with `./configure -clightgen`.

Build CompCert as usual.

The `clightgen` tool will be installed in the same directory as the
`ccomp` compiler.

## Usage
```
   clightgen [options] <C source files>
```
For each source file `src.c`, its Clight abstract syntax is generated
in `src.v`.

Run `clightgen -help` for a list of options.

Several options are shared with the `ccomp` compiler; 
see [user's manual](http://compcert.inria.fr/man/manual003.html)
for full documentation).
