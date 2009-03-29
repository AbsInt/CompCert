(*
 *
 * Copyright (c) 2001-2002, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 *  Ben Liblit          <liblit@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)

(* rmtmps.mli *)
(* remove unused things from cil files:               *)
(*   - local temporaries introduced but not used      *)
(*   - global declarations that are not used          *)
(*   - types that are not used                        *)
(*   - labels that are not used (gn)                  *)


(* Some clients may wish to augment or replace the standard strategy
 * for finding the initially reachable roots.  The optional
 * "isRoot" argument to Rmtmps.removeUnusedTemps grants this
 * flexibility.  If given, it should name a function which will return
 * true if a given global should be treated as a retained root.
 * 
 * Function Rmtmps.isDefaultRoot encapsulates the default root
 * collection, which consists of those global variables and functions
 * which are visible to the linker and runtime loader.  A client's
 * root filter can use this if the goal is to augment rather than
 * replace the standard logic.  Function Rmtmps.isExportedRoot is an
 * alternate name for this same function.
 * 
 * Function Rmtmps.isCompleteProgramRoot is an example of an alternate
 * root collection.  This function assumes that it is operating on a
 * complete program rather than just one object file.  It treats
 * "main()" as a root, as well as any function carrying the
 * "constructor" or "destructor" attribute.  All other globals are
 * candidates for removal, regardless of their linkage.
 * 
 * Note that certain CIL- and CCured-specific pragmas induce
 * additional global roots.  This functionality is always present, and
 * is not subject to replacement by "filterRoots".
 *)

type rootsFilter = Cil.global -> bool
val isDefaultRoot : rootsFilter
val isExportedRoot : rootsFilter
val isCompleteProgramRoot : rootsFilter

(* process a complete Cil file *)
val removeUnusedTemps: ?isRoot:rootsFilter -> Cil.file -> unit


val keepUnused: bool ref (* Set this to true to turn off this module *)
val rmUnusedInlines: bool ref (* Delete unused inline funcs in gcc mode? *)
