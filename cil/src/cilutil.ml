(*
 *
 * Copyright (c) 2001-2002, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
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

(* Keep here the globally-visible flags *)
let doCheck= ref false   (* Whether to check CIL *)

let logCalls = ref false (* Whether to produce a log with all the function 
                          * calls made *)
let logWrites = ref false (* Whether to produce a log with all the mem 
                          * writes made *)
let doPartial = ref false (* Whether to do partial evaluation and constant 
                          * folding *)                          
let doSimpleMem = ref false (* reduce complex memory expressions so that
                          * they contain at most one lval *) 
let doOneRet = ref false (* make a functions have at most one 'return' *)
let doStackGuard = ref false (* instrument function calls and returns to
maintain a separate stack for return addresses *)
let doHeapify = ref false (* move stack-allocated arrays to the heap *)
let makeCFG = ref false (* turn the input CIL file into something more like
                          * a CFG *)
let printStats = ref false

(* when 'sliceGlobal' is set, then when 'rmtmps' runs, only globals*)
(* marked with #pragma cilnoremove(whatever) are kept; when used with *)
(* cilly.asm.exe, the effect is to slice the input on the noremove symbols *)
let sliceGlobal = ref false


let printStages = ref false


let doCxxPP = ref false

let libDir = ref ""

let dumpFCG = ref false
let testcil = ref ""

