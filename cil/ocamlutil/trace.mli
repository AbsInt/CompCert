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

(* Trace module
 * Scott McPeak, 5/4/00
 *
 * The idea is to pepper the source with debugging printfs,
 * and be able to select which ones to actually display at
 * runtime.
 *
 * It is built on top of the Pretty module for printing data
 * structures.
 *
 * To a first approximation, this is needed to compensate for
 * the lack of a debugger that does what I want...
 *)


(* this is the list of tags (usually subsystem names) for which
 * trace output will appear *)
val traceSubsystems : string list ref

(* interface to add a new subsystem to trace (slightly more
 * convenient than direclty changing 'tracingSubsystems') *)
val traceAddSys : string -> unit

(* query whether a particular subsystem is being traced *)
val traceActive : string -> bool
   
(* add several systems, separated by commas *)
val traceAddMulti : string -> unit


(* current indentation level for tracing *)
val traceIndentLevel : int ref

(* bump up or down the indentation level, if the given subsys
 * is being traced *)
val traceIndent : string -> unit
val traceOutdent : string -> unit


(* this is the trace function; its first argument is a string
 * tag, and second argument is a 'doc' (which is what 'dprintf'
 * returns).
 *
 * so a sample usage might be
 *   (trace "mysubsys" (dprintf "something neat happened %d times\n" counter))
 *)
val trace : string -> Pretty.doc -> unit


(* special flavors that indent/outdent as well.  the indent version
 * indents *after* printing, while the outdent version outdents
 * *before* printing.  thus, a sequence like
 *
 *   (tracei "foo" (dprintf "beginning razzle-dazzle\n"))
 *     ..razzle..
 *     ..dazzle..
 *   (traceu "foo" (dprintf "done with razzle-dazzle\n"))
 *
 * will do the right thing
 *
 * update -- I changed my mind!  I decided I prefer it like this
 *   %%% sys: (myfunc args)
 *     %%% ...inner stuff...
 *     %%% sys: myfunc returning 56
 *
 * so now they both print before in/outdenting
 *)
val tracei : string -> Pretty.doc -> unit
val traceu : string -> Pretty.doc -> unit
