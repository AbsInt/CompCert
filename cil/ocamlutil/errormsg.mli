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
(** Utility functions for error-reporting *)

(** A channel for printing log messages *)
val logChannel : out_channel ref

(** If set then print debugging info *)
val debugFlag  : bool ref               

val verboseFlag : bool ref


(** Set to true if you want to see all warnings. *)
val warnFlag: bool ref

(** Error reporting functions raise this exception *)
exception Error


   (* Error reporting. All of these functions take same arguments as a 
    * Pretty.eprintf. They set the hadErrors flag, but do not raise an 
    * exception. Their return type is unit.
    *)

(** Prints an error message of the form [Error: ...]. 
    Use in conjunction with s, for example: [E.s (E.error ... )]. *)
val error:         ('a,unit,Pretty.doc,unit) format4 -> 'a

(** Similar to [error] except that its output has the form [Bug: ...] *)
val bug:           ('a,unit,Pretty.doc,unit) format4 -> 'a

(** Similar to [error] except that its output has the form [Unimplemented: ...] *)
val unimp:         ('a,unit,Pretty.doc,unit) format4 -> 'a

(** Stop the execution by raising an Error. *)
val s:             'a -> 'b

(** This is set whenever one of the above error functions are called. It must
    be cleared manually *)
val hadErrors: bool ref  

(** Like {!Errormsg.error} but does not raise the {!Errormsg.Error} 
 * exception. Return type is unit. *)
val warn:    ('a,unit,Pretty.doc,unit) format4 -> 'a

(** Like {!Errormsg.warn} but optional. Printed only if the 
 * {!Errormsg.warnFlag} is set *)
val warnOpt: ('a,unit,Pretty.doc,unit) format4 -> 'a

(** Print something to [logChannel] *)
val log:           ('a,unit,Pretty.doc,unit) format4 -> 'a

(** same as {!Errormsg.log} but do not wrap lines *)
val logg:          ('a,unit,Pretty.doc,unit) format4 -> 'a

   (* All of the error and warning reporting functions can also print a 
    * context. To register a context printing function use "pushContext". To 
    * remove the last registered one use "popContext". If one of the error 
    * reporting functions is called it will invoke all currently registered 
    * context reporting functions in the reverse order they were registered. *)

(** Do not actually print (i.e. print to /dev/null) *)
val null : ('a,unit,Pretty.doc,unit) format4 -> 'a

(** Registers a context printing function *)
val pushContext  : (unit -> Pretty.doc) -> unit

(** Removes the last registered context printing function *)
val popContext   : unit -> unit

(** Show the context stack to stderr *)
val showContext : unit -> unit

(** To ensure that the context is registered and removed properly, use the 
    function below *)
val withContext  : (unit -> Pretty.doc) -> ('a -> 'b) -> 'a -> 'b



val newline: unit -> unit  (* Call this function to announce a new line *)
val newHline: unit -> unit 

val getPosition: unit -> int * string * int (* Line number, file name, 
                                               current byte count in file *)
val getHPosition: unit -> int * string (** high-level position *)

val setHLine: int -> unit
val setHFile: string -> unit

val setCurrentLine: int -> unit
val setCurrentFile: string -> unit

(** Type for source-file locations *)
type location = 
    { file: string; (** The file name *)
      line: int;    (** The line number *)
      hfile: string; (** The high-level file name, or "" if not present *)
      hline: int;    (** The high-level line number, or 0 if not present *)
    } 

val d_loc: unit -> location -> Pretty.doc
val d_hloc: unit -> location -> Pretty.doc
    
val getLocation: unit -> location

val parse_error: string -> (* A message *) 
                 'a

(** An unknown location for use when you need one but you don't have one *)
val locUnknown: location


(** Records whether the stdin is open for reading the goal **)
val readingFromStdin: bool ref


(* Call this function to start parsing. useBasename is by default "true", 
 * meaning that the error information maintains only the basename. If the 
 * file name is - then it reads from stdin. *)
val startParsing:  ?useBasename:bool -> string -> 
  Lexing.lexbuf 

val startParsingFromString: ?file:string -> ?line:int -> string
                            -> Lexing.lexbuf

val finishParsing: unit -> unit (* Call this function to finish parsing and 
                                 * close the input channel *)


