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


(** {b An Interpreter for constructing CIL constructs} *)


(** Constructs an expression based on the program and the list of arguments. 
 * Each argument consists of a name followed by the actual data. This 
 * argument will be placed instead of occurrences of "%v:name" in the pattern 
 * (where the "v" is dependent on the type of the data). The parsing of the 
 * string is memoized. * Only the first expression is parsed. *)
val cExp: string -> (string * Cil.formatArg) list -> Cil.exp

(** Constructs an lval based on the program and the list of arguments. 
 * Only the first lvalue is parsed. 
 * The parsing of the string is memoized. *)
val cLval: string -> (string * Cil.formatArg) list -> Cil.lval

(** Constructs a type based on the program and the list of arguments. 
 * Only the first type is parsed. 
 * The parsing of the string is memoized. *)
val cType: string -> (string * Cil.formatArg) list -> Cil.typ


(** Constructs an instruction based on the program and the list of arguments. 
 * Only the first instruction is parsed. 
 * The parsing of the string is memoized. *)
val cInstr: string -> Cil.location -> 
                      (string * Cil.formatArg) list -> Cil.instr

(* Constructs a statement based on the program and the list of arguments. We 
 * also pass a function that can be used to make new varinfo's for the 
 * declared variables, and a location to be used for the statements. Only the 
 * first statement is parsed. The parsing of the string is memoized. *)
val cStmt: string -> 
           (string -> Cil.typ -> Cil.varinfo) -> 
           Cil.location -> (string * Cil.formatArg) list -> Cil.stmt

(** Constructs a list of statements *)
val cStmts: string -> 
            (string -> Cil.typ -> Cil.varinfo) -> 
            Cil.location -> (string * Cil.formatArg) list -> 
            Cil.stmt list

(** Deconstructs an expression based on the program. Produces an optional 
 * list of format arguments. The parsing of the string is memoized. *)
val dExp: string -> Cil.exp -> Cil.formatArg list option

(** Deconstructs an lval based on the program. Produces an optional 
 * list of format arguments. The parsing of the string is memoized. *)
val dLval: string -> Cil.lval -> Cil.formatArg list option


(** Deconstructs a type based on the program. Produces an optional list of 
 * format arguments. The parsing of the string is memoized. *)
val dType: string -> Cil.typ -> Cil.formatArg list option


(** Deconstructs an instruction based on the program. Produces an optional 
 * list of format arguments. The parsing of the string is memoized. *)
val dInstr: string -> Cil.instr -> Cil.formatArg list option


(** If set then will not memoize the parsed patterns *)
val noMemoize: bool ref

(** Just a testing function *)
val test: unit -> unit
