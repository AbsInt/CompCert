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

(* Trace module implementation
 * see trace.mli
 *)

open Pretty;;


(* --------- traceSubsystems --------- *)
(* this is the list of tags (usually subsystem names) for which
 * trace output will appear *)
let traceSubsystems : string list ref = ref [];;


let traceAddSys (subsys : string) : unit =
  (* (ignore (printf "traceAddSys %s\n" subsys)); *)
  traceSubsystems := subsys :: !traceSubsystems
;;


let traceActive (subsys : string) : bool =
  (* (List.mem elt list) returns true if something in list equals ('=') elt *)
  (List.mem subsys !traceSubsystems)
;;


let rec parseString (str : string) (delim : char) : string list =
begin
  if (not (String.contains str delim)) then 
    if ((String.length str) = 0) then
      [] 
    else
      [str]

  else
    let d = ((String.index str delim) + 1) in
    if (d = 1) then
      (* leading delims are eaten *)
      (parseString (String.sub str d ((String.length str) - d)) delim)
    else
      (String.sub str 0 (d-1)) ::
        (parseString (String.sub str d ((String.length str) - d)) delim)
end;;

let traceAddMulti (systems : string) : unit =
begin
  let syslist = (parseString systems ',') in
  (List.iter traceAddSys syslist)
end;;



(* --------- traceIndent --------- *)
let traceIndentLevel : int ref = ref 0;;


let traceIndent (sys : string) : unit =
  if (traceActive sys) then
    traceIndentLevel := !traceIndentLevel + 2
;;

let traceOutdent (sys : string) : unit =
  if ((traceActive sys) &&
      (!traceIndentLevel >= 2)) then
    traceIndentLevel := !traceIndentLevel - 2
;;


(* --------- trace --------- *)
(* return a tag to prepend to a trace output
 * e.g. "  %%% mysys: "
 *)
let traceTag (sys : string) : Pretty.doc =
  (* return string of 'i' spaces *)
  let rec ind (i : int) : string =
    if (i <= 0) then
      ""
    else
      " " ^ (ind (i-1))

  in
  (text ((ind !traceIndentLevel) ^ "%%% " ^ sys ^ ": "))
;;


(* this is the trace function; its first argument is a string
 * tag, and subsequent arguments are like printf formatting
 * strings ("%a" and whatnot) *)
let trace
    (subsys : string)                   (* subsystem identifier for enabling tracing *)
    (d : Pretty.doc)                    (* something made by 'dprintf' *)
    : unit =                            (* no return value *)
  (* (ignore (printf "trace %s\n" subsys)); *)

  (* see if the subsystem's tracing is turned on *)
  if (traceActive subsys) then
    begin
      (fprint stderr 80			(* print it *)
         ((traceTag subsys) ++ d));	(* with prepended subsys tag *)
      (* mb: flush after every message; useful if the program hangs in an
	 infinite loop... *)
      (flush stderr)
    end
  else
    ()			                         (* eat it *)
;;


let tracei (sys : string) (d : Pretty.doc) : unit =
  (* trace before indent *)
  (trace sys d);
  (traceIndent sys)
;;

let traceu (sys : string) (d : Pretty.doc) : unit =
  (* trace after outdent *)
  (* no -- I changed my mind -- I want trace *then* outdent *)
  (trace sys d);
  (traceOutdent sys)
;;




(* -------------------------- trash --------------------- *)
(* TRASH START

(* sm: more experimenting *)
(trace "no" (dprintf "no %d\n" 5));
(trace "yes" (dprintf "yes %d\n" 6));
(trace "maybe" (dprintf "maybe %d\n" 7));

TRASH END *)
