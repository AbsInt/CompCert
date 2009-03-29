
module E = Errormsg

(* We provide here a pointer to a function. It will be set by the lexer and 
 * used by the parser. In Ocaml lexers depend on parsers, so we we have put 
 * such functions in a separate module. *)
let add_identifier: (string -> unit) ref = 
  ref (fun _ -> E.s (E.bug "You called an uninitialized add_identifier")) 

let add_type: (string -> unit) ref = 
  ref (fun _ -> E.s (E.bug "You called an uninitialized add_type")) 

let push_context: (unit -> unit) ref = 
  ref (fun _ -> E.s (E.bug "You called an uninitialized push_context")) 

let pop_context: (unit -> unit) ref = 
  ref (fun _ -> E.s (E.bug "You called an uninitialized pop_context")) 


(* Keep here the current pattern for formatparse *)
let currentPattern = ref ""

