(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Util functions used for the expansion of built-ins and some 
   pseudo-instructions *)

open Asm
open AST
open Camlcoq
       
(* Buffering the expanded code *)

let current_code = ref ([]: instruction list)

let emit i = current_code := i :: !current_code

(* Generation of fresh labels *)
							  
let dummy_function = { fn_code = []; fn_sig = signature_main }
let current_function = ref dummy_function
let next_label = ref (None: label option)

let new_label () =
  let lbl =
    match !next_label with
    | Some l -> l
    | None ->
        (* on-demand computation of the next available label *)
        List.fold_left
          (fun next instr ->
            match instr with
            | Plabel l -> if P.lt l next then next else P.succ l
            | _ -> next)
          P.one (!current_function).fn_code
  in
    next_label := Some (P.succ lbl);
    lbl

		     
let set_current_function f =
  current_function := f; next_label := None; current_code := []

let get_current_function () =
  let c = List.rev !current_code in
  let fn = !current_function in
  set_current_function dummy_function;
  {fn with fn_code = c}
