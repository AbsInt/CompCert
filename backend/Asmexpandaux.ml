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

let get_current_function_args () =
  (!current_function).fn_sig.sig_args

let is_current_function_variadic () =
  (!current_function).fn_sig.sig_cc.cc_vararg

let get_current_function_sig () =
  (!current_function).fn_sig

let get_current_function () =
  let c = List.rev !current_code in
  let fn = !current_function in
  set_current_function dummy_function;
  {fn with fn_code = c}

(* Expand function for debug information *)

let expand_scope id lbl oldscopes newscopes =
  let opening = List.filter (fun a -> not (List.mem a oldscopes)) newscopes
  and closing = List.filter (fun a -> not (List.mem a newscopes)) oldscopes in
  List.iter (fun i -> Debug.open_scope id i lbl) opening;
  List.iter (fun i -> Debug.close_scope id i lbl) closing

let translate_annot sp preg_to_dwarf annot =
  let rec aux = function
    | BA x -> Some (sp,BA (preg_to_dwarf x))
    | BA_int _
    | BA_long _
    | BA_float _
    | BA_single _
    | BA_loadglobal _
    | BA_addrglobal _
    | BA_loadstack _
    | BA_addptr _ -> None
    | BA_addrstack ofs -> Some (sp,BA_addrstack ofs)
    | BA_splitlong (hi,lo) ->
        begin
          match (aux hi,aux lo) with
          | Some (_,hi) ,Some (_,lo) -> Some (sp,BA_splitlong (hi,lo))
          | _,_ -> None
        end in
  (match annot with
  | [] -> None
  | a::_ -> aux a)

let builtin_nop =
  let signature ={sig_args = []; sig_res = None; sig_cc = cc_default} in
  let name = coqstring_of_camlstring "__builtin_nop" in
  Pbuiltin(EF_builtin(name,signature),[],BR_none)

let rec lbl_follows = function
  | Pbuiltin (EF_debug _, _, _):: rest ->
    lbl_follows rest
  | Plabel _ :: _ -> true
  | _ -> false

let expand_debug id sp preg simple l =
  let get_lbl = function
    | None ->
        let lbl = new_label () in
        emit (Plabel lbl);
        lbl
    | Some lbl -> lbl in
  let rec  aux lbl scopes = function
    | [] -> ()
    | (Pbuiltin(EF_debug (kind,txt,_x),args,_) as i)::rest ->
        let kind = (P.to_int kind) in
        begin
          match kind with
          | 1->
              emit i;aux lbl scopes rest
          | 2 ->
              aux  lbl scopes rest
          | 3 ->
             begin
               match translate_annot sp preg args with
               | Some a ->
                   let lbl = get_lbl lbl in
                   Debug.start_live_range (id,txt) lbl a;
                   aux (Some lbl) scopes rest
               | None ->  aux lbl scopes rest
             end
          | 4 ->
              let lbl = get_lbl lbl in
              Debug.end_live_range (id,txt) lbl;
              aux (Some lbl) scopes rest
          | 5 ->
              begin
                match translate_annot sp preg args with
                | Some a->
                    Debug.stack_variable (id,txt) a;
                    aux lbl scopes rest
                | _ ->  aux lbl scopes rest
              end
          | 6  ->
              let lbl = get_lbl lbl in
              let scopes' = List.map (function BA_int x -> Int32.to_int (camlint_of_coqint x) | _ -> assert false) args in
              expand_scope id lbl scopes scopes';
              aux (Some lbl) scopes' rest
          | _ ->
              aux None scopes rest
        end
    | (Pbuiltin(EF_annot (kind, _, _),_,_) as annot)::rest ->
      simple annot;
      if P.to_int kind = 2 && lbl_follows rest then
        simple builtin_nop;
      aux None scopes rest
    | (Plabel lbl)::rest -> simple (Plabel lbl); aux (Some lbl) scopes rest
    | i::rest -> simple i; aux None scopes rest in
  (* We need to move all closing debug annotations before the last real statement *)
  let rec move_debug acc bcc = function
    | (Pbuiltin(EF_debug (kind,_,_),_,_) as i)::rest ->
        let kind = (P.to_int kind) in
        if kind = 1 then
          move_debug acc (i::bcc) rest (* Do not move debug line *)
        else
          move_debug (i::acc) bcc rest (* Move the debug annotations forward *)
    | b::rest -> List.rev ((List.rev (b::bcc)@List.rev acc)@rest) (* We found the first non debug location *)
    | [] -> List.rev acc (* This actually can never happen *) in
  aux None [] (move_debug [] [] (List.rev l))

let expand_simple simple l =
  let rec aux = function
   | (Pbuiltin(EF_annot (kind, _, _),_,_) as annot)::rest ->
     simple annot;
     if P.to_int kind = 2 && lbl_follows rest then
       simple builtin_nop;
     aux rest
   | i::rest -> simple i; aux rest
   | [] -> () in
  aux l

let expand id sp preg simple l =
  if !Clflags.option_g then
    expand_debug id sp preg simple l
  else
    expand_simple simple l
