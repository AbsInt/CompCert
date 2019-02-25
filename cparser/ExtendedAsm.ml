(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Partial emulation of GCC's extended inline assembly (experimental). *)

(* The [transf_asm] function in this module takes a full GCC-style
   extended asm statement and puts it in the form supported by
   CompCert, namely:
   - 0 or 1 output of kind "r"
   - 0, 1 or several inputs of kind "r".
   Inputs and outputs of kind "m" (memory location) are emulated
   by taking the address of the operand and treating it as
   an input of kind "r".
   Inputs of kind "i" and "n" (integer immediates) are evaluated
   at compile-time and textually substituted in the asm template.

   Extended asm statements that do not fit the forms above are rejected
   with diagnostics. *)

open Printf
open Machine
open C
open Cutil
open Diagnostics

(* Renaming of labeled and numbered operands *)

module StringMap = Map.Make(String)

let name_of_label ?(modifier = "") lbl pos =
  match lbl with
  | None ->  (* numbered argument *)
      sprintf "%%%s%d" modifier pos
  | Some l -> (* named argument *)
      sprintf "%%%s[%s]" modifier l

let set_label_reg lbl pos pos' subst =
  StringMap.add (name_of_label lbl pos) (sprintf "%%%d" pos') subst

(* These are the modifiers used by GCC for ARM:
      %Rxxx is the most significant half of a register pair
      %Qxxx is the least significant half of a register pair.
   They are not documented, and it is unclear whether other GCC ports
   have this feature and with which syntax. *)

let set_label_regpair lbl pos pos' subst =
  StringMap.add (name_of_label ~modifier:"R" lbl pos) (sprintf "%%R%d" pos')
    (StringMap.add (name_of_label ~modifier:"Q" lbl pos) (sprintf "%%Q%d" pos')
       subst)

let set_label_mem lbl pos pos' subst =
  StringMap.add (name_of_label lbl pos)
                (CBuiltins.asm_mem_argument (sprintf "%%%d" pos'))
                subst

let set_label_const lbl pos n subst =
  StringMap.add (name_of_label lbl pos) (sprintf "%Ld" n) subst

(* Operands of 64-bit integer type get split into a pair of registers
   on 32-bit platforms *)

let is_reg_pair env ty =
  match unroll env ty with
  | TInt(ik, _) -> sizeof_ikind ik > !config.sizeof_intreg
  | _ -> false

(* Transform the input operands:
     - add "&" for inputs of kind "m"
     - evaluate constants for inputs of kind "i" and "n" *)

let re_valid_input = Str.regexp "[a-zA-Z]+$"

let rec transf_inputs loc env accu pos pos' subst = function
  | [] ->
      (List.rev accu, subst)
  | (lbl, cstr, e) :: inputs ->
      let valid = Str.string_match re_valid_input cstr 0 in
      if valid && String.contains cstr 'r' then
        if is_reg_pair env e.etyp then
          transf_inputs loc env (e :: accu) (pos + 1) (pos' + 1)
                      (set_label_regpair lbl pos pos' subst) inputs
        else
          transf_inputs loc env (e :: accu) (pos + 1) (pos' + 1)
                      (set_label_reg lbl pos pos' subst) inputs
      else
      if valid && String.contains cstr 'm' then
        transf_inputs loc env (eaddrof e :: accu) (pos + 1) (pos' + 1)
                    (set_label_mem lbl pos pos' subst) inputs
      else
      if valid && (String.contains cstr 'i'
                   || String.contains cstr 'n') then begin
        let n =
          match Ceval.integer_expr env e with
          | Some n -> n
          | None -> error loc "asm argument of kind '%s' is not a constant"
                           cstr;
                    0L in
        transf_inputs loc env accu (pos + 1) pos'
                      (set_label_const lbl pos n subst) inputs
      end else begin
        error loc "unsupported feature: asm argument of kind '%s'"
          cstr;
        transf_inputs loc env (e :: accu) (pos + 1) (pos' + 1)
                    (set_label_reg lbl pos pos' subst) inputs
      end

(* Transform the output operands:
     - outputs of kind "=m" become an input (equal to the address of the output)
*)

let re_valid_output = Str.regexp "=[a-zA-Z]+$"

let transf_outputs loc env = function
  | [] ->
      (None, [], StringMap.empty, 0, 0)
  | [(lbl, cstr, e)] ->
      let valid = Str.string_match re_valid_output cstr 0 in
      if valid && String.contains cstr 'r' then
        if is_reg_pair env e.etyp then
          (Some e, [], set_label_regpair lbl 0 0 StringMap.empty, 1, 1)
        else
          (Some e, [], set_label_reg lbl 0 0 StringMap.empty, 1, 1)
      else
      if valid && String.contains cstr 'm' then
        (None, [eaddrof e],
           set_label_mem lbl 0 0 StringMap.empty, 1, 1)
      else begin
        error loc "unsupported feature: asm result of kind '%s'"
          cstr;
        (None, [], set_label_reg lbl 0 0 StringMap.empty, 1, 1)
      end
  | outputs ->
      error loc "unsupported feature: asm statement with 2 or more outputs";
      (* Bind the outputs so that we don't get another error
         when substituting the text *)
      let rec bind_outputs pos subst = function
      | [] -> (None, [], subst, pos, pos)
      | (lbl, cstr, e) :: outputs ->
          bind_outputs (pos + 1) (set_label_reg lbl pos pos subst) outputs
      in bind_outputs 0 StringMap.empty outputs

(* Check the clobber list *)

let check_clobbers loc clob =
  List.iter
    (fun c ->
      if Machregsaux.register_by_name c <> None
      || Machregsaux.is_scratch_register c
      || c = "memory" || c = "cc" (* GCC does not accept MEMORY or CC *)
      then ()
      else error loc "unrecognized asm register clobber '%s'" c)
    clob

(* Renaming of the %nnn and %[ident] placeholders in the asm text *)

let re_asm_placeholder =
  Str.regexp "\\(%[QR]?\\([0-9]+\\|\\[[a-zA-Z_][a-zA-Z_0-9]*\\]\\)\\|%%\\)"

let rename_placeholders loc template subst =
  let rename p =
    if p = "%%" then p else
      try
        StringMap.find p subst
      with Not_found ->
        error loc "'%s' in asm text does not designate any operand" p;
        "%<error>"
  in
    Str.global_substitute re_asm_placeholder
      (fun txt -> rename (Str.matched_group 1 txt))
      template

(* All together *)

let transf_asm loc env template outputs inputs clobbers =
  let (outputs', inputs1, subst1, pos, pos') =
    transf_outputs loc env outputs in
  let (inputs', subst) =
    transf_inputs loc env inputs1 pos pos' subst1 inputs in
  check_clobbers loc clobbers;
  (rename_placeholders loc template subst, outputs', inputs')
