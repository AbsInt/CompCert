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

(** Pretty-printer for Cminor *)

open Format
open Camlcoq
open Datatypes
open BinPos
open Integers
open AST
open PrintAST
open Cminor

(* Precedences and associativity -- like those of C *)

type associativity = LtoR | RtoL | NA

let rec precedence = function
  | Evar _ -> (16, NA)
  | Econst _ -> (16, NA)
  | Eunop _ -> (15, RtoL)
  | Ebinop((Omul|Odiv|Odivu|Omod|Omodu|Omulf|Odivf), _, _) -> (13, LtoR)
  | Ebinop((Oadd|Osub|Oaddf|Osubf), _, _) -> (12, LtoR)
  | Ebinop((Oshl|Oshr|Oshru), _, _) -> (11, LtoR)
  | Ebinop((Ocmp _|Ocmpu _|Ocmpf _), _, _) -> (10, LtoR)
  | Ebinop(Oand, _, _) -> (8, LtoR)
  | Ebinop(Oxor, _, _) -> (7, LtoR)
  | Ebinop(Oor, _, _) -> (6, LtoR)
  | Eload _ -> (15, RtoL)
  | Econdition _ -> (3, RtoL)

(* Naming idents.  We assume idents are encoded as in Cminorgen. *)

let ident_name id =
  match id with
  | Coq_xO n -> extern_atom n
  | Coq_xI n -> Printf.sprintf "$%ld" (camlint_of_positive n)
  | Coq_xH -> "$0"

(* Naming operators *)

let name_of_unop = function
  | Ocast8unsigned -> "int8u"
  | Ocast8signed -> "int8s"
  | Ocast16unsigned -> "int16u"
  | Ocast16signed -> "int16s"
  | Onegint -> "-"
  | Oboolval -> "(_Bool)"
  | Onotbool -> "!"
  | Onotint -> "~"
  | Onegf -> "-f"
  | Oabsf -> "absf"
  | Osingleoffloat -> "float32"
  | Ointoffloat -> "intoffloat"
  | Ointuoffloat -> "intuoffloat"
  | Ofloatofint -> "floatofint"
  | Ofloatofintu -> "floatofintu"

let comparison_name = function
  | Ceq -> "=="
  | Cne -> "!="
  | Clt -> "<"
  | Cle -> "<="
  | Cgt -> ">"
  | Cge -> ">="

let name_of_binop = function
  | Oadd -> "+"
  | Osub -> "-"
  | Omul -> "*"
  | Odiv -> "/"
  | Odivu -> "/u"
  | Omod -> "%"
  | Omodu -> "%u"
  | Oand -> "&"
  | Oor -> "|"
  | Oxor -> "^"
  | Oshl -> "<<"
  | Oshr -> ">>"
  | Oshru -> ">>u"
  | Oaddf -> "+f"
  | Osubf -> "-f"
  | Omulf -> "*f"
  | Odivf -> "/f"
  | Ocmp c -> comparison_name c
  | Ocmpu c -> comparison_name c ^ "u"
  | Ocmpf c -> comparison_name c ^ "f"

let name_of_chunk = function
  | Mint8signed -> "int8signed"
  | Mint8unsigned -> "int8unsigned"
  | Mint16signed -> "int16signed"
  | Mint16unsigned -> "int16unsigned"
  | Mint32 -> "int32"
  | Mfloat32 -> "float32"
  | Mfloat64 -> "float64"
  | Mfloat64al32 -> "float64al32"

(* Expressions *)

let rec expr p (prec, e) =
  let (prec', assoc) = precedence e in
  let (prec1, prec2) =
    if assoc = LtoR
    then (prec', prec' + 1)
    else (prec' + 1, prec') in
  if prec' < prec 
  then fprintf p "@[<hov 2>("
  else fprintf p "@[<hov 2>";
  begin match e with
  | Evar id ->
      fprintf p "%s" (ident_name id)
  | Econst(Ointconst n) ->
      fprintf p "%ld" (camlint_of_coqint n)
  | Econst(Ofloatconst f) ->
      fprintf p "%F" (camlfloat_of_coqfloat f)
  | Econst(Oaddrsymbol(id, ofs)) ->
      let ofs = camlint_of_coqint ofs in
      if ofs = 0l
      then fprintf p "\"%s\"" (extern_atom id)
      else fprintf p "(\"%s\" + %ld)" (extern_atom id) ofs
  | Econst(Oaddrstack n) ->
      fprintf p "&%ld" (camlint_of_coqint n)
  | Eunop(op, a1) ->
      fprintf p "%s %a" (name_of_unop op) expr (prec', a1)
  | Ebinop(op, a1, a2) ->
      fprintf p "%a@ %s %a"
                 expr (prec1, a1) (name_of_binop op) expr (prec2, a2)
  | Eload(chunk, a1) ->
      fprintf p "%s[%a]" (name_of_chunk chunk) expr (0, a1)
  | Econdition(a1, a2, a3) ->
      fprintf p "%a@ ? %a@ : %a" expr (4, a1) expr (4, a2) expr (4, a3)
  end;
  if prec' < prec then fprintf p ")@]" else fprintf p "@]"

let print_expr p e = expr p (0, e)

let rec print_expr_list p (first, rl) =
  match rl with
  | [] -> ()
  | r :: rl ->
      if not first then fprintf p ",@ ";
      expr p (2, r);
      print_expr_list p (false, rl)

(* Types *)

let name_of_type = function
  | Tint -> "int"
  | Tfloat -> "float"

let rec print_sig p = function
  | {sig_args = []; sig_res = None} -> fprintf p "void"
  | {sig_args = []; sig_res = Some ty} -> fprintf p "%s" (name_of_type ty)
  | {sig_args = t1 :: tl; sig_res = tres} ->
      fprintf p "%s ->@ " (name_of_type t1);
      print_sig p {sig_args = tl; sig_res = tres}

(* Statements *)

let rec print_stmt p s =
  match s with
  | Sskip ->
      fprintf p "/*skip*/"
  | Sassign(id, e2) ->
      fprintf p "@[<hv 2>%s =@ %a;@]" (ident_name id) print_expr e2
  | Sstore(chunk, a1, a2) ->
      fprintf p "@[<hv 2>%s[%a] =@ %a;@]"
              (name_of_chunk chunk) print_expr a1 print_expr a2
  | Scall(None, sg, e1, el) ->
      fprintf p "@[<hv 2>%a@,(@[<hov 0>%a@])@ : @[<hov 0>%a@];@]"
                print_expr e1
                print_expr_list (true, el)
                print_sig sg
  | Scall(Some id, sg, e1, el) ->
      fprintf p "@[<hv 2>%s =@ %a@,(@[<hov 0>%a@])@] : @[<hov 0>%a;@]"
                (ident_name id)
                print_expr e1
                print_expr_list (true, el)
                print_sig sg
  | Stailcall(sg, e1, el) ->
      fprintf p "@[<hv 2>tailcall %a@,(@[<hov 0>%a@])@ : @[<hov 0>%a@];@]"
                print_expr e1
                print_expr_list (true, el)
                print_sig sg
  | Sbuiltin(None, ef, el) ->
      fprintf p "@[<hv 2>builtin %s@,(@[<hov 0>%a@])@;@]"
                (name_of_external ef)
                print_expr_list (true, el)
  | Sbuiltin(Some id, ef, el) ->
      fprintf p "@[<hv 2>%s =@ builtin %s@,(@[<hov 0>%a@]);@]@]"
                (ident_name id)
                (name_of_external ef)
                print_expr_list (true, el)
  | Sseq(Sskip, s2) ->
      print_stmt p s2
  | Sseq(s1, Sskip) ->
      print_stmt p s1
  | Sseq(s1, s2) ->
      fprintf p "%a@ %a" print_stmt s1 print_stmt s2
  | Sifthenelse(e, s1, Sskip) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>}@]"
              print_expr e
              print_stmt s1
  | Sifthenelse(e, Sskip, s2) ->
      fprintf p "@[<v 2>if (! %a) {@ %a@;<0 -2>}@]"
              expr (15, e)
              print_stmt s2
  | Sifthenelse(e, s1, s2) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>} else {@ %a@;<0 -2>}@]"
              print_expr e
              print_stmt s1
              print_stmt s2
  | Sloop(s) ->
      fprintf p "@[<v 2>loop {@ %a@;<0 -2>}@]"
              print_stmt s
  | Sblock(s) ->
      fprintf p "@[<v 3>{{ %a@;<0 -3>}}@]"
              print_stmt s
  | Sexit n ->
      fprintf p "exit %d;" (camlint_of_nat n)
  | Sswitch(e, cases, dfl) ->
      fprintf p "@[<v 2>switch (%a) {" print_expr e;
      List.iter
        (fun (n, x) ->
           fprintf p "@ case %ld: exit %d;\n" 
                     (camlint_of_coqint n) (camlint_of_nat x))
        cases;
      fprintf p "@ default: exit %d;\n" (camlint_of_nat dfl);
      fprintf p "@;<0 -2>}@]"
  | Sreturn None ->
      fprintf p "return;"
  | Sreturn (Some e) ->
      fprintf p "return %a;" print_expr e
  | Slabel(lbl, s1) ->
      fprintf p "%s:@ %a" (ident_name lbl) print_stmt s1  (* wrong for Cminorgen output *)
  | Sgoto lbl ->
      fprintf p "goto %s;" (ident_name lbl)               (* wrong for Cminorgen output *)

(* Functions *)

let rec print_varlist p (vars, first) =
  match vars with
  | [] -> ()
  | v1 :: vl ->
      if not first then fprintf p ",@ ";
      fprintf p "%s" (ident_name v1);
      print_varlist p (vl, false)

let print_function p id f =
  fprintf p "@[<hov 4>\"%s\"(@[<hov 0>%a@])@ : @[<hov 0>%a@]@]@ "
            (extern_atom id)
            print_varlist (f.fn_params, true)
            print_sig f.fn_sig;
  fprintf p "@[<v 2>{@ ";
  let stksz = camlint_of_z f.fn_stackspace in
  if stksz <> 0l then
    fprintf p "stack %ld;@ " stksz;
  if f.fn_vars <> [] then
    fprintf p "var @[<hov 0>%a;@]@ " print_varlist (f.fn_vars, true);
  print_stmt p f.fn_body;
  fprintf p "@;<0 -2>}@]@ "

let print_extfun p id ef =
  fprintf p "@[<v 0>extern @[<hov 2>\"%s\":@ %a@]@ "
    (extern_atom id) print_sig (ef_sig ef)

let print_fundef p (id, fd) =
  match fd with
  | External ef ->
      print_extfun p id ef
  | Internal f ->
      print_function p id f

let print_init_data p = function
  | Init_int8 i -> fprintf p "int8 %ld" (camlint_of_coqint i)
  | Init_int16 i -> fprintf p "int16 %ld" (camlint_of_coqint i)
  | Init_int32 i -> fprintf p "%ld" (camlint_of_coqint i)
  | Init_float32 f -> fprintf p "float32 %F" (camlfloat_of_coqfloat f)
  | Init_float64 f -> fprintf p "%F" (camlfloat_of_coqfloat f)
  | Init_space i -> fprintf p "[%ld]" (camlint_of_coqint i)
  | Init_addrof(id,off) -> fprintf p "%ld(\"%s\")" (camlint_of_coqint off) (extern_atom id)

let rec print_init_data_list p = function
  | [] -> ()
  | [item] -> print_init_data p item
  | item::rest -> 
      (print_init_data p item;
       fprintf p ",";
       print_init_data_list p rest)

let print_globvar p gv = 
  if (gv.gvar_readonly) then
    fprintf p "readonly ";
  if (gv.gvar_volatile) then
    fprintf p "volatile ";
  fprintf p "{";
  print_init_data_list p gv.gvar_init;
  fprintf p "}"

let print_var p (id, gv) =
  fprintf p "var \"%s\" %a\n" (extern_atom id) print_globvar gv

let print_program p prog =
  fprintf p "@[<v>";
  List.iter (print_var p) prog.prog_vars;
  fprintf p "@]@[<v 0>";
  List.iter (print_fundef p) prog.prog_funct;
  fprintf p "@]@."

let destination : string option ref = ref None

let print_if prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_program (formatter_of_out_channel oc) prog;
      close_out oc
