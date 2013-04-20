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

(** Pretty-printer for Clight *)

open Format
open Camlcoq
open Datatypes
open Values
open AST
open PrintAST
open Ctypes
open Cop
open PrintCsyntax
open Clight

(* Naming temporaries *)

let temp_name (id: ident) = "$" ^ Z.to_string (Z.Zpos id)

(* Declarator (identifier + type) -- reuse from PrintCsyntax *)

(* Precedences and associativity (H&S section 7.2) *)

type associativity = LtoR | RtoL | NA

let rec precedence = function
  | Evar _ -> (16, NA)
  | Etempvar _ -> (16, NA)
  | Ederef _ -> (15, RtoL)
  | Efield _ -> (16, LtoR)
  | Econst_int _ -> (16, NA)
  | Econst_float _ -> (16, NA)
  | Econst_long _ -> (16, NA)
  | Eunop _ -> (15, RtoL)
  | Eaddrof _ -> (15, RtoL)
  | Ecast _ -> (14, RtoL)
  | Ebinop((Omul|Odiv|Omod), _, _, _) -> (13, LtoR)
  | Ebinop((Oadd|Osub), _, _, _) -> (12, LtoR)
  | Ebinop((Oshl|Oshr), _, _, _) -> (11, LtoR)
  | Ebinop((Olt|Ogt|Ole|Oge), _, _, _) -> (10, LtoR)
  | Ebinop((Oeq|One), _, _, _) -> (9, LtoR)
  | Ebinop(Oand, _, _, _) -> (8, LtoR)
  | Ebinop(Oxor, _, _, _) -> (7, LtoR)
  | Ebinop(Oor, _, _, _) -> (6, LtoR)

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
  | Evar(id, _) ->
      fprintf p "%s" (extern_atom id)
  | Etempvar(id, _) ->
      fprintf p "%s" (temp_name id)
  | Ederef(a1, _) ->
      fprintf p "*%a" expr (prec', a1)
  | Efield(a1, f, _) ->
      fprintf p "%a.%s" expr (prec', a1) (extern_atom f)
  | Econst_int(n, _) ->
      fprintf p "%ld" (camlint_of_coqint n)
  | Econst_float(f, _) ->
      fprintf p "%F" (camlfloat_of_coqfloat f)
  | Econst_long(n, _) ->
      fprintf p "%LdLL" (camlint64_of_coqint n)
  | Eunop(op, a1, _) ->
      fprintf p "%s%a" (name_unop op) expr (prec', a1)
  | Eaddrof(a1, _) ->
      fprintf p "&%a" expr (prec', a1)
  | Ebinop(op, a1, a2, _) ->
      fprintf p "%a@ %s %a"
                 expr (prec1, a1) (name_binop op) expr (prec2, a2)
  | Ecast(a1, ty) ->
      fprintf p "(%s) %a" (name_type ty) expr (prec', a1)
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

(* Statements *)

let rec print_stmt p s =
  match s with
  | Sskip ->
      fprintf p "/*skip*/;"
  | Sassign(e1, e2) ->
      fprintf p "@[<hv 2>%a =@ %a;@]" print_expr e1 print_expr e2
  | Sset(id, e2) ->
      fprintf p "@[<hv 2>%s =@ %a;@]" (temp_name id) print_expr e2
  | Scall(None, e1, el) ->
      fprintf p "@[<hv 2>%a@,(@[<hov 0>%a@]);@]"
                print_expr e1
                print_expr_list (true, el)
  | Scall(Some id, e1, el) ->
      fprintf p "@[<hv 2>%s =@ %a@,(@[<hov 0>%a@]);@]"
                (temp_name id)
                print_expr e1
                print_expr_list (true, el)
  | Sbuiltin(None, ef, tyargs, el) ->
      fprintf p "@[<hv 2>builtin %s@,(@[<hov 0>%a@]);@]"
                (name_of_external ef)
                print_expr_list (true, el)
  | Sbuiltin(Some id, ef, tyargs, el) ->
      fprintf p "@[<hv 2>%s =@ builtin %s@,(@[<hov 0>%a@]);@]"
                (temp_name id)
                (name_of_external ef)
                print_expr_list (true, el)
  | Ssequence(Sskip, s2) ->
      print_stmt p s2
  | Ssequence(s1, Sskip) ->
      print_stmt p s1
  | Ssequence(s1, s2) ->
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
  | Sloop(s1, Sskip) ->
      fprintf p "@[<v 2>while (1) {@ %a@;<0 -2>}@]"
              print_stmt s1
  | Sloop(s1, s2) ->
      fprintf p "@[<v 2>for (@[<hv 0>;@ 1;@ %a) {@]@ %a@;<0 -2>}@]"
              print_stmt_for s2
              print_stmt s1
  | Sbreak ->
      fprintf p "break;"
  | Scontinue ->
      fprintf p "continue;"
  | Sswitch(e, cases) ->
      fprintf p "@[<v 2>switch (%a) {@ %a@;<0 -2>}@]"
              print_expr e
              print_cases cases
  | Sreturn None ->
      fprintf p "return;"
  | Sreturn (Some e) ->
      fprintf p "return %a;" print_expr e
  | Slabel(lbl, s1) ->
      fprintf p "%s:@ %a" (extern_atom lbl) print_stmt s1
  | Sgoto lbl ->
      fprintf p "goto %s;" (extern_atom lbl)

and print_cases p cases =
  match cases with
  | LSdefault Sskip ->
      ()
  | LSdefault s ->
      fprintf p "@[<v 2>default:@ %a@]" print_stmt s
  | LScase(lbl, Sskip, rem) ->
      fprintf p "case %ld:@ %a"
              (camlint_of_coqint lbl)
              print_cases rem
  | LScase(lbl, s, rem) ->
      fprintf p "@[<v 2>case %ld:@ %a@]@ %a"
              (camlint_of_coqint lbl)
              print_stmt s
              print_cases rem

and print_stmt_for p s =
  match s with
  | Sskip ->
      fprintf p "/*nothing*/"
  | Sassign(e1, e2) ->
      fprintf p "%a = %a" print_expr e1 print_expr e2
  | Sset(id, e2) ->
      fprintf p "%s = %a" (temp_name id) print_expr e2
  | Ssequence(s1, s2) ->
      fprintf p "%a, %a" print_stmt_for s1 print_stmt_for s2
  | Scall(None, e1, el) ->
      fprintf p "@[<hv 2>%a@,(@[<hov 0>%a@])@]"
                print_expr e1
                print_expr_list (true, el)
  | Scall(Some id, e1, el) ->
      fprintf p "@[<hv 2>%s =@ %a@,(@[<hov 0>%a@])@]"
                (temp_name id)
                print_expr e1
                print_expr_list (true, el)
  | Sbuiltin(None, ef, tyargs, el) ->
      fprintf p "@[<hv 2>builtin %s@,(@[<hov 0>%a@]);@]"
                (name_of_external ef)
                print_expr_list (true, el)
  | Sbuiltin(Some id, ef, tyargs, el) ->
      fprintf p "@[<hv 2>%s =@ builtin %s@,(@[<hov 0>%a@]);@]"
                (temp_name id)
                (name_of_external ef)
                print_expr_list (true, el)
  | _ ->
      fprintf p "({ %a })" print_stmt s

let print_function p id f =
  fprintf p "%s@ "
            (name_cdecl (name_function_parameters (extern_atom id)
                                                  f.fn_params)
                        f.fn_return);
  fprintf p "@[<v 2>{@ ";
  List.iter
    (fun (id, ty) ->
      fprintf p "%s;@ " (name_cdecl (extern_atom id) ty))
    f.fn_vars;
  List.iter
    (fun (id, ty) ->
      fprintf p "register %s;@ " (name_cdecl (temp_name id) ty))
    f.fn_temps;
  print_stmt p f.fn_body;
  fprintf p "@;<0 -2>}@]@ @ "

let print_fundef p id fd =
  match fd with
  | External(EF_external(_,_), args, res) ->
      fprintf p "extern %s;@ @ "
                (name_cdecl (extern_atom id) (Tfunction(args, res)))
  | External(_, _, _) ->
      ()
  | Internal f ->
      print_function p id f

let print_globdef p (id, gd) =
  match gd with
  | Gfun f -> print_fundef p id f
  | Gvar v -> print_globvar p id v  (* from PrintCsyntax *)

(* Collect struct and union types *)

let rec collect_expr e =
  collect_type (typeof e);
  match e with
  | Econst_int _ -> ()
  | Econst_float _ -> ()
  | Econst_long _ -> ()
  | Evar _ -> ()
  | Etempvar _ -> ()
  | Ederef(r, _) -> collect_expr r
  | Efield(l, _, _) -> collect_expr l
  | Eaddrof(l, _) -> collect_expr l
  | Eunop(_, r, _) -> collect_expr r
  | Ebinop(_, r1, r2, _) -> collect_expr r1; collect_expr r2
  | Ecast(r, _) -> collect_expr r

let rec collect_exprlist = function
  | [] -> ()
  | r1 :: rl -> collect_expr r1; collect_exprlist rl

let rec collect_stmt = function
  | Sskip -> ()
  | Sassign(e1, e2) -> collect_expr e1; collect_expr e2
  | Sset(id, e2) -> collect_expr e2
  | Scall(optid, e1, el) -> collect_expr e1; collect_exprlist el
  | Sbuiltin(optid, ef, tyargs, el) -> collect_exprlist el
  | Ssequence(s1, s2) -> collect_stmt s1; collect_stmt s2
  | Sifthenelse(e, s1, s2) -> collect_expr e; collect_stmt s1; collect_stmt s2
  | Sloop(s1, s2) -> collect_stmt s1; collect_stmt s2
  | Sbreak -> ()
  | Scontinue -> ()
  | Sswitch(e, cases) -> collect_expr e; collect_cases cases
  | Sreturn None -> ()
  | Sreturn (Some e) -> collect_expr e
  | Slabel(lbl, s) -> collect_stmt s
  | Sgoto lbl -> ()

and collect_cases = function
  | LSdefault s -> collect_stmt s
  | LScase(lbl, s, rem) -> collect_stmt s; collect_cases rem

let collect_function f =
  collect_type f.fn_return;
  List.iter (fun (id, ty) -> collect_type ty) f.fn_params;
  List.iter (fun (id, ty) -> collect_type ty) f.fn_vars;
  List.iter (fun (id, ty) -> collect_type ty) f.fn_temps;
  collect_stmt f.fn_body

let collect_globdef (id, gd) =
  match gd with
  | Gfun(External(_, args, res)) -> collect_type_list args; collect_type res
  | Gfun(Internal f) -> collect_function f
  | Gvar v -> collect_type v.gvar_info

let collect_program p =
  List.iter collect_globdef p.prog_defs

let print_program p prog =
  struct_unions := StructUnion.empty;
  collect_program prog;
  fprintf p "@[<v 0>";
  StructUnion.iter (declare_struct_or_union p) !struct_unions;
  StructUnion.iter (print_struct_or_union p) !struct_unions;
  List.iter (print_globdef p) prog.prog_defs;
  fprintf p "@]@."

let destination : string option ref = ref None

let print_if prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_program (formatter_of_out_channel oc) prog;
      close_out oc
