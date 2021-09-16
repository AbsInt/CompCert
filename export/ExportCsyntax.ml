(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Bart Jacobs, KU Leuven                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(*  The contributions by Bart Jacobs are reused and adapted            *)
(*  under the terms of a Contributor License Agreement.                *)
(*                                                                     *)
(* *********************************************************************)

(** Export C syntax as a Coq file *)

open Format
open Camlcoq
open AST
open! Ctypes
open Cop
open Csyntax
open ExportBase
open ExportCtypes

(* Expressions *)

let name_unop = function
  | Onotbool -> "Onotbool"
  | Onotint -> "Onotint"
  | Oneg -> "Oneg"
  | Oabsfloat -> "Oabsfloat"

let name_binop = function
  | Oadd -> "Oadd"
  | Osub -> "Osub"
  | Omul -> "Omul"
  | Odiv -> "Odiv"
  | Omod -> "Omod"
  | Oand -> "Oand"
  | Oor -> "Oor"
  | Oxor -> "Oxor"
  | Oshl -> "Oshl"
  | Oshr -> "Oshr"
  | Oeq -> "Oeq"
  | Cop.One -> "One"
  | Olt -> "Olt"
  | Ogt -> "Ogt"
  | Ole -> "Ole"
  | Oge -> "Oge"

let name_incr_or_decr = function
  | Incr -> "Incr"
  | Decr -> "Decr"

let rec expr p = function
  | Eval(v, t) ->
      fprintf p "(Eval %a %a)" val_ v typ t
  | Evar(id, t) ->
      fprintf p "(Evar %a %a)" ident id typ t
  | Efield(a1, f, t) ->
      fprintf p "@[<hov 2>(Efield@ %a@ %a@ %a)@]" expr a1 ident f typ t
  | Evalof(l, t) ->
      fprintf p "@[<hov 2>(Evalof@ %a@ %a)@]" expr l typ t
  | Ederef(a1, t) ->
      fprintf p "@[<hov 2>(Ederef@ %a@ %a)@]" expr a1 typ t
  | Eaddrof(a1, t) ->
      fprintf p "@[<hov 2>(Eaddrof@ %a@ %a)@]" expr a1 typ t
  | Eunop(op, a1, t) ->
      fprintf p "@[<hov 2>(Eunop %s@ %a@ %a)@]"
         (name_unop op) expr a1 typ t
  | Ebinop(op, a1, a2, t) ->
      fprintf p "@[<hov 2>(Ebinop %s@ %a@ %a@ %a)@]"
         (name_binop op) expr a1 expr a2 typ t
  | Ecast(a1, t) ->
      fprintf p "@[<hov 2>(Ecast@ %a@ %a)@]" expr a1 typ t
  | Eseqand(a1, a2, t) ->
      fprintf p "@[<hov 2>(Eseqand@ %a@ %a@ %a)@]" expr a1 expr a2 typ t
  | Eseqor(a1, a2, t) ->
      fprintf p "@[<hov 2>(Eseqor@ %a@ %a@ %a)@]" expr a1 expr a2 typ t
  | Econdition(a1, a2, a3, t) ->
      fprintf p "@[<hov 2>(Econdition@ %a@ %a@ %a@ %a)@]" expr a1 expr a2 expr a3 typ t
  | Esizeof(t1, t) ->
      fprintf p "(Esizeof %a %a)" typ t1 typ t
  | Ealignof(t1, t) ->
      fprintf p "(Ealignof %a %a)" typ t1 typ t
  | Eassign(l, r, t) ->
      fprintf p "@[<hov 2>(Eassign@ %a@ %a@ %a)@]" expr l expr r typ t
  | Eassignop(op, l, r, t', t) ->
      fprintf p "@[<hov 2>(Eassignop@ %s@ %a@ %a@ %a %a)@]" (name_binop op) expr l expr r typ t' typ t
  | Epostincr(id, l, t) ->
      fprintf p "@[<hov 2>(Epostincr@ %s@ %a@ %a)@]" (name_incr_or_decr id) expr l typ t
  | Ecomma(a1, a2, t) ->
      fprintf p "@[<hov 2>(Ecomma@ %a@ %a@ %a)@]" expr a1 expr a2 typ t
  | Ecall(r1, rargs, t) ->
      fprintf p "@[<hov 2>(Ecall@ %a@ %a@ %a)@]" expr r1 exprlist rargs typ t
  | Ebuiltin(ef, tyargs, rargs, t) ->
      fprintf p "@[<hov 2>(Ebuiltin@ %a@ %a@ %a@ %a)@]" external_function ef typlist tyargs exprlist rargs typ t
  | Eloc(b, o, bf, t) ->
      fprintf p "@[<hov 2>(Eloc@ %a@ %a@ %a@ %a)@]" positive b coqptrofs o bitfield bf typ t
  | Eparen(r, t', t) ->
      fprintf p "@[<hov 2>(Eparen@ %a@ %a@ %a)@]" expr r typ t' typ t
and exprlist p = function
  | Enil ->
      fprintf p "Enil"
  | Econs(r1, rl) ->
      fprintf p "@[<hov 2>(Econs@ %a@ %a)@]" expr r1 exprlist rl

(* Statements *)

let rec statement p = function
  | Sskip ->
      fprintf p "Sskip"
  | Sdo(e) ->
      fprintf p "@[<hv 2>(Sdo %a)@]" expr e
  | Ssequence(s1, s2) ->
      fprintf p "@[<hv 2>(Ssequence@ %a@ %a)@]" statement s1 statement s2
  | Sifthenelse(e, s1, s2) ->
      fprintf p "@[<hv 2>(Sifthenelse %a@ %a@ %a)@]" expr e statement s1 statement s2
  | Swhile(e, s) ->
      fprintf p "@[<hv 2>(Swhile@ %a@ %a)@]" expr e statement s
  | Sdowhile(e, s) ->
      fprintf p "@[<hv 2>(Sdowhile@ %a@ %a)@]" expr e statement s
  | Sfor(s1, e, s2, s3) ->
      fprintf p "@[<hv 2>(Sfor@ %a@ %a@ %a@ %a)@]" statement s1 expr e statement s2 statement s3
  | Sbreak ->
      fprintf p "Sbreak"
  | Scontinue ->
      fprintf p "Scontinue"
  | Sreturn e ->
      fprintf p "@[<hv 2>(Sreturn %a)@]" (print_option expr) e
  | Sswitch(e, cases) ->
      fprintf p "@[<hv 2>(Sswitch %a@ %a)@]" expr e labeled_statements cases
  | Slabel(lbl, s1) ->
      fprintf p "@[<hv 2>(Slabel %a@ %a)@]" ident lbl statement s1
  | Sgoto lbl ->
      fprintf p "(Sgoto %a)" ident lbl

and labeled_statements p = function
  | LSnil ->
      (fprintf p "LSnil")
  | LScons(lbl, s, ls) ->
      fprintf p "@[<hv 2>(LScons %a@ %a@ %a)@]"
              (print_option coqZ) lbl statement s labeled_statements ls

(* Global definitions *)

let print_function p (id, f) =
  fprintf p "Definition f%s := {|@ " (sanitize (extern_atom id));
  fprintf p "  fn_return := %a;@ " typ f.fn_return;
  fprintf p "  fn_callconv := %a;@ " callconv f.fn_callconv;
  fprintf p "  fn_params := %a;@ " (print_list (print_pair ident typ)) f.fn_params;
  fprintf p "  fn_vars := %a;@ " (print_list (print_pair ident typ)) f.fn_vars;
  fprintf p "  fn_body :=@ ";
  statement p f.fn_body;
  fprintf p "@ |}.@ @ "

let print_globdef p (id, gd) =
  match gd with
  | Gfun(Ctypes.Internal f) -> print_function p (id, f)
  | Gfun(Ctypes.External _) -> ()
  | Gvar v -> print_variable typ p (id, v)

let print_ident_globdef p = function
  | (id, Gfun(Ctypes.Internal f)) ->
      fprintf p "(%a, Gfun(Internal f%s))" ident id (sanitize (extern_atom id))
  | (id, Gfun(Ctypes.External(ef, targs, tres, cc))) ->
      fprintf p "@[<hov 2>(%a,@ @[<hov 2>Gfun(External %a@ %a@ %a@ %a))@]@]"
        ident id external_function ef typlist targs typ tres callconv cc
  | (id, Gvar v) ->
      fprintf p "(%a, Gvar v%s)" ident id (sanitize (extern_atom id))

(* The prologue *)

let prologue = "\
From Coq Require Import String List ZArith.\n\
From compcert Require Import Coqlib Integers Floats Values AST Ctypes Cop Csyntax Csyntaxdefs.\n\
Import Csyntaxdefs.CsyntaxNotations.\n\
Local Open Scope Z_scope.\n\
Local Open Scope string_scope.\n\
Local Open Scope csyntax_scope.\n"

(* All together *)

let print_program p prog sourcefile =
  fprintf p "@[<v 0>";
  fprintf p "%s" prologue;
  print_gen_info ~sourcefile p;
  define_idents p;
  List.iter (print_globdef p) prog.Ctypes.prog_defs;
  fprintf p "Definition composites : list composite_definition :=@ ";
  print_list print_composite_definition p prog.prog_types;
  fprintf p ".@ @ ";
  fprintf p "Definition global_definitions : list (ident * globdef fundef type) :=@ ";
  print_list print_ident_globdef p prog.Ctypes.prog_defs;
  fprintf p ".@ @ ";
  fprintf p "Definition public_idents : list ident :=@ ";
  print_list ident p prog.Ctypes.prog_public;
  fprintf p ".@ @ ";
  fprintf p "Definition prog : Csyntax.program := @ ";
  fprintf p "  mkprogram composites global_definitions public_idents %a Logic.I.@ @ "
            ident prog.Ctypes.prog_main;
  fprintf p "@]@."
