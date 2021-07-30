(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
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
(* *********************************************************************)

(** Export Clight as a Coq file *)

open Format
open Camlcoq
open AST
open! Ctypes
open Values
open Cop
open Csyntax

(* Options, lists, pairs *)

let print_option fn p = function
  | None -> fprintf p "None"
  | Some x -> fprintf p "(Some %a)" fn x

let print_pair fn1 fn2 p (x1, x2) =
  fprintf p "@[<hov 1>(%a,@ %a)@]" fn1 x1 fn2 x2

let print_list fn p l =
  match l with
  | [] ->
      fprintf p "nil"
  | hd :: tl ->
      fprintf p "@[<hov 1>(";
      let rec plist = function
      | [] -> fprintf p "nil"
      | hd :: tl -> fprintf p "%a ::@ " fn hd; plist tl
      in plist l;
      fprintf p ")@]"

(* Numbers *)

let coqint p n =
  let n = camlint_of_coqint n in
  if n >= 0l
  then fprintf p "(Int.repr %ld)" n
  else fprintf p "(Int.repr (%ld))" n

let coqptrofs p n =
  let s = Z.to_string n in
  if Z.ge n Z.zero
  then fprintf p "(Ptrofs.repr %s)" s
  else fprintf p "(Ptrofs.repr (%s))" s

let coqint64 p n =
  let n = camlint64_of_coqint n in
  if n >= 0L
  then fprintf p "(Int64.repr %Ld)" n
  else fprintf p "(Int64.repr (%Ld))" n

let coqfloat p n =
  fprintf p "(Float.of_bits %a)" coqint64 (Floats.Float.to_bits n)

let coqsingle p n =
  fprintf p "(Float32.of_bits %a)" coqint (Floats.Float32.to_bits n)

let positive p n =
  fprintf p "%s%%positive" (Z.to_string (Z.Zpos n))

let coqN p n =
  fprintf p "%s%%N" (Z.to_string (Z.of_N n))

let coqZ p n =
  if Z.ge n Z.zero
  then fprintf p "%s" (Z.to_string n)
  else fprintf p "(%s)" (Z.to_string n)

(* Coq strings *)

let coqstring p s =
  fprintf p "\"%s\"" (camlstring_of_coqstring s)

(* Identifiers *)

exception Not_an_identifier

let sanitize s =
  let s' = Bytes.create (String.length s) in
  for i = 0 to String.length s - 1 do
    Bytes.set  s' i
    (match String.get s i with
      | 'A'..'Z' | 'a'..'z' | '0'..'9' | '_' as c -> c
      | ' ' | '$' -> '_'
      | _ -> raise Not_an_identifier)
  done;
  Bytes.to_string s'

let ident p id =
  try
    let s = Hashtbl.find string_of_atom id in
    fprintf p "_%s" (sanitize s)
  with Not_found | Not_an_identifier ->
    positive p id

let iter_hashtbl_sorted (h: ('a, string) Hashtbl.t) (f: 'a * string -> unit) =
  List.iter f
    (List.fast_sort (fun (k1, d1) (k2, d2) -> String.compare d1 d2)
      (Hashtbl.fold (fun k d accu -> (k, d) :: accu) h []))

let define_idents p =
  iter_hashtbl_sorted
    string_of_atom
    (fun (id, name) ->
      try
        if !use_canonical_atoms && id = pos_of_string name then
          fprintf p "Definition _%s : ident := $\"%s\".@ "
                    (sanitize name) name
        else
          fprintf p "Definition _%s : ident := %a.@ "
                    (sanitize name) positive id
      with Not_an_identifier ->
        ());
  fprintf p "@ "

(* Raw attributes *)

let attribute p a =
  if a = noattr then
    fprintf p "noattr"
  else
    fprintf p "{| attr_volatile := %B; attr_alignas := %a |}"
              a.attr_volatile
              (print_option coqN) a.attr_alignas

(* Types *)

let rec typ p t =
  match attr_of_type t with
  | { attr_volatile = false; attr_alignas = None} ->
        rtyp p t
  | { attr_volatile = true; attr_alignas = None} ->
        fprintf p "(tvolatile %a)" rtyp t
  | { attr_volatile = false; attr_alignas = Some n} ->
        fprintf p "(talignas %a %a)" coqN n rtyp t
  | { attr_volatile = true; attr_alignas = Some n} ->
        fprintf p "(tvolatile_alignas %a %a)" coqN n rtyp t

and rtyp p = function
  | Tvoid -> fprintf p "tvoid"
  | Ctypes.Tint(sz, sg, _) ->
      fprintf p "%s" (
        match sz, sg with
        | I8, Signed -> "tschar"
        | I8, Unsigned -> "tuchar"
        | I16, Signed -> "tshort"
        | I16, Unsigned -> "tushort"
        | I32, Signed -> "tint"
        | I32, Unsigned -> "tuint"
        | IBool, _ -> "tbool")
  | Ctypes.Tlong(sg, _) ->
      fprintf p "%s" (
        match sg with
        | Signed -> "tlong"
        | Unsigned -> "tulong")
  | Ctypes.Tfloat(sz, _) ->
      fprintf p "%s" (
        match sz with
        | F32 -> "tfloat"
        | F64 -> "tdouble")
  | Tpointer(t, _) ->
      fprintf p "(tptr %a)" typ t
  | Tarray(t, sz, _) ->
      fprintf p "(tarray %a %ld)" typ t (Z.to_int32 sz)
  | Tfunction(targs, tres, cc) ->
      fprintf p "@[<hov 2>(Tfunction@ %a@ %a@ %a)@]"
                typlist targs typ tres callconv cc
  | Tstruct(id, _) ->
      fprintf p "(Tstruct %a noattr)" ident id
  | Tunion(id, _) ->
      fprintf p "(Tunion %a noattr)" ident id

and typlist p = function
  | Tnil ->
      fprintf p "Tnil"
  | Tcons(t, tl) ->
      fprintf p "@[<hov 2>(Tcons@ %a@ %a)@]" typ t typlist tl

and callconv p cc =
  if cc = cc_default
  then fprintf p "cc_default"
  else fprintf p "{|cc_vararg:=%a; cc_unproto:=%b; cc_structret:=%b|}"
                  (print_option coqZ) cc.cc_vararg cc.cc_unproto cc.cc_structret

(* External functions *)

let asttype p t =
  fprintf p "%s"
     (match t with
      | AST.Tint -> "AST.Tint"
      | AST.Tfloat -> "AST.Tfloat"
      | AST.Tlong -> "AST.Tlong"
      | AST.Tsingle -> "AST.Tsingle"
      | AST.Tany32 -> "AST.Tany32"
      | AST.Tany64 -> "AST.Tany64")

let astrettype p = function
  | AST.Tret t -> asttype p t
  | AST.Tvoid -> fprintf p "AST.Tvoid"
  | AST.Tint8signed -> fprintf p "AST.Tint8signed"
  | AST.Tint8unsigned -> fprintf p "AST.Tint8unsigned"
  | AST.Tint16signed -> fprintf p "AST.Tint16signed"
  | AST.Tint16unsigned -> fprintf p "AST.Tint16unsigned"

let name_of_chunk = function
  | Mint8signed -> "Mint8signed"
  | Mint8unsigned -> "Mint8unsigned"
  | Mint16signed -> "Mint16signed"
  | Mint16unsigned -> "Mint16unsigned"
  | Mint32 -> "Mint32"
  | Mint64 -> "Mint64"
  | Mfloat32 -> "Mfloat32"
  | Mfloat64 -> "Mfloat64"
  | Many32 -> "Many32"
  | Many64 -> "Many64"

let signatur p sg =
  fprintf p "@[<hov 2>(mksignature@ %a@ %a@ %a)@]"
     (print_list asttype) sg.sig_args
     astrettype sg.sig_res
     callconv sg.sig_cc

let external_function p = function
  | EF_external(name, sg) ->
      fprintf p "@[<hov 2>(EF_external %a@ %a)@]" coqstring name signatur sg
  | EF_builtin(name, sg) ->
      fprintf p "@[<hov 2>(EF_builtin %a@ %a)@]" coqstring name signatur sg
  | EF_runtime(name, sg) ->
      fprintf p "@[<hov 2>(EF_runtime %a@ %a)@]" coqstring name signatur sg
  | EF_vload chunk ->
      fprintf p "(EF_vload %s)" (name_of_chunk chunk)
  | EF_vstore chunk ->
      fprintf p "(EF_vstore %s)" (name_of_chunk chunk)
  | EF_malloc -> fprintf p "EF_malloc"
  | EF_free -> fprintf p "EF_free"
  | EF_memcpy(sz, al) ->
      fprintf p "(EF_memcpy %ld %ld)" (Z.to_int32 sz) (Z.to_int32 al)
  | EF_annot(kind, text, targs) ->
      fprintf p "(EF_annot %a %a %a)"
                positive kind coqstring text (print_list asttype) targs
  | EF_annot_val(kind, text, targ) ->
      fprintf p "(EF_annot_val %a %a %a)"
                positive kind coqstring text asttype targ
  | EF_debug(kind, text, targs) ->
      fprintf p "(EF_debug %a %a %a)"
                positive kind positive text (print_list asttype) targs
  | EF_inline_asm(text, sg, clob) ->
      fprintf p "@[<hov 2>(EF_inline_asm %a@ %a@ %a)@]"
              coqstring text
              signatur sg
              (print_list coqstring) clob

(* Values *)

let val_ p = function
  | Vundef -> fprintf p "Vundef"
  | Vint i -> fprintf p "(Vint %a)" coqint i
  | Vlong l -> fprintf p "(Vlong %a)" coqint64 l
  | Vfloat f -> fprintf p "(Vfloat %a)" coqfloat f
  | Vsingle s -> fprintf p "(Vsingle %a)" coqsingle s
  | Vptr(b, o) -> fprintf p "(Vptr %a %a)" positive b coqptrofs o

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
  | Eloc(b, o, t) ->
      fprintf p "@[<hov 2>(Eloc@ %a@ %a@ %a)@]" positive b coqptrofs o typ t
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

let print_function p (id, f) =
  fprintf p "Definition f_%s := {|@ " (sanitize (extern_atom id));
  fprintf p "  fn_return := %a;@ " typ f.fn_return;
  fprintf p "  fn_callconv := %a;@ " callconv f.fn_callconv;
  fprintf p "  fn_params := %a;@ " (print_list (print_pair ident typ)) f.fn_params;
  fprintf p "  fn_vars := %a;@ " (print_list (print_pair ident typ)) f.fn_vars;
  fprintf p "  fn_body :=@ ";
  statement p f.fn_body;
  fprintf p "@ |}.@ @ "

let init_data p = function
  | Init_int8 n -> fprintf p "Init_int8 %a" coqint n
  | Init_int16 n -> fprintf p "Init_int16 %a" coqint n
  | Init_int32 n -> fprintf p "Init_int32 %a" coqint n
  | Init_int64 n -> fprintf p "Init_int64 %a" coqint64 n
  | Init_float32 n -> fprintf p "Init_float32 %a" coqsingle n
  | Init_float64 n -> fprintf p "Init_float64 %a" coqfloat n
  | Init_space n -> fprintf p "Init_space %a" coqZ n
  | Init_addrof(id,ofs) -> fprintf p "Init_addrof %a %a" ident id coqptrofs ofs

let print_variable p (id, v) =
  fprintf p "Definition v_%s := {|@ " (sanitize (extern_atom id));
  fprintf p "  gvar_info := %a;@ " typ v.gvar_info;
  fprintf p "  gvar_init := %a;@ " (print_list init_data) v.gvar_init;
  fprintf p "  gvar_readonly := %B;@ " v.gvar_readonly;
  fprintf p "  gvar_volatile := %B@ " v.gvar_volatile;
  fprintf p "|}.@ @ "

let print_globdef p (id, gd) =
  match gd with
  | Gfun(Ctypes.Internal f) -> print_function p (id, f)
  | Gfun(Ctypes.External _) -> ()
  | Gvar v -> print_variable p (id, v)

let print_ident_globdef p = function
  | (id, Gfun(Ctypes.Internal f)) ->
      fprintf p "(%a, Gfun(Internal f_%s))" ident id (sanitize (extern_atom id))
  | (id, Gfun(Ctypes.External(ef, targs, tres, cc))) ->
      fprintf p "@[<hov 2>(%a,@ @[<hov 2>Gfun(External %a@ %a@ %a@ %a))@]@]"
        ident id external_function ef typlist targs typ tres callconv cc
  | (id, Gvar v) ->
      fprintf p "(%a, Gvar v_%s)" ident id (sanitize (extern_atom id))

(* Composite definitions *)

let print_composite_definition p (Composite(id, su, m, a)) =
  fprintf p "@[<hv 2>Composite %a %s@ %a@ %a@]"
    ident id
    (match su with Struct -> "Struct" | Union -> "Union")
    (print_list (print_pair ident typ)) m
    attribute a

(* The prologue *)

let prologue = "\
From Coq Require Import String List ZArith.\n\
From compcert Require Import Coqlib Integers Floats Values AST Ctypes Cop Csyntax Csyntaxdefs.\n\
Import Csyntaxdefs.CsyntaxNotations.\n\
Local Open Scope Z_scope.\n\
Local Open Scope string_scope.\n\
Local Open Scope csyntax_scope.\n"

(* Information about this run of csyntaxgen *)

let print_csyntaxgen_info p sourcefile =
  fprintf p "@[<v 2>Module Info.";
  fprintf p "@ Definition version := %S." Version.version;
  fprintf p "@ Definition build_number := %S." Version.buildnr;
  fprintf p "@ Definition build_tag := %S." Version.tag;
  fprintf p "@ Definition build_branch := %S." Version.branch;
  fprintf p "@ Definition arch := %S." Configuration.arch;
  fprintf p "@ Definition model := %S." Configuration.model;
  fprintf p "@ Definition abi := %S." Configuration.abi;
  fprintf p "@ Definition bitsize := %d." (if Archi.ptr64 then 64 else 32);
  fprintf p "@ Definition big_endian := %B." Archi.big_endian;
  fprintf p "@ Definition source_file := %S." sourcefile;
  fprintf p "@]@ End Info.@ @ "  
  
(* All together *)

let print_program p prog sourcefile =
  fprintf p "@[<v 0>";
  fprintf p "%s" prologue;
  print_csyntaxgen_info p sourcefile;
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
