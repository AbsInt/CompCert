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

(** Pretty-printer for Csyntax *)

open Printf
open Format
open Camlcoq
open Datatypes
open Values
open AST
open Globalenvs
open Ctypes
open Cop
open Csyntax

let name_unop = function
  | Onotbool -> "!"
  | Onotint  -> "~"
  | Oneg     -> "-"

let name_binop = function
  | Oadd -> "+"
  | Osub -> "-"
  | Omul -> "*"
  | Odiv -> "/"
  | Omod -> "%"
  | Oand -> "&"
  | Oor  -> "|"
  | Oxor -> "^"
  | Oshl -> "<<"
  | Oshr -> ">>"
  | Oeq  -> "=="
  | One  -> "!="
  | Olt  -> "<"
  | Ogt  -> ">"
  | Ole  -> "<="
  | Oge  -> ">="

let name_inttype sz sg =
  match sz, sg with
  | I8, Signed -> "signed char"
  | I8, Unsigned -> "unsigned char"
  | I16, Signed -> "short"
  | I16, Unsigned -> "unsigned short"
  | I32, Signed -> "int"
  | I32, Unsigned -> "unsigned int"
  | IBool, _ -> "_Bool"

let name_floattype sz =
  match sz with
  | F32 -> "float"
  | F64 -> "double"

let name_longtype sg =
  match sg with
  | Signed -> "long long"
  | Unsigned -> "unsigned long long"

(* Collecting the names and fields of structs and unions *)

module StructUnion = Map.Make(String)

let struct_unions = ref StructUnion.empty

(* Declarator (identifier + type) *)

let attributes a =
  if attr_volatile a then " volatile" else ""

let name_optid id =
  if id = "" then "" else " " ^ id

(*
let parenthesize_if_pointer id =
  if String.length id > 0 && id.[0] = '*' then "(" ^ id ^ ")" else id
*)

let rec name_cdecl id ty =
  match ty with
  | Tvoid ->
      "void" ^ name_optid id
  | Tint(sz, sg, a) ->
      name_inttype sz sg ^ attributes a ^ name_optid id
  | Tfloat(sz, a) ->
      name_floattype sz ^ attributes a ^ name_optid id
  | Tlong(sg, a) ->
      name_longtype sg ^ attributes a ^ name_optid id
  | Tpointer(t, a) ->
      let id' =
        match t with
        | Tfunction _ | Tarray _ -> sprintf "(*%s%s)" (attributes a) id
        | _                      -> sprintf "*%s%s" (attributes a) id in
      name_cdecl id' t
  | Tarray(t, n, a) ->
      name_cdecl (sprintf "%s[%ld]" id (camlint_of_coqint n)) t
  | Tfunction(args, res) ->
      let b = Buffer.create 20 in
      if id = ""
      then Buffer.add_string b "(*)"
      else Buffer.add_string b id;
      Buffer.add_char b '(';
      begin match args with
      | Tnil ->
          Buffer.add_string b "void"
      | _ ->
          let rec add_args first = function
          | Tnil -> ()
          | Tcons(t1, tl) ->
              if not first then Buffer.add_string b ", ";
              Buffer.add_string b (name_cdecl "" t1);
              add_args false tl in
          add_args true args
      end;
      Buffer.add_char b ')';
      name_cdecl (Buffer.contents b) res
  | Tstruct(name, fld, a) ->
      extern_atom name ^ attributes a ^ name_optid id
  | Tunion(name, fld, a) ->
      extern_atom name ^ attributes a ^ name_optid id
  | Tcomp_ptr(name, a) ->
      extern_atom name ^ " *" ^ attributes a ^ id

(* Type *)

let name_type ty = name_cdecl "" ty

(* Precedences and associativity (H&S section 7.2) *)

type associativity = LtoR | RtoL | NA

let rec precedence = function
  | Eloc _ -> (16, NA)
  | Evar _ -> (16, NA)
  | Ederef _ -> (15, RtoL)
  | Efield _ -> (16, LtoR)
  | Eval _ -> (16, NA)
  | Evalof(l, _) -> precedence l
  | Esizeof _ -> (15, RtoL)
  | Ealignof _ -> (15, RtoL)
  | Ecall _ | Ebuiltin _ -> (16, LtoR)
  | Epostincr _ -> (16, LtoR)
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
  | Eseqand _ -> (5, LtoR)
  | Eseqor _ -> (4, LtoR)
  | Econdition _ -> (3, RtoL)
  | Eassign _ -> (2, RtoL)
  | Eassignop _ -> (2, RtoL)
  | Ecomma _ -> (1, LtoR)
  | Eparen _ -> (14, RtoL)

(* Expressions *)

let print_pointer_hook
   : (formatter -> Values.block * Integers.Int.int -> unit) ref
   = ref (fun p (b, ofs) -> ())

let print_value p v =
  match v with
  | Vint n -> fprintf p "%ld" (camlint_of_coqint n)
  | Vfloat f -> fprintf p "%F" (camlfloat_of_coqfloat f)
  | Vlong n -> fprintf p "%Ld" (camlint64_of_coqint n)
  | Vptr(b, ofs) -> fprintf p "<ptr%a>" !print_pointer_hook (b, ofs)
  | Vundef -> fprintf p "<undef>"

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
  | Eloc(b, ofs, _) ->
      fprintf p "<loc%a>" !print_pointer_hook (b, ofs)
  | Evar(id, _) ->
      fprintf p "%s" (extern_atom id)
  | Ederef(a1, _) ->
      fprintf p "*%a" expr (prec', a1)
  | Efield(a1, f, _) ->
      fprintf p "%a.%s" expr (prec', a1) (extern_atom f)
  | Evalof(l, _) ->
      expr p (prec, l)
  | Eval(v, _) ->
      print_value p (v)
  | Esizeof(ty, _) ->
      fprintf p "sizeof(%s)" (name_type ty)
  | Ealignof(ty, _) ->
      fprintf p "__alignof__(%s)" (name_type ty)
  | Eunop(op, a1, _) ->
      fprintf p "%s%a" (name_unop op) expr (prec', a1)
  | Eaddrof(a1, _) ->
      fprintf p "&%a" expr (prec', a1)
  | Epostincr(id, a1, _) ->
      fprintf p "%a%s" expr (prec', a1)
                        (match id with Incr -> "++" | Decr -> "--")
  | Ebinop(op, a1, a2, _) ->
      fprintf p "%a@ %s %a"
                 expr (prec1, a1) (name_binop op) expr (prec2, a2)
  | Ecast(a1, ty) ->
      fprintf p "(%s) %a" (name_type ty) expr (prec', a1)
  | Eassign(a1, a2, _) ->
      fprintf p "%a =@ %a" expr (prec1, a1) expr (prec2, a2)
  | Eassignop(op, a1, a2, _, _) ->
      fprintf p "%a %s=@ %a" expr (prec1, a1) (name_binop op) expr (prec2, a2)
  | Eseqand(a1, a2, _) ->
      fprintf p "%a@ && %a" expr (prec1, a1) expr (prec2, a2)
  | Eseqor(a1, a2, _) ->
      fprintf p "%a@ || %a" expr (prec1, a1) expr (prec2, a2)
  | Econdition(a1, a2, a3, _) ->
      fprintf p "%a@ ? %a@ : %a" expr (4, a1) expr (4, a2) expr (4, a3)
  | Ecomma(a1, a2, _) ->
      fprintf p "%a,@ %a" expr (prec1, a1) expr (prec2, a2)
  | Ecall(a1, al, _) ->
      fprintf p "%a@[<hov 1>(%a)@]" expr (prec', a1) exprlist (true, al)
  | Ebuiltin(EF_memcpy(sz, al), _, args, _) ->
      fprintf p "__builtin_memcpy_aligned@[<hov 1>(%ld,@ %ld,@ %a)@]"
                (camlint_of_coqint sz) (camlint_of_coqint al)
                exprlist (true, args)
  | Ebuiltin(EF_annot(txt, _), _, args, _) ->
      fprintf p "__builtin_annot@[<hov 1>(%S%a)@]"
                (extern_atom txt) exprlist (false, args)
  | Ebuiltin(EF_annot_val(txt, _), _, args, _) ->
      fprintf p "__builtin_annot_val@[<hov 1>(%S%a)@]"
                (extern_atom txt) exprlist (false, args)
  | Ebuiltin(_, _, args, _) ->
      fprintf p "<unknown builtin>@[<hov 1>(%a)@]" exprlist (true, args)
  | Eparen(a1, ty) ->
      fprintf p "(%s) %a" (name_type ty) expr (prec', a1)
  end;
  if prec' < prec then fprintf p ")@]" else fprintf p "@]"

and exprlist p (first, rl) =
  match rl with
  | Enil -> ()
  | Econs(r, rl) ->
      if not first then fprintf p ",@ ";
      expr p (2, r);
      exprlist p (false, rl)

let print_expr p e = expr p (0, e)
let print_exprlist p el = exprlist p (true, el)

(* Statements *)

let rec print_stmt p s =
  match s with
  | Sskip ->
      fprintf p "/*skip*/;"
  | Sdo e ->
      fprintf p "%a;" print_expr e
  | Ssequence(s1, s2) ->
      fprintf p "%a@ %a" print_stmt s1 print_stmt s2
  | Sifthenelse(e, s1, Sskip) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>}@]"
              print_expr e
              print_stmt s1
  | Sifthenelse(e, s1, s2) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>} else {@ %a@;<0 -2>}@]"
              print_expr e
              print_stmt s1
              print_stmt s2
  | Swhile(e, s) ->
      fprintf p "@[<v 2>while (%a) {@ %a@;<0 -2>}@]"
              print_expr e
              print_stmt s
  | Sdowhile(e, s) ->
      fprintf p "@[<v 2>do {@ %a@;<0 -2>} while(%a);@]"
              print_stmt s
              print_expr e
  | Sfor(s_init, e, s_iter, s_body) ->
      fprintf p "@[<v 2>for (@[<hv 0>%a;@ %a;@ %a) {@]@ %a@;<0 -2>}@]"
              print_stmt_for s_init
              print_expr e
              print_stmt_for s_iter
              print_stmt s_body
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
  | Sdo e ->
      print_expr p e
  | Ssequence(s1, s2) ->
      fprintf p "%a, %a" print_stmt_for s1 print_stmt_for s2
  | _ ->
      fprintf p "({ %a })" print_stmt s

let name_function_parameters fun_name params =
  let b = Buffer.create 20 in
  Buffer.add_string b fun_name;
  Buffer.add_char b '(';
  begin match params with
  | [] ->
      Buffer.add_string b "void"
  | _ ->
      let rec add_params first = function
      | [] -> ()
      | (id, ty) :: rem ->
          if not first then Buffer.add_string b ", ";
          Buffer.add_string b (name_cdecl (extern_atom id) ty);
          add_params false rem in
      add_params true params
  end;
  Buffer.add_char b ')';
  Buffer.contents b

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

let string_of_init id =
  let b = Buffer.create (List.length id) in
  let add_init = function
  | Init_int8 n ->
      let c = Int32.to_int (camlint_of_coqint n) in
      if c >= 32 && c <= 126 && c <> Char.code '\"' && c <> Char.code '\\'
      then Buffer.add_char b (Char.chr c)
      else Buffer.add_string b (Printf.sprintf "\\%03o" c)
  | _ ->
      assert false
  in List.iter add_init id; Buffer.contents b

let chop_last_nul id =
  match List.rev id with
  | Init_int8 Z.Z0 :: tl -> List.rev tl
  | _ -> id

let print_init p = function
  | Init_int8 n -> fprintf p "%ld,@ " (camlint_of_coqint n)
  | Init_int16 n -> fprintf p "%ld,@ " (camlint_of_coqint n)
  | Init_int32 n -> fprintf p "%ld,@ " (camlint_of_coqint n)
  | Init_int64 n -> fprintf p "%Ld,@ " (camlint64_of_coqint n)
  | Init_float32 n -> fprintf p "%F,@ " (camlfloat_of_coqfloat n)
  | Init_float64 n -> fprintf p "%F,@ " (camlfloat_of_coqfloat n)
  | Init_space n -> fprintf p "/* skip %ld, */@ " (camlint_of_coqint n)
  | Init_addrof(symb, ofs) ->
      let ofs = camlint_of_coqint ofs in
      if ofs = 0l
      then fprintf p "&%s,@ " (extern_atom symb)
      else fprintf p "(void *)((char *)&%s + %ld),@ " (extern_atom symb) ofs

let re_string_literal = Str.regexp "__stringlit_[0-9]+"

let print_globvar p id v =
  let name1 = extern_atom id in
  let name2 = if v.gvar_readonly then "const " ^ name1 else name1 in
  let name3 = if v.gvar_volatile then "volatile " ^ name2 else name2 in
  match v.gvar_init with
  | [] ->
      fprintf p "extern %s;@ @ "
              (name_cdecl name3 v.gvar_info)
  | [Init_space _] ->
      fprintf p "%s;@ @ "
              (name_cdecl name3 v.gvar_info)
  | _ ->
      fprintf p "@[<hov 2>%s = "
              (name_cdecl name3 v.gvar_info);
      if Str.string_match re_string_literal (extern_atom id) 0
      && List.for_all (function Init_int8 _ -> true | _ -> false) v.gvar_init
      then
        fprintf p "\"%s\"" (string_of_init (chop_last_nul v.gvar_init))
      else begin
        fprintf p "{@ ";
        List.iter (print_init p) v.gvar_init;
        fprintf p "}"
      end;
      fprintf p ";@]@ @ "

let print_globdef p (id, gd) =
  match gd with
  | Gfun f -> print_fundef p id f
  | Gvar v -> print_globvar p id v

(* Collect struct and union types *)

let rec collect_type = function
  | Tvoid -> ()
  | Tint _ -> ()
  | Tfloat _ -> ()
  | Tlong _ -> ()
  | Tpointer(t, _) -> collect_type t
  | Tarray(t, _, _) -> collect_type t
  | Tfunction(args, res) -> collect_type_list args; collect_type res
  | Tstruct(id, fld, _) | Tunion(id, fld, _) ->
      let s = extern_atom id in
      if not (StructUnion.mem s !struct_unions) then begin
        struct_unions := StructUnion.add s fld !struct_unions;
        collect_fields fld
      end
  | Tcomp_ptr _ -> ()

and collect_type_list = function
  | Tnil -> ()
  | Tcons(hd, tl) -> collect_type hd; collect_type_list tl

and collect_fields = function
  | Fnil -> ()
  | Fcons(id, hd, tl) -> collect_type hd; collect_fields tl

let rec collect_expr e =
  collect_type (typeof e);
  match e with
  | Eloc _ -> assert false
  | Evar _ -> ()
  | Ederef(r, _) -> collect_expr r
  | Efield(l, _, _) -> collect_expr l
  | Eval _ -> ()
  | Evalof(l, _) -> collect_expr l
  | Eaddrof(l, _) -> collect_expr l
  | Eunop(_, r, _) -> collect_expr r
  | Ebinop(_, r1, r2, _) -> collect_expr r1; collect_expr r2
  | Ecast(r, _) -> collect_expr r
  | Eseqand(r1, r2, _) -> collect_expr r1; collect_expr r2
  | Eseqor(r1, r2, _) -> collect_expr r1; collect_expr r2
  | Econdition(r1, r2, r3, _) -> 
      collect_expr r1; collect_expr r2; collect_expr r3
  | Esizeof(ty, _) -> collect_type ty
  | Ealignof(ty, _) -> collect_type ty
  | Eassign(l, r, _) -> collect_expr l; collect_expr r
  | Eassignop(_, l, r, _, _) -> collect_expr l; collect_expr r
  | Epostincr(_, l, _) -> collect_expr l
  | Ecomma(r1, r2, _) -> collect_expr r1; collect_expr r2
  | Ecall(r1, rl, _) ->  collect_expr r1; collect_exprlist rl
  | Ebuiltin(_, _, rl, _) -> collect_exprlist rl
  | Eparen _ -> assert false

and collect_exprlist = function
  | Enil -> ()
  | Econs(r1, rl) ->  collect_expr r1; collect_exprlist rl

let rec collect_stmt = function
  | Sskip -> ()
  | Sdo e -> collect_expr e
  | Ssequence(s1, s2) -> collect_stmt s1; collect_stmt s2
  | Sifthenelse(e, s1, s2) -> collect_expr e; collect_stmt s1; collect_stmt s2
  | Swhile(e, s) -> collect_expr e; collect_stmt s
  | Sdowhile(e, s) -> collect_stmt s; collect_expr e
  | Sfor(s_init, e, s_iter, s_body) ->
      collect_stmt s_init; collect_expr e;
      collect_stmt s_iter; collect_stmt s_body
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
  collect_stmt f.fn_body

let collect_globdef (id, gd) =
  match gd with
  | Gfun(External(_, args, res)) -> collect_type_list args; collect_type res
  | Gfun(Internal f) -> collect_function f
  | Gvar v -> collect_type v.gvar_info

let collect_program p =
  List.iter collect_globdef p.prog_defs

let declare_struct_or_union p name fld =
  fprintf p "%s;@ @ " name

let print_struct_or_union p name fld =
  fprintf p "@[<v 2>%s {" name;
  let rec print_fields = function
  | Fnil -> ()
  | Fcons(id, ty, rem) ->
      fprintf p "@ %s;" (name_cdecl (extern_atom id) ty);
      print_fields rem in
  print_fields fld;
  fprintf p "@;<0 -2>};@]@ @ "

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
