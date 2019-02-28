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

open Format
open Camlcoq
open Values
open AST
open Ctypes
open Cop
open Csyntax

let name_unop = function
  | Onotbool -> "!"
  | Onotint  -> "~"
  | Oneg     -> "-"
  | Oabsfloat -> "__builtin_fabs"

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
  | Cop.One  -> "!="
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

(* Declarator (identifier + type) *)

let attributes a =
  let s1 = if a.attr_volatile then " volatile" else "" in
  match a.attr_alignas with
  | None -> s1
  | Some l ->
      sprintf " _Alignas(%Ld)%s" (Int64.shift_left 1L (N.to_int l)) s1

let attributes_space a =
  let s = attributes a in
  if String.length s = 0 then s else s ^ " "

let name_optid id =
  if id = "" then "" else " " ^ id

let rec name_cdecl id ty =
  match ty with
  | Tvoid ->
      "void" ^ name_optid id
  | Ctypes.Tint(sz, sg, a) ->
      name_inttype sz sg ^ attributes a ^ name_optid id
  | Ctypes.Tfloat(sz, a) ->
      name_floattype sz ^ attributes a ^ name_optid id
  | Ctypes.Tlong(sg, a) ->
      name_longtype sg ^ attributes a ^ name_optid id
  | Tpointer(t, a) ->
      let id' =
        match t with
        | Tfunction _ | Tarray _ -> sprintf "(*%s%s)" (attributes_space a) id
        | _                      -> sprintf "*%s%s" (attributes_space a) id in
      name_cdecl id' t
  | Tarray(t, n, a) ->
      name_cdecl (sprintf "%s[%ld]" id (camlint_of_coqint n)) t
  | Tfunction(args, res, cconv) ->
      let b = Buffer.create 20 in
      if id = ""
      then Buffer.add_string b "(*)"
      else Buffer.add_string b id;
      Buffer.add_char b '(';
      let rec add_args first = function
      | Tnil ->
          if first then
            Buffer.add_string b
               (if cconv.cc_vararg then "..." else "void")
          else if cconv.cc_vararg then
            Buffer.add_string b ", ..."
          else
            ()
      | Tcons(t1, tl) ->
          if not first then Buffer.add_string b ", ";
          Buffer.add_string b (name_cdecl "" t1);
          add_args false tl in
      if not cconv.cc_unproto then add_args true args;
      Buffer.add_char b ')';
      name_cdecl (Buffer.contents b) res
  | Tstruct(name, a) ->
      "struct " ^ extern_atom name ^ attributes a ^ name_optid id
  | Tunion(name, a) ->
      "union " ^ extern_atom name ^ attributes a ^ name_optid id

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
  | Ebinop((Oeq|Cop.One), _, _, _) -> (9, LtoR)
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

let print_typed_value p v ty =
  match v, ty with
  | Vint n, Ctypes.Tint(I32, Unsigned, _) ->
      fprintf p "%luU" (camlint_of_coqint n)
  | Vint n, _ ->
      fprintf p "%ld" (camlint_of_coqint n)
  | Vfloat f, _ ->
      fprintf p "%.15F" (camlfloat_of_coqfloat f)
  | Vsingle f, _ ->
      fprintf p "%.15Ff" (camlfloat_of_coqfloat32 f)
  | Vlong n, Ctypes.Tlong(Unsigned, _) ->
      fprintf p "%LuLLU" (camlint64_of_coqint n)
  | Vlong n, _ ->
      fprintf p "%LdLL" (camlint64_of_coqint n)
  | Vptr(b, ofs), _ ->
      fprintf p "<ptr%a>" !print_pointer_hook (b, ofs)
  | Vundef, _ ->
      fprintf p "<undef>"

let print_value p v = print_typed_value p v Tvoid

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
  | Eval(v, ty) ->
      print_typed_value p v ty
  | Esizeof(ty, _) ->
      fprintf p "sizeof(%s)" (name_type ty)
  | Ealignof(ty, _) ->
      fprintf p "__alignof__(%s)" (name_type ty)
  | Eunop(Oabsfloat, a1, _) ->
      fprintf p "__builtin_fabs(%a)" expr (2, a1)
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
  | Eassign(res, Ebuiltin(EF_inline_asm(txt, sg, clob), _, args, _), _) ->
      extended_asm p txt (Some res) args clob
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
  | Ebuiltin(EF_annot(_,txt, _), _, args, _) ->
      fprintf p "__builtin_annot@[<hov 1>(%S%a)@]"
                (camlstring_of_coqstring txt) exprlist (false, args)
  | Ebuiltin(EF_annot_val(_,txt, _), _, args, _) ->
      fprintf p "__builtin_annot_intval@[<hov 1>(%S%a)@]"
                (camlstring_of_coqstring txt) exprlist (false, args)
  | Ebuiltin(EF_external(id, sg), _, args, _) ->
      fprintf p "%s@[<hov 1>(%a)@]" (camlstring_of_coqstring id) exprlist (true, args)
  | Ebuiltin(EF_runtime(id, sg), _, args, _) ->
      fprintf p "%s@[<hov 1>(%a)@]" (camlstring_of_coqstring id) exprlist (true, args)
  | Ebuiltin(EF_inline_asm(txt, sg, clob), _, args, _) ->
      extended_asm p txt None args clob
  | Ebuiltin(EF_debug(kind,txt,_),_,args,_) ->
      fprintf p "__builtin_debug@[<hov 1>(%d,%S%a)@]"
        (P.to_int kind) (extern_atom txt) exprlist (false,args)
  | Ebuiltin(_, _, args, _) ->
      fprintf p "<unknown builtin>@[<hov 1>(%a)@]" exprlist (true, args)
  | Eparen(a1, tycast, ty) ->
      fprintf p "(%s) %a" (name_type tycast) expr (prec', a1)
  end;
  if prec' < prec then fprintf p ")@]" else fprintf p "@]"

and exprlist p (first, rl) =
  match rl with
  | Enil -> ()
  | Econs(r, rl) ->
      if not first then fprintf p ",@ ";
      expr p (2, r);
      exprlist p (false, rl)

and extended_asm p txt res args clob =
  fprintf p "asm volatile (@[<hv 0>%S" (camlstring_of_coqstring txt);
  fprintf p "@ :";
  begin match res with
  | None -> ()
  | Some e -> fprintf p " \"=r\"(%a)" expr (0, e)
  end;
  let rec inputs p (first, el) =
    match el with
    | Enil -> ()
    | Econs(e1, el) ->
        if not first then fprintf p ",@ ";
        fprintf p "\"r\"(%a)" expr (0, e1);
        inputs p (false, el) in
  fprintf p "@ : @[<hov 0>%a@]" inputs (true, args);
  begin match clob with
  | [] -> ()
  | c1 :: cl ->
      fprintf p "@ : @[<hov 0>%S" (camlstring_of_coqstring c1);
      List.iter
        (fun c -> fprintf p ",@ %S" (camlstring_of_coqstring c))
        cl;
      fprintf p "@]"
  end;
  fprintf p ")@]"

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
  | LSnil ->
      ()
  | LScons(lbl, Sskip, rem) ->
      fprintf p "%a:@ %a"
              print_case_label lbl
              print_cases rem
  | LScons(lbl, s, rem) ->
      fprintf p "@[<v 2>%a:@ %a@]@ %a"
              print_case_label lbl
              print_stmt s
              print_cases rem

and print_case_label p = function
  | None -> fprintf p "default"
  | Some lbl -> fprintf p "case %s" (Z.to_string lbl)

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

let name_function_parameters fun_name params cconv =
  let b = Buffer.create 20 in
  Buffer.add_string b fun_name;
  Buffer.add_char b '(';
  begin match params with
  | [] ->
      Buffer.add_string b (if cconv.cc_vararg then "..." else "void")
  | _ ->
      let rec add_params first = function
      | [] ->
          if cconv.cc_vararg then Buffer.add_string b ",..."
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
                                                  f.fn_params f.fn_callconv)
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
  | Ctypes.External((EF_external _ | EF_runtime _| EF_malloc | EF_free), args, res, cconv) ->
      fprintf p "extern %s;@ @ "
                (name_cdecl (extern_atom id) (Tfunction(args, res, cconv)))
  | Ctypes.External(_, _, _, _) ->
      ()
  | Ctypes.Internal f ->
      print_function p id f

let print_fundecl p id fd =
  match fd with
  | Ctypes.Internal f ->
      let linkage = if C2C.atom_is_static id then "static" else "extern" in
      fprintf p "%s %s;@ @ " linkage
                (name_cdecl (extern_atom id) (Csyntax.type_of_function f))
  | _ -> ()

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
  | Init_int8 n -> fprintf p "%ld" (camlint_of_coqint n)
  | Init_int16 n -> fprintf p "%ld" (camlint_of_coqint n)
  | Init_int32 n -> fprintf p "%ld" (camlint_of_coqint n)
  | Init_int64 n -> fprintf p "%LdLL" (camlint64_of_coqint n)
  | Init_float32 n -> fprintf p "%.15F" (camlfloat_of_coqfloat n)
  | Init_float64 n -> fprintf p "%.15F" (camlfloat_of_coqfloat n)
  | Init_space n -> fprintf p "/* skip %s */@ " (Z.to_string n)
  | Init_addrof(symb, ofs) ->
      let ofs = camlint_of_coqint ofs in
      if ofs = 0l
      then fprintf p "&%s" (extern_atom symb)
      else fprintf p "(void *)((char *)&%s + %ld)" (extern_atom symb) ofs

let print_composite_init p il =
  fprintf p "{@ ";
  List.iter
    (fun i ->
      print_init p i;
      match i with Init_space _ -> () | _ -> fprintf p ",@ ")
    il;
  fprintf p "}"

let re_string_literal = Str.regexp "__stringlit_[0-9]+"

let print_globvar p id v =
  let name1 = extern_atom id in
  let name2 = if v.gvar_readonly then "const " ^ name1 else name1 in
  match v.gvar_init with
  | [] ->
      fprintf p "extern %s;@ @ "
              (name_cdecl name2 v.gvar_info)
  | [Init_space _] ->
      fprintf p "%s;@ @ "
              (name_cdecl name2 v.gvar_info)
  | _ ->
      fprintf p "@[<hov 2>%s = "
              (name_cdecl name2 v.gvar_info);
      begin match v.gvar_info, v.gvar_init with
      | (Ctypes.Tint _ | Ctypes.Tlong _ | Ctypes.Tfloat _ | Tpointer _ | Tfunction _),
        [i1] ->
          print_init p i1
      | _, il ->
          if Str.string_match re_string_literal (extern_atom id) 0
          && List.for_all (function Init_int8 _ -> true | _ -> false) il
          then fprintf p "\"%s\"" (string_of_init (chop_last_nul il))
          else print_composite_init p il
      end;
      fprintf p ";@]@ @ "

let print_globvardecl p  id v =
  let name = extern_atom id in
  let name = if v.gvar_readonly then "const "^name else name in
  let linkage = if C2C.atom_is_static id then "static" else "extern" in
  fprintf p "%s %s;@ @ " linkage (name_cdecl name v.gvar_info)

let print_globdecl p (id,gd) =
  match gd with
  | Gfun f -> print_fundecl p id f
  | Gvar v -> print_globvardecl p id v

let print_globdef p (id, gd) =
  match gd with
  | Gfun f -> print_fundef p id f
  | Gvar v -> print_globvar p id v

let struct_or_union = function Struct -> "struct" | Union -> "union"

let declare_composite p (Composite(id, su, m, a)) =
  fprintf p "%s %s;@ " (struct_or_union su) (extern_atom id)

let define_composite p (Composite(id, su, m, a)) =
  fprintf p "@[<v 2>%s %s%s {"
          (struct_or_union su) (extern_atom id) (attributes a);
  List.iter
    (fun (fid, fty) ->
      fprintf p "@ %s;" (name_cdecl (extern_atom fid) fty))
    m;
  fprintf p "@;<0 -2>};@]@ @ "

let print_program p prog =
  fprintf p "@[<v 0>";
  List.iter (declare_composite p) prog.prog_types;
  List.iter (define_composite p) prog.prog_types;
  List.iter (print_globdecl p) prog.Ctypes.prog_defs;
  List.iter (print_globdef p) prog.Ctypes.prog_defs;
  fprintf p "@]@."

let destination : string option ref = ref None

let print_if prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_program (formatter_of_out_channel oc) prog;
      close_out oc
