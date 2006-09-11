(** Pretty-printer for Csyntax *)

open Format
open Camlcoq
open CList
open Datatypes
open AST
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

let name_floattype sz =
  match sz with
  | F32 -> "float"
  | F64 -> "double"

(* Collecting the names and fields of structs and unions *)

module StructUnionSet = Set.Make(struct
  type t = string * fieldlist
  let compare = (compare: t -> t -> int)
end)

let struct_unions = ref StructUnionSet.empty

let register_struct_union id fld =
  struct_unions := StructUnionSet.add (extern_atom id, fld) !struct_unions

(* Declarator (identifier + type) *)

let name_optid id =
  if id = "" then "" else " " ^ id

let parenthesize_if_pointer id =
  if String.length id > 0 && id.[0] = '*' then "(" ^ id ^ ")" else id

let rec name_cdecl id ty =
  match ty with
  | Tvoid ->
      "void" ^ name_optid id
  | Tint(sz, sg) ->
      name_inttype sz sg ^ name_optid id
  | Tfloat sz ->
      name_floattype sz ^ name_optid id
  | Tpointer t ->
      name_cdecl ("*" ^ id) t
  | Tarray(t, n) ->
      name_cdecl
        (sprintf "%s[%ld]" (parenthesize_if_pointer id) (camlint_of_coqint n))
        t
  | Tfunction(args, res) ->
      let b = Buffer.create 20 in
      if id = ""
      then Buffer.add_string b "(*)"
      else Buffer.add_string b (parenthesize_if_pointer id);
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
  | Tstruct(name, fld) ->
      extern_atom name ^ name_optid id
  | Tunion(name, fld) ->
      extern_atom name ^ name_optid id
  | Tcomp_ptr name ->
      extern_atom name ^ " *" ^ id

(* Type *)

let name_type ty = name_cdecl "" ty

(* Expressions *)

let parenthesis_level (Expr (e, ty)) =
  match e with
  | Econst_int _ -> 0
  | Econst_float _ -> 0
  | Evar _ -> 0
  | Eunop(_, _) -> 30
  | Ederef _ -> 20
  | Eaddrof _ -> 30
  | Ebinop(op, _, _) ->
      begin match op with
      | Oand | Oor | Oxor -> 75
      | Oeq | One | Olt | Ogt | Ole | Oge -> 70
      | Oadd | Osub | Oshl | Oshr -> 60
      | Omul | Odiv | Omod -> 40
      end
  | Ecast _ -> 30
  | Eindex(_, _) -> 20
  | Ecall(_, _) -> 20
  | Eandbool(_, _) -> 80
  | Eorbool(_, _) -> 80
  | Esizeof _ -> 20
  | Efield _ -> 20

let rec print_expr p (Expr (eb, ty) as e) =
  let level = parenthesis_level e in
  match eb with
  | Econst_int n ->
      fprintf p "%ld" (camlint_of_coqint n)
  | Econst_float f ->
      fprintf p "%F" f
  | Evar id ->
      fprintf p "%s" (extern_atom id)
  | Eunop(op, e1) ->
      fprintf p "%s%a" (name_unop op) print_expr_prec (level, e1)
  | Ederef e ->
      fprintf p "*%a" print_expr_prec (level, e)
  | Eaddrof e ->
      fprintf p "&%a" print_expr_prec (level, e)
  | Ebinop(op, e1, e2) ->
      fprintf p "@[<hov 0>%a@ %s %a@]"
                print_expr_prec (level, e1)
                (name_binop op)
                print_expr_prec (level, e2)
  | Ecast(ty, e1) ->
      fprintf p "@[<hov 2>(%s)@,%a@]"
                (name_type ty)
                print_expr_prec (level, e1)
  | Eindex(e1, e2) ->
      fprintf p "@[<hov 2>%a@,[%a]@]"
                print_expr_prec (level, e1)
                print_expr_prec (level, e2)
  | Ecall(e1, el) ->
      fprintf p "@[<hov 2>%a@,(@[<hov 0>%a@])@]"
                print_expr_prec (level, e1)
                print_expr_list (true, el)
  | Eandbool(e1, e2) ->
      fprintf p "@[<hov 0>%a@ && %a@]"
                print_expr_prec (level, e1)
                print_expr_prec (level, e2)
  | Eorbool(e1, e2) ->
      fprintf p "@[<hov 0>%a@ || %a@]"
                print_expr_prec (level, e1)
                print_expr_prec (level, e2)
  | Esizeof ty ->
      fprintf p "sizeof(%s)" (name_type ty)
  | Efield(e1, id) ->
      fprintf p "%a.%s" print_expr_prec (level, e1) (extern_atom id)

and print_expr_prec p (context_prec, e) =
  let this_prec = parenthesis_level e in
  if this_prec >= context_prec
  then fprintf p "(%a)" print_expr e
  else print_expr p e

and print_expr_list p (first, el) =
  match el with
  | Enil -> ()
  | Econs(e1, et) ->
      if not first then fprintf p ",@ ";
      print_expr p e1;
      print_expr_list p (false, et)

let rec print_stmt p s =
  match s with
  | Sskip ->
      fprintf p "/*skip*/;"
  | Sexpr e ->
      fprintf p "%a;" print_expr e
  | Sassign(e1, e2) ->
      fprintf p "@[<hv 2>%a =@ %a;@]" print_expr e1 print_expr e2
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
  | Sexpr e ->
      fprintf p "%a" print_expr e
  | Sassign(e1, e2) ->
      fprintf p "%a = %a" print_expr e1 print_expr e2
  | Ssequence(s1, s2) ->
      fprintf p "%a, %a" print_stmt_for s1 print_stmt_for s2
  | _ ->
      fprintf p "<impossible>"

let name_function_parameters fun_name params =
  let b = Buffer.create 20 in
  Buffer.add_string b fun_name;
  Buffer.add_char b '(';
  begin match params with
  | Coq_nil ->
      Buffer.add_string b "void"
  | _ ->
      let rec add_params first = function
      | Coq_nil -> ()
      | Coq_cons(Coq_pair(id, ty), rem) ->
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
  coqlist_iter
    (fun (Coq_pair(id, ty)) ->
      fprintf p "%s;@ " (name_cdecl (extern_atom id) ty))
    f.fn_vars;
  print_stmt p f.fn_body;
  fprintf p "@;<0 -2>}@]@ @ "

let print_fundef p (Coq_pair(id, fd)) =
  match fd with
  | External(_, args, res) ->
      fprintf p "extern %s;@ @ "
                (name_cdecl (extern_atom id) (Tfunction(args, res)))
  | Internal f ->
      print_function p id f

let print_init p = function
  | Init_int8 n -> fprintf p "%ld,@ " (camlint_of_coqint n)
  | Init_int16 n -> fprintf p "%ld,@ " (camlint_of_coqint n)
  | Init_int32 n -> fprintf p "%ld,@ " (camlint_of_coqint n)
  | Init_float32 n -> fprintf p "%F,@ " n
  | Init_float64 n -> fprintf p "%F,@ " n
  | Init_space n -> fprintf p "/* skip %ld*/@ " (camlint_of_coqint n)

let print_globvar p (Coq_pair(Coq_pair(id, init), ty)) =
  match init with
  | Coq_nil ->
      fprintf p "extern %s;@ @ "
              (name_cdecl (extern_atom id) ty)
  | Coq_cons(Init_space _, Coq_nil) ->
      fprintf p "%s;@ @ "
              (name_cdecl (extern_atom id) ty)
  | _ ->
      fprintf p "@[<hov 2>%s = {@ "
              (name_cdecl (extern_atom id) ty);
      coqlist_iter (print_init p) init;
      fprintf p "};@]@ @ "

(* Collect struct and union types *)

let rec collect_type = function
  | Tvoid -> ()
  | Tint(sz, sg) -> ()
  | Tfloat sz -> ()
  | Tpointer t -> collect_type t
  | Tarray(t, n) -> collect_type t
  | Tfunction(args, res) -> collect_type_list args; collect_type res
  | Tstruct(id, fld) -> register_struct_union id fld; collect_fields fld
  | Tunion(id, fld) -> register_struct_union id fld; collect_fields fld
  | Tcomp_ptr _ -> ()

and collect_type_list = function
  | Tnil -> ()
  | Tcons(hd, tl) -> collect_type hd; collect_type_list tl

and collect_fields = function
  | Fnil -> ()
  | Fcons(id, hd, tl) -> collect_type hd; collect_fields tl

let rec collect_expr (Expr(ed, ty)) =
  match ed with
  | Econst_int n -> ()
  | Econst_float f -> ()
  | Evar id -> ()
  | Eunop(op, e1) -> collect_expr e1
  | Ederef e -> collect_expr e
  | Eaddrof e -> collect_expr e
  | Ebinop(op, e1, e2) -> collect_expr e1; collect_expr e2
  | Ecast(ty, e1) -> collect_type ty; collect_expr e1
  | Eindex(e1, e2) -> collect_expr e1; collect_expr e2
  | Ecall(e1, el) -> collect_expr e1; collect_expr_list el
  | Eandbool(e1, e2) -> collect_expr e1; collect_expr e2
  | Eorbool(e1, e2) -> collect_expr e1; collect_expr e2
  | Esizeof ty -> collect_type ty
  | Efield(e1, id) -> collect_expr e1

and collect_expr_list = function
  | Enil -> ()
  | Econs(hd, tl) -> collect_expr hd; collect_expr_list tl

let rec collect_stmt = function
  | Sskip -> ()
  | Sexpr e -> collect_expr e
  | Sassign(e1, e2) -> collect_expr e1; collect_expr e2
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

and collect_cases = function
  | LSdefault s -> collect_stmt s
  | LScase(lbl, s, rem) -> collect_stmt s; collect_cases rem

let collect_function f =
  collect_type f.fn_return;
  coqlist_iter (fun (Coq_pair(id, ty)) -> collect_type ty) f.fn_params;
  coqlist_iter (fun (Coq_pair(id, ty)) -> collect_type ty) f.fn_vars;
  collect_stmt f.fn_body

let collect_fundef (Coq_pair(id, fd)) =
  match fd with
  | External(_, args, res) -> collect_type_list args; collect_type res
  | Internal f -> collect_function f

let collect_globvar (Coq_pair(Coq_pair(id, init), ty)) =
  collect_type ty

let collect_program p =
  coqlist_iter collect_globvar p.prog_vars;
  coqlist_iter collect_fundef p.prog_funct

let declare_struct_or_union p (name, fld) =
  fprintf p "%s;@ @ " name

let print_struct_or_union p (name, fld) =
  fprintf p "@[<v 2>%s {" name;
  let rec print_fields = function
  | Fnil -> ()
  | Fcons(id, ty, rem) ->
      fprintf p "@ %s;" (name_cdecl (extern_atom id) ty);
      print_fields rem in
  print_fields fld;
  fprintf p "@;<0 -2>};@]@ "

let print_program p prog =
  struct_unions := StructUnionSet.empty;
  collect_program prog;
  fprintf p "@[<v 0>";
  StructUnionSet.iter (declare_struct_or_union p) !struct_unions;
  StructUnionSet.iter (print_struct_or_union p) !struct_unions;
  coqlist_iter (print_globvar p) prog.prog_vars;
  coqlist_iter (print_fundef p) prog.prog_funct;
  fprintf p "@]@."


