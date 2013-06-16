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

(** Export Clight as a Coq file *)

open Format
open Camlcoq
open Datatypes
open Values
open AST
open Ctypes
open Cop
open Clight

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

(* Identifiers *)

exception Not_an_identifier

let sanitize s =
  let s' = String.create (String.length s) in
  for i = 0 to String.length s - 1 do
    s'.[i] <-
      match s.[i] with
      | 'A'..'Z' | 'a'..'z' | '0'..'9' | '_' as c -> c
      | ' ' | '$' -> '_'
      | _ -> raise Not_an_identifier
  done;
  s'

module StringSet = Set.Make(String)

let temp_names : (ident, string) Hashtbl.t = Hashtbl.create 17
let all_temp_names : StringSet.t ref = ref StringSet.empty

let ident p id =
  try
    let s = Hashtbl.find string_of_atom id in
    fprintf p "_%s" (sanitize s)
  with Not_found | Not_an_identifier ->
  try
    let s = Hashtbl.find temp_names id in
    fprintf p "%s" s
  with Not_found ->
    fprintf p "%ld%%positive" (P.to_int32 id)

let define_idents p =
  Hashtbl.iter
    (fun id name ->
      try
        fprintf p "Definition _%s : ident := %ld%%positive.@ "
                  (sanitize name) (P.to_int32 id)
      with Not_an_identifier ->
        ())
    string_of_atom;
  Hashtbl.iter
    (fun id name ->
      fprintf p "Definition %s : ident := %ld%%positive.@ "
                name (P.to_int32 id))
    temp_names;
  fprintf p "@ "

let rec find_temp_name name counter =
  let name' =
    if counter = 0 then name ^ "'" else sprintf "%s'%d" name counter in
  if StringSet.mem name' !all_temp_names
  then find_temp_name name (counter + 1)
  else name'

let name_temporary t v =
  (* Try to give "t" a name that is the name of "v" with a prime
     plus a number to disambiguate if needed. *)
  if not (Hashtbl.mem string_of_atom t || Hashtbl.mem temp_names t) then begin
    try
      let vname = "_" ^ sanitize (Hashtbl.find string_of_atom v) in
      let tname = find_temp_name vname 0 in
      Hashtbl.add temp_names t tname;
      all_temp_names := StringSet.add tname !all_temp_names
    with Not_found | Not_an_identifier ->
      ()
  end

(* Numbers *)

let coqint p n =
  let n = camlint_of_coqint n in
  if n >= 0l
  then fprintf p "(Int.repr %ld)" n
  else fprintf p "(Int.repr (%ld))" n

let coqfloat p n =
  let n = camlint64_of_coqint(Floats.Float.bits_of_double n) in
  if n >= 0L
  then fprintf p "(Float.double_of_bits (Int64.repr %Ld))" n
  else fprintf p "(Float.double_of_bits (Int64.repr (%Ld)))" n

let coqint64 p n =
  let n = camlint64_of_coqint n in
  if n >= 0L
  then fprintf p "(Int64.repr %Ld)" n
  else fprintf p "(Int64.repr (%Ld))" n

(* Types *)

let use_struct_names = ref true

let rec typ p t =
  let a = attr_of_type t in
  if a (*.attr_volatile*)
  then fprintf p "(tvolatile %a)" rtyp t
  else rtyp p t

and rtyp p = function
  | Tvoid -> fprintf p "tvoid"
  | Tint(sz, sg, _) ->
      fprintf p "%s" (
        match sz, sg with
        | I8, Signed -> "tschar"
        | I8, Unsigned -> "tuchar"
        | I16, Signed -> "tshort"
        | I16, Unsigned -> "tushort"
        | I32, Signed -> "tint"
        | I32, Unsigned -> "tuint"
        | IBool, _ -> "tbool")
  | Tlong(sg, _) ->
      fprintf p "%s" (
        match sg with
        | Signed -> "tlong"
        | Unsigned -> "tulong")
  | Tfloat(sz, _) ->
      fprintf p "%s" (
        match sz with
        | F32 -> "tfloat"
        | F64 -> "tdouble")
  | Tpointer(t, _) ->
      fprintf p "(tptr %a)" typ t
  | Tarray(t, sz, _) ->
      fprintf p "(tarray %a %ld)" typ t (Z.to_int32 sz)
  | Tfunction(targs, tres) ->
      fprintf p "@[<hov 2>(Tfunction@ %a@ %a)@]" typlist targs typ tres
  | Tstruct(id, flds, _) ->
      if !use_struct_names
      then fprintf p "t%a" ident id
      else fprintf p "@[<hov 2>(Tstruct %a@ %a@ noattr)@]" ident id fieldlist flds
  | Tunion(id, flds, _) ->
      if !use_struct_names
      then fprintf p "t%a" ident id
      else fprintf p "@[<hov 2>(Tunion %a@ %a@ noattr)@]" ident id fieldlist flds
  | Tcomp_ptr(id, _) ->
      fprintf p "(Tcomp_ptr %a noattr)" ident id

and typlist p = function
  | Tnil ->
      fprintf p "Tnil"
  | Tcons(t, tl) ->
      fprintf p "@[<hov 2>(Tcons@ %a@ %a)@]" typ t typlist tl

and fieldlist p = function
  | Fnil ->
      fprintf p "Fnil"
  | Fcons(id, t, fl) ->
      fprintf p "@[<hov 2>(Fcons %a@ %a@ %a)@]" ident id typ t fieldlist fl

(* External functions *)

let asttype p t =
  fprintf p "%s"
     (match t with
      | AST.Tint -> "AST.Tint"
      | AST.Tfloat -> "AST.Tfloat"
      | AST.Tlong -> "AST.Tlong"
      | AST.Tsingle -> "AST.Tsingle")

let name_of_chunk = function
  | Mint8signed -> "Mint8signed"
  | Mint8unsigned -> "Mint8unsigned"
  | Mint16signed -> "Mint16signed"
  | Mint16unsigned -> "Mint16unsigned"
  | Mint32 -> "Mint32"
  | Mint64 -> "Mint64"
  | Mfloat32 -> "Mfloat32"
  | Mfloat64 -> "Mfloat64"
  | Mfloat64al32 -> "Mfloat64al32"

let signatur p sg =
  fprintf p "@[<hov 2>(mksignature@ %a@ %a)@]" (print_list asttype) sg.sig_args (print_option asttype) sg.sig_res

let assertions = ref ([]: (ident * annot_arg list) list)

let annot_arg p = function
  | AA_arg ty ->
      fprintf p "AA_arg %a" asttype ty
  | AA_int n ->
      fprintf p "AA_int %a" coqint n
  | AA_float n ->
      fprintf p "AA_float %a" coqfloat n

let external_function p = function
  | EF_external(name, sg) ->
      fprintf p "@[<hov 2>(EF_external %a@ %a)@]" ident name signatur sg
  | EF_builtin(name, sg) ->
      fprintf p "@[<hov 2>(EF_builtin %a@ %a)@]" ident name signatur sg
  | EF_vload chunk ->
      fprintf p "(EF_vload %s)" (name_of_chunk chunk)
  | EF_vstore chunk ->
      fprintf p "(EF_vstore %s)" (name_of_chunk chunk)
  | EF_vload_global(chunk, id, ofs) ->
      fprintf p "(EF_vload_global %s %a %a)" (name_of_chunk chunk) ident id coqint ofs
  | EF_vstore_global(chunk, id, ofs) ->
      fprintf p "(EF_vstore_global %s %a %a)" (name_of_chunk chunk) ident id coqint ofs
  | EF_malloc -> fprintf p "EF_malloc"
  | EF_free -> fprintf p "EF_free"
  | EF_memcpy(sz, al) ->
      fprintf p "(EF_memcpy %ld %ld)" (Z.to_int32 sz) (Z.to_int32 al)
  | EF_annot(text, targs) -> 
      assertions := (text, targs) :: !assertions;
      fprintf p "(EF_annot %ld%%positive %a)" (P.to_int32 text) (print_list annot_arg) targs
  | EF_annot_val(text, targ) ->
      assertions := (text, [AA_arg targ]) :: !assertions;
      fprintf p "(EF_annot_val %ld%%positive %a)" (P.to_int32 text) asttype targ
  | EF_inline_asm(text) ->
      fprintf p "(EF_inline_asm %ld%%positive)" (P.to_int32 text)

(* Expressions *)

let name_unop = function
  | Onotbool -> "Onotbool"
  | Onotint -> "Onotint"
  | Oneg -> "Oneg"

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
  | One -> "One"
  | Olt -> "Olt"
  | Ogt -> "Ogt"
  | Ole -> "Ole"
  | Oge -> "Oge"

let rec expr p = function
  | Evar(id, t) ->
      fprintf p "(Evar %a %a)" ident id typ t
  | Etempvar(id, t) ->
      fprintf p "(Etempvar %a %a)" ident id typ t
  | Ederef(a1, t) ->
      fprintf p "@[<hov 2>(Ederef@ %a@ %a)@]" expr a1 typ t
  | Efield(a1, f, t) ->
      fprintf p "@[<hov 2>(Efield@ %a@ %a@ %a)@]" expr a1 ident f typ t
  | Econst_int(n, t) ->
      fprintf p "(Econst_int %a %a)" coqint n typ t
  | Econst_float(n, t) ->
      fprintf p "(Econst_float %a %a)" coqfloat n typ t
  | Econst_long(n, t) ->
      fprintf p "(Econst_long %a %a)" coqint64 n typ t
  | Eunop(op, a1, t) ->
      fprintf p "@[<hov 2>(Eunop %s@ %a@ %a)@]"
         (name_unop op) expr a1 typ t
  | Eaddrof(a1, t) ->
      fprintf p "@[<hov 2>(Eaddrof@ %a@ %a)@]" expr a1 typ t
  | Ebinop(op, a1, a2, t) ->
      fprintf p "@[<hov 2>(Ebinop %s@ %a@ %a@ %a)@]"
         (name_binop op) expr a1 expr a2 typ t
  | Ecast(a1, t) ->
      fprintf p "@[<hov 2>(Ecast@ %a@ %a)@]" expr a1 typ t

(* Statements *)

let rec stmt p = function
  | Sskip ->
      fprintf p "Sskip"
  | Sassign(e1, e2) ->
      fprintf p "@[<hov 2>(Sassign@ %a@ %a)@]" expr e1 expr e2
  | Sset(id, e2) ->
      fprintf p "@[<hov 2>(Sset %a@ %a)@]" ident id expr e2
  | Scall(optid, e1, el) ->
      fprintf p "@[<hov 2>(Scall %a@ %a@ %a)@]"
        (print_option ident) optid expr e1 (print_list expr) el
  | Sbuiltin(optid, ef, tyl, el) ->
      fprintf p "@[<hov 2>(Sbuiltin %a@ %a@ %a@ %a)@]"
        (print_option ident) optid 
        external_function ef
        typlist tyl
        (print_list expr) el
  | Ssequence(Sskip, s2) ->
      stmt p s2
  | Ssequence(s1, Sskip) ->
      stmt p s1
  | Ssequence(s1, s2) ->
      fprintf p "@[<hv 2>(Ssequence@ %a@ %a)@]" stmt s1 stmt s2
  | Sifthenelse(e, s1, s2) ->
      fprintf p "@[<hv 2>(Sifthenelse %a@ %a@ %a)@]" expr e stmt s1 stmt s2
  | Sloop (Ssequence (Sifthenelse(e, Sskip, Sbreak), s), Sskip) ->
      fprintf p "@[<hv 2>(Swhile@ %a@ %a)@]" expr e stmt s
  | Sloop (Ssequence (Ssequence(Sskip, Sifthenelse(e, Sskip, Sbreak)), s), Sskip) ->
      fprintf p "@[<hv 2>(Swhile@ %a@ %a)@]" expr e stmt s
  | Sloop(s1, s2) ->
      fprintf p "@[<hv 2>(Sloop@ %a@ %a)@]" stmt s1 stmt s2
  | Sbreak ->
      fprintf p "Sbreak"
  | Scontinue ->
      fprintf p "Scontinue"
  | Sswitch(e, cases) ->
      fprintf p "@[<hv 2>(Sswitch %a@ %a)@]" expr e lblstmts cases
  | Sreturn e ->
      fprintf p "@[<hv 2>(Sreturn %a)@]" (print_option expr) e
  | Slabel(lbl, s1) ->
      fprintf p "@[<hv 2>(Slabel %a@ %a)@]" ident lbl stmt s1
  | Sgoto lbl ->
      fprintf p "(Sgoto %a)" ident lbl

and lblstmts p = function
  | LSdefault s ->
      fprintf p "@[<hv 2>(LSdefault@ %a)@]" stmt s
  | LScase(lbl, s, ls) ->
      fprintf p "@[<hv 2>(LScase %a@ %a@ %a)@]" coqint lbl stmt s lblstmts ls

let print_function p (id, f) =
  fprintf p "Definition f_%s := {|@ " (extern_atom id);
  fprintf p "  fn_return := %a;@ " typ f.fn_return;
  fprintf p "  fn_params := %a;@ " (print_list (print_pair ident typ)) f.fn_params;
  fprintf p "  fn_vars := %a;@ " (print_list (print_pair ident typ)) f.fn_vars;
  fprintf p "  fn_temps := %a;@ " (print_list (print_pair ident typ)) f.fn_temps;
  fprintf p "  fn_body :=@ ";
  stmt p f.fn_body;
  fprintf p "@ |}.@ @ "

let init_data p = function
  | Init_int8 n -> fprintf p "Init_int8 %a" coqint n
  | Init_int16 n -> fprintf p "Init_int16 %a" coqint n
  | Init_int32 n -> fprintf p "Init_int32 %a" coqint n
  | Init_int64 n -> fprintf p "Init_int64 %a" coqint64 n
  | Init_float32 n -> fprintf p "Init_float32 %a" coqfloat n
  | Init_float64 n -> fprintf p "Init_float64 %a" coqfloat n
  | Init_space n -> fprintf p "Init_space %ld" (Z.to_int32 n)
  | Init_addrof(id,ofs) -> fprintf p "Init_addrof %a %a" ident id coqint ofs

let print_variable p (id, v) =
  fprintf p "Definition v_%s := {|@ " (extern_atom id);
  fprintf p "  gvar_info := %a;@ " typ v.gvar_info;
  fprintf p "  gvar_init := %a;@ " (print_list init_data) v.gvar_init;
  fprintf p "  gvar_readonly := %B;@ " v.gvar_readonly;
  fprintf p "  gvar_volatile := %B@ " v.gvar_volatile;
  fprintf p "|}.@ @ "

let print_globdef p (id, gd) =
  match gd with
  | Gfun(Internal f) -> print_function p (id, f)
  | Gfun(External _) -> ()
  | Gvar v -> print_variable p (id, v)

let print_ident_globdef p = function
  | (id, Gfun(Internal f)) -> 
      fprintf p "(%a, Gfun(Internal f_%s))" ident id (extern_atom id)
  | (id, Gfun(External(ef, targs, tres))) ->
      fprintf p "@[<hov 2>(%a,@ @[<hov 2>Gfun(External %a@ %a@ %a))@]@]"
        ident id external_function ef typlist targs typ tres
  | (id, Gvar v) ->
      fprintf p "(%a, Gvar v_%s)" ident id (extern_atom id)

(* Collecting the names and fields of structs and unions *)

module TypeSet = Set.Make(struct
  type t = coq_type
  let compare = Pervasives.compare
end)

let struct_unions = ref TypeSet.empty

let register_struct_union ty =
  struct_unions := TypeSet.add ty !struct_unions

let rec collect_type = function
  | Tvoid -> ()
  | Tint _ -> ()
  | Tlong _ -> ()
  | Tfloat _ -> ()
  | Tpointer(t, _) -> collect_type t
  | Tarray(t, _, _) -> collect_type t
  | Tfunction(args, res) -> collect_type_list args; collect_type res
  | Tstruct(id, fld, _) ->
      register_struct_union (Tstruct(id, fld, noattr)) (*; collect_fields fld*)
  | Tunion(id, fld, _) ->
      register_struct_union (Tunion(id, fld, noattr)) (*; collect_fields fld*)
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

let rec temp_of_expr = function
  | Etempvar(tmp, _) -> Some tmp
  | Ecast(e, _) -> temp_of_expr e
  | _ -> None

let rec collect_stmt = function
  | Sskip -> ()
  | Sassign(e1, e2) -> collect_expr e1; collect_expr e2
  | Sset(id, e2) ->
      begin match temp_of_expr e2 with
      | Some tmp -> name_temporary tmp id
      | None -> ()
      end;
      collect_expr e2
  | Scall(optid, e1, el) -> collect_expr e1; collect_exprlist el
  | Sbuiltin(optid, ef, tyl, el) -> collect_exprlist el
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

let define_struct p ty =
  match ty with
  | Tstruct(id, _, _) | Tunion(id, _, _) ->
      fprintf p "@[<hv 2>Definition t%a :=@  %a.@]@ " ident id typ ty
  | _ -> assert false

let define_structs p prog =
  use_struct_names := false;
  TypeSet.iter (define_struct p) !struct_unions;
  use_struct_names := true;
  fprintf p "@ "

(* Assertion processing *)

let re_annot_param = Str.regexp "%%\\|%[1-9][0-9]*"

type fragment = Text of string | Param of int

(* For compatibility with OCaml < 4.00 *)
let list_iteri f l =
  let rec iteri i = function
  | [] -> ()
  | a::l -> f i a; iteri (i + 1) l
  in iteri 0 l

let print_assertion p (txt, targs) =
  let frags =
    List.map
      (function
       | Str.Text s -> Text s
       | Str.Delim "%%" -> Text "%"
       | Str.Delim s -> Param(int_of_string(String.sub s 1 (String.length s - 1))))
      (Str.full_split re_annot_param (extern_atom txt)) in
  let max_param = ref 0 in
  List.iter
    (function
     | Text _ -> ()
     | Param n -> max_param := max n !max_param)
    frags;
  fprintf p "  | %ld%%positive, " (P.to_int32 txt);
  list_iteri
    (fun i targ ->
      match targ with
      | AA_arg _ -> fprintf p "_x%d :: " (i + 1)
      | _ -> ())
    targs;
  fprintf p "nil =>@ ";
  list_iteri
    (fun i targ ->
      match targ with
      | AA_arg _ -> ()
      | AA_int n ->  fprintf p "    let _x%d := %a in@ " (i + 1) coqint n
      | AA_float n ->  fprintf p "    let _x%d := %a in@ " (i + 1) coqfloat n)
    targs;
  fprintf p "    ";
  List.iter
    (function
     | Text s -> fprintf p "%s" s
     | Param n -> fprintf p "_x%d" n)
    frags;
  fprintf p "@ "

let print_assertions p =
  if !assertions <> [] then begin
    fprintf p "Definition assertions (id: ident) args : Prop :=@ ";
    fprintf p "  match id, args with@ ";
    List.iter (print_assertion p) !assertions;
    fprintf p "  | _, _ => False@ ";
    fprintf p "  end.@ @ "
  end

(* The prologue *)

let prologue = "\
Require Import Clightdefs.

Local Open Scope Z_scope.

"

(* All together *)

let print_program p prog =
  fprintf p "@[<v 0>";
  fprintf p "%s" prologue;
  Hashtbl.clear temp_names;
  all_temp_names := StringSet.empty;
  struct_unions := TypeSet.empty;
  List.iter collect_globdef prog.prog_defs;
  define_idents p;
  define_structs p prog;
  List.iter (print_globdef p) prog.prog_defs;
  fprintf p "Definition prog : Clight.program := {|@ ";
  fprintf p "prog_defs :=@ %a;@ " (print_list print_ident_globdef) prog.prog_defs;
  fprintf p "prog_main := %a@ " ident prog.prog_main;
  fprintf p "|}.@ ";
  print_assertions p;
  fprintf p "@]@."

