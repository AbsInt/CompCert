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

open Format
open Camlcoq
open AST
open Values

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

let sanitize_char = function
  | 'A'..'Z' | 'a'..'z' | '0'..'9' | '_' as c -> c
  | ' ' | '$' -> '_'
  | _ -> raise Not_an_identifier

let sanitize s =
  if s <> ""
  then "_" ^ String.map sanitize_char s
  else "empty_ident"

let temp_names : (ident, string) Hashtbl.t = Hashtbl.create 17

let ident p id =
  try
    let s = Hashtbl.find string_of_atom id in
    fprintf p "%s" (sanitize s)
  with Not_found | Not_an_identifier ->
  try
    let s = Hashtbl.find temp_names id in
    fprintf p "%s" s
  with Not_found ->
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
          fprintf p "Definition %s : ident := $\"%s\".@ "
                    (sanitize name) name
        else
          fprintf p "Definition %s : ident := %a.@ "
                    (sanitize name) positive id
      with Not_an_identifier ->
        ());
  iter_hashtbl_sorted
    temp_names
    (fun (id, name) ->
      fprintf p "Definition %s : ident := %a.@ "
                name positive id);
  fprintf p "@ "

let name_temporary t =
  if not (Hashtbl.mem string_of_atom t) && not (Hashtbl.mem temp_names t)
  then begin
    let t0 = first_unused_ident () in
    let d = Z.succ (Z.sub (Z.Zpos t) (Z.Zpos t0)) in
    Hashtbl.add temp_names t ("_t'" ^ Z.to_string d)
  end

let name_opt_temporary = function
  | None -> ()
  | Some id -> name_temporary id

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

let callconv p cc =
  if cc = cc_default
  then fprintf p "cc_default"
  else fprintf p "{|cc_vararg:=%a; cc_unproto:=%b; cc_structret:=%b|}"
                  (print_option coqZ) cc.cc_vararg cc.cc_unproto cc.cc_structret

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

(* Variables *)

let init_data p = function
  | Init_int8 n -> fprintf p "Init_int8 %a" coqint n
  | Init_int16 n -> fprintf p "Init_int16 %a" coqint n
  | Init_int32 n -> fprintf p "Init_int32 %a" coqint n
  | Init_int64 n -> fprintf p "Init_int64 %a" coqint64 n
  | Init_float32 n -> fprintf p "Init_float32 %a" coqsingle n
  | Init_float64 n -> fprintf p "Init_float64 %a" coqfloat n
  | Init_space n -> fprintf p "Init_space %a" coqZ n
  | Init_addrof(id,ofs) -> fprintf p "Init_addrof %a %a" ident id coqptrofs ofs

let print_variable print_info p (id, v) =
  fprintf p "Definition v%s := {|@ " (sanitize (extern_atom id));
  fprintf p "  gvar_info := %a;@ " print_info v.gvar_info;
  fprintf p "  gvar_init := %a;@ " (print_list init_data) v.gvar_init;
  fprintf p "  gvar_readonly := %B;@ " v.gvar_readonly;
  fprintf p "  gvar_volatile := %B@ " v.gvar_volatile;
  fprintf p "|}.@ @ "

(* Values *)

let val_ p = function
  | Vundef -> fprintf p "Vundef"
  | Vint i -> fprintf p "(Vint %a)" coqint i
  | Vlong l -> fprintf p "(Vlong %a)" coqint64 l
  | Vfloat f -> fprintf p "(Vfloat %a)" coqfloat f
  | Vsingle s -> fprintf p "(Vsingle %a)" coqsingle s
  | Vptr(b, o) -> fprintf p "(Vptr %a %a)" positive b coqptrofs o

(* Information about this run of clightgen or csyntaxgen *)

let print_gen_info ~sourcefile ?normalized p =
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
  begin match normalized with
  | None -> ()
  | Some b -> fprintf p "@ Definition normalized := %B." b
  end;
  fprintf p "@]@ End Info.@ @ "  
  
