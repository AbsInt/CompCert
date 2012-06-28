(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Interpreting CompCert C sources *)

type caml_float = float

open Format
open Camlcoq
open Datatypes
open BinPos
open BinInt
open AST
open Integers
open Floats
open Values
open Memory
open Globalenvs
open Events
open Csyntax
open Csem
open Clflags

(* Configuration *)

let trace = ref 1   (* 0 if quiet, 1 if normally verbose, 2 if full trace *)

type mode = First | Random | All

let mode = ref First

let random_volatiles = ref false

(* Printing events *)

let print_id_ofs p (id, ofs) =
  let id = extern_atom id and ofs = camlint_of_coqint ofs in
  if ofs = 0l
  then fprintf p " %s" id
  else fprintf p " %s%+ld" id ofs

let print_eventval p = function
  | EVint n -> fprintf p "%ld" (camlint_of_coqint n)
  | EVfloat f -> fprintf p "%F" (camlfloat_of_coqfloat f)
  | EVptr_global(id, ofs) -> fprintf p "&%a" print_id_ofs (id, ofs)

let print_eventval_list p = function
  | [] -> ()
  | v1 :: vl ->
      print_eventval p v1;
      List.iter (fun v -> fprintf p ",@ %a" print_eventval v) vl

let print_event p = function
  | Event_syscall(id, args, res) ->
      fprintf p "extcall %s(%a) -> %a"
                (extern_atom id)
                print_eventval_list args
                print_eventval res
  | Event_vload(chunk, id, ofs, res) ->
      fprintf p "volatile load %s[&%s%+ld] -> %a"
                (PrintCminor.name_of_chunk chunk)
                (extern_atom id) (camlint_of_coqint ofs)
                print_eventval res
  | Event_vstore(chunk, id, ofs, arg) ->
      fprintf p "volatile store %s[&%s%+ld] <- %a"
                (PrintCminor.name_of_chunk chunk)
                (extern_atom id) (camlint_of_coqint ofs)
                print_eventval arg
  | Event_annot(text, args) ->
      fprintf p "annotation \"%s\" %a"
                (extern_atom text)
                print_eventval_list args

(* Printing states *)

let name_of_fundef prog fd =
  let rec find_name = function
  | [] -> "<unknown function>"
  | (id, fd') :: rem ->
      if fd = fd' then extern_atom id else find_name rem
  in find_name prog.prog_funct

let name_of_function prog fn =
  name_of_fundef prog (Internal fn)

let invert_local_variable e b =
  Maps.PTree.fold 
    (fun res id (b', _) -> if b = b' then Some id else res)
    e None

let print_pointer ge e p (b, ofs) =
  match invert_local_variable e b with
  | Some id -> print_id_ofs p (id, ofs)
  | None ->
      match Genv.invert_symbol ge b with
      | Some id -> print_id_ofs p (id, ofs)
      | None -> ()

let print_val = PrintCsyntax.print_value

let print_val_list p vl =
  match vl with
  | [] -> ()
  | v1 :: vl ->
      print_val p v1;
      List.iter (fun v -> fprintf p ",@ %a" print_val v) vl

let print_state p (prog, ge, s) =
  match s with
  | State(f, s, k, e, m) ->
      PrintCsyntax.print_pointer_hook := print_pointer ge e;
      fprintf p "in function %s, statement@ @[<hv 0>%a@]"
              (name_of_function prog f)
              PrintCsyntax.print_stmt s
  | ExprState(f, r, k, e, m) ->
      PrintCsyntax.print_pointer_hook := print_pointer ge e;
      fprintf p "in function %s, expression@ @[<hv 0>%a@]"
              (name_of_function prog f)
              PrintCsyntax.print_expr r
  | Callstate(fd, args, k, m) ->
      PrintCsyntax.print_pointer_hook := print_pointer ge Maps.PTree.empty;
      fprintf p "calling@ @[<hov 2>%s(%a)@]"
              (name_of_fundef prog fd)
              print_val_list args
  | Returnstate(res, k, m) ->
      PrintCsyntax.print_pointer_hook := print_pointer ge Maps.PTree.empty;
      fprintf p "returning@ %a"
              print_val res
  | Stuckstate ->
      fprintf p "stuck after an undefined expression"

let mem_of_state = function
  | State(f, s, k, e, m) -> m
  | ExprState(f, r, k, e, m) -> m
  | Callstate(fd, args, k, m) -> m
  | Returnstate(res, k, m) -> m
  | Stuckstate -> assert false

(* Comparing memory states *)

let compare_mem m1 m2 = (* should permissions be taken into account? *)
  Pervasives.compare (m1.Mem.nextblock, m1.Mem.mem_contents)
                     (m2.Mem.nextblock, m1.Mem.mem_contents)

(* Comparing continuations *)

let some_expr = Evar(Coq_xH, Tvoid)

let rank_cont = function
  | Kstop -> 0
  | Kdo _ -> 1
  | Kseq _ -> 2
  | Kifthenelse _ -> 3
  | Kwhile1 _ -> 4
  | Kwhile2 _ -> 5
  | Kdowhile1 _ -> 6
  | Kdowhile2 _ -> 7
  | Kfor2 _ -> 8
  | Kfor3 _ -> 9
  | Kfor4 _ -> 10
  | Kswitch1 _ -> 11
  | Kswitch2 _ -> 12
  | Kreturn _ -> 13
  | Kcall _ -> 14

let rec compare_cont k1 k2 =
  if k1 == k2 then 0 else
  match k1, k2 with
  | Kstop, Kstop -> 0
  | Kdo k1, Kdo k2 -> compare_cont k1 k2
  | Kseq(s1, k1), Kseq(s2, k2) ->  
      let c = compare s1 s2 in if c <> 0 then c else compare_cont k1 k2
  | Kifthenelse(s1, s1', k1), Kifthenelse(s2, s2', k2) ->
      let c = compare (s1,s1') (s2,s2') in
      if c <> 0 then c else compare_cont k1 k2
  | Kwhile1(e1, s1, k1), Kwhile1(e2, s2, k2) ->
      let c = compare (e1,s1) (e2,s2) in
      if c <> 0 then c else compare_cont k1 k2
  | Kwhile2(e1, s1, k1), Kwhile2(e2, s2, k2) ->
      let c = compare (e1,s1) (e2,s2) in
      if c <> 0 then c else compare_cont k1 k2
  | Kdowhile1(e1, s1, k1), Kdowhile1(e2, s2, k2) ->
      let c = compare (e1,s1) (e2,s2) in
      if c <> 0 then c else compare_cont k1 k2
  | Kdowhile2(e1, s1, k1), Kdowhile2(e2, s2, k2) ->
      let c = compare (e1,s1) (e2,s2) in
      if c <> 0 then c else compare_cont k1 k2
  | Kfor2(e1, s1, s1', k1), Kfor2(e2, s2, s2', k2) ->
      let c = compare (e1,s1,s1') (e2,s2,s2') in
      if c <> 0 then c else compare_cont k1 k2
  | Kfor3(e1, s1, s1', k1), Kfor3(e2, s2, s2', k2) ->
      let c = compare (e1,s1,s1') (e2,s2,s2') in
      if c <> 0 then c else compare_cont k1 k2
  | Kfor4(e1, s1, s1', k1), Kfor4(e2, s2, s2', k2) ->
      let c = compare (e1,s1,s1') (e2,s2,s2') in
      if c <> 0 then c else compare_cont k1 k2
  | Kswitch1(sl1, k1), Kswitch1(sl2, k2) ->
      let c = compare sl1 sl2 in
      if c <> 0 then c else compare_cont k1 k2
  | Kreturn k1, Kreturn k2 ->
      compare_cont k1 k2
  | Kcall(f1, e1, c1, ty1, k1), Kcall(f2, e2, c2, ty2, k2) ->
      let c = compare (f1, e1, c1 some_expr, ty1) (f2, e2, c2 some_expr, ty2) in
      if c <> 0 then c else compare_cont k1 k2
  | _, _ ->
      compare (rank_cont k1) (rank_cont k2)

(* Comparing states *)

let rank_state = function
  | State _ -> 0
  | ExprState _ -> 1
  | Callstate _ -> 2
  | Returnstate _ -> 3
  | Stuckstate -> 4

let compare_state s1 s2 =
  if s1 == s2 then 0 else
  match s1, s2 with
  | State(f1,s1,k1,e1,m1), State(f2,s2,k2,e2,m2) ->
      let c = compare (f1,s1,e1) (f2,s2,e2) in if c <> 0 then c else
      let c = compare_cont k1 k2 in if c <> 0 then c else
      compare_mem m1 m2
  | ExprState(f1,r1,k1,e1,m1), ExprState(f2,r2,k2,e2,m2) ->
      let c = compare (f1,r1,e1) (f2,r2,e2) in if c <> 0 then c else
      let c = compare_cont k1 k2 in if c <> 0 then c else
      compare_mem m1 m2
  | Callstate(fd1,args1,k1,m1), Callstate(fd2,args2,k2,m2) ->
      let c = compare (fd1,args1) (fd2,args2) in if c <> 0 then c else
      let c = compare_cont k1 k2 in if c <> 0 then c else
      compare_mem m1 m2
  | Returnstate(res1,k1,m1), Returnstate(res2,k2,m2) ->
      let c = compare res1 res2 in if c <> 0 then c else
      let c = compare_cont k1 k2 in if c <> 0 then c else
      compare_mem m1 m2
  | _, _ ->
      compare (rank_state s1) (rank_state s2)

module StateSet =
  Set.Make(struct type t = state let compare = compare_state end)

(* Extract a string from a global pointer *)

let extract_string ge m id ofs =
  let b = Buffer.create 80 in
  let rec extract blk ofs =
    match Memory.Mem.load Mint8unsigned m blk ofs with
    | Some(Vint n) ->
        let c = Char.chr (Int32.to_int (camlint_of_coqint n)) in
        if c = '\000' then begin
          Some(Buffer.contents b)
        end else begin
          Buffer.add_char b c; 
          extract blk (coq_Zsucc ofs)
        end
    | _ ->
        None in
  match Genv.find_symbol ge id with
  | None -> None
  | Some blk -> extract blk ofs

(* Emulation of printf *)

(* All ISO C 99 formats except size modifiers [ll] (long long) and [L]
   (long double) *)

let re_conversion = Str.regexp
  "%[-+0# ]*[0-9]*\\(\\.[0-9]*\\)?\\([lhjzt]\\|hh\\)?\\([aAcdeEfgGinopsuxX%]\\)"

external format_float: string -> caml_float -> string
  = "caml_format_float"
external format_int32: string -> int32 -> string
  = "caml_int32_format"

let do_printf ge m fmt args =

  let b = Buffer.create 80 in
  let len = String.length fmt in

  let opt_search_forward pos =
    try Some(Str.search_forward re_conversion fmt pos)
    with Not_found -> None in

  let rec scan pos args =
    if pos < len then begin
    match opt_search_forward pos with
    | None ->
        Buffer.add_substring b fmt pos (len - pos)
    | Some pos1 ->
        Buffer.add_substring b fmt pos (pos1 - pos);
        let pat = Str.matched_string fmt
        and conv = Str.matched_group 3 fmt
        and pos' = Str.match_end() in
        match args, conv.[0] with
        | _, '%' ->
            Buffer.add_char b '%';
            scan pos' args
        | [], _ ->
            Buffer.add_string b "<missing argument>";
            scan pos' []
        | EVint i :: args', ('d'|'i'|'u'|'o'|'x'|'X'|'c') ->
            Buffer.add_string b (format_int32 pat (camlint_of_coqint i));
            scan pos' args'
        | EVfloat f :: args', ('f'|'e'|'E'|'g'|'G'|'a') ->
            Buffer.add_string b (format_float pat (camlfloat_of_coqfloat f));
            scan pos' args'
        | EVptr_global(id, ofs) :: args', 's' ->
            Buffer.add_string b
              (match extract_string ge m id ofs with
               | Some s -> s
               | None -> "<bad string>");
            scan pos' args'
        | EVptr_global(id, ofs) :: args', 'p' ->
            Printf.bprintf b "<&%s%+ld>" (extern_atom id) (camlint_of_coqint ofs);
            scan pos' args'
        | _ :: args', _ ->
            Buffer.add_string b "<formatting error>";
            scan pos' args'
    end
  in scan 0 args; Buffer.contents b

(* Implementing external functions *)

let re_stub = Str.regexp "\\$[if]*$"

let chop_stub name = Str.replace_first re_stub "" name

let rec world = Determinism.World(world_io, world_vload, world_vstore)

and world_io id args =
  match chop_stub(extern_atom id), args with
  | "printf", EVptr_global(id, ofs) :: args' ->
      Some(EVint Integers.Int.zero, world)
  | _, _ ->
      None

and world_vload chunk id ofs =
  assert !random_volatiles;
  let res = match chunk with
    | Mint8signed -> EVint(coqint_of_camlint(Int32.sub (Random.int32 0x100l) 0x80l))
    | Mint8unsigned -> EVint(coqint_of_camlint(Random.int32 0x100l))
    | Mint16signed -> EVint(coqint_of_camlint(Int32.sub (Random.int32 0x10000l) 0x8000l))
    | Mint16unsigned -> EVint(coqint_of_camlint(Random.int32 0x10000l))
    | Mint32 -> EVint(coqint_of_camlint(Random.int32 0x7FFF_FFFFl))
    | Mfloat32 -> EVfloat(
	Floats.Float.singleoffloat(coqfloat_of_camlfloat(Random.float 1.0)))
    | Mfloat64 -> EVfloat(coqfloat_of_camlfloat(Random.float 1.0))
  in Some(res, world)

and world_vstore chunk id ofs v =
  assert !random_volatiles;
  Some world

let do_event p ge time s ev =
  if !trace >= 1 then
    fprintf p "@[<hov 2>Time %d: observable event: %a@]@."
              time print_event ev;
  match ev with
  | Event_syscall(name, EVptr_global(id, ofs) :: args', res) 
    when chop_stub (extern_atom name) = "printf" ->
      flush stderr;
      let m = mem_of_state s in
      begin match extract_string ge m id ofs with
      | Some fmt -> print_string (do_printf ge m fmt args')
      | None -> print_string "<bad printf>\n"
      end;
      flush stdout
  | _ -> ()

let do_events p ge time s t =
  List.iter (do_event p ge time s) t

(* Debugging stuck expressions *)

let (|||) a b = a || b (* strict boolean or *)

let diagnose_stuck_expr p ge f a kont e m =
  let rec diagnose k a =
  (* diagnose subexpressions first *)
  let found =
    match k, a with
    | LV, Ederef(r, ty) -> diagnose RV r
    | LV, Efield(r, f, ty) -> diagnose RV r
    | RV, Evalof(l, ty) -> diagnose LV l
    | RV, Eaddrof(l, ty) -> diagnose LV l
    | RV, Eunop(op, r1, ty) -> diagnose RV r1
    | RV, Ebinop(op, r1, r2, ty) -> diagnose RV r1 ||| diagnose RV r2
    | RV, Ecast(r1, ty) -> diagnose RV r1
    | RV, Econdition(r1, r2, r3, ty) -> diagnose RV r1
    | RV, Eassign(l1, r2, ty) -> diagnose LV l1 ||| diagnose RV r2
    | RV, Eassignop(op, l1, r2, tyres, ty) -> diagnose LV l1 ||| diagnose RV r2
    | RV, Epostincr(id, l, ty) -> diagnose LV l
    | RV, Ecomma(r1, r2, ty) -> diagnose RV r1
    | RV, Eparen(r1, ty) -> diagnose RV r1
    | RV, Ecall(r1, rargs, ty) -> diagnose RV r1 ||| diagnose_list rargs
    | _, _ -> false in
  if found then true else begin
    let l = Cexec.step_expr ge e world k a m in
    if List.exists (fun (ctx,red) -> red = Cexec.Stuckred) l then begin
      PrintCsyntax.print_pointer_hook := print_pointer ge e;
      fprintf p "@[<hov 2>Stuck subexpression:@ %a@]@."
              PrintCsyntax.print_expr a;
      true
    end else false
  end

  and diagnose_list al =
    match al with
    | Enil -> false
    | Econs(a1, al') -> diagnose RV a1 ||| diagnose_list al'

  in diagnose RV a

let diagnose_stuck_state p ge = function
  | ExprState(f,a,k,e,m) -> ignore(diagnose_stuck_expr p ge f a k e m)
  | _ -> ()

(* Exploration *)

let do_step p prog ge time s =
  if !trace >= 2 then
    fprintf p "@[<hov 2>Time %d: %a@]@." time print_state (prog, ge, s);
  match Cexec.at_final_state s with
  | Some r ->
      if !trace >= 1 then begin
        fprintf p "Time %d: program terminated (exit code = %ld)@."
                  time (camlint_of_coqint r);
        []
      end else begin
        exit (Int32.to_int (camlint_of_coqint r))
      end
  | None ->
      let l = Cexec.do_step ge world s in
      if l = [] || List.exists (fun (t,s) -> s = Stuckstate) l then begin
        pp_set_max_boxes p 1000;
        fprintf p "@[<hov 2>Stuck state: %a@]@." print_state (prog, ge, s);
        diagnose_stuck_state p ge s;
        fprintf p "ERROR: Undefined behavior@.";
        exit 126
      end else begin
        List.iter (fun (t, s') -> do_events p ge time s t) l;
        List.map snd l
      end

let rec explore p prog ge time ss =
  let succs =
    StateSet.fold (fun s l -> do_step p prog ge time s @ l) ss [] in
  if succs <> [] then begin
    let ss' =
      match !mode with
      | First -> StateSet.singleton (List.hd succs)
      | Random -> StateSet.singleton (List.nth succs (Random.int (List.length succs)))
      | All -> List.fold_right StateSet.add succs StateSet.empty in
    explore p prog ge (time + 1) ss'
  end

(* Massaging the source program *)

let unvolatile prog =
  let unvolatile_globvar (id, gv) =
    (id, if gv.gvar_volatile
         then {gv with gvar_readonly = false; gvar_volatile = false}
         else gv) in
  {prog with prog_vars = List.map unvolatile_globvar prog.prog_vars}

let change_main_function p old_main old_main_ty =
  let old_main = Evalof(Evar(old_main, old_main_ty), old_main_ty) in
  let arg1 = Eval(Vint(coqint_of_camlint 0l), type_int32s) in
  let arg2 = arg1 in
  let body =
    Sreturn(Some(Ecall(old_main, Econs(arg1, Econs(arg2, Enil)), type_int32s))) in
  let new_main_fn =
    { fn_return = type_int32s; fn_params = []; fn_vars = []; fn_body = body } in
  let new_main_id = intern_string "___main" in
  { p with
    prog_main = new_main_id;
    prog_funct = (new_main_id, Internal new_main_fn) :: p.prog_funct }

let fixup_main p =
  try
    match type_of_fundef (List.assoc p.prog_main p.prog_funct) with
    | Tfunction(Tnil, Tint(I32, Signed, _)) ->
        Some p
    | Tfunction(Tcons(Tint _, Tcons(Tpointer(Tpointer(Tint(I8,_,_),_),_), Tnil)),
                Tint _) as ty ->
        Some (change_main_function p p.prog_main ty)
    | _ ->
        fprintf err_formatter "ERROR: wrong type for main() function";
        None
  with Not_found ->
    fprintf err_formatter "ERROR: no main() function";
    None

(* Execution of a whole program *)

let execute prog =
  Random.self_init();
  let p = std_formatter in
  pp_set_max_indent p 30;
  pp_set_max_boxes p 10;
  match fixup_main prog with
  | None -> ()
  | Some prog1 ->
      let prog2 = if !random_volatiles then prog1 else unvolatile prog1 in
      match Cexec.do_initial_state prog2 with
      | None ->
          fprintf p "ERROR: Initial state undefined@."
      | Some(ge, s) ->
          explore p prog2 ge 0 (StateSet.singleton s)
