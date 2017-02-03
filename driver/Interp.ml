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

open Format
open Camlcoq
open AST
open Integers
open Values
open Memory
open Globalenvs
open Events
open Ctypes
open Csyntax
open Csem

(* Configuration *)

let trace = ref 1   (* 0 if quiet, 1 if normally verbose, 2 if full trace *)

type mode = First | Random | All

let mode = ref First

(* Printing events *)

let print_id_ofs p (id, ofs) =
  let id = extern_atom id and ofs = camlint_of_coqint ofs in
  if ofs = 0l
  then fprintf p " %s" id
  else fprintf p " %s%+ld" id ofs

let print_eventval p = function
  | EVint n -> fprintf p "%ld" (camlint_of_coqint n)
  | EVfloat f -> fprintf p "%.15F" (camlfloat_of_coqfloat f)
  | EVsingle f -> fprintf p "%.15F" (camlfloat_of_coqfloat32 f)
  | EVlong n -> fprintf p "%LdLL" (camlint64_of_coqint n)
  | EVptr_global(id, ofs) -> fprintf p "&%a" print_id_ofs (id, ofs)

let print_eventval_list p = function
  | [] -> ()
  | v1 :: vl ->
      print_eventval p v1;
      List.iter (fun v -> fprintf p ",@ %a" print_eventval v) vl

let print_event p = function
  | Event_syscall(id, args, res) ->
      fprintf p "extcall %s(%a) -> %a"
                (camlstring_of_coqstring id)
                print_eventval_list args
                print_eventval res
  | Event_vload(chunk, id, ofs, res) ->
      fprintf p "volatile load %s[&%s%+ld] -> %a"
                (PrintAST.name_of_chunk chunk)
                (extern_atom id) (camlint_of_coqint ofs)
                print_eventval res
  | Event_vstore(chunk, id, ofs, arg) ->
      fprintf p "volatile store %s[&%s%+ld] <- %a"
                (PrintAST.name_of_chunk chunk)
                (extern_atom id) (camlint_of_coqint ofs)
                print_eventval arg
  | Event_annot(text, args) ->
      fprintf p "annotation \"%s\" %a"
                (camlstring_of_coqstring text)
                print_eventval_list args

(* Printing states *)

let name_of_fundef prog fd =
  let rec find_name = function
  | [] -> "<unknown function>"
  | (id, Gfun fd') :: rem ->
      if fd == fd' then extern_atom id else find_name rem
  | (id, Gvar v) :: rem ->
      find_name rem
  in find_name prog.Ctypes.prog_defs

let name_of_function prog fn =
  let rec find_name = function
  | [] -> "<unknown function>"
  | (id, Gfun(Ctypes.Internal fn')) :: rem ->
      if fn == fn' then extern_atom id else find_name rem
  | (id, _) :: rem ->
      find_name rem
  in find_name prog.Ctypes.prog_defs

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
      PrintCsyntax.print_pointer_hook := print_pointer ge.genv_genv e;
      fprintf p "in function %s, statement@ @[<hv 0>%a@]"
              (name_of_function prog f)
              PrintCsyntax.print_stmt s
  | ExprState(f, r, k, e, m) ->
      PrintCsyntax.print_pointer_hook := print_pointer ge.genv_genv e;
      fprintf p "in function %s, expression@ @[<hv 0>%a@]"
              (name_of_function prog f)
              PrintCsyntax.print_expr r
  | Callstate(fd, args, k, m) ->
      PrintCsyntax.print_pointer_hook := print_pointer ge.genv_genv Maps.PTree.empty;
      fprintf p "calling@ @[<hov 2>%s(%a)@]"
              (name_of_fundef prog fd)
              print_val_list args
  | Returnstate(res, k, m) ->
      PrintCsyntax.print_pointer_hook := print_pointer ge.genv_genv Maps.PTree.empty;
      fprintf p "returning@ %a"
              print_val res
  | Stuckstate ->
      fprintf p "stuck after an undefined expression"

(* Comparing memory states *)

let compare_mem m1 m2 =
  (* assumes nextblocks were already compared equal *)
  (* should permissions be taken into account? *)
  Pervasives.compare m1.Mem.mem_contents m2.Mem.mem_contents

(* Comparing continuations *)

let some_expr = Eval(Vint Int.zero, Tvoid)

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
  | Stuckstate -> assert false

let mem_state = function
  | State(f, s, k, e, m) -> m
  | ExprState(f, r, k, e, m) -> m
  | Callstate(fd, args, k, m) -> m
  | Returnstate(res, k, m) -> m
  | Stuckstate -> assert false

let compare_state s1 s2 =
  if s1 == s2 then 0 else
  let c = P.compare (mem_state s1).Mem.nextblock (mem_state s2).Mem.nextblock in
  if c <> 0 then c else begin
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
  end

(* Maps of states already explored. *)

module StateMap =
  Map.Make(struct
             type t = state
             let compare = compare_state
           end)

(* Extract a string from a global pointer *)

let extract_string m blk ofs =
  let b = Buffer.create 80 in
  let rec extract blk ofs =
    match Mem.load Mint8unsigned m blk ofs with
    | Some(Vint n) ->
        let c = Char.chr (Z.to_int n) in
        if c = '\000' then begin
          Some(Buffer.contents b)
        end else begin
          Buffer.add_char b c;
          extract blk (Z.succ ofs)
        end
    | _ ->
        None in
  extract blk ofs

(* Emulation of printf *)

(* All ISO C 99 formats *)

let re_conversion = Str.regexp (
  "\\(%[-+0# ]*[0-9]*\\(\\.[0-9]*\\)?\\)" (* group 1: flags, width, precision *)
^ "\\(\\|[lhjztL]\\|hh\\|ll\\)"            (* group 3: length modifier *)
^ "\\([aAcdeEfgGinopsuxX%]\\)"            (* group 4: conversion specifier *)
)

external format_float: string -> float -> string
  = "caml_format_float"
external format_int32: string -> int32 -> string
  = "caml_int32_format"
external format_int64: string -> int64 -> string
  = "caml_int64_format"

let format_value m flags length conv arg =
  match conv.[0], length, arg with
  | ('d'|'i'|'u'|'o'|'x'|'X'|'c'), (""|"h"|"hh"|"l"|"z"|"t"), Vint i ->
      format_int32 (flags ^ conv) (camlint_of_coqint i)
  | ('d'|'i'|'u'|'o'|'x'|'X'|'c'), (""|"h"|"hh"|"l"|"z"|"t"), _ ->
      "<int argument expected>"
  | ('d'|'i'|'u'|'o'|'x'|'X'), ("ll"|"j"), Vlong i ->
      format_int64 (flags ^ conv) (camlint64_of_coqint i)
  | ('d'|'i'|'u'|'o'|'x'|'X'), ("ll"|"j"), _ ->
      "<long long argument expected"
  | ('f'|'e'|'E'|'g'|'G'|'a'), (""|"l"), Vfloat f ->
      format_float (flags ^ conv) (camlfloat_of_coqfloat f)
  | ('f'|'e'|'E'|'g'|'G'|'a'), "", _ ->
      "<float argument expected"
  | 's', "", Vptr(blk, ofs) ->
      begin match extract_string m blk ofs with
      | Some s -> s
      | None -> "<bad string>"
      end
  | 's', "", _ ->
      "<pointer argument expected>"
  | 'p', "", Vptr(blk, ofs) ->
      Printf.sprintf "<%ld%+ld>" (P.to_int32 blk) (camlint_of_coqint ofs)
  | 'p', "", Vint i ->
      format_int32 (flags ^ "x") (camlint_of_coqint i)
  | 'p', "", _ ->
      "<int or pointer argument expected>"
  | _, _, _ ->
      "<unrecognized format>"

let do_printf m fmt args =

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
        let flags = Str.matched_group 1 fmt
        and length = Str.matched_group 3 fmt
        and conv = Str.matched_group 4 fmt
        and pos' = Str.match_end() in
        if conv = "%" then begin
          Buffer.add_char b '%';
          scan pos' args
        end else begin
          match args with
          | [] ->
              Buffer.add_string b "<missing argument>";
              scan pos' []
          | arg :: args' ->
              Buffer.add_string b (format_value m flags length conv arg);
              scan pos' args'
        end
    end
  in scan 0 args; Buffer.contents b

(* Implementation of external functions *)

let (>>=) opt f = match opt with None -> None | Some arg -> f arg

(* Like eventval_of_val, but accepts static globals as well *)

let convert_external_arg ge v t =
  match v with
  | Vint i -> Some (EVint i)
  | Vfloat f -> Some (EVfloat f)
  | Vsingle f -> Some (EVsingle f)
  | Vlong n -> Some (EVlong n)
  | Vptr(b, ofs) ->
      Senv.invert_symbol ge b >>= fun id -> Some (EVptr_global(id, ofs))
  | _ -> None

let rec convert_external_args ge vl tl =
  match vl, tl with
  | [], [] -> Some []
  | v1::vl, t1::tl ->
      convert_external_arg ge v1 t1 >>= fun e1 ->
      convert_external_args ge vl tl >>= fun el -> Some (e1 :: el)
  | _, _ -> None

let do_external_function id sg ge w args m =
  match camlstring_of_coqstring id, args with
  | "printf", Vptr(b, ofs) :: args' ->
      extract_string m b ofs >>= fun fmt ->
      let fmt' = do_printf m fmt args' in
      let len = coqint_of_camlint (Int32.of_int (String.length fmt')) in
      Format.print_string fmt';
      flush stdout;
      convert_external_args ge args sg.sig_args >>= fun eargs ->
      Some(((w, [Event_syscall(id, eargs, EVint len)]), Vint len), m)
  | _ ->
      None

let do_inline_assembly txt sg ge w args m = None

(* Implementing external functions producing observable events *)

let rec world ge m =
  lazy (Determinism.World(world_io ge m, world_vload ge m, world_vstore ge m))

and world_io ge m id args =
  None

and world_vload ge m chunk id ofs =
  Genv.find_symbol ge.genv_genv id >>= fun b ->
  Mem.load chunk m b ofs >>= fun v ->
  Cexec.eventval_of_val ge v (type_of_chunk chunk) >>= fun ev ->
  Some(ev, world ge m)

and world_vstore ge m chunk id ofs ev =
  Genv.find_symbol ge.genv_genv id >>= fun b ->
  Cexec.val_of_eventval ge ev (type_of_chunk chunk) >>= fun v ->
  Mem.store chunk m b ofs v >>= fun m' ->
  Some(world ge m')

let do_event p ge time w ev =
  if !trace >= 1 then
    fprintf p "@[<hov 2>Time %d: observable event:@ %a@]@."
              time print_event ev;
  (* Return new world after external action *)
  match ev with
  | Event_vstore(chunk, id, ofs, v) ->
      begin match Determinism.nextworld_vstore w chunk id ofs v with
      | None -> assert false
      | Some w' -> w'
      end
  | _ -> w

let rec do_events p ge time w t =
  match t with
  | [] -> w
  | ev :: t' -> do_events p ge time (do_event p ge time w ev) t'

(* Debugging stuck expressions *)

let (|||) a b = a || b (* strict boolean or *)

let diagnose_stuck_expr p ge w f a kont e m =
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
    | RV, Eparen(r1, tycast, ty) -> diagnose RV r1
    | RV, Ecall(r1, rargs, ty) -> diagnose RV r1 ||| diagnose_list rargs
    | RV, Ebuiltin(ef, tyargs, rargs, ty) -> diagnose_list rargs
    | _, _ -> false in
  if found then true else begin
    let l = Cexec.step_expr ge do_external_function do_inline_assembly e w k a m in
    if List.exists (fun (ctx,red) -> red = Cexec.Stuckred) l then begin
      PrintCsyntax.print_pointer_hook := print_pointer ge.genv_genv e;
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

let diagnose_stuck_state p ge w = function
  | ExprState(f,a,k,e,m) -> ignore(diagnose_stuck_expr p ge w f a k e m)
  | _ -> ()

(* Execution of a single step.  Return list of triples
   (reduction rule, next state, next world). *)

let do_step p prog ge time s w =
  match Cexec.at_final_state s with
  | Some r ->
      if !trace >= 1 then
        fprintf p "Time %d: program terminated (exit code = %ld)@."
                  time (camlint_of_coqint r);
      begin match !mode with
      | All -> []
      | First | Random -> exit (Int32.to_int (camlint_of_coqint r))
      end
  | None ->
      let l = Cexec.do_step ge do_external_function do_inline_assembly w s in
      if l = []
      || List.exists (fun (Cexec.TR(r,t,s)) -> s = Stuckstate) l
      then begin
        pp_set_max_boxes p 1000;
        fprintf p "@[<hov 2>Stuck state: %a@]@." print_state (prog, ge, s);
        diagnose_stuck_state p ge w s;
        fprintf p "ERROR: Undefined behavior@.";
        exit 126
      end else begin
        List.map (fun (Cexec.TR(r, t, s')) -> (r, s', do_events p ge time w t)) l
      end

(* Exploration of a single execution. *)

let rec explore_one p prog ge time s w =
  if !trace >= 2 then
    fprintf p "@[<hov 2>Time %d:@ %a@]@." time print_state (prog, ge, s);
  let succs = do_step p prog ge time s w in
  if succs <> [] then begin
    let (r, s', w') =
      match !mode with
      | First -> List.hd succs
      | Random -> List.nth succs (Random.int (List.length succs))
      | All -> assert false in
    if !trace >= 2 then
      fprintf p "--[%s]-->@." (camlstring_of_coqstring r);
    explore_one p prog ge (time + 1) s' w'
  end

(* Exploration of all possible executions. *)

let rec explore_all p prog ge time states =
  if !trace >= 2 then begin
    List.iter
      (fun (n, s, w) ->
         fprintf p "@[<hov 2>State %d.%d: @ %a@]@."
                   time n print_state (prog, ge, s))
      states
  end;
  let rec explore_next nextstates seen numseen = function
  | [] ->
      List.rev nextstates
  | (n, s, w) :: states ->
      add_reducts nextstates seen numseen states n (do_step p prog ge time s w)

  and add_reducts nextstates seen numseen states n = function
  | [] ->
      explore_next nextstates seen numseen states
  | (r, s', w') :: reducts ->
      let (n', nextstates', seen', numseen') =
        try
          (StateMap.find s' seen, nextstates, seen, numseen)
        with Not_found ->
          (numseen,
           (numseen, s', w') :: nextstates,
           StateMap.add s' numseen seen,
           numseen + 1) in
      if !trace >= 2 then begin
        fprintf p "Transition state %d.%d --[%s]--> state %d.%d@."
                  time n (camlstring_of_coqstring r) (time + 1) n'
      end;
      add_reducts nextstates' seen' numseen' states n reducts
  in
    let nextstates = explore_next [] StateMap.empty 1 states in
    if nextstates <> [] then explore_all p prog ge (time + 1) nextstates

(* The variant of the source program used to build the world for
   executing events.
   Volatile variables are turned into non-volatile ones, so that
     reads and writes can be performed.
   Other variables are turned into empty vars, so that
     reads and writes just fail.
   Functions are preserved, although they are not used. *)

let world_program prog =
  let change_def (id, gd) =
    match gd with
    | Gvar gv ->
        let gv' =
          if gv.gvar_volatile then
            {gv with gvar_readonly = false; gvar_volatile = false}
          else
            {gv with gvar_init = []} in
        (id, Gvar gv')
    | Gfun fd ->
        (id, gd) in
 {prog with Ctypes.prog_defs = List.map change_def prog.Ctypes.prog_defs}

(* Massaging the program to get a suitable "main" function *)

let change_main_function p old_main old_main_ty =
  let old_main = Evalof(Evar(old_main, old_main_ty), old_main_ty) in
  let arg1 = Eval(Vint(coqint_of_camlint 0l), type_int32s) in
  let arg2 = arg1 in
  let body =
    Sreturn(Some(Ecall(old_main, Econs(arg1, Econs(arg2, Enil)), type_int32s))) in
  let new_main_fn =
    { fn_return = type_int32s; fn_callconv = cc_default;
      fn_params = []; fn_vars = []; fn_body = body } in
  let new_main_id = intern_string "___main" in
  { prog_main = new_main_id;
    Ctypes.prog_defs = (new_main_id, Gfun(Ctypes.Internal new_main_fn)) :: p.Ctypes.prog_defs;
    Ctypes.prog_public = p.Ctypes.prog_public;
    prog_types = p.prog_types;
    prog_comp_env = p.prog_comp_env }

let rec find_main_function name = function
  | [] -> None
  | (id, Gfun fd) :: gdl -> if id = name then Some fd else find_main_function name gdl
  | (id, Gvar v) :: gdl -> find_main_function name gdl

let fixup_main p =
  match find_main_function p.Ctypes.prog_main p.Ctypes.prog_defs with
  | None ->
      fprintf err_formatter "ERROR: no main() function@.";
      None
  | Some main_fd ->
      match type_of_fundef main_fd with
      | Tfunction(Tnil, Ctypes.Tint(I32, Signed, _), _) ->
          Some p
      | Tfunction(Tcons(Ctypes.Tint _, Tcons(Tpointer(Tpointer(Ctypes.Tint(I8,_,_),_),_), Tnil)),
                  Ctypes.Tint _, _) as ty ->
          Some (change_main_function p p.Ctypes.prog_main ty)
      | _ ->
          fprintf err_formatter "ERROR: wrong type for main() function@.";
          None

(* Execution of a whole program *)

let execute prog =
  Random.self_init();
  let p = std_formatter in
  pp_set_max_indent p 30;
  pp_set_max_boxes p 10;
  match fixup_main prog with
  | None -> exit 126
  | Some prog1 ->
      let wprog = world_program prog1 in
      let wge = globalenv wprog in
      match Genv.init_mem (program_of_program wprog) with
      | None ->
          fprintf p "ERROR: World memory state undefined@."; exit 126
      | Some wm ->
      match Cexec.do_initial_state prog1 with
      | None ->
          fprintf p "ERROR: Initial state undefined@."; exit 126
      | Some(ge, s) ->
          match !mode with
          | First | Random ->
              explore_one p prog1 ge 0 s (world wge wm)
          | All ->
              explore_all p prog1 ge 0 [(1, s, world wge wm)]
