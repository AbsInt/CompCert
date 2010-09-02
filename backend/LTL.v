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

(** The LTL intermediate language: abstract syntax and semantics.

  LTL (``Location Transfer Language'') is the target language
  for register allocation and the source language for linearization. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Conventions.

(** * Abstract syntax *)

(** LTL is close to RTL, but uses locations instead of pseudo-registers. *)

Definition node := positive.

Inductive instruction: Type :=
  | Lnop: node -> instruction
  | Lop: operation -> list loc -> loc -> node -> instruction
  | Lload: memory_chunk -> addressing -> list loc -> loc -> node -> instruction
  | Lstore: memory_chunk -> addressing -> list loc -> loc -> node -> instruction
  | Lcall: signature -> loc + ident -> list loc -> loc -> node -> instruction
  | Ltailcall: signature -> loc + ident -> list loc -> instruction
  | Lbuiltin: external_function -> list loc -> loc -> node -> instruction
  | Lcond: condition -> list loc -> node -> node -> instruction
  | Ljumptable: loc -> list node -> instruction
  | Lreturn: option loc -> instruction.

Definition code: Type := PTree.t instruction.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_params: list loc;
  fn_stacksize: Z;
  fn_code: code;
  fn_entrypoint: node
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

(** * Operational semantics *)

Definition genv := Genv.t fundef unit.
Definition locset := Locmap.t.

Definition locmap_optget (ol: option loc) (dfl: val) (ls: locset) : val :=
  match ol with
  | None => dfl
  | Some l => ls l
  end.

Fixpoint init_locs (vl: list val) (rl: list loc) {struct rl} : locset :=
  match rl, vl with
  | r1 :: rs, v1 :: vs => Locmap.set r1 v1 (init_locs vs rs)
  | _, _ => Locmap.init Vundef
  end.

(** [postcall_locs ls] returns the location set [ls] after a function
  call.  Caller-save registers and temporary registers
  are set to [undef], reflecting the fact that the called
  function can modify them freely. *)

Definition postcall_locs (ls: locset) : locset :=
  fun (l: loc) =>
    match l with
    | R r =>
        if In_dec Loc.eq (R r) temporaries then
          Vundef
        else if In_dec Loc.eq (R r) destroyed_at_call then
          Vundef
        else
          ls (R r)
    | S s => ls (S s)
    end.

(** Temporaries destroyed across instructions *)

Definition undef_temps (ls: locset) := Locmap.undef temporaries ls.

(** LTL execution states. *)

Inductive stackframe : Type :=
  | Stackframe:
      forall (res: loc)         (**r where to store the result *)
             (f: function)      (**r calling function *)
             (sp: val)          (**r stack pointer in calling function *)
             (ls: locset)       (**r location state in calling function *)
             (pc: node),        (**r program point in calling function *)
      stackframe.

Inductive state : Type :=
  | State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r function currently executing *)
             (sp: val)                (**r stack pointer *)
             (pc: node)               (**r current program point *)
             (ls: locset)             (**r location state *)
             (m: mem),                (**r memory state *)
      state
  | Callstate:
      forall (stack: list stackframe) (**r call stack *)
             (f: fundef)              (**r function to call *)
             (args: list val)         (**r arguments to the call *)
             (m: mem),                (**r memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe) (**r call stack *)
             (v: val)                 (**r return value for the call *)
             (m: mem),                (**r memory state *)
      state.


Section RELSEM.

Variable ge: genv.

Definition find_function (los: loc + ident) (rs: locset) : option fundef :=
  match los with
  | inl l => Genv.find_funct ge (rs l)
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

(** The LTL transition relation is very similar to that of RTL,
  with locations being used in place of pseudo-registers.
  The main difference is for the [call] instruction: caller-save
  registers are set to [Vundef] across the call, using the [postcall_locs]
  function defined above.  This forces the LTL producer to avoid
  storing values live across the call in a caller-save register. *)

Inductive step: state -> trace -> state -> Prop :=
  | exec_Lnop:
      forall s f sp pc rs m pc',
      (fn_code f)!pc = Some(Lnop pc') ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m)
  | exec_Lop:
      forall s f sp pc rs m op args res pc' v,
      (fn_code f)!pc = Some(Lop op args res pc') ->
      eval_operation ge sp op (map rs args) = Some v ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' (Locmap.set res v (undef_temps rs)) m)
  | exec_Lload:
      forall s f sp pc rs m chunk addr args dst pc' a v,
      (fn_code f)!pc = Some(Lload chunk addr args dst pc') ->
      eval_addressing ge sp addr (map rs args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' (Locmap.set dst v (undef_temps rs)) m)
  | exec_Lstore:
      forall s f sp pc rs m chunk addr args src pc' a m',
      (fn_code f)!pc = Some(Lstore chunk addr args src pc') ->
      eval_addressing ge sp addr (map rs args) = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' (undef_temps rs) m')
  | exec_Lcall:
      forall s f sp pc rs m sig ros args res pc' f',
      (fn_code f)!pc = Some(Lcall sig ros args res pc') ->
      find_function ros rs = Some f' ->
      funsig f' = sig ->
      step (State s f sp pc rs m)
        E0 (Callstate (Stackframe res f sp (postcall_locs rs) pc' :: s)
                      f' (List.map rs args) m)
  | exec_Ltailcall:
      forall s f stk pc rs m sig ros args f' m',
      (fn_code f)!pc = Some(Ltailcall sig ros args) ->
      find_function ros rs = Some f' ->
      funsig f' = sig ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s f (Vptr stk Int.zero) pc rs m)
        E0 (Callstate s f' (List.map rs args) m')
  | exec_Lbuiltin:
      forall s f sp pc rs m ef args res pc' t v m',
      (fn_code f)!pc = Some(Lbuiltin ef args res pc') ->
      external_call ef ge (map rs args) m t v m' ->
      step (State s f sp pc rs m)
         t (State s f sp pc' (Locmap.set res v rs) m')
  | exec_Lcond_true:
      forall s f sp pc rs m cond args ifso ifnot,
      (fn_code f)!pc = Some(Lcond cond args ifso ifnot) ->
      eval_condition cond (map rs args) = Some true ->
      step (State s f sp pc rs m)
        E0 (State s f sp ifso (undef_temps rs) m)
  | exec_Lcond_false:
      forall s f sp pc rs m cond args ifso ifnot,
      (fn_code f)!pc = Some(Lcond cond args ifso ifnot) ->
      eval_condition cond (map rs args) = Some false ->
      step (State s f sp pc rs m)
        E0 (State s f sp ifnot (undef_temps rs) m)
  | exec_Ljumptable:
      forall s f sp pc rs m arg tbl n pc',
      (fn_code f)!pc = Some(Ljumptable arg tbl) ->
      rs arg = Vint n ->
      list_nth_z tbl (Int.signed n) = Some pc' ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' (undef_temps rs) m)
  | exec_Lreturn:
      forall s f stk pc rs m or m',
      (fn_code f)!pc = Some(Lreturn or) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s f (Vptr stk Int.zero) pc rs m)
        E0 (Returnstate s (locmap_optget or Vundef rs) m')
  | exec_function_internal:
      forall s f args m m' stk,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      step (Callstate s (Internal f) args m)
        E0 (State s f (Vptr stk Int.zero) f.(fn_entrypoint) (init_locs args f.(fn_params)) m')
  | exec_function_external:
      forall s ef t args res m m',
      external_call ef ge args m t res m' ->
      step (Callstate s (External ef) args m)
         t (Returnstate s res m')
  | exec_return:
      forall res f sp rs pc s vres m,
      step (Returnstate (Stackframe res f sp rs pc :: s) vres m)
        E0 (State s f sp pc (Locmap.set res vres rs) m).

End RELSEM.

(** Execution of a whole program boils down to invoking its main
  function.  The result of the program is the return value of the
  main function, to be found in the machine register dictated
  by the calling conventions. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      initial_state p (Callstate nil f nil m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall n m,
      final_state (Returnstate nil (Vint n) m) n.

Definition exec_program (p: program) (beh: program_behavior) : Prop :=
  program_behaves step (initial_state p) final_state (Genv.globalenv p) beh.

(** * Operations over LTL *)

(** Computation of the possible successors of an instruction.
  This is used in particular for dataflow analyses. *)

Definition successors_instr (i: instruction) : list node :=
  match i with
  | Lnop s => s :: nil
  | Lop op args res s => s :: nil
  | Lload chunk addr args dst s => s :: nil
  | Lstore chunk addr args src s => s :: nil
  | Lcall sig ros args res s => s :: nil
  | Ltailcall sig ros args => nil
  | Lbuiltin ef args res s => s :: nil
  | Lcond cond args ifso ifnot => ifso :: ifnot :: nil
  | Ljumptable arg tbl => tbl
  | Lreturn optarg => nil
  end.

Definition successors (f: function): PTree.t (list node) :=
  PTree.map (fun pc i => successors_instr i) f.(fn_code).
