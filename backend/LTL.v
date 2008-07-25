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
Require Import Mem.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Conventions.

(** * Abstract syntax *)

(** LTL is close to RTL, but uses locations instead of pseudo-registers. *)

Definition node := positive.

Inductive instruction: Set :=
  | Lnop: node -> instruction
  | Lop: operation -> list loc -> loc -> node -> instruction
  | Lload: memory_chunk -> addressing -> list loc -> loc -> node -> instruction
  | Lstore: memory_chunk -> addressing -> list loc -> loc -> node -> instruction
  | Lcall: signature -> loc + ident -> list loc -> loc -> node -> instruction
  | Ltailcall: signature -> loc + ident -> list loc -> instruction
  | Lalloc: loc -> loc -> node -> instruction
  | Lcond: condition -> list loc -> node -> node -> instruction
  | Lreturn: option loc -> instruction.

Definition code: Set := PTree.t instruction.

Record function: Set := mkfunction {
  fn_sig: signature;
  fn_params: list loc;
  fn_stacksize: Z;
  fn_code: code;
  fn_entrypoint: node;
  fn_nextpc: node;
  fn_code_wf: forall (pc: node), Plt pc fn_nextpc \/ fn_code!pc = None
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => f.(fn_sig)
  | External ef => ef.(ef_sig)
  end.

(** * Operational semantics *)

Definition genv := Genv.t fundef.
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


Section RELSEM.

(** [parmov srcs dsts ls] performs the parallel assignment
  of locations [dsts] to the values of the corresponding locations
  [srcs].  *)

Fixpoint parmov (srcs dsts: list loc) (ls: locset) {struct srcs} : locset :=
  match srcs, dsts with
  | s1 :: sl, d1 :: dl => Locmap.set d1 (ls s1) (parmov sl dl ls)
  | _, _ => ls
  end.

(** [postcall_regs ls] returns the location set [ls] after a function
  call.  Caller-save registers and temporary registers
  are set to [undef], reflecting the fact that the called
  function can modify them freely. *)

Definition postcall_regs (ls: locset) : locset :=
  fun (l: loc) =>
    match l with
    | R r =>
        if In_dec Loc.eq (R r) Conventions.temporaries then
          Vundef
        else if In_dec Loc.eq (R r) Conventions.destroyed_at_call then
          Vundef
        else
          ls (R r)
    | S s => ls (S s)
    end.

(** LTL execution states. *)

Inductive stackframe : Set :=
  | Stackframe:
      forall (res: loc)         (**r where to store the result *)
             (f: function)      (**r calling function *)
             (sp: val)          (**r stack pointer in calling function *)
             (ls: locset)       (**r location state in calling function *)
             (pc: node),        (**r program point in calling function *)
      stackframe.

Inductive state : Set :=
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

(** The main difference between the LTL transition relation
  and the RTL transition relation is the handling of function calls.
  In RTL, arguments and results to calls are transmitted via
  [vargs] and [vres] components of [Callstate] and [Returnstate],
  respectively.  The semantics takes care of transferring these values
  between the pseudo-registers of the caller and of the callee.
  
  In lower-level intermediate languages (e.g [Linear], [Mach], [PPC]),
  arguments and results are transmitted implicitly: the generated
  code for the caller arranges for arguments to be left in conventional
  registers and stack locations, as determined by the calling conventions,
  where the function being called will find them.  Similarly,
  conventional registers will be used to pass the result value back
  to the caller.

  In LTL, we take an hybrid view of argument and result passing.
  The LTL code does not contain (yet) instructions for moving
  arguments and results to the conventional registers.  However,
  the dynamic semantics "goes through the motions" of such code:
- The [exec_Lcall] transition from [State] to [Callstate]
  leaves the values of arguments in the conventional locations
  given by [loc_arguments].
- The [exec_function_internal] transition from [Callstate] to [State]
  changes the view of stack slots ([Outgoing] slots slide to
  [Incoming] slots as per [call_regs]), then recovers the
  values of parameters from the conventional locations given by
  [loc_parameters].
- The [exec_Lreturn] transition from [State] to [Returnstate]
  moves the result value to the conventional location [loc_result],
  then restores the values of callee-save locations from
  the location state of the caller, using [return_regs].
- The [exec_return] transition from [Returnstate] to [State]
  reads the result value from the conventional location [loc_result],
  then stores it in the result location for the [Lcall] instruction.

This complicated protocol will make it much easier to prove
the correctness of the [Stacking] pass later, which inserts actual
code that performs all the shuffling of arguments and results
described above.
*)

Inductive step: state -> trace -> state -> Prop :=
  | exec_Lnop:
      forall s f sp pc rs m pc',
      (fn_code f)!pc = Some(Lnop pc') ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m)
  | exec_Lop:
      forall s f sp pc rs m op args res pc' v,
      (fn_code f)!pc = Some(Lop op args res pc') ->
      eval_operation ge sp op (map rs args) m = Some v ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' (Locmap.set res v rs) m)
  | exec_Lload:
      forall s f sp pc rs m chunk addr args dst pc' a v,
      (fn_code f)!pc = Some(Lload chunk addr args dst pc') ->
      eval_addressing ge sp addr (map rs args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' (Locmap.set dst v rs) m)
  | exec_Lstore:
      forall s f sp pc rs m chunk addr args src pc' a m',
      (fn_code f)!pc = Some(Lstore chunk addr args src pc') ->
      eval_addressing ge sp addr (map rs args) = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m')
  | exec_Lcall:
      forall s f sp pc rs m sig ros args res pc' f',
      (fn_code f)!pc = Some(Lcall sig ros args res pc') ->
      find_function ros rs = Some f' ->
      funsig f' = sig ->
      step (State s f sp pc rs m)
        E0 (Callstate (Stackframe res f sp (postcall_regs rs) pc' :: s)
                      f' (List.map rs args) m)
  | exec_Ltailcall:
      forall s f stk pc rs m sig ros args f',
      (fn_code f)!pc = Some(Ltailcall sig ros args) ->
      find_function ros rs = Some f' ->
      funsig f' = sig ->
      step (State s f (Vptr stk Int.zero) pc rs m)
        E0 (Callstate s f' (List.map rs args) (Mem.free m stk))
  | exec_Lalloc:
      forall s f sp pc rs m pc' arg res sz m' b,
      (fn_code f)!pc = Some(Lalloc arg res pc') ->
      rs arg = Vint sz ->
      Mem.alloc m 0 (Int.signed sz) = (m', b) ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' (Locmap.set res (Vptr b Int.zero) (postcall_regs rs)) m')
  | exec_Lcond_true:
      forall s f sp pc rs m cond args ifso ifnot,
      (fn_code f)!pc = Some(Lcond cond args ifso ifnot) ->
      eval_condition cond (map rs args) m = Some true ->
      step (State s f sp pc rs m)
        E0 (State s f sp ifso rs m)
  | exec_Lcond_false:
      forall s f sp pc rs m cond args ifso ifnot,
      (fn_code f)!pc = Some(Lcond cond args ifso ifnot) ->
      eval_condition cond (map rs args) m = Some false ->
      step (State s f sp pc rs m)
        E0 (State s f sp ifnot rs m)
  | exec_Lreturn:
      forall s f stk pc rs m or,
      (fn_code f)!pc = Some(Lreturn or) ->
      step (State s f (Vptr stk Int.zero) pc rs m)
        E0 (Returnstate s (locmap_optget or Vundef rs) (Mem.free m stk))
  | exec_function_internal:
      forall s f args m m' stk,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      step (Callstate s (Internal f) args m)
        E0 (State s f (Vptr stk Int.zero) f.(fn_entrypoint) (init_locs args f.(fn_params)) m')
  | exec_function_external:
      forall s ef t args res m,
      event_match ef args t res ->
      step (Callstate s (External ef) args m)
         t (Returnstate s res m)
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
  | initial_state_intro: forall b f,
      let ge := Genv.globalenv p in
      let m0 := Genv.init_mem p in
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

Definition successors (f: function) (pc: node) : list node :=
  match f.(fn_code)!pc with
  | None => nil
  | Some i =>
      match i with
      | Lnop s => s :: nil
      | Lop op args res s => s :: nil
      | Lload chunk addr args dst s => s :: nil
      | Lstore chunk addr args src s => s :: nil
      | Lcall sig ros args res s => s :: nil
      | Ltailcall sig ros args => nil
      | Lalloc arg res s => s :: nil
      | Lcond cond args ifso ifnot => ifso :: ifnot :: nil
      | Lreturn optarg => nil
      end
  end.
