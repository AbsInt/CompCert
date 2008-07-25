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

(** The LTLin intermediate language: abstract syntax and semantcs *)

(** The LTLin language is a variant of LTL where control-flow is not
    expressed as a graph of basic blocks, but as a linear list of
    instructions with explicit labels and ``goto'' instructions. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import Conventions.

(** * Abstract syntax *)

Definition label := positive.

(** LTLin instructions are similar to those of LTL.
  Except the last three, these instructions continue in sequence
  with the next instruction in the linear list of instructions.
  Unconditional branches [Lgoto] and conditional branches [Lcond]
  transfer control to the given code label.  Labels are explicitly
  inserted in the instruction list as pseudo-instructions [Llabel]. *)

Inductive instruction: Set :=
  | Lop: operation -> list loc -> loc -> instruction
  | Lload: memory_chunk -> addressing -> list loc -> loc -> instruction
  | Lstore: memory_chunk -> addressing -> list loc -> loc -> instruction
  | Lcall: signature -> loc + ident -> list loc -> loc -> instruction
  | Ltailcall: signature -> loc + ident -> list loc -> instruction
  | Lalloc: loc -> loc -> instruction
  | Llabel: label -> instruction
  | Lgoto: label -> instruction
  | Lcond: condition -> list loc -> label -> instruction
  | Lreturn: option loc -> instruction.

Definition code: Set := list instruction.

Record function: Set := mkfunction {
  fn_sig: signature;
  fn_params: list loc;
  fn_stacksize: Z;
  fn_code: code
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => f.(fn_sig)
  | External ef => ef.(ef_sig)
  end.

Definition genv := Genv.t fundef.
Definition locset := Locmap.t.

(** * Operational semantics *)

(** Looking up labels in the instruction list.  *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Llabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Llabel lbl else instr <> Llabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

(** [find_label lbl c] returns a list of instruction, suffix of the
  code [c], that immediately follows the [Llabel lbl] pseudo-instruction.
  If the label [lbl] is multiply-defined, the first occurrence is
  retained.  If the label [lbl] is not defined, [None] is returned. *)

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | i1 :: il => if is_label lbl i1 then Some il else find_label lbl il
  end.

(** The states of the dynamic semantics are similar to those used
  in the LTL semantics (see module [LTL]).  The only difference
  is that program points [pc] (nodes of the CFG in LTL) become
  code sequences [c] (suffixes of the code of the current function).
*)

Inductive stackframe : Set :=
  | Stackframe:
      forall (res: loc)       (**r where to store the result *)
             (f: function)    (**r calling function *)
             (sp: val)        (**r stack pointer in calling function *)
             (ls: locset)     (**r location state in calling function *)
             (c: code),       (**r program point in calling function *)
      stackframe.

Inductive state : Set :=
  | State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r function currently executing *)
             (sp: val)                (**r stack pointer *)
             (c: code)                (**r current program point *)
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

(*
Definition parent_callsig (stack: list stackframe) : signature :=
  match stack with
  | nil => mksignature nil (Some Tint)
  | Stackframe sg res f sp ls pc :: stack' => sg
  end.
*)

Section RELSEM.

Variable ge: genv.

Definition find_function (ros: loc + ident) (rs: locset) : option fundef :=
  match ros with
  | inl r => Genv.find_funct ge (rs r)
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

Inductive step: state -> trace -> state -> Prop :=
  | exec_Lop:
      forall s f sp op args res b rs m v,
      eval_operation ge sp op (map rs args) m = Some v ->
      step (State s f sp (Lop op args res :: b) rs m)
        E0 (State s f sp b (Locmap.set res v rs) m)
  | exec_Lload:
      forall s f sp chunk addr args dst b rs m a v,
      eval_addressing ge sp addr (map rs args) = Some a ->
      loadv chunk m a = Some v ->
      step (State s f sp (Lload chunk addr args dst :: b) rs m)
        E0 (State s f sp b (Locmap.set dst v rs) m)
  | exec_Lstore:
      forall s f sp chunk addr args src b rs m m' a,
      eval_addressing ge sp addr (map rs args) = Some a ->
      storev chunk m a (rs src) = Some m' ->
      step (State s f sp (Lstore chunk addr args src :: b) rs m)
        E0 (State s f sp b rs m')
  | exec_Lcall:
      forall s f sp sig ros args res b rs m f',
      find_function ros rs = Some f' ->
      sig = funsig f' ->
      step (State s f sp (Lcall sig ros args res :: b) rs m)
        E0 (Callstate (Stackframe res f sp (postcall_regs rs) b :: s)
                      f' (List.map rs args) m)
  | exec_Ltailcall:
      forall s f stk sig ros args b rs m f',
      find_function ros rs = Some f' ->
      sig = funsig f' ->
      step (State s f (Vptr stk Int.zero) (Ltailcall sig ros args :: b) rs m)
        E0 (Callstate s f' (List.map rs args) (Mem.free m stk))
  | exec_Lalloc:
      forall s f sp arg res b rs m sz m' blk,
      rs arg = Vint sz ->
      Mem.alloc m 0 (Int.signed sz) = (m', blk) ->
      step (State s f sp (Lalloc arg res :: b) rs m)
        E0 (State s f sp b (Locmap.set res (Vptr blk Int.zero) (postcall_regs rs)) m')
  | exec_Llabel:
      forall s f sp lbl b rs m,
      step (State s f sp (Llabel lbl :: b) rs m)
        E0 (State s f sp b rs m)
  | exec_Lgoto:
      forall s f sp lbl b rs m b',
      find_label lbl f.(fn_code) = Some b' ->
      step (State s f sp (Lgoto lbl :: b) rs m)
        E0 (State s f sp b' rs m)
  | exec_Lcond_true:
      forall s f sp cond args lbl b rs m b',
      eval_condition cond (map rs args) m = Some true ->
      find_label lbl f.(fn_code) = Some b' ->
      step (State s f sp (Lcond cond args lbl :: b) rs m)
        E0 (State s f sp b' rs m)
  | exec_Lcond_false:
      forall s f sp cond args lbl b rs m,
      eval_condition cond (map rs args) m = Some false ->
      step (State s f sp (Lcond cond args lbl :: b) rs m)
        E0 (State s f sp b rs m)
  | exec_Lreturn:
      forall s f stk rs m or b,
      step (State s f (Vptr stk Int.zero) (Lreturn or :: b) rs m)
        E0 (Returnstate s (locmap_optget or Vundef rs) (Mem.free m stk))
  | exec_function_internal:
      forall s f args m m' stk,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      step (Callstate s (Internal f) args m)
        E0 (State s f (Vptr stk Int.zero) f.(fn_code) (init_locs args f.(fn_params)) m')
  | exec_function_external:
      forall s ef args t res m,
      event_match ef args t res ->
      step (Callstate s (External ef) args m)
         t (Returnstate s res m)
  | exec_return:
      forall res f sp rs b s vres m,
      step (Returnstate (Stackframe res f sp rs b :: s) vres m)
        E0 (State s f sp b (Locmap.set res vres rs) m).

End RELSEM.

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

(** * Properties of the operational semantics *)

Lemma find_label_is_tail:
  forall lbl c c', find_label lbl c = Some c' -> is_tail c' c.
Proof.
  induction c; simpl; intros.
  discriminate.
  destruct (is_label lbl a). inv H. constructor. constructor.
  constructor. auto.
Qed.
  
