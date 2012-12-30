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
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import LTL.

(** * Abstract syntax *)

Definition label := positive.

(** LTLin instructions are similar to those of LTL.
  Except the last three, these instructions continue in sequence
  with the next instruction in the linear list of instructions.
  Unconditional branches [Lgoto] and conditional branches [Lcond]
  transfer control to the given code label.  Labels are explicitly
  inserted in the instruction list as pseudo-instructions [Llabel]. *)

Inductive instruction: Type :=
  | Lop: operation -> list loc -> loc -> instruction
  | Lload: memory_chunk -> addressing -> list loc -> loc -> instruction
  | Lstore: memory_chunk -> addressing -> list loc -> loc -> instruction
  | Lcall: signature -> loc + ident -> list loc -> loc -> instruction
  | Ltailcall: signature -> loc + ident -> list loc -> instruction
  | Lbuiltin: external_function -> list loc -> loc -> instruction
  | Llabel: label -> instruction
  | Lgoto: label -> instruction
  | Lcond: condition -> list loc -> label -> instruction
  | Ljumptable: loc -> list label -> instruction
  | Lreturn: option loc -> instruction.

Definition code: Type := list instruction.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_params: list loc;
  fn_stacksize: Z;
  fn_code: code
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

Definition genv := Genv.t fundef unit.
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

Inductive stackframe : Type :=
  | Stackframe:
      forall (res: loc)       (**r where to store the result *)
             (f: function)    (**r calling function *)
             (sp: val)        (**r stack pointer in calling function *)
             (ls: locset)     (**r location state in calling function *)
             (c: code),       (**r program point in calling function *)
      stackframe.

Inductive state : Type :=
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
        E0 (State s f sp b (Locmap.set res v (undef_temps rs)) m)
  | exec_Lload:
      forall s f sp chunk addr args dst b rs m a v,
      eval_addressing ge sp addr (map rs args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      step (State s f sp (Lload chunk addr args dst :: b) rs m)
        E0 (State s f sp b (Locmap.set dst v (undef_temps rs)) m)
  | exec_Lstore:
      forall s f sp chunk addr args src b rs m m' a,
      eval_addressing ge sp addr (map rs args) = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      step (State s f sp (Lstore chunk addr args src :: b) rs m)
        E0 (State s f sp b (undef_temps rs) m')
  | exec_Lcall:
      forall s f sp sig ros args res b rs m f',
      find_function ros rs = Some f' ->
      sig = funsig f' ->
      step (State s f sp (Lcall sig ros args res :: b) rs m)
        E0 (Callstate (Stackframe res f sp (postcall_locs rs) b :: s)
                      f' (List.map rs args) m)
  | exec_Ltailcall:
      forall s f stk sig ros args b rs m f' m',
      find_function ros rs = Some f' ->
      sig = funsig f' ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s f (Vptr stk Int.zero) (Ltailcall sig ros args :: b) rs m)
        E0 (Callstate s f' (List.map rs args) m')
  | exec_Lbuiltin:
      forall s f sp rs m ef args res b t v m',
      external_call ef ge (map rs args) m t v m' ->
      step (State s f sp (Lbuiltin ef args res :: b) rs m)
         t (State s f sp b (Locmap.set res v rs) m')
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
        E0 (State s f sp b' (undef_temps rs) m)
  | exec_Lcond_false:
      forall s f sp cond args lbl b rs m,
      eval_condition cond (map rs args) m = Some false ->
      step (State s f sp (Lcond cond args lbl :: b) rs m)
        E0 (State s f sp b (undef_temps rs) m)
  | exec_Ljumptable:
      forall s f sp arg tbl b rs m n lbl b',
      rs arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      find_label lbl f.(fn_code) = Some b' ->
      step (State s f sp (Ljumptable arg tbl :: b) rs m)
        E0 (State s f sp b' (undef_temps rs) m)
  | exec_Lreturn:
      forall s f stk rs m or b m',
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s f (Vptr stk Int.zero) (Lreturn or :: b) rs m)
        E0 (Returnstate s (locmap_optget or Vundef rs) m')
  | exec_function_internal:
      forall s f args m m' stk,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      step (Callstate s (Internal f) args m)
        E0 (State s f (Vptr stk Int.zero) f.(fn_code) (init_locs args f.(fn_params)) m')
  | exec_function_external:
      forall s ef args t res m m',
      external_call ef ge args m t res m' ->
      step (Callstate s (External ef) args m)
         t (Returnstate s res m')
  | exec_return:
      forall res f sp rs b s vres m,
      step (Returnstate (Stackframe res f sp rs b :: s) vres m)
        E0 (State s f sp b (Locmap.set res vres rs) m).

End RELSEM.

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

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

(** * Properties of the operational semantics *)

Lemma find_label_is_tail:
  forall lbl c c', find_label lbl c = Some c' -> is_tail c' c.
Proof.
  induction c; simpl; intros.
  discriminate.
  destruct (is_label lbl a). inv H. constructor. constructor.
  constructor. auto.
Qed.
  
