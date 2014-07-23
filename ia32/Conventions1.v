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

(** Function calling conventions and other conventions regarding the use of 
    machine registers and stack slots. *)

Require Import Coqlib.
Require Import AST.
Require Import Events.
Require Import Locations.

(** * Classification of machine registers *)

(** Machine registers (type [mreg] in module [Locations]) are divided in
  the following groups:
- Callee-save registers, whose value is preserved across a function call.
- Caller-save registers that can be modified during a function call.

  We follow the x86-32 application binary interface (ABI) in our choice
  of callee- and caller-save registers.
*)

Definition int_caller_save_regs := AX :: CX :: DX :: nil.

Definition float_caller_save_regs := X0 :: X1 :: X2 :: X3 :: X4 :: X5 :: X6 :: X7 :: nil.

Definition int_callee_save_regs := BX :: SI :: DI :: BP :: nil.

Definition float_callee_save_regs : list mreg := nil.

Definition destroyed_at_call :=
  FP0 :: int_caller_save_regs ++ float_caller_save_regs.

Definition dummy_int_reg := AX.     (**r Used in [Regalloc]. *)
Definition dummy_float_reg := X0.   (**r Used in [Regalloc]. *)

(** The [index_int_callee_save] and [index_float_callee_save] associate
  a unique positive integer to callee-save registers.  This integer is
  used in [Stacking] to determine where to save these registers in
  the activation record if they are used by the current function. *)

Definition index_int_callee_save (r: mreg) :=
  match r with
  | BX => 0 | SI => 1 | DI => 2 | BP => 3 | _ => -1
  end.

Definition index_float_callee_save (r: mreg) := -1.

Ltac ElimOrEq :=
  match goal with
  |  |- (?x = ?y) \/ _ -> _ =>
       let H := fresh in
       (intro H; elim H; clear H;
        [intro H; rewrite <- H; clear H | ElimOrEq])
  |  |- False -> _ =>
       let H := fresh in (intro H; contradiction)
  end.

Ltac OrEq :=
  match goal with
  | |- (?x = ?x) \/ _ => left; reflexivity
  | |- (?x = ?y) \/ _ => right; OrEq
  | |- False => fail
  end.

Ltac NotOrEq :=
  match goal with
  | |- (?x = ?y) \/ _ -> False =>
       let H := fresh in (
       intro H; elim H; clear H; [intro; discriminate | NotOrEq])
  | |- False -> False =>
       contradiction
  end.

Lemma index_int_callee_save_pos:
  forall r, In r int_callee_save_regs -> index_int_callee_save r >= 0.
Proof.
  intro r. simpl; ElimOrEq; unfold index_int_callee_save; omega.
Qed.

Lemma index_float_callee_save_pos:
  forall r, In r float_callee_save_regs -> index_float_callee_save r >= 0.
Proof.
  intro r. simpl; ElimOrEq; unfold index_float_callee_save; omega.
Qed.

Lemma index_int_callee_save_pos2:
  forall r, index_int_callee_save r >= 0 -> In r int_callee_save_regs.
Proof.
  destruct r; simpl; intro; omegaContradiction || OrEq.
Qed.

Lemma index_float_callee_save_pos2:
  forall r, index_float_callee_save r >= 0 -> In r float_callee_save_regs.
Proof.
  unfold index_float_callee_save; intros. omegaContradiction.
Qed.

Lemma index_int_callee_save_inj:
  forall r1 r2, 
  In r1 int_callee_save_regs ->
  In r2 int_callee_save_regs ->
  r1 <> r2 ->
  index_int_callee_save r1 <> index_int_callee_save r2.
Proof.
  intros r1 r2. 
  simpl; ElimOrEq; ElimOrEq; unfold index_int_callee_save;
  intros; congruence.
Qed.

Lemma index_float_callee_save_inj:
  forall r1 r2, 
  In r1 float_callee_save_regs ->
  In r2 float_callee_save_regs ->
  r1 <> r2 ->
  index_float_callee_save r1 <> index_float_callee_save r2.
Proof.
  simpl; intros. contradiction.
Qed.

(** The following lemmas show that
    (destroyed at call, integer callee-save, float callee-save)
    is a partition of the set of machine registers. *)

Lemma int_float_callee_save_disjoint:
  list_disjoint int_callee_save_regs float_callee_save_regs.
Proof.
  red; intros r1 r2. simpl; ElimOrEq; ElimOrEq; discriminate.
Qed.

Lemma register_classification:
  forall r, 
  In r destroyed_at_call \/ In r int_callee_save_regs \/ In r float_callee_save_regs.
Proof.
  destruct r; 
  try (left; simpl; OrEq);
  try (right; left; simpl; OrEq);
  try (right; right; simpl; OrEq).
Qed.

Lemma int_callee_save_not_destroyed:
  forall r, 
    In r destroyed_at_call -> In r int_callee_save_regs -> False.
Proof.
  intros. revert H0 H. simpl. ElimOrEq; NotOrEq.
Qed.

Lemma float_callee_save_not_destroyed:
  forall r, 
    In r destroyed_at_call -> In r float_callee_save_regs -> False.
Proof.
  intros. revert H0 H. simpl. ElimOrEq; NotOrEq.
Qed.

Lemma int_callee_save_type:
  forall r, In r int_callee_save_regs -> mreg_type r = Tany32.
Proof.
  intro. simpl; ElimOrEq; reflexivity.
Qed.

Lemma float_callee_save_type:
  forall r, In r float_callee_save_regs -> mreg_type r = Tany64.
Proof.
  intro. simpl; ElimOrEq; reflexivity.
Qed.

Ltac NoRepet :=
  match goal with
  | |- list_norepet nil =>
      apply list_norepet_nil
  | |- list_norepet (?a :: ?b) =>
      apply list_norepet_cons; [simpl; intuition discriminate | NoRepet]
  end.

Lemma int_callee_save_norepet:
  list_norepet int_callee_save_regs.
Proof.
  unfold int_callee_save_regs; NoRepet.
Qed.

Lemma float_callee_save_norepet:
  list_norepet float_callee_save_regs.
Proof.
  unfold float_callee_save_regs; NoRepet.
Qed.

(** * Function calling conventions *)

(** The functions in this section determine the locations (machine registers
  and stack slots) used to communicate arguments and results between the
  caller and the callee during function calls.  These locations are functions
  of the signature of the function and of the call instruction.  
  Agreement between the caller and the callee on the locations to use
  is guaranteed by our dynamic semantics for Cminor and RTL, which demand 
  that the signature of the call instruction is identical to that of the
  called function.

  Calling conventions are largely arbitrary: they must respect the properties
  proved in this section (such as no overlapping between the locations
  of function arguments), but this leaves much liberty in choosing actual
  locations.  To ensure binary interoperability of code generated by our
  compiler with libraries compiled by another compiler, we
  implement the standard x86 conventions. *)

(** ** Location of function result *)

(** The result value of a function is passed back to the caller in
  registers [AX] or [FP0], depending on the type of the returned value.
  We treat a function without result as a function with one integer result. *)

Definition loc_result (s: signature) : list mreg :=
  match s.(sig_res) with
  | None => AX :: nil
  | Some (Tint | Tany32) => AX :: nil
  | Some (Tfloat | Tsingle) => FP0 :: nil
  | Some Tany64 => X0 :: nil
  | Some Tlong => DX :: AX :: nil
  end.

(** The result registers have types compatible with that given in the signature. *)

Lemma loc_result_type:
  forall sig,
  subtype_list (proj_sig_res' sig) (map mreg_type (loc_result sig)) = true.
Proof.
  intros. unfold proj_sig_res', loc_result. destruct (sig_res sig) as [[]|]; auto.
Qed.

(** The result locations are caller-save registers *)

Lemma loc_result_caller_save:
  forall (s: signature) (r: mreg),
  In r (loc_result s) -> In r destroyed_at_call.
Proof.
  intros.
  assert (r = AX \/ r = DX \/ r = FP0 \/ r = X0).
    unfold loc_result in H. destruct (sig_res s) as [[]|]; simpl in H; intuition.
  destruct H0 as [A | [A | [A | A]]]; subst r; simpl; OrEq.
Qed.

(** ** Location of function arguments *)

(** All arguments are passed on stack. (Snif.) *)

Fixpoint loc_arguments_rec
    (tyl: list typ) (ofs: Z) {struct tyl} : list loc :=
  match tyl with
  | nil => nil
  | Tint :: tys => S Outgoing ofs Tint :: loc_arguments_rec tys (ofs + 1)
  | Tfloat :: tys => S Outgoing ofs Tfloat :: loc_arguments_rec tys (ofs + 2)
  | Tsingle :: tys => S Outgoing ofs Tsingle :: loc_arguments_rec tys (ofs + 1)
  | Tlong :: tys => S Outgoing (ofs + 1) Tint :: S Outgoing ofs Tint :: loc_arguments_rec tys (ofs + 2)
  | Tany32 :: tys => S Outgoing ofs Tany32 :: loc_arguments_rec tys (ofs + 1)
  | Tany64 :: tys => S Outgoing ofs Tany64 :: loc_arguments_rec tys (ofs + 2)
  end.

(** [loc_arguments s] returns the list of locations where to store arguments
  when calling a function with signature [s].  *)

Definition loc_arguments (s: signature) : list loc :=
  loc_arguments_rec s.(sig_args) 0.

(** [size_arguments s] returns the number of [Outgoing] slots used
  to call a function with signature [s]. *)

Fixpoint size_arguments_rec
    (tyl: list typ) (ofs: Z) {struct tyl} : Z :=
  match tyl with
  | nil => ofs
  | ty :: tys => size_arguments_rec tys (ofs + typesize ty)
  end.

Definition size_arguments (s: signature) : Z :=
  size_arguments_rec s.(sig_args) 0.

(** Argument locations are either caller-save registers or [Outgoing] 
  stack slots at nonnegative offsets. *)

Definition loc_argument_acceptable (l: loc) : Prop :=
  match l with
  | R r => In r destroyed_at_call
  | S Outgoing ofs ty => ofs >= 0 /\ ty <> Tlong
  | _ => False
  end.

Remark loc_arguments_rec_charact:
  forall tyl ofs l,
  In l (loc_arguments_rec tyl ofs) ->
  match l with
  | S Outgoing ofs' ty => ofs' >= ofs /\ ty <> Tlong
  | _ => False
  end.
Proof.
  induction tyl; simpl loc_arguments_rec; intros.
- destruct H.
- assert (REC: forall ofs1, In l (loc_arguments_rec tyl ofs1) -> ofs1 > ofs -> 
               match l with
               | R _ => False
               | S Local _ _ => False
               | S Incoming _ _ => False
               | S Outgoing ofs' ty => ofs' >= ofs /\ ty <> Tlong
               end).
  { intros. exploit IHtyl; eauto. destruct l; auto. destruct sl; intuition omega
. }
  destruct a; simpl in H; repeat (destruct H);
  ((eapply REC; eauto; omega) || (split; [omega|congruence])).
Qed.

Lemma loc_arguments_acceptable:
  forall (s: signature) (l: loc),
  In l (loc_arguments s) -> loc_argument_acceptable l.
Proof.
  unfold loc_arguments; intros.
  exploit loc_arguments_rec_charact; eauto. 
  unfold loc_argument_acceptable.
  destruct l; tauto.
Qed.

Hint Resolve loc_arguments_acceptable: locs.

(** The offsets of [Outgoing] arguments are below [size_arguments s]. *)

Remark size_arguments_rec_above:
  forall tyl ofs0, ofs0 <= size_arguments_rec tyl ofs0.
Proof.
  induction tyl; simpl; intros.
  omega.
  apply Zle_trans with (ofs0 + typesize a); auto. 
  generalize (typesize_pos a); omega.
Qed.

Lemma size_arguments_above:
  forall s, size_arguments s >= 0.
Proof.
  intros; unfold size_arguments. apply Zle_ge.  
  apply size_arguments_rec_above.
Qed.

Lemma loc_arguments_bounded:
  forall (s: signature) (ofs: Z) (ty: typ),
  In (S Outgoing ofs ty) (loc_arguments s) ->
  ofs + typesize ty <= size_arguments s.
Proof.
  intros until ty. unfold loc_arguments, size_arguments. generalize (sig_args s) 0.
  induction l; simpl; intros.
- contradiction.
- Ltac decomp :=
  match goal with
  | [ H: _ \/ _ |- _ ] => destruct H; decomp
  | [ H: S _ _ _ = S _ _ _ |- _ ] => inv H
  | _ => idtac
  end.
  destruct a; simpl in H; decomp; auto; try apply size_arguments_rec_above.
  simpl typesize. replace (z + 1 + 1) with (z + 2) by omega. apply size_arguments_rec_above.
  simpl typesize. apply Zle_trans with (ofs + 2). omega. apply size_arguments_rec_above.
Qed.

Lemma loc_arguments_main:
  loc_arguments signature_main = nil.
Proof.
  reflexivity.
Qed.
