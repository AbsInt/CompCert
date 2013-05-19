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
Require Import Locations.

(** * Classification of machine registers *)

(** Machine registers (type [mreg] in module [Locations]) are divided in
  the following groups:
- Temporaries used for spilling, reloading, and parallel move operations.
- Allocatable registers, that can be assigned to RTL pseudo-registers.
  These are further divided into:
-- Callee-save registers, whose value is preserved across a function call.
-- Caller-save registers that can be modified during a function call.

  We follow the PowerPC application binary interface (ABI) in our choice
  of callee- and caller-save registers.
*)

Definition int_caller_save_regs :=
  R0 :: R1 :: R2 :: R3 :: R12 :: nil.

Definition float_caller_save_regs :=
  F0 :: F1 :: F2 :: F3 :: F4 :: F5 :: F6 :: F7 :: nil.

Definition int_callee_save_regs :=
  R4 :: R5 :: R6 :: R7 :: R8 :: R9 :: R10 :: R11 :: nil.

Definition float_callee_save_regs :=
  F8 :: F9 :: F10 :: F11 :: F12 :: F13 :: F14 :: F15 :: nil.

Definition destroyed_at_call :=
  int_caller_save_regs ++ float_caller_save_regs.

Definition dummy_int_reg := R0.     (**r Used in [Coloring]. *)
Definition dummy_float_reg := F0.   (**r Used in [Coloring]. *)

(** The [index_int_callee_save] and [index_float_callee_save] associate
  a unique positive integer to callee-save registers.  This integer is
  used in [Stacking] to determine where to save these registers in
  the activation record if they are used by the current function. *)

Definition index_int_callee_save (r: mreg) :=
  match r with
  | R4 => 0  | R5 => 1  | R6 => 2  | R7 => 3
  | R8 => 4  | R9 => 5  | R10 => 6 | R11 => 7
  | _ => -1
  end.

Definition index_float_callee_save (r: mreg) :=
  match r with
  | F8 => 0  | F9 => 1  | F10 => 2  | F11 => 3
  | F12 => 4  | F13 => 5  | F14 => 6  | F15 => 7
  | _ => -1
  end.

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
  destruct r; simpl; intro; omegaContradiction || OrEq.
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
  intros r1 r2. 
  simpl; ElimOrEq; ElimOrEq; unfold index_float_callee_save;
  intros; congruence.
Qed.

(** The following lemmas show that
    (temporaries, destroyed at call, integer callee-save, float callee-save)
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
  forall r, In r int_callee_save_regs -> mreg_type r = Tint.
Proof.
  intro. simpl; ElimOrEq; reflexivity.
Qed.

Lemma float_callee_save_type:
  forall r, In r float_callee_save_regs -> mreg_type r = Tfloat.
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
  locations.  *)

(** ** Location of function result *)

(** The result value of a function is passed back to the caller in
  registers [R0] or [F0] or [R0,R1], depending on the type of the
  returned value.  We treat a function without result as a function
  with one integer result. *)

Definition loc_result (s: signature) : list mreg :=
  match s.(sig_res) with
  | None => R0 :: nil
  | Some Tint => R0 :: nil
  | Some (Tfloat | Tsingle) => F0 :: nil
  | Some Tlong => R1 :: R0 :: nil
  end.

(** The result location is a caller-save register or a temporary *)

Lemma loc_result_caller_save:
  forall (s: signature) (r: mreg), 
  In r (loc_result s) -> In r destroyed_at_call.
Proof.
  intros.
  assert (r = R0 \/ r = R1 \/ r = F0).
    unfold loc_result in H. destruct (sig_res s); [destruct t|idtac]; simpl in H; intuition.
  destruct H0 as [A | [A | A]]; subst r; simpl; OrEq.
Qed.

(** ** Location of function arguments *)

(** We use the following calling conventions, adapted from the ARM EABI:
- The first 4 integer arguments are passed in registers [R0] to [R3].
- The first 2 float arguments are passed in registers [F0] and [F2].
- The first 4 float arguments are passed in registers [F0] to [F3].
- The first 2 integer arguments are passed in an aligned pair of two integer
  registers.
- Each float argument passed in a float register ``consumes'' an aligned pair
  of two integer registers.
- Each single argument passed in a float register ``consumes'' an integer
  register.
- Extra arguments are passed on the stack, in [Outgoing] slots, consecutively
  assigned (1 word for an integer or single argument, 2 words for a float
  or a long), starting at word offset 0.

This convention is not quite that of the ARM EABI, whereas every float
argument are passed in one or two integer registers.  Unfortunately,
this does not fit the data model of CompCert.  In [PrintAsm.ml]
we insert additional code around function calls and returns that moves
data appropriately. *)

Definition ireg_param (n: Z) : mreg :=
  if zeq n (-4) then R0
  else if zeq n (-3) then R1
  else if zeq n (-2) then R2
  else R3.

Definition freg_param (n: Z) : mreg :=
  if zeq n (-4) then F0 else F2.

Definition sreg_param (n: Z) : mreg :=
  if zeq n (-4) then F0
  else if zeq n (-3) then F1
  else if zeq n (-2) then F2
  else F3.

Fixpoint loc_arguments_rec (tyl: list typ) (ofs: Z) {struct tyl} : list loc :=
  match tyl with
  | nil => nil
  | Tint :: tys =>
      (if zle 0 ofs then S Outgoing ofs Tint else R (ireg_param ofs))
      :: loc_arguments_rec tys (ofs + 1)
  | Tfloat :: tys =>
      let ofs := align ofs 2 in
      (if zle 0 ofs then S Outgoing ofs Tfloat else R (freg_param ofs))
      :: loc_arguments_rec tys (ofs + 2)
  | Tsingle :: tys =>
      (if zle 0 ofs then S Outgoing ofs Tsingle else R (sreg_param ofs))
      :: loc_arguments_rec tys (ofs + 1)
  | Tlong :: tys =>
      let ofs := align ofs 2 in
      (if zle 0 ofs then S Outgoing (ofs + 1) Tint else R (ireg_param (ofs + 1)))
      :: (if zle 0 ofs then S Outgoing ofs Tint else R (ireg_param ofs))
      :: loc_arguments_rec tys (ofs + 2)
  end.

(** [loc_arguments s] returns the list of locations where to store arguments
  when calling a function with signature [s].  *)

Definition loc_arguments (s: signature) : list loc :=
  loc_arguments_rec s.(sig_args) (-4).

(** [size_arguments s] returns the number of [Outgoing] slots used
  to call a function with signature [s]. *)

Fixpoint size_arguments_rec (tyl: list typ) (ofs: Z) {struct tyl} : Z :=
  match tyl with
  | nil => ofs
  | (Tint | Tsingle) :: tys => size_arguments_rec tys (ofs + 1)
  | (Tfloat | Tlong) :: tys => size_arguments_rec tys (align ofs 2 + 2)
  end.

Definition size_arguments (s: signature) : Z :=
  Zmax 0 (size_arguments_rec s.(sig_args) (-4)).

(** Argument locations are either non-temporary registers or [Outgoing] 
  stack slots at nonnegative offsets. *)

Definition loc_argument_acceptable (l: loc) : Prop :=
  match l with
  | R r => In r destroyed_at_call
  | S Outgoing ofs ty => ofs >= 0 /\ ty <> Tlong
  | _ => False
  end.

Remark ireg_param_caller_save:
  forall n, In (ireg_param n) destroyed_at_call.
Proof.
  unfold ireg_param; intros.
  destruct (zeq n (-4)). simpl; auto. 
  destruct (zeq n (-3)). simpl; auto. 
  destruct (zeq n (-2)); simpl; auto.
Qed.

Remark freg_param_caller_save:
  forall n, In (freg_param n) destroyed_at_call.
Proof.
  unfold freg_param; intros. destruct (zeq n (-4)); simpl; OrEq.
Qed.

Remark sreg_param_caller_save:
  forall n, In (sreg_param n) destroyed_at_call.
Proof.
  unfold sreg_param; intros.
  destruct (zeq n (-4)). simpl; tauto. 
  destruct (zeq n (-3)). simpl; tauto. 
  destruct (zeq n (-2)); simpl; tauto.
Qed.

Remark loc_arguments_rec_charact:
  forall tyl ofs l,
  In l (loc_arguments_rec tyl ofs) ->
  match l with
  | R r => In r destroyed_at_call
  | S Outgoing ofs' ty => ofs' >= 0 /\ ofs <= ofs' /\ ty <> Tlong
  | S _ _ _ => False
  end.
Proof.
  induction tyl; simpl loc_arguments_rec; intros.
  elim H.
  destruct a.
- (* Tint *)
  destruct H.
  subst l. destruct (zle 0 ofs).
  split. omega. split. omega. congruence.
  apply ireg_param_caller_save.
  exploit IHtyl; eauto. destruct l; auto. destruct sl; auto. intuition omega.
- (* Tfloat *)
  assert (ofs <= align ofs 2) by (apply align_le; omega).
  destruct H.
  subst l. destruct (zle 0 (align ofs 2)).
  split. omega. split. auto. congruence.
  apply freg_param_caller_save.
  exploit IHtyl; eauto. destruct l; auto. destruct sl; auto. intuition omega.
- (* Tlong *)
  assert (ofs <= align ofs 2) by (apply align_le; omega).
  destruct H.
  subst l. destruct (zle 0 (align ofs 2)).
  split. omega. split. omega. congruence.
  apply ireg_param_caller_save.
  destruct H.
  subst l. destruct (zle 0 (align ofs 2)).
  split. omega. split. omega. congruence.
  apply ireg_param_caller_save.
  exploit IHtyl; eauto. destruct l; auto. destruct sl; auto. intuition omega.
- (* Tsingle *)
  destruct H.
  subst l. destruct (zle 0 ofs).
  split. omega. split. omega. congruence.
  apply sreg_param_caller_save.
  exploit IHtyl; eauto. destruct l; auto. destruct sl; auto. intuition omega.
Qed.

Lemma loc_arguments_acceptable:
  forall (s: signature) (r: loc),
  In r (loc_arguments s) -> loc_argument_acceptable r.
Proof.
  unfold loc_arguments, loc_argument_acceptable; intros.
  generalize (loc_arguments_rec_charact _ _ _ H).
  destruct r; auto.
  destruct sl; auto.
  tauto.
Qed.
Hint Resolve loc_arguments_acceptable: locs.

(** The offsets of [Outgoing] arguments are below [size_arguments s]. *)

Remark size_arguments_rec_above:
  forall tyl ofs,
  ofs <= size_arguments_rec tyl ofs.
Proof.
  induction tyl; simpl; intros.
  omega.
  destruct a.
  apply Zle_trans with (ofs + 1); auto; omega.
  assert (ofs <= align ofs 2) by (apply align_le; omega).
  apply Zle_trans with (align ofs 2 + 2); auto; omega.
  assert (ofs <= align ofs 2) by (apply align_le; omega).
  apply Zle_trans with (align ofs 2 + 2); auto; omega.
  apply Zle_trans with (ofs + 1); auto; omega.
Qed.

Lemma size_arguments_above:
  forall s, size_arguments s >= 0.
Proof.
  intros; unfold size_arguments. apply Zle_ge. apply Zmax1.
Qed.

Lemma loc_arguments_bounded:
  forall (s: signature) (ofs: Z) (ty: typ),
  In (S Outgoing ofs ty) (loc_arguments s) ->
  ofs + typesize ty <= size_arguments s.
Proof.
  intros.
  assert (forall tyl ofs0,
          0 <= ofs0 ->
          ofs0 <= Zmax 0 (size_arguments_rec tyl ofs0)).
  {
    intros. generalize (size_arguments_rec_above tyl ofs0). intros.
    rewrite Zmax_spec. rewrite zlt_false. auto. omega.
  } 
  assert (forall tyl ofs0,
    In (S Outgoing ofs ty) (loc_arguments_rec tyl ofs0) ->
    ofs + typesize ty <= Zmax 0 (size_arguments_rec tyl ofs0)).
  {
    induction tyl; simpl; intros.
    elim H1.
    destruct a.
  - (* Tint *)
    destruct H1; auto. destruct (zle 0 ofs0); inv H1. apply H0. omega. 
  - (* Tfloat *)
    destruct H1; auto. destruct (zle 0 (align ofs0 2)); inv H1. apply H0. omega.
  - (* Tlong *)
    destruct H1.
    destruct (zle 0 (align ofs0 2)); inv H1.
    eapply Zle_trans. 2: apply H0. simpl typesize; omega. omega. 
    destruct H1; auto.
    destruct (zle 0 (align ofs0 2)); inv H1.
    eapply Zle_trans. 2: apply H0. simpl typesize; omega. omega.
  - (* Tsingle *)
    destruct H1; auto. destruct (zle 0 ofs0); inv H1. apply H0. omega. 
  }
  unfold size_arguments. apply H1. auto.  
Qed.
