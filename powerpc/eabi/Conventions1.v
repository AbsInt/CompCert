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
- Callee-save registers, whose value is preserved across a function call.
- Caller-save registers that can be modified during a function call.

  We follow the PowerPC/EABI application binary interface (ABI) in our choice
  of callee- and caller-save registers.
*)

Definition int_caller_save_regs :=
  R3 :: R4 :: R5 :: R6 :: R7 :: R8 :: R9 :: R10 :: R11 :: R12 :: nil.

Definition float_caller_save_regs :=
  F0 :: F1 :: F2 :: F3 :: F4 :: F5 :: F6 :: F7 :: F8 :: F9 :: F10 :: F11 :: F12 :: F13 :: nil.

Definition int_callee_save_regs :=
  R31 :: R30 :: R29 :: R28 :: R27 :: R26 :: R25 :: R24 :: R23 ::
  R22 :: R21 :: R20 :: R19 :: R18 :: R17 :: R16 :: R15 :: R14 :: nil.

Definition float_callee_save_regs :=
  F31 :: F30 :: F29 :: F28 :: F27 :: F26 :: F25 :: F24 :: F23 ::
  F22 :: F21 :: F20 :: F19 :: F18 :: F17 :: F16 :: F15 :: F14 :: nil.

Definition destroyed_at_call :=
  int_caller_save_regs ++ float_caller_save_regs.

Definition dummy_int_reg := R3.     (**r Used in [Coloring]. *)
Definition dummy_float_reg := F0.   (**r Used in [Coloring]. *)

(** The [index_int_callee_save] and [index_float_callee_save] associate
  a unique positive integer to callee-save registers.  This integer is
  used in [Stacking] to determine where to save these registers in
  the activation record if they are used by the current function. *)

Definition index_int_callee_save (r: mreg) :=
  match r with
  | R14 => 17 | R15 => 16 | R16 => 15 | R17 => 14
  | R18 => 13 | R19 => 12 | R20 => 11 | R21 => 10
  | R22 => 9  | R23 => 8  | R24 => 7  | R25 => 6 
  | R26 => 5  | R27 => 4  | R28 => 3  | R29 => 2 
  | R30 => 1  | R31 => 0  | _ => -1
  end.

Definition index_float_callee_save (r: mreg) :=
  match r with
  | F14 => 17 | F15 => 16 | F16 => 15 | F17 => 14
  | F18 => 13 | F19 => 12 | F20 => 11 | F21 => 10
  | F22 => 9  | F23 => 8  | F24 => 7  | F25 => 6 
  | F26 => 5  | F27 => 4  | F28 => 3  | F29 => 2 
  | F30 => 1  | F31 => 0  | _ => -1
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
  locations.  To ensure binary interoperability of code generated by our
  compiler with libraries compiled by another PowerPC compiler, we
  implement the standard conventions defined in the PowerPC/EABI
  application binary interface. *)

(** ** Location of function result *)

(** The result value of a function is passed back to the caller in
  registers [R3] or [F1] or [R3, R4], depending on the type of the returned value.
  We treat a function without result as a function with one integer result. *)

Definition loc_result (s: signature) : list mreg :=
  match s.(sig_res) with
  | None => R3 :: nil
  | Some Tint => R3 :: nil
  | Some (Tfloat | Tsingle) => F1 :: nil
  | Some Tlong => R3 :: R4 :: nil
  end.

(** The result location is a caller-save register *)

Lemma loc_result_caller_save:
  forall (s: signature) (r: mreg), 
  In r (loc_result s) -> In r destroyed_at_call.
Proof.
  intros.
  assert (r = R3 \/ r = R4 \/ r = F1).
    unfold loc_result in H. destruct (sig_res s); [destruct t|idtac]; simpl in H; intuition.
  destruct H0 as [A | [A | A]]; subst r; simpl; OrEq.
Qed.

(** ** Location of function arguments *)

(** The PowerPC EABI states the following convention for passing arguments
  to a function:
- The first 8 integer arguments are passed in registers [R3] to [R10].
- The first 8 float arguments are passed in registers [F1] to [F8].
- The first 4 long integer arguments are passed in register pairs [R3,R4] ... [R9,R10].
- Extra arguments are passed on the stack, in [Outgoing] slots, consecutively
  assigned (1 word for an integer argument, 2 words for a float),
  starting at word offset 0.
- No stack space is reserved for the arguments that are passed in registers.
*)

Definition int_param_regs :=
  R3 :: R4 :: R5 :: R6 :: R7 :: R8 :: R9 :: R10 :: nil.
Definition float_param_regs :=
  F1 :: F2 :: F3 :: F4 :: F5 :: F6 :: F7 :: F8 :: nil.

Fixpoint loc_arguments_rec
    (tyl: list typ) (ir fr ofs: Z) {struct tyl} : list loc :=
  match tyl with
  | nil => nil
  | Tint :: tys =>
      match list_nth_z int_param_regs ir with
      | None =>
          S Outgoing ofs Tint :: loc_arguments_rec tys ir fr (ofs + 1)
      | Some ireg =>
          R ireg :: loc_arguments_rec tys (ir + 1) fr ofs
      end
  | (Tfloat | Tsingle) :: tys =>
      match list_nth_z float_param_regs fr with
      | None =>
          let ofs := align ofs 2 in
          S Outgoing ofs Tfloat :: loc_arguments_rec tys ir fr (ofs + 2)
      | Some freg =>
          R freg :: loc_arguments_rec tys ir (fr + 1) ofs
      end
  | Tlong :: tys =>
      let ir := align ir 2 in
      match list_nth_z int_param_regs ir, list_nth_z int_param_regs (ir + 1) with
      | Some r1, Some r2 =>
          R r1 :: R r2 :: loc_arguments_rec tys (ir + 2) fr ofs
      | _, _ =>
          let ofs := align ofs 2 in
          S Outgoing ofs Tint :: S Outgoing (ofs + 1) Tint :: loc_arguments_rec tys ir fr (ofs + 2)
      end
  end.

(** [loc_arguments s] returns the list of locations where to store arguments
  when calling a function with signature [s].  *)

Definition loc_arguments (s: signature) : list loc :=
  loc_arguments_rec s.(sig_args) 0 0 0.

(** [size_arguments s] returns the number of [Outgoing] slots used
  to call a function with signature [s]. *)

Fixpoint size_arguments_rec (tyl: list typ) (ir fr ofs: Z) {struct tyl} : Z :=
  match tyl with
  | nil => ofs
  | Tint :: tys =>
      match list_nth_z int_param_regs ir with
      | None => size_arguments_rec tys ir fr (ofs + 1)
      | Some ireg => size_arguments_rec tys (ir + 1) fr ofs
      end
  | (Tfloat | Tsingle) :: tys =>
      match list_nth_z float_param_regs fr with
      | None => size_arguments_rec tys ir fr (align ofs 2 + 2)
      | Some freg => size_arguments_rec tys ir (fr + 1) ofs
      end
  | Tlong :: tys =>
      let ir := align ir 2 in
      match list_nth_z int_param_regs ir, list_nth_z int_param_regs (ir + 1) with
      | Some r1, Some r2 => size_arguments_rec tys (ir + 2) fr ofs
      | _, _ => size_arguments_rec tys ir fr (align ofs 2 + 2)
      end
  end.

Definition size_arguments (s: signature) : Z :=
  size_arguments_rec s.(sig_args) 0 0 0.

(** A tail-call is possible for a signature if the corresponding
    arguments are all passed in registers. *)

Definition tailcall_possible (s: signature) : Prop :=
  forall l, In l (loc_arguments s) ->
  match l with R _ => True | S _ _ _ => False end.

(** Argument locations are either caller-save registers or [Outgoing] 
  stack slots at nonnegative offsets. *)

Definition loc_argument_acceptable (l: loc) : Prop :=
  match l with
  | R r => In r destroyed_at_call
  | S Outgoing ofs ty => ofs >= 0 /\ ty <> Tlong
  | _ => False
  end.

Remark loc_arguments_rec_charact:
  forall tyl ir fr ofs l,
  In l (loc_arguments_rec tyl ir fr ofs) ->
  match l with
  | R r => In r int_param_regs \/ In r float_param_regs
  | S Outgoing ofs' ty => ofs' >= ofs /\ ty <> Tlong
  | S _ _ _ => False
  end.
Proof.
Opaque list_nth_z.
  induction tyl; simpl loc_arguments_rec; intros.
  elim H.
  destruct a.
- (* int *)
  destruct (list_nth_z int_param_regs ir) as [r|] eqn:E; destruct H.
  subst. left. eapply list_nth_z_in; eauto.
  eapply IHtyl; eauto.
  subst. split. omega. congruence.
  exploit IHtyl; eauto. destruct l; auto. destruct sl; auto. intuition omega.
- (* float *)
  destruct (list_nth_z float_param_regs fr) as [r|] eqn:E; destruct H. 
  subst. right. eapply list_nth_z_in; eauto.
  eapply IHtyl; eauto.
  subst. split. apply Zle_ge. apply align_le. omega. congruence.
  exploit IHtyl; eauto. destruct l; auto. destruct sl; auto.
  assert (ofs <= align ofs 2) by (apply align_le; omega). 
  intuition omega.
- (* long *)
  set (ir' := align ir 2) in *.
  destruct (list_nth_z int_param_regs ir') as [r1|] eqn:E1.
  destruct (list_nth_z int_param_regs (ir' + 1)) as [r2|] eqn:E2.
  destruct H. subst; left; eapply list_nth_z_in; eauto.
  destruct H. subst; left; eapply list_nth_z_in; eauto.
  eapply IHtyl; eauto.
  assert (ofs <= align ofs 2) by (apply align_le; omega). 
  destruct H. subst. split. omega. congruence.
  destruct H. subst. split. omega. congruence.
  exploit IHtyl; eauto. destruct l; auto. destruct sl; auto. intuition omega.
  assert (ofs <= align ofs 2) by (apply align_le; omega). 
  destruct H. subst. split. omega. congruence. 
  destruct H. subst. split. omega. congruence.
  exploit IHtyl; eauto. destruct l; auto. destruct sl; auto. intuition omega. 
- (* single *)
  destruct (list_nth_z float_param_regs fr) as [r|] eqn:E; destruct H. 
  subst. right. eapply list_nth_z_in; eauto.
  eapply IHtyl; eauto.
  subst. split. apply Zle_ge. apply align_le. omega. congruence.
  exploit IHtyl; eauto. destruct l; auto. destruct sl; auto.
  assert (ofs <= align ofs 2) by (apply align_le; omega). 
  intuition omega.
Qed.

Lemma loc_arguments_acceptable:
  forall (s: signature) (l: loc),
  In l (loc_arguments s) -> loc_argument_acceptable l.
Proof.
  unfold loc_arguments; intros.
  generalize (loc_arguments_rec_charact _ _ _ _ _ H).
  destruct l.
  intro H0; elim H0; simpl; ElimOrEq; OrEq.
  destruct sl; try contradiction. simpl. intuition omega.
Qed. 
Hint Resolve loc_arguments_acceptable: locs.

(** The offsets of [Outgoing] arguments are below [size_arguments s]. *)

Remark size_arguments_rec_above:
  forall tyl ir fr ofs0,
  ofs0 <= size_arguments_rec tyl ir fr ofs0.
Proof.
  induction tyl; simpl; intros.
  omega.
  destruct a.
  destruct (list_nth_z int_param_regs ir); eauto. apply Zle_trans with (ofs0 + 1); auto; omega.
  destruct (list_nth_z float_param_regs fr); eauto.
  apply Zle_trans with (align ofs0 2). apply align_le; omega.
  apply Zle_trans with (align ofs0 2 + 2); auto; omega.
  set (ir' := align ir 2).
  destruct (list_nth_z int_param_regs ir'); eauto.
  destruct (list_nth_z int_param_regs (ir' + 1)); eauto.
  apply Zle_trans with (align ofs0 2). apply align_le; omega.
  apply Zle_trans with (align ofs0 2 + 2); auto; omega.
  apply Zle_trans with (align ofs0 2). apply align_le; omega.
  apply Zle_trans with (align ofs0 2 + 2); auto; omega.
  destruct (list_nth_z float_param_regs fr); eauto.
  apply Zle_trans with (align ofs0 2). apply align_le; omega.
  apply Zle_trans with (align ofs0 2 + 2); auto; omega.
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
  intros.
  assert (forall tyl ir fr ofs0,
    In (S Outgoing ofs ty) (loc_arguments_rec tyl ir fr ofs0) ->
    ofs + typesize ty <= size_arguments_rec tyl ir fr ofs0).
{
  induction tyl; simpl; intros.
  elim H0.
  destruct a.
- (* int *)
  destruct (list_nth_z int_param_regs ir); destruct H0. 
  congruence.
  eauto.
  inv H0. apply size_arguments_rec_above.
  eauto.
- (* float *)
  destruct (list_nth_z float_param_regs fr); destruct H0. 
  congruence.
  eauto.
  inv H0. apply size_arguments_rec_above. eauto. 
- (* long *)
  set (ir' := align ir 2) in *.
  destruct (list_nth_z int_param_regs ir').
  destruct (list_nth_z int_param_regs (ir' + 1)).
  destruct H0. congruence. destruct H0. congruence. eauto.
  destruct H0. inv H0. 
  transitivity (align ofs0 2 + 2). simpl; omega. eauto.  apply size_arguments_rec_above.
  destruct H0. inv H0.
  transitivity (align ofs0 2 + 2). simpl; omega. eauto.  apply size_arguments_rec_above.
  eauto. 
  destruct H0. inv H0. 
  transitivity (align ofs0 2 + 2). simpl; omega. eauto.  apply size_arguments_rec_above.
  destruct H0. inv H0.
  transitivity (align ofs0 2 + 2). simpl; omega. eauto.  apply size_arguments_rec_above.
  eauto.
- (* single *)
  destruct (list_nth_z float_param_regs fr); destruct H0. 
  congruence.
  eauto.
  inv H0. apply size_arguments_rec_above. eauto. 
  }
  eauto.
Qed.
