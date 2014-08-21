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
Require Archi.

(** * Classification of machine registers *)

(** Machine registers (type [mreg] in module [Locations]) are divided in
  the following groups:
- Temporaries used for spilling, reloading, and parallel move operations.
- Allocatable registers, that can be assigned to RTL pseudo-registers.
  These are further divided into:
-- Callee-save registers, whose value is preserved across a function call.
-- Caller-save registers that can be modified during a function call.

  We follow the ARM application binary interface (EABI) in our choice
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
  locations.  *)

(** ** Location of function result *)

(** The result value of a function is passed back to the caller in
  registers [R0] or [F0] or [R0,R1], depending on the type of the
  returned value.  We treat a function without result as a function
  with one integer result.

  For the "softfloat" convention, results of FP types should be passed
  in [R0] or [R0,R1].  This doesn't fit the CompCert register model,
  so we have code in [arm/PrintAsm.ml] that inserts additional moves
  to/from [F0]. *)

Definition loc_result (s: signature) : list mreg :=
  match s.(sig_res) with
  | None => R0 :: nil
  | Some (Tint | Tany32) => R0 :: nil
  | Some (Tfloat | Tsingle | Tany64) => F0 :: nil
  | Some Tlong => R1 :: R0 :: nil
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
  assert (r = R0 \/ r = R1 \/ r = F0).
    unfold loc_result in H. destruct (sig_res s); [destruct t|idtac]; simpl in H; intuition.
  destruct H0 as [A | [A | A]]; subst r; simpl; OrEq.
Qed.

(** ** Location of function arguments *)

(** For the "hardfloat" configuration, we use the following calling conventions,
    adapted from the ARM EABI-HF:
- The first 4 integer arguments are passed in registers [R0] to [R3].
- The first 2 long integer arguments are passed in an aligned pair of
  two integer registers.
- The first 8 single- and double-precision float arguments are passed
  in registers [F0...F7]
- Extra arguments are passed on the stack, in [Outgoing] slots, consecutively
  assigned (1 word for an integer or single argument, 2 words for a float
  or a long), starting at word offset 0.

This convention is not quite that of the ARM EABI-HF, whereas single float
arguments are passed in 32-bit float registers.  Unfortunately,
this does not fit the data model of CompCert.  In [PrintAsm.ml]
we insert additional code around function calls that moves
data appropriately. *)

Definition int_param_regs :=
  R0 :: R1 :: R2 :: R3 :: nil.

Definition float_param_regs :=
  F0 :: F1 :: F2 :: F3 :: F4 :: F5 :: F6 :: F7 :: nil.

Definition ireg_param (n: Z) : mreg :=
  match list_nth_z int_param_regs n with Some r => r | None => R0 end.

Definition freg_param (n: Z) : mreg :=
  match list_nth_z float_param_regs n with Some r => r | None => F0 end.

Fixpoint loc_arguments_hf
     (tyl: list typ) (ir fr ofs: Z) {struct tyl} : list loc :=
  match tyl with
  | nil => nil
  | (Tint | Tany32) as ty :: tys =>
      if zlt ir 4
      then R (ireg_param ir) :: loc_arguments_hf tys (ir + 1) fr ofs
      else S Outgoing ofs ty :: loc_arguments_hf tys ir fr (ofs + 1)
  | (Tfloat | Tany64) as ty :: tys =>
      if zlt fr 8
      then R (freg_param fr) :: loc_arguments_hf tys ir (fr + 1) ofs
      else let ofs := align ofs 2 in
           S Outgoing ofs ty :: loc_arguments_hf tys ir fr (ofs + 2)
  | Tsingle :: tys =>
      if zlt fr 8
      then R (freg_param fr) :: loc_arguments_hf tys ir (fr + 1) ofs
      else S Outgoing ofs Tsingle :: loc_arguments_hf tys ir fr (ofs + 1)
  | Tlong :: tys =>
      let ir := align ir 2 in
      if zlt ir 4
      then R (ireg_param (ir + 1)) :: R (ireg_param ir) :: loc_arguments_hf tys (ir + 2) fr ofs
      else let ofs := align ofs 2 in
          S Outgoing (ofs + 1) Tint :: S Outgoing ofs Tint :: loc_arguments_hf tys ir fr (ofs + 2)
  end.

(** For the "softfloat" configuration, as well as for variable-argument functions
  in the "hardfloat" configuration, we use the default ARM EABI (not HF)
  calling conventions:
- The first 4 integer arguments are passed in registers [R0] to [R3].
- The first 2 long integer arguments are passed in an aligned pair of
  two integer registers.
- The first 2 double-precision float arguments are passed in [F0] or [F2]
- The first 4 single-precision float arguments are passed in [F0...F3]
- Integer arguments and float arguments are kept in sync so that
  they can all be mapped back to [R0...R3] in [PrintAsm.ml].
- Extra arguments are passed on the stack, in [Outgoing] slots, consecutively
  assigned (1 word for an integer or single argument, 2 words for a float
  or a long), starting at word offset 0.

This convention is not quite that of the ARM EABI, whereas every float
argument are passed in one or two integer registers.  Unfortunately,
this does not fit the data model of CompCert.  In [PrintAsm.ml]
we insert additional code around function calls and returns that moves
data appropriately. *)

Fixpoint loc_arguments_sf
     (tyl: list typ) (ofs: Z) {struct tyl} : list loc :=
  match tyl with
  | nil => nil
  | (Tint|Tany32) as ty :: tys =>
      (if zlt ofs 0 then R (ireg_param (ofs + 4)) else S Outgoing ofs ty)
      :: loc_arguments_sf tys (ofs + 1)
  | (Tfloat|Tany64) as ty :: tys =>
      let ofs := align ofs 2 in
      (if zlt ofs 0 then R (freg_param (ofs + 4)) else S Outgoing ofs ty)
      :: loc_arguments_sf tys (ofs + 2)
  | Tsingle :: tys =>
      (if zlt ofs 0 then R (freg_param (ofs + 4)) else S Outgoing ofs Tsingle)
      :: loc_arguments_sf tys (ofs + 1)
  | Tlong :: tys =>
      let ofs := align ofs 2 in
      (if zlt ofs 0 then R (ireg_param (ofs+1+4)) else S Outgoing (ofs+1) Tint)
      :: (if zlt ofs 0 then R (ireg_param (ofs+4)) else S Outgoing ofs Tint)
      :: loc_arguments_sf tys (ofs + 2)
  end.

(** [loc_arguments s] returns the list of locations where to store arguments
  when calling a function with signature [s].  *)

Definition loc_arguments (s: signature) : list loc :=
  match Archi.abi with
  | Archi.Softfloat =>
      loc_arguments_sf s.(sig_args) (-4)
  | Archi.Hardfloat =>
      if s.(sig_cc).(cc_vararg)
      then loc_arguments_sf s.(sig_args) (-4)
      else loc_arguments_hf s.(sig_args) 0 0 0
  end.

(** [size_arguments s] returns the number of [Outgoing] slots used
  to call a function with signature [s]. *)

Fixpoint size_arguments_hf (tyl: list typ) (ir fr ofs: Z) {struct tyl} : Z :=
  match tyl with
  | nil => ofs
  | (Tint|Tany32) :: tys =>
      if zlt ir 4
      then size_arguments_hf tys (ir + 1) fr ofs
      else size_arguments_hf tys ir fr (ofs + 1)
  | (Tfloat|Tany64) :: tys =>
      if zlt fr 8
      then size_arguments_hf tys ir (fr + 1) ofs
      else size_arguments_hf tys ir fr (align ofs 2 + 2)
  | Tsingle :: tys =>
      if zlt fr 8
      then size_arguments_hf tys ir (fr + 1) ofs
      else size_arguments_hf tys ir fr (ofs + 1)
  | Tlong :: tys =>
      let ir := align ir 2 in
      if zlt ir 4
      then size_arguments_hf tys (ir + 2) fr ofs
      else size_arguments_hf tys ir fr (align ofs 2 + 2)
  end.

Fixpoint size_arguments_sf (tyl: list typ) (ofs: Z) {struct tyl} : Z :=
  match tyl with
  | nil => Zmax 0 ofs
  | (Tint | Tsingle | Tany32) :: tys => size_arguments_sf tys (ofs + 1)
  | (Tfloat | Tlong | Tany64) :: tys => size_arguments_sf tys (align ofs 2 + 2)
  end.

Definition size_arguments (s: signature) : Z :=
  match Archi.abi with
  | Archi.Softfloat =>
      size_arguments_sf s.(sig_args) (-4)
  | Archi.Hardfloat =>
      if s.(sig_cc).(cc_vararg)
      then size_arguments_sf s.(sig_args) (-4)
      else size_arguments_hf s.(sig_args) 0 0 0
  end.

(** Argument locations are either non-temporary registers or [Outgoing] 
  stack slots at nonnegative offsets. *)

Definition loc_argument_acceptable (l: loc) : Prop :=
  match l with
  | R r => In r destroyed_at_call
  | S Outgoing ofs ty => ofs >= 0 /\ ty <> Tlong
  | _ => False
  end.

Remark ireg_param_in_params: forall n, In (ireg_param n) int_param_regs.
Proof.
  unfold ireg_param; intros. 
  destruct (list_nth_z int_param_regs n) as [r|] eqn:NTH.
  eapply list_nth_z_in; eauto. 
  simpl; auto.
Qed.

Remark freg_param_in_params: forall n, In (freg_param n) float_param_regs.
Proof.
  unfold freg_param; intros. 
  destruct (list_nth_z float_param_regs n) as [r|] eqn:NTH.
  eapply list_nth_z_in; eauto. 
  simpl; auto.
Qed.

Remark loc_arguments_hf_charact:
  forall tyl ir fr ofs l,
  In l (loc_arguments_hf tyl ir fr ofs) ->
  match l with
  | R r => In r int_param_regs \/ In r float_param_regs
  | S Outgoing ofs' ty => ofs' >= ofs /\ ty <> Tlong
  | S _ _ _ => False
  end.
Proof.
  assert (INCR: forall l ofs1 ofs2,
            match l with
            | R r => In r int_param_regs \/ In r float_param_regs
            | S Outgoing ofs' ty => ofs' >= ofs2 /\ ty <> Tlong
            | S _ _ _ => False
            end ->
            ofs1 <= ofs2 ->
            match l with
            | R r => In r int_param_regs \/ In r float_param_regs
            | S Outgoing ofs' ty => ofs' >= ofs1 /\ ty <> Tlong
            | S _ _ _ => False
            end).
  {
    intros. destruct l; auto. destruct sl; auto. intuition omega.
  }
  induction tyl; simpl loc_arguments_hf; intros.
  elim H.
  destruct a.
- (* int *)
  destruct (zlt ir 4); destruct H.
  subst. left; apply ireg_param_in_params.
  eapply IHtyl; eauto.
  subst. split; [omega | congruence].
  eapply INCR. eapply IHtyl; eauto. omega.
- (* float *)
  destruct (zlt fr 8); destruct H.
  subst. right; apply freg_param_in_params.
  eapply IHtyl; eauto.
  subst. split. apply Zle_ge. apply align_le. omega. congruence.
  eapply INCR. eapply IHtyl; eauto.
  apply Zle_trans with (align ofs 2). apply align_le; omega. omega.
- (* long *)
  set (ir' := align ir 2) in *.
  assert (ofs <= align ofs 2) by (apply align_le; omega). 
  destruct (zlt ir' 4).
  destruct H. subst l; left; apply ireg_param_in_params.
  destruct H. subst l; left; apply ireg_param_in_params.
  eapply IHtyl; eauto.
  destruct H. subst l; split; [ omega | congruence ].
  destruct H. subst l; split; [ omega | congruence ].
  eapply INCR. eapply IHtyl; eauto. omega.
- (* single *)
  destruct (zlt fr 8); destruct H.
  subst. right; apply freg_param_in_params.
  eapply IHtyl; eauto.
  subst. split; [omega | congruence].
  eapply INCR. eapply IHtyl; eauto. omega.
- (* any32 *)
  destruct (zlt ir 4); destruct H.
  subst. left; apply ireg_param_in_params.
  eapply IHtyl; eauto.
  subst. split; [omega | congruence].
  eapply INCR. eapply IHtyl; eauto. omega.
- (* any64 *)
  destruct (zlt fr 8); destruct H.
  subst. right; apply freg_param_in_params.
  eapply IHtyl; eauto.
  subst. split. apply Zle_ge. apply align_le. omega. congruence.
  eapply INCR. eapply IHtyl; eauto.
  apply Zle_trans with (align ofs 2). apply align_le; omega. omega.
Qed.

Remark loc_arguments_sf_charact:
  forall tyl ofs l,
  In l (loc_arguments_sf tyl ofs) ->
  match l with
  | R r => In r int_param_regs \/ In r float_param_regs
  | S Outgoing ofs' ty => ofs' >= Zmax 0 ofs /\ ty <> Tlong
  | S _ _ _ => False
  end.
Proof.
  assert (INCR: forall l ofs1 ofs2,
            match l with
            | R r => In r int_param_regs \/ In r float_param_regs
            | S Outgoing ofs' ty => ofs' >= Zmax 0 ofs2 /\ ty <> Tlong
            | S _ _ _ => False
            end ->
            ofs1 <= ofs2 ->
            match l with
            | R r => In r int_param_regs \/ In r float_param_regs
            | S Outgoing ofs' ty => ofs' >= Zmax 0 ofs1 /\ ty <> Tlong
            | S _ _ _ => False
            end).
  {
    intros. destruct l; auto. destruct sl; auto. intuition xomega.
  }
  induction tyl; simpl loc_arguments_sf; intros.
  elim H.
  destruct a.
- (* int *)
  destruct H. 
  destruct (zlt ofs 0); subst l. 
  left; apply ireg_param_in_params.
  split. xomega. congruence.
  eapply INCR. eapply IHtyl; eauto. omega.
- (* float *)
  set (ofs' := align ofs 2) in *.
  assert (ofs <= ofs') by (apply align_le; omega).
  destruct H.
  destruct (zlt ofs' 0); subst l.
  right; apply freg_param_in_params.
  split. xomega. congruence.
  eapply INCR. eapply IHtyl; eauto. omega.
- (* long *)
  set (ofs' := align ofs 2) in *.
  assert (ofs <= ofs') by (apply align_le; omega).
  destruct H.
  destruct (zlt ofs' 0); subst l.
  left; apply ireg_param_in_params.
  split. xomega. congruence.
  destruct H.
  destruct (zlt ofs' 0); subst l.
  left; apply ireg_param_in_params.
  split. xomega. congruence.
  eapply INCR. eapply IHtyl; eauto. omega.
- (* single *)
  destruct H. 
  destruct (zlt ofs 0); subst l. 
  right; apply freg_param_in_params.
  split. xomega. congruence.
  eapply INCR. eapply IHtyl; eauto. omega.
- (* any32 *)
  destruct H. 
  destruct (zlt ofs 0); subst l. 
  left; apply ireg_param_in_params.
  split. xomega. congruence.
  eapply INCR. eapply IHtyl; eauto. omega.
- (* any64 *)
  set (ofs' := align ofs 2) in *.
  assert (ofs <= ofs') by (apply align_le; omega).
  destruct H.
  destruct (zlt ofs' 0); subst l.
  right; apply freg_param_in_params.
  split. xomega. congruence.
  eapply INCR. eapply IHtyl; eauto. omega.
Qed.

Lemma loc_arguments_acceptable:
  forall (s: signature) (l: loc),
  In l (loc_arguments s) -> loc_argument_acceptable l.
Proof.
  unfold loc_arguments; intros.
  assert (forall r, In r int_param_regs \/ In r float_param_regs -> In r destroyed_at_call).
  {
    intros. elim H0; simpl; ElimOrEq; OrEq.
  }
  assert (In l (loc_arguments_sf (sig_args s) (-4)) -> loc_argument_acceptable l).
  { intros. red. exploit loc_arguments_sf_charact; eauto. destruct l; auto. }
  assert (In l (loc_arguments_hf (sig_args s) 0 0 0) -> loc_argument_acceptable l).
  { intros. red. exploit loc_arguments_hf_charact; eauto. destruct l; auto. }
  destruct Archi.abi; [ | destruct (cc_vararg (sig_cc s)) ]; auto.
Qed.

Hint Resolve loc_arguments_acceptable: locs.

(** The offsets of [Outgoing] arguments are below [size_arguments s]. *)

Remark size_arguments_hf_above:
  forall tyl ir fr ofs0,
  ofs0 <= size_arguments_hf tyl ir fr ofs0.
Proof.
  induction tyl; simpl; intros.
  omega.
  destruct a.
  destruct (zlt ir 4); eauto. apply Zle_trans with (ofs0 + 1); auto; omega.
  destruct (zlt fr 8); eauto.
  apply Zle_trans with (align ofs0 2). apply align_le; omega.
  apply Zle_trans with (align ofs0 2 + 2); auto; omega.
  set (ir' := align ir 2).
  destruct (zlt ir' 4); eauto. 
  apply Zle_trans with (align ofs0 2). apply align_le; omega.
  apply Zle_trans with (align ofs0 2 + 2); auto; omega.
  destruct (zlt fr 8); eauto.
  apply Zle_trans with (ofs0 + 1); eauto. omega.
  destruct (zlt ir 4); eauto. apply Zle_trans with (ofs0 + 1); auto; omega.
  destruct (zlt fr 8); eauto.
  apply Zle_trans with (align ofs0 2). apply align_le; omega.
  apply Zle_trans with (align ofs0 2 + 2); auto; omega.
Qed.

Remark size_arguments_sf_above:
  forall tyl ofs0,
  Zmax 0 ofs0 <= size_arguments_sf tyl ofs0.
Proof.
  induction tyl; simpl; intros.
  omega.
  destruct a; (eapply Zle_trans; [idtac|eauto]). 
  xomega.
  assert (ofs0 <= align ofs0 2) by (apply align_le; omega). xomega.
  assert (ofs0 <= align ofs0 2) by (apply align_le; omega). xomega.
  xomega.
  xomega.
  assert (ofs0 <= align ofs0 2) by (apply align_le; omega). xomega.
Qed.

Lemma size_arguments_above:
  forall s, size_arguments s >= 0.
Proof.
  intros; unfold size_arguments. apply Zle_ge.
  assert (0 <= size_arguments_sf (sig_args s) (-4)).
  { change 0 with (Zmax 0 (-4)). apply size_arguments_sf_above. }
  assert (0 <= size_arguments_hf (sig_args s) 0 0 0).
  { apply size_arguments_hf_above. }
  destruct Archi.abi; [ | destruct (cc_vararg (sig_cc s)) ]; auto.
Qed.

Lemma loc_arguments_hf_bounded:
  forall ofs ty tyl ir fr ofs0,
  In (S Outgoing ofs ty) (loc_arguments_hf tyl ir fr ofs0) ->
  ofs + typesize ty <= size_arguments_hf tyl ir fr ofs0.
Proof.
  induction tyl; simpl; intros.
  elim H.
  destruct a.
- (* int *)
  destruct (zlt ir 4); destruct H.
  discriminate.
  eauto.
  inv H. apply size_arguments_hf_above. 
  eauto.
- (* float *)
  destruct (zlt fr 8); destruct H.
  discriminate.
  eauto. 
  inv H. apply size_arguments_hf_above. 
  eauto.
- (* long *)
  destruct (zlt (align ir 2) 4).
  destruct H. discriminate. destruct H. discriminate. eauto. 
  destruct H. inv H.
  rewrite <- Zplus_assoc. simpl. apply size_arguments_hf_above.
  destruct H. inv H.
  eapply Zle_trans. 2: apply size_arguments_hf_above. simpl; omega.
  eauto.
- (* float *)
  destruct (zlt fr 8); destruct H.
  discriminate.
  eauto.
  inv H. apply size_arguments_hf_above.
  eauto.
- (* any32 *)
  destruct (zlt ir 4); destruct H.
  discriminate.
  eauto.
  inv H. apply size_arguments_hf_above. 
  eauto.
- (* any64 *)
  destruct (zlt fr 8); destruct H.
  discriminate.
  eauto. 
  inv H. apply size_arguments_hf_above. 
  eauto.
Qed.

Lemma loc_arguments_sf_bounded:
  forall ofs ty tyl ofs0,
  In (S Outgoing ofs ty) (loc_arguments_sf tyl ofs0) ->
  Zmax 0 (ofs + typesize ty) <= size_arguments_sf tyl ofs0.
Proof.
  induction tyl; simpl; intros.
  elim H.
  destruct a.
- (* int *)
  destruct H. 
  destruct (zlt ofs0 0); inv H. apply size_arguments_sf_above. 
  eauto.
- (* float *)
  destruct H.
  destruct (zlt (align ofs0 2) 0); inv H. apply size_arguments_sf_above.
  eauto.
- (* long *)
  destruct H. 
  destruct (zlt (align ofs0 2) 0); inv H.
  rewrite <- Zplus_assoc. simpl. apply size_arguments_sf_above.
  destruct H. 
  destruct (zlt (align ofs0 2) 0); inv H.
  eapply Zle_trans. 2: apply size_arguments_sf_above. simpl; xomega.
  eauto.
- (* float *)
  destruct H. 
  destruct (zlt ofs0 0); inv H. apply size_arguments_sf_above. 
  eauto.
- (* any32 *)
  destruct H. 
  destruct (zlt ofs0 0); inv H. apply size_arguments_sf_above. 
  eauto.
- (* any64 *)
  destruct H.
  destruct (zlt (align ofs0 2) 0); inv H. apply size_arguments_sf_above.
  eauto.
Qed.

Lemma loc_arguments_bounded:
  forall (s: signature) (ofs: Z) (ty: typ),
  In (S Outgoing ofs ty) (loc_arguments s) ->
  ofs + typesize ty <= size_arguments s.
Proof.
  unfold loc_arguments, size_arguments; intros.
  assert (In (S Outgoing ofs ty) (loc_arguments_sf (sig_args s) (-4)) ->
          ofs + typesize ty <= size_arguments_sf (sig_args s) (-4)).
  { intros. eapply Zle_trans. 2: eapply loc_arguments_sf_bounded; eauto. xomega. }
  assert (In (S Outgoing ofs ty) (loc_arguments_hf (sig_args s) 0 0 0) ->
          ofs + typesize ty <= size_arguments_hf (sig_args s) 0 0 0).
  { intros. eapply loc_arguments_hf_bounded; eauto. }
  destruct Archi.abi; [ | destruct (cc_vararg (sig_cc s)) ]; eauto.
Qed.

Lemma loc_arguments_main:
  loc_arguments signature_main = nil.
Proof.
  unfold loc_arguments. 
  destruct Archi.abi; reflexivity.
Qed.
