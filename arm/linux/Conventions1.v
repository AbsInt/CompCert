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
  R0 :: R1 :: R2 :: R3 :: nil.

Definition float_caller_save_regs :=
  F0 :: F1 :: F2 :: F3 :: F4 :: F5 :: nil.

Definition int_callee_save_regs :=
  R4 :: R5 :: R6 :: R7 :: R8 :: R9 :: R11 :: nil.

Definition float_callee_save_regs :=
  F8 :: F9 :: F10 :: F11 :: F12 :: F13 :: F14 :: F15 :: nil.

Definition destroyed_at_call_regs :=
  int_caller_save_regs ++ float_caller_save_regs.

Definition destroyed_at_call :=
  List.map R destroyed_at_call_regs.

Definition int_temporaries := IT1 :: IT2 :: nil.

Definition float_temporaries := FT1 :: FT2 :: nil.
  
Definition temporary_regs := int_temporaries ++ float_temporaries.

Definition temporaries := List.map R temporary_regs.

Definition destroyed_at_move_regs: list mreg := nil.

Definition destroyed_at_move := List.map R destroyed_at_move_regs.

Definition dummy_int_reg := R0.     (**r Used in [Coloring]. *)
Definition dummy_float_reg := F0.   (**r Used in [Coloring]. *)

(** The [index_int_callee_save] and [index_float_callee_save] associate
  a unique positive integer to callee-save registers.  This integer is
  used in [Stacking] to determine where to save these registers in
  the activation record if they are used by the current function. *)

Definition index_int_callee_save (r: mreg) :=
  match r with
  | R4 => 0  | R5 => 1  | R6 => 2  | R7 => 3
  | R8 => 4  | R9 => 5  | R11 => 6
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
  (In (R r) temporaries \/ In (R r) destroyed_at_call) \/
  (In r int_callee_save_regs \/ In r float_callee_save_regs).
Proof.
  destruct r; 
  try (left; left; simpl; OrEq);
  try (left; right; simpl; OrEq);
  try (right; left; simpl; OrEq);
  try (right; right; simpl; OrEq).
Qed.

Lemma int_callee_save_not_destroyed:
  forall r, 
    In (R r) temporaries \/ In (R r) destroyed_at_call ->
    ~(In r int_callee_save_regs).
Proof.
  intros; red; intros. elim H.
  generalize H0. simpl; ElimOrEq; NotOrEq.
  generalize H0. simpl; ElimOrEq; NotOrEq.
Qed.

Lemma float_callee_save_not_destroyed:
  forall r, 
    In (R r) temporaries \/ In (R r) destroyed_at_call ->
    ~(In r float_callee_save_regs).
Proof.
  intros; red; intros. elim H.
  generalize H0. simpl; ElimOrEq; NotOrEq.
  generalize H0. simpl; ElimOrEq; NotOrEq.
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
  compiler with libraries compiled by another ARM EABI compiler, we
  implement *almost* the standard conventions defined in the ARM EABI application
  binary interface, with two exceptions:
- Double-precision arguments and results are passed in VFP double registers
  instead of pairs of integer registers.
- Single-precision arguments and results are passed as double-precision floats.
*)

(** ** Location of function result *)

(** The result value of a function is passed back to the caller in
  registers [R0] or [F0], depending on the type of the returned value.
  We treat a function without result as a function with one integer result. *)

Definition loc_result (s: signature) : mreg :=
  match s.(sig_res) with
  | None => R0
  | Some Tint => R0
  | Some Tfloat => F0
  end.

(** The result location has the type stated in the signature. *)

Lemma loc_result_type:
  forall sig,
  mreg_type (loc_result sig) =
  match sig.(sig_res) with None => Tint | Some ty => ty end.
Proof.
  intros; unfold loc_result.
  destruct (sig_res sig). 
  destruct t; reflexivity.
  reflexivity.
Qed.

(** The result location is a caller-save register or a temporary *)

Lemma loc_result_caller_save:
  forall (s: signature), 
  In (R (loc_result s)) destroyed_at_call \/ In (R (loc_result s)) temporaries.
Proof.
  intros; unfold loc_result. left;
  destruct (sig_res s). 
  destruct t; simpl; OrEq.
  simpl; OrEq.
Qed.

(** ** Location of function arguments *)

(** We use the following calling conventions, adapted from the ARM EABI:
- The first 4 integer arguments are passed in registers [R0] to [R3].
- The first 2 float arguments are passed in registers [F0] and [F1].
- Each float argument passed in a float register ``consumes'' an aligned pair
  of two integer registers.
- Extra arguments are passed on the stack, in [Outgoing] slots, consecutively
  assigned (1 word for an integer argument, 2 words for a float),
  starting at word offset 0.
*)

Function ireg_param (n: Z) : mreg :=
  if zeq n (-4) then R0
  else if zeq n (-3) then R1
  else if zeq n (-2) then R2
  else if zeq n (-1) then R3
  else R4. (**r should not happen *)

Function freg_param (n: Z) : mreg :=
  if zeq n (-4) then F0
  else if zeq n (-3) then F1
  else if zeq n (-2) then F1
  else F2.  (**r should not happen *)


Fixpoint loc_arguments_rec (tyl: list typ) (ofs: Z) {struct tyl} : list loc :=
  match tyl with
  | nil => nil
  | Tint :: tys =>
      (if zle 0 ofs then S (Outgoing ofs Tint) else R (ireg_param ofs))
      :: loc_arguments_rec tys (ofs + 1)
  | Tfloat :: tys =>
      (if zle (-1) ofs then S (Outgoing (align ofs 2) Tfloat) else R (freg_param ofs))
      :: loc_arguments_rec tys (align ofs 2 + 2)
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
  | Tint :: tys => size_arguments_rec tys (ofs + 1)
  | Tfloat :: tys => size_arguments_rec tys (align ofs 2 + 2)
  end.

Definition size_arguments (s: signature) : Z :=
  Zmax 0 (size_arguments_rec s.(sig_args) (-4)).

(** Argument locations are either non-temporary registers or [Outgoing] 
  stack slots at nonnegative offsets. *)

Definition loc_argument_acceptable (l: loc) : Prop :=
  match l with
  | R r => ~(In l temporaries)
  | S (Outgoing ofs ty) => ofs >= 0
  | _ => False
  end.

Lemma align_monotone:
  forall x1 x2 y, y > 0 -> x1 <= x2 -> align x1 y <= align x2 y.
Proof.
  intros. unfold align. apply Zmult_le_compat_r. apply Z_div_le. 
  omega. omega. omega.
Qed.

Remark loc_arguments_rec_charact:
  forall tyl ofs l,
  In l (loc_arguments_rec tyl ofs) ->
  match l with
  | R r => 
       (exists n, ofs <= n < 0 /\ r = ireg_param n)
    \/ (exists n, ofs <= n < -1 /\ r = freg_param n)
  | S (Outgoing ofs' ty) => ofs' >= 0 /\ ofs' >= ofs
  | S _ => False
  end.
Proof.
  induction tyl; simpl loc_arguments_rec; intros.
  elim H.
  destruct a; elim H; intro.
  subst l. destruct (zle 0 ofs). omega.
  left. exists ofs; split; auto; omega.
  generalize (IHtyl _ _ H0). 
  destruct l. intros [[n A] | [n A]]; [left|right]; exists n; intuition omega.
  destruct s; auto; omega.
  subst l. destruct (zle (-1) ofs).
  split. apply Zle_ge. change 0 with (align (-1) 2). apply align_monotone; omega.
  apply Zle_ge. apply align_le. omega.
  right. exists ofs. intuition.
  assert (ofs <= align ofs 2) by (apply align_le; omega).
  generalize (IHtyl _ _ H0). 
  destruct l. intros [[n A] | [n A]]; [left|right]; exists n; intuition omega.
  destruct s; auto; omega.
Qed.

Lemma loc_notin_in_diff:
  forall l ll,
  Loc.notin l ll <-> (forall l', In l' ll -> Loc.diff l l').
Proof.
  induction ll; simpl; intuition. subst l'. auto. 
Qed.
  
Remark loc_arguments_rec_notin_local:
  forall tyl ofs ofs0 ty0,
  Loc.notin (S (Local ofs0 ty0)) (loc_arguments_rec tyl ofs).
Proof.
  intros. rewrite loc_notin_in_diff. intros. 
  exploit loc_arguments_rec_charact; eauto. 
  destruct l'; intros; simpl; auto. destruct s; auto; contradiction.
Qed.

Lemma loc_arguments_acceptable:
  forall (s: signature) (r: loc),
  In r (loc_arguments s) -> loc_argument_acceptable r.
Proof.
  unfold loc_arguments; intros.
  generalize (loc_arguments_rec_charact _ _ _ H).
  destruct r; simpl.
  intros [[n [A B]] | [n [A B]]]; subst m.
  functional induction (ireg_param n); intuition congruence.
  functional induction (freg_param n); intuition congruence.
  destruct s0; tauto.
Qed.
Hint Resolve loc_arguments_acceptable: locs.

(** Arguments are parwise disjoint (in the sense of [Loc.norepet]). *)

Lemma loc_arguments_norepet:
  forall (s: signature), Loc.norepet (loc_arguments s).
Proof.
  unfold loc_arguments; intros. 
  assert (forall tyl ofs, -4 <= ofs -> Loc.norepet (loc_arguments_rec tyl ofs)).
    induction tyl; simpl; intros.
    constructor.
    destruct a; constructor.
    rewrite loc_notin_in_diff. intros. exploit loc_arguments_rec_charact; eauto. 
    destruct (zle 0 ofs); destruct l'; simpl; auto.
    destruct s0; intuition.
    intros [[n [A B]] | [n [A B]]]; subst m.
    functional induction (ireg_param ofs); functional induction (ireg_param n); congruence || omegaContradiction.
    functional induction (ireg_param ofs); functional induction (freg_param n); congruence || omegaContradiction.
    apply IHtyl. omega.
    rewrite loc_notin_in_diff. intros. exploit loc_arguments_rec_charact; eauto. 
    destruct (zle (-1) ofs); destruct l'; simpl; auto.
    destruct s0; intuition.
    intros [[n [A B]] | [n [A B]]]; subst m.
    functional induction (freg_param ofs); functional induction (ireg_param n); congruence || omegaContradiction.
    functional induction (freg_param ofs); functional induction (freg_param n); try (congruence || omegaContradiction).
    compute in A. intuition.
    compute in A. intuition.
    compute in A. intuition.
    compute in A. intuition.
    compute in A. intuition.
    apply IHtyl. assert (ofs <= align ofs 2) by (apply align_le; omega). omega.
  apply H. omega.
Qed.

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
Qed.

Lemma size_arguments_above:
  forall s, size_arguments s >= 0.
Proof.
  intros; unfold size_arguments. apply Zle_ge. apply Zmax1.
Qed.

Lemma loc_arguments_bounded:
  forall (s: signature) (ofs: Z) (ty: typ),
  In (S (Outgoing ofs ty)) (loc_arguments s) ->
  ofs + typesize ty <= size_arguments s.
Proof.
  intros.
  assert (forall tyl ofs0,
          0 <= ofs0 ->
          ofs0 <= Zmax 0 (size_arguments_rec tyl ofs0)).
    intros. generalize (size_arguments_rec_above tyl ofs0). intros.
    rewrite Zmax_spec. rewrite zlt_false. auto. omega. 
  assert (forall tyl ofs0,
    In (S (Outgoing ofs ty)) (loc_arguments_rec tyl ofs0) ->
    ofs + typesize ty <= Zmax 0 (size_arguments_rec tyl ofs0)).
  induction tyl; simpl; intros.
  elim H1.
  destruct a; elim H1; intros.
  destruct (zle 0 ofs0); inv H2. apply H0. omega. auto.
  destruct (zle (-1) ofs0); inv H2. apply H0. 
  assert (align (-1) 2 <= align ofs0 2). apply align_monotone. omega. auto.
  change (align (-1) 2) with 0 in H2. omega. 
  auto.
 
  unfold size_arguments. apply H1. auto.  
Qed.

(** Temporary registers do not overlap with argument locations. *)

Lemma loc_arguments_not_temporaries:
  forall sig, Loc.disjoint (loc_arguments sig) temporaries.
Proof.
  intros; red; intros x1 x2 A B.
  exploit loc_arguments_acceptable; eauto. unfold loc_argument_acceptable. 
  destruct x1; intros. simpl. destruct x2; auto. intuition congruence.
  destruct s; try contradiction. revert B. simpl. ElimOrEq; auto.
Qed.
Hint Resolve loc_arguments_not_temporaries: locs.

(** Argument registers are caller-save. *)

Lemma arguments_caller_save:
  forall sig r,
  In (R r) (loc_arguments sig) -> In (R r) destroyed_at_call.
Proof.
  unfold loc_arguments; intros.
  destruct (loc_arguments_rec_charact _ _ _ H) as [[n [A B]] | [n [A B]]]; subst r.
  functional induction (ireg_param n); simpl; auto. omegaContradiction.
  functional induction (freg_param n); simpl; auto 10.
Qed.

(** Argument locations agree in number with the function signature. *)

Lemma loc_arguments_length:
  forall sig,
  List.length (loc_arguments sig) = List.length sig.(sig_args).
Proof.
  assert (forall tyl ofs, List.length (loc_arguments_rec tyl ofs) = List.length tyl).
  induction tyl; simpl; intros.
  auto.
  destruct a; simpl; decEq; auto.

  intros. unfold loc_arguments. auto.
Qed.

(** Argument locations agree in types with the function signature. *)

Lemma loc_arguments_type:
  forall sig, List.map Loc.type (loc_arguments sig) = sig.(sig_args).
Proof.
  assert (forall tyl ofs, List.map Loc.type (loc_arguments_rec tyl ofs) = tyl).
  induction tyl; simpl; intros.
  auto.
  destruct a; simpl; decEq; auto.
  destruct (zle 0 ofs). auto. functional induction (ireg_param ofs); auto.
  destruct (zle (-1) ofs). auto. functional induction (freg_param ofs); auto.

  intros. unfold loc_arguments. apply H. 
Qed.
