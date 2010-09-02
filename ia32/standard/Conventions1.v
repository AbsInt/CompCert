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

  We follow the x86-32 application binary interface (ABI) in our choice
  of callee- and caller-save registers.
*)

Definition int_caller_save_regs := AX :: nil.

Definition float_caller_save_regs := X0 :: X1 :: X2 :: X3 :: X4 :: X5 :: nil.

Definition int_callee_save_regs := BX :: SI :: DI :: BP :: nil.

Definition float_callee_save_regs : list mreg := nil.

Definition destroyed_at_call_regs :=
  int_caller_save_regs ++ float_caller_save_regs.

Definition destroyed_at_call :=
  List.map R destroyed_at_call_regs.

Definition int_temporaries := IT1 :: IT2 :: nil.

Definition float_temporaries := FT1 :: FT2 :: FP0 :: nil.
  
Definition temporaries := 
  R IT1 :: R IT2 :: R FT1 :: R FT2 :: R FP0 :: nil.

Definition dummy_int_reg := AX.     (**r Used in [Coloring]. *)
Definition dummy_float_reg := X0.   (**r Used in [Coloring]. *)

(** The [index_int_callee_save] and [index_float_callee_save] associate
  a unique positive integer to callee-save registers.  This integer is
  used in [Stacking] to determine where to save these registers in
  the activation record if they are used by the current function. *)

Definition index_int_callee_save (r: mreg) :=
  match r with
  | BX => 1 | SI => 2 | DI => 3 | BP => 4 | _ => -1
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
  compiler with libraries compiled by another compiler, we
  implement the standard x86 conventions. *)

(** ** Location of function result *)

(** The result value of a function is passed back to the caller in
  registers [AX] or [FP0], depending on the type of the returned value.
  We treat a function without result as a function with one integer result. *)

Definition loc_result (s: signature) : mreg :=
  match s.(sig_res) with
  | None => AX
  | Some Tint => AX
  | Some Tfloat => FP0
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
  intros; unfold loc_result.
  destruct (sig_res s).
  destruct t. left; simpl; OrEq. right; simpl; OrEq.
  left; simpl; OrEq.
Qed.

(** ** Location of function arguments *)

(** All arguments are passed on stack. (Snif.) *)

Fixpoint loc_arguments_rec
    (tyl: list typ) (ofs: Z) {struct tyl} : list loc :=
  match tyl with
  | nil => nil
  | Tint :: tys => S (Outgoing ofs Tint) :: loc_arguments_rec tys (ofs + 1)
  | Tfloat :: tys => S (Outgoing ofs Tfloat) :: loc_arguments_rec tys (ofs + 2)
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
  | Tint :: tys => size_arguments_rec tys (ofs + 1)
  | Tfloat :: tys => size_arguments_rec tys (ofs + 2)
  end.

Definition size_arguments (s: signature) : Z :=
  size_arguments_rec s.(sig_args) 0.

(** A tail-call is possible for a signature if the corresponding
    arguments are all passed in registers. *)

Definition tailcall_possible (s: signature) : Prop :=
  forall l, In l (loc_arguments s) ->
  match l with R _ => True | S _ => False end.

(** Argument locations are either non-temporary registers or [Outgoing] 
  stack slots at nonnegative offsets. *)

Definition loc_argument_acceptable (l: loc) : Prop :=
  match l with
  | R r => ~(In l temporaries)
  | S (Outgoing ofs ty) => ofs >= 0
  | _ => False
  end.

Remark loc_arguments_rec_charact:
  forall tyl ofs l,
  In l (loc_arguments_rec tyl ofs) ->
  match l with
  | S (Outgoing ofs' ty) => ofs' >= ofs
  | _ => False
  end.
Proof.
  induction tyl; simpl loc_arguments_rec; intros.
  elim H.
  destruct a; simpl in H; destruct H.
  subst l. omega.
  generalize (IHtyl _ _ H). destruct l; auto. destruct s; auto. omega. 
  subst l. omega.
  generalize (IHtyl _ _ H). destruct l; auto. destruct s; auto. omega. 
Qed.

Lemma loc_arguments_acceptable:
  forall (s: signature) (r: loc),
  In r (loc_arguments s) -> loc_argument_acceptable r.
Proof.
  unfold loc_arguments; intros.
  generalize (loc_arguments_rec_charact  _ _ _ H).
  destruct r; tauto.
Qed.
Hint Resolve loc_arguments_acceptable: locs.

(** Arguments are parwise disjoint (in the sense of [Loc.norepet]). *)

Remark loc_arguments_rec_notin_local:
  forall tyl ofs ofs0 ty0,
  Loc.notin (S (Local ofs0 ty0)) (loc_arguments_rec tyl ofs).
Proof.
  induction tyl; simpl; intros.
  auto.
  destruct a; simpl; auto.
Qed.

Remark loc_arguments_rec_notin_outgoing:
  forall tyl ofs ofs0 ty0,
  ofs0 + typesize ty0 <= ofs ->
  Loc.notin (S (Outgoing ofs0 ty0)) (loc_arguments_rec tyl ofs).
Proof.
  induction tyl; simpl; intros.
  auto.
  destruct a.
  split. simpl. omega. apply IHtyl. omega. 
  split. simpl. omega. apply IHtyl. omega. 
Qed.

Lemma loc_arguments_norepet:
  forall (s: signature), Loc.norepet (loc_arguments s).
Proof.
  intros. unfold loc_arguments. generalize (sig_args s) 0.
  induction l; simpl; intros.
  constructor.
  destruct a; constructor.
  apply loc_arguments_rec_notin_outgoing. simpl; omega. auto.
  apply loc_arguments_rec_notin_outgoing. simpl; omega. auto.
Qed.

(** The offsets of [Outgoing] arguments are below [size_arguments s]. *)

Remark size_arguments_rec_above:
  forall tyl ofs0, ofs0 <= size_arguments_rec tyl ofs0.
Proof.
  induction tyl; simpl; intros.
  omega.
  destruct a.
  apply Zle_trans with (ofs0 + 1); auto; omega.
  apply Zle_trans with (ofs0 + 2); auto; omega.
Qed.

Lemma size_arguments_above:
  forall s, size_arguments s >= 0.
Proof.
  intros; unfold size_arguments. apply Zle_ge.  
  apply size_arguments_rec_above.
Qed.

Lemma loc_arguments_bounded:
  forall (s: signature) (ofs: Z) (ty: typ),
  In (S (Outgoing ofs ty)) (loc_arguments s) ->
  ofs + typesize ty <= size_arguments s.
Proof.
  intros until ty. unfold loc_arguments, size_arguments. generalize (sig_args s) 0.
  induction l; simpl; intros.
  elim H.
  destruct a; simpl in H; destruct H.
  inv H. apply size_arguments_rec_above.
  auto.
  inv H. apply size_arguments_rec_above.
  auto.
Qed.

(** Temporary registers do not overlap with argument locations. *)

Lemma loc_arguments_not_temporaries:
  forall sig, Loc.disjoint (loc_arguments sig) temporaries.
Proof.
  intros; red; intros x1 x2 H.
  generalize (loc_arguments_rec_charact _ _ _ H).
  destruct x1. tauto. destruct s; intuition.
  revert H1. simpl; ElimOrEq; auto.
Qed.
Hint Resolve loc_arguments_not_temporaries: locs.

(** Argument registers are caller-save. *)

Lemma arguments_caller_save:
  forall sig r,
  In (R r) (loc_arguments sig) -> In (R r) destroyed_at_call.
Proof.
  unfold loc_arguments; intros.
  elim (loc_arguments_rec_charact _ _ _ H); simpl.
Qed.

(** Argument locations agree in number with the function signature. *)

Lemma loc_arguments_length:
  forall sig,
  List.length (loc_arguments sig) = List.length sig.(sig_args).
Proof.
  intros. unfold loc_arguments. generalize (sig_args sig) 0.
  induction l; simpl; intros. auto. destruct a; simpl; decEq; auto.
Qed.

(** Argument locations agree in types with the function signature. *)

Lemma loc_arguments_type:
  forall sig, List.map Loc.type (loc_arguments sig) = sig.(sig_args).
Proof.
  intros. unfold loc_arguments. generalize (sig_args sig) 0. 
  induction l; simpl; intros. auto. destruct a; simpl; decEq; auto.
Qed.
