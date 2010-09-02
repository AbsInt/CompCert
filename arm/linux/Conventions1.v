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
  F0 :: F1 :: nil.

Definition int_callee_save_regs :=
  R4 :: R5 :: R6 :: R7 :: R8 :: R9 :: R11 :: nil.

Definition float_callee_save_regs :=
  F4 :: F5 :: F6 :: F7 :: nil.

Definition destroyed_at_call_regs :=
  int_caller_save_regs ++ float_caller_save_regs.

Definition destroyed_at_call :=
  List.map R destroyed_at_call_regs.

Definition int_temporaries := IT1 :: IT2 :: nil.

Definition float_temporaries := FT1 :: FT2 :: nil.
  
Definition temporaries := 
  R IT1 :: R IT2 :: R FT1 :: R FT2 :: nil.

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
  | F4 => 0  | F5 => 1  | F6 => 2  | F7 => 3
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
  compiler with libraries compiled by another PowerPC compiler, we
  implement the standard conventions defined in the PowerPC application
  binary interface. *)

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

(** We use the following calling conventions, adapted from the ARM ABI:
- The first 4 integer arguments are passed in registers [R0] to [R3].
- The first 2 float arguments are passed in registers [F0] and [F1].
- Each float argument passed in a float register ``consumes'' two
  integer arguments.
- Extra arguments are passed on the stack, in [Outgoing] slots, consecutively
  assigned (1 word for an integer argument, 2 words for a float),
  starting at word offset 0.

These conventions are somewhat baroque, but they are mandated by the ABI.
*)

Fixpoint loc_arguments_rec
    (tyl: list typ) (iregl: list mreg) (fregl: list mreg)
    (ofs: Z) {struct tyl} : list loc :=
  match tyl with
  | nil => nil
  | Tint :: tys =>
      match iregl with
      | nil =>
          S (Outgoing ofs Tint) :: loc_arguments_rec tys nil fregl (ofs + 1)
      | ireg :: iregs =>
          R ireg :: loc_arguments_rec tys iregs fregl ofs
      end
  | Tfloat :: tys =>
      match fregl with
      | nil =>
          S (Outgoing ofs Tfloat) ::
          loc_arguments_rec tys iregl nil (ofs + 2)
      | freg :: fregs =>
          match iregl with
          | nil =>
              S (Outgoing ofs Tfloat) ::
              loc_arguments_rec tys nil fregl (ofs + 2)
          | ireg :: nil =>
              R freg ::
              loc_arguments_rec tys nil fregs (ofs + 1)              
          | ireg1 :: ireg2 :: iregs =>
              R freg ::
              loc_arguments_rec tys iregs fregs ofs
          end
      end
  end.

Definition int_param_regs :=
  R0 :: R1 :: R2 :: R3 :: nil.
Definition float_param_regs :=
  F0 :: F1 :: nil.

(** [loc_arguments s] returns the list of locations where to store arguments
  when calling a function with signature [s].  *)

Definition loc_arguments (s: signature) : list loc :=
  loc_arguments_rec s.(sig_args) int_param_regs float_param_regs 0.

(** [size_arguments s] returns the number of [Outgoing] slots used
  to call a function with signature [s]. *)

Fixpoint size_arguments_rec
    (tyl: list typ) (iregl: list mreg) (fregl: list mreg)
    (ofs: Z) {struct tyl} : Z :=
  match tyl with
  | nil => ofs
  | Tint :: tys =>
      match iregl with
      | nil => size_arguments_rec tys nil fregl (ofs + 1)
      | ireg :: iregs => size_arguments_rec tys iregs fregl ofs
      end
  | Tfloat :: tys =>
      match fregl with
      | nil =>
          size_arguments_rec tys iregl nil (ofs + 2)
      | freg :: fregs =>
          match iregl with
          | nil =>
              size_arguments_rec tys nil fregl (ofs + 2)
          | ireg :: nil =>
              size_arguments_rec tys nil fregs (ofs + 1)              
          | ireg1 :: ireg2 :: iregs =>
              size_arguments_rec tys iregs fregs ofs
          end
      end
  end.

Definition size_arguments (s: signature) : Z :=
  size_arguments_rec s.(sig_args) int_param_regs float_param_regs 0.

(** Argument locations are either non-temporary registers or [Outgoing] 
  stack slots at nonnegative offsets. *)

Definition loc_argument_acceptable (l: loc) : Prop :=
  match l with
  | R r => ~(In l temporaries)
  | S (Outgoing ofs ty) => ofs >= 0
  | _ => False
  end.

Remark loc_arguments_rec_charact:
  forall tyl iregl fregl ofs l,
  In l (loc_arguments_rec tyl iregl fregl ofs) ->
  match l with
  | R r => In r iregl \/ In r fregl
  | S (Outgoing ofs' ty) => ofs' >= ofs
  | S _ => False
  end.
Proof.
  induction tyl; simpl loc_arguments_rec; intros.
  elim H.
  destruct a. 
  destruct iregl; elim H; intro. 
  subst l. omega.
  generalize (IHtyl _ _ _ _ H0). destruct l; auto. destruct s; auto. omega.
  subst l. auto with coqlib.
  generalize (IHtyl _ _ _ _ H0). destruct l; auto. simpl; intuition.
  destruct fregl. 
  elim H; intro.
  subst l. omega.
  generalize (IHtyl _ _ _ _ H0). destruct l; auto. destruct s; auto. omega.
  destruct iregl.
  elim H; intro.
  subst l. omega.
  generalize (IHtyl _ _ _ _ H0). destruct l; auto. destruct s; auto. omega.
  destruct iregl.
  elim H; intro.
  subst l. auto with coqlib.
  generalize (IHtyl _ _ _ _ H0). destruct l; auto.
  intros [A|B]. elim A. auto with coqlib.
  destruct s; auto. omega.
  elim H; intro.
  subst l. auto with coqlib.
  generalize (IHtyl _ _ _ _ H0). destruct l; auto.
  intros [A|B]; auto with coqlib.
Qed.

Lemma loc_arguments_acceptable:
  forall (s: signature) (r: loc),
  In r (loc_arguments s) -> loc_argument_acceptable r.
Proof.
  unfold loc_arguments; intros.
  generalize (loc_arguments_rec_charact _ _ _ _ _ H).
  destruct r.
  intro H0; elim H0. simpl. unfold not. ElimOrEq; NotOrEq.
  simpl. unfold not. ElimOrEq; NotOrEq.
  destruct s0; try contradiction.
  simpl. omega. 
Qed. 
Hint Resolve loc_arguments_acceptable: locs.

(** Arguments are parwise disjoint (in the sense of [Loc.norepet]). *)

Remark loc_arguments_rec_notin_reg:
  forall tyl iregl fregl ofs r,
  ~(In r iregl) -> ~(In r fregl) ->
  Loc.notin (R r) (loc_arguments_rec tyl iregl fregl ofs).
Proof.
  induction tyl; simpl; intros.
  auto.
  destruct a. 
  destruct iregl; simpl. auto.
  simpl in H. split. apply sym_not_equal. tauto.
  apply IHtyl. tauto. tauto.
  destruct fregl; simpl. auto. simpl in H0. 
  destruct iregl; simpl. auto.
  destruct iregl; simpl. 
  split. apply sym_not_equal. tauto. apply IHtyl. hnf. tauto. tauto. 
  split. apply sym_not_equal. tauto. apply IHtyl.  
  red; intro. apply H. auto with coqlib. tauto.
Qed.

Remark loc_arguments_rec_notin_local:
  forall tyl iregl fregl ofs ofs0 ty0,
  Loc.notin (S (Local ofs0 ty0)) (loc_arguments_rec tyl iregl fregl ofs).
Proof.
  induction tyl; simpl; intros.
  auto.
  destruct a.
  destruct iregl; simpl; auto.
  destruct fregl; simpl; auto.
  destruct iregl; simpl; auto.
  destruct iregl; simpl; auto.
Qed.

Remark loc_arguments_rec_notin_outgoing:
  forall tyl iregl fregl ofs ofs0 ty0,
  ofs0 + typesize ty0 <= ofs ->
  Loc.notin (S (Outgoing ofs0 ty0)) (loc_arguments_rec tyl iregl fregl ofs).
Proof.
  induction tyl; simpl; intros.
  auto.
  destruct a.
  destruct iregl; simpl. 
  split. omega. eapply IHtyl. omega.
  auto.
  destruct fregl; simpl. 
  split. omega. eapply IHtyl. omega.
  destruct iregl; simpl.
  split. omega. eapply IHtyl. omega.
  destruct iregl; simpl.
  split; auto. eapply IHtyl. omega.
  split; auto.
Qed.

Lemma loc_arguments_norepet:
  forall (s: signature), Loc.norepet (loc_arguments s).
Proof.
  assert (forall tyl iregl fregl ofs,
    list_norepet iregl ->
    list_norepet fregl ->
    list_disjoint iregl fregl ->
    Loc.norepet (loc_arguments_rec tyl iregl fregl ofs)).
  induction tyl; simpl; intros.
  constructor.
  destruct a. 
  destruct iregl; constructor.
  apply loc_arguments_rec_notin_outgoing. simpl; omega. auto.
  apply loc_arguments_rec_notin_reg. inversion H. auto.
  apply list_disjoint_notin with (m :: iregl); auto with coqlib.
  apply IHtyl. inv H; auto. auto.
  eapply list_disjoint_cons_left; eauto.

  destruct fregl. constructor.
  apply loc_arguments_rec_notin_outgoing. simpl; omega. auto.
  destruct iregl. constructor.
  apply loc_arguments_rec_notin_outgoing. simpl; omega. auto.
  destruct iregl; constructor.
  apply loc_arguments_rec_notin_reg.
  red; intro. apply (H1 m m). auto with coqlib. auto with coqlib. auto. 
  inv H0; auto.
  apply IHtyl. constructor. inv H0; auto. 
  red; intros. elim H2.
  apply loc_arguments_rec_notin_reg.
  red; intros. elim (H1 m m); auto with coqlib.
  inv H0; auto.
  apply IHtyl. inv H. inv H5. auto. inv H0; auto. 
  red; intros. apply H1; auto with coqlib.

  intro. unfold loc_arguments. apply H.
  unfold int_param_regs. NoRepet.
  unfold float_param_regs. NoRepet.
  red; intros x y; simpl. ElimOrEq; ElimOrEq; discriminate.
Qed.

(** The offsets of [Outgoing] arguments are below [size_arguments s]. *)

Remark size_arguments_rec_above:
  forall tyl iregl fregl ofs0,
  ofs0 <= size_arguments_rec tyl iregl fregl ofs0.
Proof.
  induction tyl; simpl; intros.
  omega.
  destruct a.
  destruct iregl. apply Zle_trans with (ofs0 + 1); auto; omega. auto.
  destruct fregl. apply Zle_trans with (ofs0 + 2); auto; omega.
  destruct iregl. apply Zle_trans with (ofs0 + 2); auto; omega.
  destruct iregl. apply Zle_trans with (ofs0 + 1); auto; omega.
  auto.
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
  intros.
  assert (forall tyl iregl fregl ofs0,
    In (S (Outgoing ofs ty)) (loc_arguments_rec tyl iregl fregl ofs0) ->
    ofs + typesize ty <= size_arguments_rec tyl iregl fregl ofs0).
  induction tyl; simpl; intros.
  elim H0.
  destruct a. destruct iregl; elim H0; intro.
  inv H1. simpl. apply size_arguments_rec_above. auto.
  discriminate. auto. 
  destruct fregl. elim H0; intro.
  inv H1. simpl. apply size_arguments_rec_above. auto.
  destruct iregl. elim H0; intro.
  inv H1. simpl. apply size_arguments_rec_above. auto.
  destruct iregl.
  elim H0; intro. inv H1. auto.
  elim H0; intro. inv H1. auto.
 
  unfold size_arguments. eapply H0. unfold loc_arguments in H. eauto.
Qed.

(** Temporary registers do not overlap with argument locations. *)

Lemma loc_arguments_not_temporaries:
  forall sig, Loc.disjoint (loc_arguments sig) temporaries.
Proof.
  intros; red; intros x1 x2 H.
  generalize (loc_arguments_rec_charact _ _ _ _ _ H).
  destruct x1. 
  intro H0; elim H0; simpl; (ElimOrEq; ElimOrEq; congruence).
  destruct s; try contradiction. intro.
  simpl; ElimOrEq; auto.
Qed.
Hint Resolve loc_arguments_not_temporaries: locs.

(** Argument registers are caller-save. *)

Lemma arguments_caller_save:
  forall sig r,
  In (R r) (loc_arguments sig) -> In (R r) destroyed_at_call.
Proof.
  unfold loc_arguments; intros.
  elim (loc_arguments_rec_charact _ _ _ _ _ H); simpl.
  ElimOrEq; intuition.
  ElimOrEq; intuition.
Qed.

(** Argument locations agree in number with the function signature. *)

Lemma loc_arguments_length:
  forall sig,
  List.length (loc_arguments sig) = List.length sig.(sig_args).
Proof.
  assert (forall tyl iregl fregl ofs,
    List.length (loc_arguments_rec tyl iregl fregl ofs) = List.length tyl).
  induction tyl; simpl; intros.
  auto.
  destruct a. 
  destruct iregl; simpl; decEq; auto.
  destruct fregl; simpl; decEq; auto.
  destruct iregl; simpl. decEq; auto.
  destruct iregl; simpl; decEq; auto.

  intros. unfold loc_arguments. auto.
Qed.

(** Argument locations agree in types with the function signature. *)

Lemma loc_arguments_type:
  forall sig, List.map Loc.type (loc_arguments sig) = sig.(sig_args).
Proof.
  assert (forall tyl iregl fregl ofs,
    (forall r, In r iregl -> mreg_type r = Tint) ->
    (forall r, In r fregl -> mreg_type r = Tfloat) ->
    List.map Loc.type (loc_arguments_rec tyl iregl fregl ofs) = tyl).
  induction tyl; simpl; intros.
  auto.
  destruct a. 
  destruct iregl; simpl; f_equal; eauto with coqlib. 
  destruct fregl; simpl.
  f_equal; eauto with coqlib.
  destruct iregl; simpl.
  f_equal; eauto with coqlib.
  destruct iregl; simpl; f_equal; eauto with coqlib.
  apply IHtyl. simpl; tauto. auto with coqlib. 
  apply IHtyl. auto with coqlib. auto with coqlib.

  intros. unfold loc_arguments. apply H. 
  intro; simpl. ElimOrEq; reflexivity.
  intro; simpl. ElimOrEq; reflexivity.
Qed.
