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

(** Correctness proof for the translation from Linear to Mach. *)

(** This file proves semantic preservation for the [Stacking] pass.
  For the target language Mach, we use the abstract semantics
  given in file [Machabstr], where a part of the activation record
  is not resident in memory.  Combined with the semantic equivalence
  result between the two Mach semantics (see file [Machabstr2concr]),
  the proof in this file also shows semantic preservation with
  respect to the concrete Mach semantics. *)

Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Op.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Import Linear.
Require Import Lineartyping.
Require Import Mach.
Require Import Machabstr.
Require Import Bounds.
Require Import Conventions.
Require Import Stacking.

(** * Properties of frames and frame accesses *)

(** ``Good variable'' properties for frame accesses. *)

Lemma typesize_typesize:
  forall ty, AST.typesize ty = 4 * Locations.typesize ty.
Proof.
  destruct ty; auto.
Qed.

Lemma get_slot_ok:
  forall fr ty ofs,
  24 <= ofs -> fr.(fr_low) + ofs + 4 * typesize ty <= 0 ->
  exists v, get_slot fr ty ofs v.
Proof.
  intros. rewrite <- typesize_typesize in H0.
  exists (fr.(fr_contents) ty (fr.(fr_low) + ofs)). constructor; auto. 
Qed.

Lemma set_slot_ok:
  forall fr ty ofs v,
  24 <= ofs -> fr.(fr_low) + ofs + 4 * typesize ty <= 0 ->
  exists fr', set_slot fr ty ofs v fr'.
Proof.
  intros. rewrite <- typesize_typesize in H0.
  econstructor. constructor; eauto.
Qed.

Lemma slot_gss: 
  forall fr1 ty ofs v fr2,
  set_slot fr1 ty ofs v fr2 ->
  get_slot fr2 ty ofs v.
Proof.
  intros. inv H. constructor; auto.
  simpl. destruct (typ_eq ty ty); try congruence.
  rewrite zeq_true. auto.
Qed.

Remark frame_update_gso:
  forall fr ty ofs v ty' ofs',
  ofs' + 4 * typesize ty' <= ofs \/ ofs + 4 * typesize ty <= ofs' ->
  fr_contents (update ty ofs v fr) ty' ofs' = fr_contents fr ty' ofs'.
Proof.
  intros.
  generalize (typesize_pos ty); intro.
  generalize (typesize_pos ty'); intro.
  simpl. rewrite zeq_false. 2: omega.
  repeat rewrite <- typesize_typesize in H.
  destruct (zle (ofs' + AST.typesize ty') ofs). auto.
  destruct (zle (ofs + AST.typesize ty) ofs'). auto.
  omegaContradiction.
Qed.

Remark frame_update_overlap:
  forall fr ty ofs v ty' ofs',
  ofs <> ofs' ->
  ofs' + 4 * typesize ty' > ofs -> ofs + 4 * typesize ty > ofs' ->
  fr_contents (update ty ofs v fr) ty' ofs' = Vundef.
Proof.
  intros. simpl. rewrite zeq_false; auto.
  rewrite <- typesize_typesize in H0. 
  rewrite <- typesize_typesize in H1.
  repeat rewrite zle_false; auto.
Qed.

Remark frame_update_mismatch:
  forall fr ty ofs v ty',
  ty <> ty' ->
  fr_contents (update ty ofs v fr) ty' ofs = Vundef.
Proof.
  intros. simpl. rewrite zeq_true. 
  destruct (typ_eq ty ty'); congruence.
Qed.

Lemma slot_gso:
  forall fr1 ty ofs v fr2 ty' ofs' v',
  set_slot fr1 ty ofs v fr2 ->
  get_slot fr1 ty' ofs' v' ->
  ofs' + 4 * typesize ty' <= ofs \/ ofs + 4 * typesize ty <= ofs' ->
  get_slot fr2 ty' ofs' v'.
Proof.
  intros. inv H. inv H0.
  constructor; auto.
  symmetry. simpl fr_low. apply frame_update_gso. omega.
Qed.

Lemma slot_gi:
  forall f ofs ty,
  24 <= ofs -> fr_low (init_frame f) + ofs + 4 * typesize ty <= 0 ->
  get_slot (init_frame f) ty ofs Vundef.
Proof.
  intros. rewrite <- typesize_typesize in H0. constructor; auto.
Qed.

Section PRESERVATION.

Variable prog: Linear.program.
Variable tprog: Mach.program.
Hypothesis TRANSF: transf_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.


Section FRAME_PROPERTIES.

Variable stack: list Machabstr.stackframe.
Variable f: Linear.function.
Let b := function_bounds f.
Let fe := make_env b.
Variable tf: Mach.function.
Hypothesis TRANSF_F: transf_function f = OK tf.

Lemma unfold_transf_function:
  tf = Mach.mkfunction
         f.(Linear.fn_sig)
         (transl_body f fe)
         f.(Linear.fn_stacksize)
         fe.(fe_size).
Proof.
  generalize TRANSF_F. unfold transf_function.
  case (zlt (Linear.fn_stacksize f) 0). intros; discriminate.
  case (zlt (- Int.min_signed) (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros. unfold fe. unfold b. congruence.
Qed.

Lemma size_no_overflow: fe.(fe_size) <= -Int.min_signed.
Proof.
  generalize TRANSF_F. unfold transf_function.
  case (zlt (Linear.fn_stacksize f) 0). intros; discriminate.
  case (zlt (- Int.min_signed) (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros. unfold fe, b. omega.
Qed.

(** A frame index is valid if it lies within the resource bounds
  of the current function. *)

Definition index_valid (idx: frame_index) :=
  match idx with
  | FI_local x Tint => 0 <= x < b.(bound_int_local)
  | FI_local x Tfloat => 0 <= x < b.(bound_float_local)
  | FI_arg x ty => 14 <= x /\ x + typesize ty <= b.(bound_outgoing)
  | FI_saved_int x => 0 <= x < b.(bound_int_callee_save)
  | FI_saved_float x => 0 <= x < b.(bound_float_callee_save)
  end.

Definition type_of_index (idx: frame_index) :=
  match idx with
  | FI_local x ty => ty
  | FI_arg x ty => ty
  | FI_saved_int x => Tint
  | FI_saved_float x => Tfloat
  end.

(** Non-overlap between the memory areas corresponding to two
  frame indices. *)

Definition index_diff (idx1 idx2: frame_index) : Prop :=
  match idx1, idx2 with
  | FI_local x1 ty1, FI_local x2 ty2 =>
      x1 <> x2 \/ ty1 <> ty2
  | FI_arg x1 ty1, FI_arg x2 ty2 =>
      x1 + typesize ty1 <= x2 \/ x2 + typesize ty2 <= x1
  | FI_saved_int x1, FI_saved_int x2 => x1 <> x2
  | FI_saved_float x1, FI_saved_float x2 => x1 <> x2
  | _, _ => True
  end.

Remark align_float_part:
  4 * bound_outgoing b + 4 * bound_int_local b + 4 * bound_int_callee_save b <=
  align (4 * bound_outgoing b + 4 * bound_int_local b + 4 * bound_int_callee_save b) 8.
Proof.
  apply align_le. omega.
Qed.

Ltac AddPosProps :=
  generalize (bound_int_local_pos b); intro;
  generalize (bound_float_local_pos b); intro;
  generalize (bound_int_callee_save_pos b); intro;
  generalize (bound_float_callee_save_pos b); intro;
  generalize (bound_outgoing_pos b); intro;
  generalize align_float_part; intro.

Lemma size_pos: fe.(fe_size) >= 24.
Proof.
  AddPosProps.
  unfold fe, make_env, fe_size. omega.
Qed.

Opaque function_bounds.

Lemma offset_of_index_disj:
  forall idx1 idx2,
  index_valid idx1 -> index_valid idx2 ->
  index_diff idx1 idx2 ->
  offset_of_index fe idx1 + 4 * typesize (type_of_index idx1) <= offset_of_index fe idx2 \/
  offset_of_index fe idx2 + 4 * typesize (type_of_index idx2) <= offset_of_index fe idx1.
Proof.
  AddPosProps.
  intros.
  destruct idx1; destruct idx2;
  try (destruct t); try (destruct t0);
  unfold offset_of_index, fe, make_env,
    fe_size, fe_ofs_int_local, fe_ofs_int_callee_save,
    fe_ofs_float_local, fe_ofs_float_callee_save,
    type_of_index, typesize;
  simpl in H5; simpl in H6; simpl in H7;
  try omega.
  assert (z <> z0). intuition auto. omega.
  assert (z <> z0). intuition auto. omega.
Qed.

(** The following lemmas give sufficient conditions for indices
  of various kinds to be valid. *)

Lemma index_local_valid:
  forall ofs ty,
  slot_within_bounds f b (Local ofs ty) ->
  index_valid (FI_local ofs ty).
Proof.
  unfold slot_within_bounds, index_valid. auto.
Qed.

Lemma index_arg_valid:
  forall ofs ty,
  slot_within_bounds f b (Outgoing ofs ty) ->
  index_valid (FI_arg ofs ty).
Proof.
  unfold slot_within_bounds, index_valid. auto.
Qed.

Lemma index_saved_int_valid:
  forall r,
  In r int_callee_save_regs ->
  index_int_callee_save r < b.(bound_int_callee_save) ->
  index_valid (FI_saved_int (index_int_callee_save r)).
Proof.
  intros. red. split. 
  apply Zge_le. apply index_int_callee_save_pos; auto. 
  auto.
Qed.

Lemma index_saved_float_valid:
  forall r,
  In r float_callee_save_regs ->
  index_float_callee_save r < b.(bound_float_callee_save) ->
  index_valid (FI_saved_float (index_float_callee_save r)).
Proof.
  intros. red. split. 
  apply Zge_le. apply index_float_callee_save_pos; auto. 
  auto.
Qed.

Hint Resolve index_local_valid index_arg_valid
             index_saved_int_valid index_saved_float_valid: stacking.

(** The offset of a valid index lies within the bounds of the frame. *)

Lemma offset_of_index_valid:
  forall idx,
  index_valid idx ->
  24 <= offset_of_index fe idx /\
  offset_of_index fe idx + 4 * typesize (type_of_index idx) <= fe.(fe_size).
Proof.
  AddPosProps.
  intros.
  destruct idx; try destruct t;
  unfold offset_of_index, fe, make_env,
    fe_size, fe_ofs_int_local, fe_ofs_int_callee_save,
    fe_ofs_float_local, fe_ofs_float_callee_save,
    type_of_index, typesize;
  simpl in H5;
  omega.
Qed. 

(** Offsets for valid index are representable as signed machine integers
  without loss of precision. *)

Lemma offset_of_index_no_overflow:
  forall idx,
  index_valid idx ->
  Int.signed (Int.repr (offset_of_index fe idx)) = offset_of_index fe idx.
Proof.
  intros.
  generalize (offset_of_index_valid idx H). intros [A B].
  apply Int.signed_repr.
  split. apply Zle_trans with 24; auto. compute; intro; discriminate.
  assert (offset_of_index fe idx < fe_size fe).
    generalize (typesize_pos (type_of_index idx)); intro. omega.
  apply Zlt_succ_le. 
  change (Zsucc Int.max_signed) with (- Int.min_signed).
  generalize size_no_overflow. omega. 
Qed.

(** Admissible evaluation rules for the [Mgetstack] and [Msetstack]
  instructions, in case the offset is computed with [offset_of_index]. *)

Lemma exec_Mgetstack':
  forall sp idx ty c rs fr dst m v,
  index_valid idx ->
  get_slot fr ty (offset_of_index fe idx) v ->
  step tge 
     (State stack tf sp
            (Mgetstack (Int.repr (offset_of_index fe idx)) ty dst :: c)
            rs fr m)
  E0 (State stack tf sp c (rs#dst <- v) fr m).
Proof.
  intros. apply exec_Mgetstack.
  rewrite offset_of_index_no_overflow. auto. auto.
Qed.

Lemma exec_Msetstack':
  forall sp idx ty c rs fr src m fr',
  index_valid idx ->
  set_slot fr ty (offset_of_index fe idx) (rs src) fr' ->
  step tge
     (State stack tf sp
           (Msetstack src (Int.repr (offset_of_index fe idx)) ty :: c) 
           rs fr m)
  E0 (State stack tf sp c rs fr' m).
Proof.
  intros. apply exec_Msetstack.
  rewrite offset_of_index_no_overflow. auto. auto.
Qed.

(** An alternate characterization of the [get_slot] and [set_slot]
  operations in terms of the following [index_val] frame access
  function. *)

Definition index_val (idx: frame_index) (fr: frame) :=
  fr.(fr_contents) (type_of_index idx) (fr.(fr_low) + offset_of_index fe idx).

Lemma get_slot_index:
  forall fr idx ty v,
  index_valid idx ->
  fr.(fr_low) = -fe.(fe_size) ->
  ty = type_of_index idx ->
  v = index_val idx fr ->
  get_slot fr ty (offset_of_index fe idx) v.
Proof.
  intros. subst v; subst ty.
  generalize (offset_of_index_valid idx H); intros [A B].
  rewrite <- typesize_typesize in B. 
  unfold index_val. apply get_slot_intro; auto.
  rewrite H0. omega.
Qed.

Lemma set_slot_index:
  forall fr idx v,
  index_valid idx ->
  fr.(fr_low) = -fe.(fe_size) ->
  exists fr', set_slot fr (type_of_index idx) (offset_of_index fe idx) v fr'.
Proof.
  intros. 
  generalize (offset_of_index_valid idx H); intros [A B].
  apply set_slot_ok; auto. rewrite H0. omega.
Qed.

(** Alternate ``good variable'' properties for [get_slot] and [set_slot]. *)

Lemma slot_iss:
  forall fr idx v fr',
  set_slot fr (type_of_index idx) (offset_of_index fe idx) v fr' ->
  index_val idx fr' = v.
Proof.
  intros. exploit slot_gss; eauto. intro. inv H0. auto.
Qed.

Lemma slot_iso:
  forall fr idx v fr' idx',
  set_slot fr (type_of_index idx) (offset_of_index fe idx) v fr' ->
  index_diff idx idx' ->
  index_valid idx -> index_valid idx' ->
  index_val idx' fr' = index_val idx' fr.
Proof.
  intros. generalize (offset_of_index_disj idx idx' H1 H2 H0). intro.
  inv H. unfold index_val. simpl fr_low. apply frame_update_gso.
  omega.
Qed.

(** * Agreement between location sets and Mach environments *)

(** The following [agree] predicate expresses semantic agreement between:
- on the Linear side, the current location set [ls] and the location
  set at function entry [ls0];
- on the Mach side, a register set [rs] plus the current and parent frames
  [fr] and [parent]. 
*)

Record agree (ls: locset) (rs: regset) (fr parent: frame) (ls0: locset) : Prop :=
  mk_agree {
    (** Machine registers have the same values on the Linear and Mach sides. *)
    agree_reg:
      forall r, ls (R r) = rs r;

    (** Machine registers outside the bounds of the current function
        have the same values they had at function entry.  In other terms,
        these registers are never assigned. *)
    agree_unused_reg:
      forall r, ~(mreg_within_bounds b r) -> rs r = ls0 (R r);

    (** The low bound of the current frame is [- fe.(fe_size)]. *)
    agree_size:
      fr.(fr_low) = -fe.(fe_size);

    (** Local and outgoing stack slots (on the Linear side) have
        the same values as the one loaded from the current Mach frame 
        at the corresponding offsets. *)
    agree_locals:
      forall ofs ty, 
      slot_within_bounds f b (Local ofs ty) ->
      ls (S (Local ofs ty)) = index_val (FI_local ofs ty) fr;
    agree_outgoing:
      forall ofs ty, 
      slot_within_bounds f b (Outgoing ofs ty) ->
      ls (S (Outgoing ofs ty)) = index_val (FI_arg ofs ty) fr;

    (** Incoming stack slots (on the Linear side) have
        the same values as the one loaded from the parent Mach frame 
        at the corresponding offsets. *)
    agree_incoming:
      forall ofs ty,
      slot_within_bounds f b (Incoming ofs ty) ->
      get_slot parent ty (Int.signed (Int.repr (4 * ofs))) (ls (S (Incoming ofs ty)));

    (** The areas of the frame reserved for saving used callee-save
        registers always contain the values that those registers had
        on function entry. *)
    agree_saved_int:
      forall r,
      In r int_callee_save_regs ->
      index_int_callee_save r < b.(bound_int_callee_save) ->
      index_val (FI_saved_int (index_int_callee_save r)) fr = ls0 (R r);
    agree_saved_float:
      forall r,
      In r float_callee_save_regs ->
      index_float_callee_save r < b.(bound_float_callee_save) ->
      index_val (FI_saved_float (index_float_callee_save r)) fr = ls0 (R r)
  }.

Hint Resolve agree_reg agree_unused_reg agree_size 
             agree_locals agree_outgoing agree_incoming
             agree_saved_int agree_saved_float: stacking.

(** Values of registers and register lists. *)

Lemma agree_eval_reg:
  forall ls rs fr parent ls0 r,
  agree ls rs fr parent ls0 -> rs r = ls (R r).
Proof.
  intros. symmetry. eauto with stacking.
Qed.

Lemma agree_eval_regs:
  forall ls rs fr parent ls0 rl,
  agree ls rs fr parent ls0 -> rs##rl = reglist ls rl.
Proof.
  induction rl; simpl; intros.
  auto. f_equal. eapply agree_eval_reg; eauto. auto.
Qed.

Hint Resolve agree_eval_reg agree_eval_regs: stacking.

(** Preservation of agreement under various assignments:
  of machine registers, of local slots, of outgoing slots. *)

Lemma agree_set_reg:
  forall ls rs fr parent ls0 r v,
  agree ls rs fr parent ls0 ->
  mreg_within_bounds b r ->
  agree (Locmap.set (R r) v ls) (Regmap.set r v rs) fr parent ls0.
Proof.
  intros. constructor; eauto with stacking.
  intros. case (mreg_eq r r0); intro.
  subst r0. rewrite Locmap.gss; rewrite Regmap.gss; auto.
  rewrite Locmap.gso. rewrite Regmap.gso. eauto with stacking.
  auto. red. auto.
  intros. rewrite Regmap.gso. eauto with stacking. 
  red; intro; subst r0. contradiction.
  intros. rewrite Locmap.gso. eauto with stacking. red. auto.
  intros. rewrite Locmap.gso. eauto with stacking. red. auto.
  intros. rewrite Locmap.gso. eauto with stacking. red. auto.
Qed.

Lemma agree_set_local:
  forall ls rs fr parent ls0 v ofs ty,
  agree ls rs fr parent ls0 ->
  slot_within_bounds f b (Local ofs ty) ->
  exists fr',
    set_slot fr ty (offset_of_index fe (FI_local ofs ty)) v fr' /\
    agree (Locmap.set (S (Local ofs ty)) v ls) rs fr' parent ls0.
Proof.
  intros.
  generalize (set_slot_index fr _ v (index_local_valid _ _ H0) 
                (agree_size _ _ _ _ _ H)).
  intros [fr' SET].
  exists fr'. split. auto. constructor; eauto with stacking.
  (* agree_reg *)
  intros. rewrite Locmap.gso. eauto with stacking. red; auto.
  (* agree_size *)
  inversion SET. rewrite H3; simpl fr_low. eauto with stacking.
  (* agree_local *)
  intros. case (slot_eq (Local ofs ty) (Local ofs0 ty0)); intro.
  rewrite <- e. rewrite Locmap.gss. 
  replace (FI_local ofs0 ty0) with (FI_local ofs ty).
  symmetry. eapply slot_iss; eauto. congruence.
  assert (ofs <> ofs0 \/ ty <> ty0).
    case (zeq ofs ofs0); intro. compare ty ty0; intro.
    congruence. tauto.  tauto. 
  rewrite Locmap.gso. transitivity (index_val (FI_local ofs0 ty0) fr).
  eauto with stacking. symmetry. eapply slot_iso; eauto.
  simpl. auto.
  (* agree_outgoing *)
  intros. rewrite Locmap.gso. transitivity (index_val (FI_arg ofs0 ty0) fr).
  eauto with stacking. symmetry. eapply slot_iso; eauto.
  red; auto. red; auto. 
  (* agree_incoming *)
  intros. rewrite Locmap.gso. eauto with stacking. red. auto.
  (* agree_saved_int *)
  intros. rewrite <- (agree_saved_int _ _ _ _ _ H r H1 H2). 
  eapply slot_iso; eauto with stacking. red; auto.
  (* agree_saved_float *)
  intros. rewrite <- (agree_saved_float _ _ _ _ _ H r H1 H2). 
  eapply slot_iso; eauto with stacking. red; auto.
Qed.

Lemma agree_set_outgoing:
  forall ls rs fr parent ls0 v ofs ty,
  agree ls rs fr parent ls0 ->
  slot_within_bounds f b (Outgoing ofs ty) ->
  exists fr',
    set_slot fr ty (offset_of_index fe (FI_arg ofs ty)) v fr' /\
    agree (Locmap.set (S (Outgoing ofs ty)) v ls) rs fr' parent ls0.
Proof.
  intros. 
  generalize (set_slot_index fr _ v (index_arg_valid _ _ H0)
                (agree_size _ _ _ _ _ H)).
  intros [fr' SET].
  exists fr'. split. exact SET. constructor; eauto with stacking.
  (* agree_reg *)
  intros. rewrite Locmap.gso. eauto with stacking. red; auto.
  (* agree_size *)
  inversion SET. subst fr'; simpl fr_low. eauto with stacking.
  (* agree_local *)
  intros. rewrite Locmap.gso. 
  transitivity (index_val (FI_local ofs0 ty0) fr).
  eauto with stacking. symmetry. eapply slot_iso; eauto.
  red; auto. red; auto. 
  (* agree_outgoing *)
  intros. unfold Locmap.set. 
  case (Loc.eq (S (Outgoing ofs ty)) (S (Outgoing ofs0 ty0))); intro.
  (* same location *)
  replace ofs0 with ofs. replace ty0 with ty. 
  symmetry. eapply slot_iss; eauto.
  congruence. congruence.
  (* overlapping locations *)
  caseEq (Loc.overlap (S (Outgoing ofs ty)) (S (Outgoing ofs0 ty0))); intros.
  inv SET. unfold index_val, type_of_index, offset_of_index.
  destruct (zeq ofs ofs0).
  subst ofs0. symmetry. apply frame_update_mismatch. 
  destruct ty; destruct ty0; simpl; congruence.
  generalize (Loc.overlap_not_diff _ _ H2). intro. simpl in H5.
  simpl fr_low. symmetry. apply frame_update_overlap. omega. omega. omega.
  (* different locations *)
  transitivity (index_val (FI_arg ofs0 ty0) fr).
  eauto with stacking.
  symmetry. eapply slot_iso; eauto. 
  simpl. eapply Loc.overlap_aux_false_1; eauto.
  (* agree_incoming *)
  intros. rewrite Locmap.gso. eauto with stacking. red. auto.
  (* saved ints *)
  intros. rewrite <- (agree_saved_int _ _ _ _ _ H r H1 H2). 
  eapply slot_iso; eauto with stacking. red; auto.
  (* saved floats *)
  intros. rewrite <- (agree_saved_float _ _ _ _ _ H r H1 H2). 
  eapply slot_iso; eauto with stacking. red; auto.
Qed.
(*
Lemma agree_return_regs:
  forall ls rs fr parent ls0 ls' rs',
  agree ls rs fr parent ls0 ->
  (forall r,
    In (R r) temporaries \/ In (R r) destroyed_at_call ->
    rs' r = ls' (R r)) ->
  (forall r,
    In r int_callee_save_regs \/ In r float_callee_save_regs ->
    rs' r = rs r) ->
  agree (LTL.return_regs ls ls') rs' fr parent ls0.
Proof.
  intros. constructor; unfold LTL.return_regs; eauto with stacking.
  (* agree_reg *)
  intros. case (In_dec Loc.eq (R r) temporaries); intro.
  symmetry. apply H0. tauto.
  case (In_dec Loc.eq (R r) destroyed_at_call); intro.
  symmetry. apply H0. tauto.
  rewrite H1. eauto with stacking. 
  generalize (register_classification r); tauto.
  (* agree_unused_reg *)
  intros. rewrite H1. eauto with stacking.
  generalize H2; unfold mreg_within_bounds; case (mreg_type r); intro.
  left. apply index_int_callee_save_pos2. 
  generalize (bound_int_callee_save_pos b); intro. omega.
  right. apply index_float_callee_save_pos2. 
  generalize (bound_float_callee_save_pos b); intro. omega.
Qed. 
*)

Lemma agree_return_regs:
  forall ls rs fr parent ls0 rs',
  agree ls rs fr parent ls0 ->
  (forall r,
    ~In r int_callee_save_regs -> ~In r float_callee_save_regs ->
    rs' r = rs r) ->
  (forall r,
    In r int_callee_save_regs \/ In r float_callee_save_regs ->
    rs' r = ls0 (R r)) ->
  (forall r, LTL.return_regs ls0 ls (R r) = rs' r).
Proof.
  intros; unfold LTL.return_regs.
  case (In_dec Loc.eq (R r) temporaries); intro.
  rewrite H0. eapply agree_reg; eauto. 
    apply int_callee_save_not_destroyed; auto.
    apply float_callee_save_not_destroyed; auto.
  case (In_dec Loc.eq (R r) destroyed_at_call); intro.
  rewrite H0. eapply agree_reg; eauto.
    apply int_callee_save_not_destroyed; auto.
    apply float_callee_save_not_destroyed; auto.
  symmetry; apply H1.
  generalize (register_classification r); tauto.
Qed.

(** Agreement over callee-save registers and stack locations *)

Definition agree_callee_save (ls1 ls2: locset) : Prop :=
  forall l,
  match l with
  | R r => In r int_callee_save_regs \/ In r float_callee_save_regs
  | S s => True
  end ->
  ls2 l = ls1 l.

Remark mreg_not_within_bounds:
  forall r,
  ~mreg_within_bounds b r -> In r int_callee_save_regs \/ In r float_callee_save_regs.
Proof.
  intro r; unfold mreg_within_bounds.
  destruct (mreg_type r); intro.
  left. apply index_int_callee_save_pos2. 
  generalize (bound_int_callee_save_pos b). omega.
  right. apply index_float_callee_save_pos2. 
  generalize (bound_float_callee_save_pos b). omega.
Qed.

Lemma agree_callee_save_agree:
  forall ls rs fr parent ls1 ls2,
  agree ls rs fr parent ls1 ->
  agree_callee_save ls1 ls2 ->
  agree ls rs fr parent ls2.
Proof.
  intros. inv H. constructor; auto.
  intros. rewrite agree_unused_reg0; auto.
  symmetry. apply H0. apply mreg_not_within_bounds; auto.
  intros. rewrite (H0 (R r)); auto. 
  intros. rewrite (H0 (R r)); auto. 
Qed.

Lemma agree_callee_save_return_regs:
  forall ls1 ls2,
  agree_callee_save (LTL.return_regs ls1 ls2) ls1.
Proof.
  intros; red; intros.
  unfold LTL.return_regs. destruct l; auto.
  generalize (int_callee_save_not_destroyed m); intro.
  generalize (float_callee_save_not_destroyed m); intro.
  destruct (In_dec Loc.eq (R m) temporaries). tauto.
  destruct (In_dec Loc.eq (R m) destroyed_at_call). tauto.
  auto.
Qed.

Lemma agree_callee_save_set_result:
  forall ls1 ls2 v sg,
  agree_callee_save ls1 ls2 ->
  agree_callee_save (Locmap.set (R (Conventions.loc_result sg)) v ls1) ls2.
Proof.
  intros; red; intros. rewrite H; auto. 
  symmetry; apply Locmap.gso. destruct l; simpl; auto.
  red; intro. subst m. elim (loc_result_not_callee_save _ H0).
Qed.

(** A variant of [agree] used for return frames. *)

Definition agree_frame (ls: locset) (fr parent: frame) (ls0: locset) : Prop :=
  exists rs, agree ls rs fr parent ls0.

Lemma agree_frame_agree:
  forall ls1 ls2 rs fr parent ls0,
  agree_frame ls1 fr parent ls0 ->
  agree_callee_save ls2 ls1 ->
  (forall r, rs r = ls2 (R r)) ->
  agree ls2 rs fr parent ls0.
Proof.
  intros. destruct H as [rs' AG]. inv AG.
  constructor; auto.
  intros. rewrite <- agree_unused_reg0; auto.
  rewrite <- agree_reg0. rewrite H1. symmetry; apply H0.
  apply mreg_not_within_bounds; auto.
  intros. rewrite <- H0; auto.
  intros. rewrite <- H0; auto.
  intros. rewrite <- H0; auto.
Qed.

(** * Correctness of saving and restoring of callee-save registers *)

(** The following lemmas show the correctness of the register saving
  code generated by [save_callee_save]: after this code has executed,
  the register save areas of the current frame do contain the
  values of the callee-save registers used by the function. *)

Section SAVE_CALLEE_SAVE.

Variable bound: frame_env -> Z.
Variable number: mreg -> Z.
Variable mkindex: Z -> frame_index.
Variable ty: typ.
Variable sp: val.
Variable csregs: list mreg.
Hypothesis number_inj: 
  forall r1 r2, In r1 csregs -> In r2 csregs -> r1 <> r2 -> number r1 <> number r2.
Hypothesis mkindex_valid:
  forall r, In r csregs -> number r < bound fe -> index_valid (mkindex (number r)).
Hypothesis mkindex_typ:
  forall z, type_of_index (mkindex z) = ty.
Hypothesis mkindex_inj:
  forall z1 z2, z1 <> z2 -> mkindex z1 <> mkindex z2.
Hypothesis mkindex_diff:
  forall r idx,
  idx <> mkindex (number r) -> index_diff (mkindex (number r)) idx.

Lemma save_callee_save_regs_correct:
  forall l k rs fr m,
  incl l csregs ->
  list_norepet l ->
  fr.(fr_low) = -fe.(fe_size) ->
  exists fr',
    star step tge 
       (State stack tf sp
         (save_callee_save_regs bound number mkindex ty fe l k) rs fr m)
    E0 (State stack tf sp k rs fr' m)
  /\ fr'.(fr_low) = - fe.(fe_size)
  /\ (forall r,
       In r l -> number r < bound fe ->
       index_val (mkindex (number r)) fr' = rs r)
  /\ (forall idx,
       index_valid idx ->
       (forall r,
         In r l -> number r < bound fe -> idx <> mkindex (number r)) ->
       index_val idx fr' = index_val idx fr).
Proof.
  induction l; intros; simpl save_callee_save_regs.
  (* base case *)
  exists fr. split. apply star_refl. split. auto. 
  split. intros. elim H2. auto.
  (* inductive case *)
  set (k1 := save_callee_save_regs bound number mkindex ty fe l k).
  assert (R1: incl l csregs). eauto with coqlib.
  assert (R2: list_norepet l). inversion H0; auto.
  unfold save_callee_save_reg.
  destruct (zlt (number a) (bound fe)).
  (* a store takes place *)
  assert (VALID: index_valid (mkindex (number a))).
    apply mkindex_valid. auto with coqlib. auto.
  exploit set_slot_index; eauto.
  intros [fr1 SET].
  exploit (IHl k rs fr1 m); auto. inv SET; auto. 
  fold k1. intros [fr' [A [B [C D]]]].
  exists fr'.
  split. eapply star_left.
  apply exec_Msetstack'; eauto with stacking. rewrite <- (mkindex_typ (number a)). eauto.
  eexact A. traceEq.
  split. auto. 
  split. intros. elim H2; intros. subst r. 
    rewrite D. eapply slot_iss; eauto.  
    apply mkindex_valid; auto.
    intros. apply mkindex_inj. apply number_inj; auto with coqlib.
    inversion H0. red; intro; subst r; contradiction.
    apply C; auto.
  intros. transitivity (index_val idx fr1).
    apply D; auto. 
    intros. apply H3; eauto with coqlib.
    eapply slot_iso; eauto.
    apply mkindex_diff. apply H3. auto with coqlib.
    auto.
  (* no store takes place *)
  exploit (IHl k rs fr m); auto. intros [fr' [A [B [C D]]]].
  exists fr'. split. exact A. split. exact B.
  split. intros. elim H2; intros. subst r. omegaContradiction.
    apply C; auto. 
  intros. apply D; auto.
    intros. apply H3; auto with coqlib.
Qed.

End SAVE_CALLEE_SAVE. 

Lemma save_callee_save_int_correct:
  forall k sp rs fr m,
  fr.(fr_low) = - fe.(fe_size) ->
  exists fr',
    star step tge 
       (State stack tf sp
         (save_callee_save_int fe k) rs fr m)
    E0 (State stack tf sp k rs fr' m)
  /\ fr'.(fr_low) = - fe.(fe_size)
  /\ (forall r,
       In r int_callee_save_regs ->
       index_int_callee_save r < bound_int_callee_save b ->
       index_val (FI_saved_int (index_int_callee_save r)) fr' = rs r)
  /\ (forall idx,
       index_valid idx ->
       match idx with FI_saved_int _ => False | _ => True end ->
       index_val idx fr' = index_val idx fr).
Proof.
  intros.
  exploit (save_callee_save_regs_correct fe_num_int_callee_save index_int_callee_save FI_saved_int
                                         Tint sp int_callee_save_regs).
  exact index_int_callee_save_inj.
  intros. red. split; auto. generalize (index_int_callee_save_pos r H0). omega.
  auto.
  intros; congruence.
  intros until idx. destruct idx; simpl; auto. congruence.
  apply incl_refl.
  apply int_callee_save_norepet. eauto.
  intros [fr' [A [B [C D]]]]. 
  exists fr'; intuition. unfold save_callee_save_int; eauto. 
  apply D. auto. intros; subst idx. auto.
Qed.

Lemma save_callee_save_float_correct:
  forall k sp rs fr m,
  fr.(fr_low) = - fe.(fe_size) ->
  exists fr',
    star step tge 
       (State stack tf sp
         (save_callee_save_float fe k) rs fr m)
    E0 (State stack tf sp k rs fr' m)
  /\ fr'.(fr_low) = - fe.(fe_size)
  /\ (forall r,
       In r float_callee_save_regs ->
       index_float_callee_save r < bound_float_callee_save b ->
       index_val (FI_saved_float (index_float_callee_save r)) fr' = rs r)
  /\ (forall idx,
       index_valid idx ->
       match idx with FI_saved_float _ => False | _ => True end ->
       index_val idx fr' = index_val idx fr).
Proof.
  intros.
  exploit (save_callee_save_regs_correct fe_num_float_callee_save index_float_callee_save FI_saved_float
                                         Tfloat sp float_callee_save_regs).
  exact index_float_callee_save_inj.
  intros. red. split; auto. generalize (index_float_callee_save_pos r H0). omega.
  auto.
  intros; congruence.
  intros until idx. destruct idx; simpl; auto. congruence.
  apply incl_refl.
  apply float_callee_save_norepet. eauto.
  intros [fr' [A [B [C D]]]]. 
  exists fr'; intuition. unfold save_callee_save_float; eauto. 
  apply D. auto. intros; subst idx. auto.
Qed.

Lemma save_callee_save_correct:
  forall sp k rs fr m ls,
  (forall r, rs r = ls (R r)) ->
  (forall ofs ty, 
     14 <= ofs -> 
     ofs + typesize ty <= size_arguments f.(Linear.fn_sig) ->
     get_slot (parent_frame stack) ty (Int.signed (Int.repr (4 * ofs))) (ls (S (Outgoing ofs ty)))) ->
  fr.(fr_low) = - fe.(fe_size) ->
  (forall idx, index_valid idx -> index_val idx fr = Vundef) ->
  exists fr',
    star step tge
       (State stack tf sp (save_callee_save fe k) rs fr m)
    E0 (State stack tf sp k rs fr' m)
  /\ agree (LTL.call_regs ls) rs fr' (parent_frame stack) ls.
Proof.
  intros. unfold save_callee_save.
  exploit save_callee_save_int_correct; eauto. 
  intros [fr1 [A1 [B1 [C1 D1]]]].
  exploit save_callee_save_float_correct. eexact B1. 
  intros [fr2 [A2 [B2 [C2 D2]]]].
  exists fr2.
  split. eapply star_trans. eexact A1. eexact A2. traceEq.
  constructor; unfold LTL.call_regs; auto.
  (* agree_local *)
  intros. rewrite D2; auto with stacking. 
  rewrite D1; auto with stacking. 
  symmetry. auto with stacking.
  (* agree_outgoing *)
  intros. rewrite D2; auto with stacking. 
  rewrite D1; auto with stacking. 
  symmetry. auto with stacking. 
  (* agree_incoming *)
  intros. simpl in H3. apply H0. tauto. tauto.
  (* agree_saved_int *)
  intros. rewrite D2; auto with stacking.
  rewrite C1; auto with stacking. 
  (* agree_saved_float *)
  intros. rewrite C2; auto with stacking. 
Qed.

(** The following lemmas show the correctness of the register reloading
  code generated by [reload_callee_save]: after this code has executed,
  all callee-save registers contain the same values they had at
  function entry. *)

Section RESTORE_CALLEE_SAVE.

Variable bound: frame_env -> Z.
Variable number: mreg -> Z.
Variable mkindex: Z -> frame_index.
Variable ty: typ.
Variable sp: val.
Variable csregs: list mreg.
Hypothesis mkindex_valid:
  forall r, In r csregs -> number r < bound fe -> index_valid (mkindex (number r)).
Hypothesis mkindex_typ:
  forall z, type_of_index (mkindex z) = ty.
Hypothesis number_within_bounds:
  forall r, In r csregs ->
  (number r < bound fe <-> mreg_within_bounds b r).
Hypothesis mkindex_val:
  forall ls rs fr ls0 r, 
  agree ls rs fr (parent_frame stack) ls0 -> In r csregs -> number r < bound fe ->
  index_val (mkindex (number r)) fr = ls0 (R r).

Lemma restore_callee_save_regs_correct:
  forall k fr m ls0 l ls rs,
  incl l csregs ->
  list_norepet l -> 
  agree ls rs fr (parent_frame stack) ls0 ->
  exists ls', exists rs',
    star step tge
      (State stack tf sp
        (restore_callee_save_regs bound number mkindex ty fe l k) rs fr m)
   E0 (State stack tf sp k rs' fr m)
  /\ (forall r, In r l -> rs' r = ls0 (R r))
  /\ (forall r, ~(In r l) -> rs' r = rs r)
  /\ agree ls' rs' fr (parent_frame stack) ls0.
Proof.
  induction l; intros; simpl restore_callee_save_regs.
  (* base case *)
  exists ls. exists rs. 
  split. apply star_refl. 
  split. intros. elim H2. 
  split. auto. auto.
  (* inductive case *)
  set (k1 := restore_callee_save_regs bound number mkindex ty fe l k).
  assert (R0: In a csregs). apply H; auto with coqlib.
  assert (R1: incl l csregs). eauto with coqlib.
  assert (R2: list_norepet l). inversion H0; auto.
  unfold restore_callee_save_reg.
  destruct (zlt (number a) (bound fe)).
  set (ls1 := Locmap.set (R a) (ls0 (R a)) ls).
  set (rs1 := Regmap.set a (ls0 (R a)) rs).
  assert (R3: agree ls1 rs1 fr (parent_frame stack) ls0). 
    unfold ls1, rs1. apply agree_set_reg. auto. 
    rewrite <- number_within_bounds; auto. 
  generalize (IHl ls1 rs1 R1 R2 R3). 
  intros [ls' [rs' [A [B [C D]]]]].
  exists ls'. exists rs'. split. 
  apply star_left with E0 (State stack tf sp k1 rs1 fr m) E0.
  unfold rs1; apply exec_Mgetstack'; eauto with stacking.
  apply get_slot_index; eauto with stacking.
  symmetry. eapply mkindex_val; eauto.  
  auto. traceEq.
  split. intros. elim H2; intros.
  subst r. rewrite C. unfold rs1. apply Regmap.gss. inversion H0; auto.
  auto.
  split. intros. simpl in H2. rewrite C. unfold rs1. apply Regmap.gso.
  apply sym_not_eq; tauto. tauto.
  assumption.
  (* no load takes place *)
  generalize (IHl ls rs R1 R2 H1).  
  intros [ls' [rs' [A [B [C D]]]]].
  exists ls'; exists rs'. split. assumption.
  split. intros. elim H2; intros. 
  subst r. apply (agree_unused_reg _ _ _ _ _ D).
  rewrite <- number_within_bounds. auto. omega. auto.
  split. intros. simpl in H2. apply C. tauto.
  assumption.
Qed.

End RESTORE_CALLEE_SAVE.

Lemma restore_int_callee_save_correct:
  forall sp k fr m ls0 ls rs,
  agree ls rs fr (parent_frame stack) ls0 ->
  exists ls', exists rs',
    star step tge
       (State stack tf sp
         (restore_callee_save_int fe k) rs fr m)
    E0 (State stack tf sp k rs' fr m)
  /\ (forall r, In r int_callee_save_regs -> rs' r = ls0 (R r))
  /\ (forall r, ~(In r int_callee_save_regs) -> rs' r = rs r)
  /\ agree ls' rs' fr (parent_frame stack) ls0.
Proof.
  intros. unfold restore_callee_save_int.
  apply restore_callee_save_regs_correct with int_callee_save_regs ls.
  intros; simpl. split; auto. generalize (index_int_callee_save_pos r H0). omega.
  auto.
  intros. unfold mreg_within_bounds. 
  rewrite (int_callee_save_type r H0). tauto. 
  eauto with stacking. 
  apply incl_refl.
  apply int_callee_save_norepet.
  auto.
Qed.

Lemma restore_float_callee_save_correct:
  forall sp k fr m ls0 ls rs,
  agree ls rs fr (parent_frame stack) ls0 ->
  exists ls', exists rs',
    star step tge
       (State stack tf sp
          (restore_callee_save_float fe k) rs fr m)
    E0 (State stack tf sp k rs' fr m)
  /\ (forall r, In r float_callee_save_regs -> rs' r = ls0 (R r))
  /\ (forall r, ~(In r float_callee_save_regs) -> rs' r = rs r)
  /\ agree ls' rs' fr (parent_frame stack) ls0.
Proof.
  intros. unfold restore_callee_save_float.
  apply restore_callee_save_regs_correct with float_callee_save_regs ls.
  intros; simpl. split; auto. generalize (index_float_callee_save_pos r H0). omega.
  auto.
  intros. unfold mreg_within_bounds. 
  rewrite (float_callee_save_type r H0). tauto. 
  eauto with stacking. 
  apply incl_refl.
  apply float_callee_save_norepet.
  auto.
Qed.

Lemma restore_callee_save_correct:
  forall sp k fr m ls0 ls rs,
  agree ls rs fr (parent_frame stack) ls0 ->
  exists rs',
    star step tge
       (State stack tf sp (restore_callee_save fe k) rs fr m)
    E0 (State stack tf sp k rs' fr m)
  /\ (forall r, 
        In r int_callee_save_regs \/ In r float_callee_save_regs -> 
        rs' r = ls0 (R r))
  /\ (forall r, 
        ~(In r int_callee_save_regs) ->
        ~(In r float_callee_save_regs) ->
        rs' r = rs r).
Proof.
  intros. unfold restore_callee_save.
  exploit restore_int_callee_save_correct; eauto.
  intros [ls1 [rs1 [A [B [C D]]]]].
  exploit restore_float_callee_save_correct. eexact D.
  intros [ls2 [rs2 [P [Q [R S]]]]].
  exists rs2. split. eapply star_trans. eexact A. eexact P. traceEq.
  split. intros. elim H0; intros.
  rewrite R. apply B. auto. apply list_disjoint_notin with int_callee_save_regs.
  apply int_float_callee_save_disjoint. auto.
  apply Q. auto.
  intros. rewrite R. apply C. auto. auto.
Qed.

End FRAME_PROPERTIES.

(** * Semantic preservation *)

(** Preservation of code labels through the translation. *)

Section LABELS.

Remark find_label_fold_right:
  forall (A: Set) (fn: A -> Mach.code -> Mach.code) lbl,
  (forall x k, Mach.find_label lbl (fn x k) = Mach.find_label lbl k) ->  forall (args: list A) k,
  Mach.find_label lbl (List.fold_right fn k args) = Mach.find_label lbl k.
Proof.
  induction args; simpl. auto. 
  intros. rewrite H. auto.
Qed.

Remark find_label_save_callee_save:
  forall fe lbl k,
  Mach.find_label lbl (save_callee_save fe k) = Mach.find_label lbl k.
Proof.
  intros. unfold save_callee_save, save_callee_save_int, save_callee_save_float, save_callee_save_regs.
  repeat rewrite find_label_fold_right. reflexivity.
  intros. unfold save_callee_save_reg. 
  case (zlt (index_float_callee_save x) (fe_num_float_callee_save fe));
  intro; reflexivity.
  intros. unfold save_callee_save_reg.  
  case (zlt (index_int_callee_save x) (fe_num_int_callee_save fe));
  intro; reflexivity.
Qed.

Remark find_label_restore_callee_save:
  forall fe lbl k,
  Mach.find_label lbl (restore_callee_save fe k) = Mach.find_label lbl k.
Proof.
  intros. unfold restore_callee_save, restore_callee_save_int, restore_callee_save_float, restore_callee_save_regs.
  repeat rewrite find_label_fold_right. reflexivity.
  intros. unfold restore_callee_save_reg. 
  case (zlt (index_float_callee_save x) (fe_num_float_callee_save fe));
  intro; reflexivity.
  intros. unfold restore_callee_save_reg. 
  case (zlt (index_int_callee_save x) (fe_num_int_callee_save fe));
  intro; reflexivity.
Qed.

Lemma find_label_transl_code:
  forall fe lbl c,
  Mach.find_label lbl (transl_code fe c) =
    option_map (transl_code fe) (Linear.find_label lbl c).
Proof.
  induction c; simpl; intros.
  auto.
  destruct a; unfold transl_instr; auto.
  destruct s; simpl; auto.
  destruct s; simpl; auto.
  rewrite find_label_restore_callee_save. auto.
  simpl. case (peq lbl l); intro. reflexivity. auto.
  rewrite find_label_restore_callee_save. auto.
Qed.

Lemma transl_find_label:
  forall f tf lbl c,
  transf_function f = OK tf ->
  Linear.find_label lbl f.(Linear.fn_code) = Some c ->
  Mach.find_label lbl tf.(Mach.fn_code) = 
    Some (transl_code (make_env (function_bounds f)) c).
Proof.
  intros. rewrite (unfold_transf_function _ _ H).  simpl. 
  unfold transl_body. rewrite find_label_save_callee_save.
  rewrite find_label_transl_code. rewrite H0. reflexivity.
Qed.

End LABELS.

(** Code inclusion property for Linear executions. *)

Lemma find_label_incl:
  forall lbl c c', 
  Linear.find_label lbl c = Some c' -> incl c' c.
Proof.
  induction c; simpl.
  intros; discriminate.
  intro c'. case (Linear.is_label lbl a); intros.
  injection H; intro; subst c'. red; intros; auto with coqlib. 
  apply incl_tl. auto.
Qed.

(** Preservation / translation of global symbols and functions. *)

Lemma symbols_preserved:
  forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_symbol_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof
  (Genv.find_funct_transf_partial transf_fundef TRANSF).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  exists tf,
  Genv.find_funct_ptr tge v = Some tf /\ transf_fundef f = OK tf.
Proof
  (Genv.find_funct_ptr_transf_partial transf_fundef TRANSF).

Lemma sig_preserved:
  forall f tf, transf_fundef f = OK tf -> Mach.funsig tf = Linear.funsig f.
Proof.
  intros until tf; unfold transf_fundef, transf_partial_fundef.
  destruct f. unfold transf_function. 
  destruct (zlt (Linear.fn_stacksize f) 0). simpl; congruence.
  destruct (zlt (- Int.min_signed) (fe_size (make_env (function_bounds f)))). simpl; congruence.
  unfold bind. intros. inversion H; reflexivity. 
  intro. inversion H. reflexivity.
Qed.

Lemma find_function_translated:
  forall f0 ls rs fr parent ls0 ros f,
  agree f0 ls rs fr parent ls0 ->
  Linear.find_function ge ros ls = Some f ->
  exists tf,
  find_function tge ros rs = Some tf /\ transf_fundef f = OK tf.
Proof.
  intros until f; intro AG.
  destruct ros; simpl.
  rewrite (agree_eval_reg _ _ _ _ _ _ m AG). intro.
  apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i); try congruence.
  intro. apply function_ptr_translated; auto.
Qed.

Hypothesis wt_prog: wt_program prog.

Lemma find_function_well_typed:
  forall ros ls f,
  Linear.find_function ge ros ls = Some f -> wt_fundef f.
Proof.
  intros until f; destruct ros; simpl; unfold ge.
  intro. eapply Genv.find_funct_prop; eauto.
  destruct (Genv.find_symbol (Genv.globalenv prog) i); try congruence.
  intro. eapply Genv.find_funct_ptr_prop; eauto. 
Qed.

(** Correctness of stack pointer relocation in operations and
  addressing modes. *)

Definition shift_sp (tf: Mach.function) (sp: val) :=
  Val.add sp (Vint (Int.repr (-tf.(fn_framesize)))).

Remark shift_offset_sp:
  forall f tf sp n v,
  transf_function f = OK tf ->
  offset_sp sp n = Some v ->
  offset_sp (shift_sp tf sp)
    (Int.add (Int.repr (fe_size (make_env (function_bounds f)))) n) = Some v.
Proof.
  intros. destruct sp; try discriminate.
  unfold offset_sp in *. 
  unfold shift_sp. 
  rewrite (unfold_transf_function _ _ H). unfold fn_framesize.
  unfold Val.add. rewrite <- Int.neg_repr. 
  set (p := Int.repr (fe_size (make_env (function_bounds f)))).
  inversion H0. decEq. decEq. 
  rewrite Int.add_assoc. decEq. 
  rewrite <- Int.add_assoc. 
  rewrite (Int.add_commut (Int.neg p) p). rewrite Int.add_neg_zero. 
  rewrite Int.add_commut. apply Int.add_zero.
Qed.

Lemma shift_eval_operation:
  forall f tf sp op args m v,
  transf_function f = OK tf ->
  eval_operation ge sp op args m = Some v ->
  eval_operation tge (shift_sp tf sp) 
                 (transl_op (make_env (function_bounds f)) op) args m =
  Some v.
Proof.
  intros until v. destruct op; intros; auto.
  simpl in *. rewrite symbols_preserved. auto.
  destruct args; auto. unfold eval_operation in *. unfold transl_op.
  apply shift_offset_sp; auto.
Qed.

Lemma shift_eval_addressing:
  forall f tf sp addr args v,
  transf_function f = OK tf ->
  eval_addressing ge sp addr args = Some v ->
  eval_addressing tge (shift_sp tf sp) 
                 (transl_addr (make_env (function_bounds f)) addr) args =
  Some v.
Proof.
  intros. destruct addr; auto.
  simpl. rewrite symbols_preserved. auto.
  simpl. rewrite symbols_preserved. auto.
  unfold transl_addr, eval_addressing in *.
  destruct args; try discriminate.
  apply shift_offset_sp; auto.
Qed.

(** Preservation of the arguments to an external call. *)

Section EXTERNAL_ARGUMENTS.

Variable ls: locset.
Variable fr: frame.
Variable rs: regset.
Variable sg: signature.
Hypothesis AG1: forall r, rs r = ls (R r).
Hypothesis AG2: forall (ofs : Z) (ty : typ),
      14 <= ofs ->
      ofs + typesize ty <= size_arguments sg ->
      get_slot fr ty (Int.signed (Int.repr (4 * ofs)))
                     (ls (S (Outgoing ofs ty))).

Lemma transl_external_arguments_rec:
  forall locs,
  (forall l, In l locs -> loc_argument_acceptable l) ->
  (forall ofs ty, In (S (Outgoing ofs ty)) locs ->
                  ofs + typesize ty <= size_arguments sg) ->
  extcall_args rs fr locs ls##locs.
Proof.
  induction locs; simpl; intros.
  constructor.
  constructor. 
  assert (loc_argument_acceptable a). apply H; auto.
  destruct a; red in H1.
  rewrite <- AG1. constructor. 
  destruct s; try contradiction.
  constructor. apply AG2. omega. apply H0. auto.
  apply IHlocs; auto.
Qed.

Lemma transl_external_arguments:
  extcall_arguments rs fr sg (ls ## (loc_arguments sg)).
Proof.
  unfold extcall_arguments. 
  apply transl_external_arguments_rec. 
  exact (Conventions.loc_arguments_acceptable sg).
  exact (Conventions.loc_arguments_bounded sg).
Qed.

End EXTERNAL_ARGUMENTS.

(** The proof of semantic preservation relies on simulation diagrams
  of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                  +|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  Matching between source and target states is defined by [match_states]
  below.  It implies:
- Agreement between, on the Linear side, the location sets [ls]
  and [parent_locset s] of the current function and its caller,
  and on the Mach side the register set [rs], the frame [fr]
  and the caller's frame [parent_frame ts].
- Inclusion between the Linear code [c] and the code of the
  function [f] being executed.
- Well-typedness of [f].
*)

Inductive match_stacks: list Linear.stackframe -> list Machabstr.stackframe -> Prop :=
  | match_stacks_nil:
      match_stacks nil nil
  | match_stacks_cons:
      forall f sp c ls tf fr s ts,
      match_stacks s ts ->
      transf_function f = OK tf ->
      wt_function f ->
      agree_frame f ls fr (parent_frame ts) (parent_locset s) ->
      incl c (Linear.fn_code f) ->
      match_stacks
       (Linear.Stackframe f sp ls c :: s)
       (Machabstr.Stackframe tf (shift_sp tf sp) (transl_code (make_env (function_bounds f)) c) fr :: ts).

Inductive match_states: Linear.state -> Machabstr.state -> Prop :=
  | match_states_intro:
      forall s f sp c ls m ts tf rs fr
        (STACKS: match_stacks s ts)
        (TRANSL: transf_function f = OK tf)
        (WTF: wt_function f)
        (AG: agree f ls rs fr (parent_frame ts) (parent_locset s))
        (INCL: incl c (Linear.fn_code f)),
      match_states (Linear.State s f sp c ls m)
                   (Machabstr.State ts tf (shift_sp tf sp) (transl_code (make_env (function_bounds f)) c) rs fr m)
  | match_states_call:
      forall s f ls m ts tf rs
        (STACKS: match_stacks s ts)
        (TRANSL: transf_fundef f = OK tf)
        (WTF: wt_fundef f)
        (AG1: forall r, rs r = ls (R r))
        (AG2: forall ofs ty, 
                14 <= ofs -> 
                ofs + typesize ty <= size_arguments (Linear.funsig f) ->
                get_slot (parent_frame ts) ty (Int.signed (Int.repr (4 * ofs))) (ls (S (Outgoing ofs ty))))
        (AG3: agree_callee_save ls (parent_locset s)),
      match_states (Linear.Callstate s f ls m)
                   (Machabstr.Callstate ts tf rs m)
  | match_states_return:
      forall s ls m ts rs
        (STACKS: match_stacks s ts)
        (AG1: forall r, rs r = ls (R r))
        (AG2: agree_callee_save ls (parent_locset s)),
      match_states (Linear.Returnstate s ls m)
                   (Machabstr.Returnstate ts rs m).

Theorem transf_step_correct:
  forall s1 t s2, Linear.step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2', plus step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  assert (RED: forall f i c,
          transl_code (make_env (function_bounds f)) (i :: c) = 
          transl_instr (make_env (function_bounds f)) i
                       (transl_code (make_env (function_bounds f)) c)).
    intros. reflexivity.
  induction 1; intros;
  try inv MS;
  try rewrite RED;
  try (generalize (WTF _ (INCL _ (in_eq _ _))); intro WTI);
  try (generalize (function_is_within_bounds f WTF _ (INCL _ (in_eq _ _)));
       intro BOUND; simpl in BOUND);
  unfold transl_instr.
  (* Lgetstack *)
  inv WTI. destruct BOUND.
  exists (State ts tf (shift_sp tf sp) (transl_code (make_env (function_bounds f)) b)
             (rs0#r <- (rs (S sl))) fr m).
  split. destruct sl. 
  (* Lgetstack, local *)
  apply plus_one. eapply exec_Mgetstack'; eauto.
  apply get_slot_index. apply index_local_valid. auto. 
  eapply agree_size; eauto. reflexivity. 
  eapply agree_locals; eauto.
  (* Lgetstack, incoming *)
  apply plus_one; apply exec_Mgetparam.
  unfold offset_of_index. eapply agree_incoming; eauto.
  (* Lgetstack, outgoing *)
  apply plus_one; apply exec_Mgetstack'; eauto.
  apply get_slot_index. apply index_arg_valid. auto. 
  eapply agree_size; eauto. reflexivity. 
  eapply agree_outgoing; eauto.
  (* Lgetstack, common *)
  econstructor; eauto with coqlib. 
  apply agree_set_reg; auto.

  (* Lsetstack *)
  inv WTI. destruct sl.

  (* Lsetstack, local *)
  generalize (agree_set_local _ _ _ _ _ _ (rs0 r) _ _ AG BOUND).
  intros [fr' [SET AG']].
  econstructor; split.
  apply plus_one. eapply exec_Msetstack'; eauto.
  econstructor; eauto with coqlib.
  replace (rs (R r)) with (rs0 r). auto.
  symmetry. eapply agree_reg; eauto.
  (* Lsetstack, incoming *)
  contradiction.
  (* Lsetstack, outgoing *)
  generalize (agree_set_outgoing _ _ _ _ _ _ (rs0 r) _ _ AG BOUND).
  intros [fr' [SET AG']].
  econstructor; split.
  apply plus_one. eapply exec_Msetstack'; eauto.
  econstructor; eauto with coqlib.
  replace (rs (R r)) with (rs0 r). auto.
  symmetry. eapply agree_reg; eauto.

  (* Lop *)
  exists (State ts tf (shift_sp tf sp) (transl_code (make_env (function_bounds f)) b) (rs0#res <- v) fr m); split.
  apply plus_one. apply exec_Mop. 
  apply shift_eval_operation. auto. 
  change mreg with RegEq.t.
  rewrite (agree_eval_regs _ _ _ _ _ _ args AG). auto.
  econstructor; eauto with coqlib.
  apply agree_set_reg; auto.

  (* Lload *)
  exists (State ts tf (shift_sp tf sp) (transl_code (make_env (function_bounds f)) b) (rs0#dst <- v) fr m); split.
  apply plus_one; eapply exec_Mload; eauto.
  apply shift_eval_addressing; auto. 
  change mreg with RegEq.t.
  rewrite (agree_eval_regs _ _ _ _ _ _ args AG). eauto.
  econstructor; eauto with coqlib.
  apply agree_set_reg; auto.

  (* Lstore *)
  econstructor; split.
  apply plus_one; eapply exec_Mstore; eauto.
  apply shift_eval_addressing; eauto. 
  change mreg with RegEq.t.
  rewrite (agree_eval_regs _ _ _ _ _ _ args AG). eauto.
  rewrite (agree_eval_reg _ _ _ _ _ _ src AG). eauto.
  econstructor; eauto with coqlib.

  (* Lcall *) 
  assert (WTF': wt_fundef f'). eapply find_function_well_typed; eauto.
  exploit find_function_translated; eauto. 
  intros [tf' [FIND' TRANSL']].
  econstructor; split.
  apply plus_one; eapply exec_Mcall; eauto.
  econstructor; eauto. 
  econstructor; eauto with coqlib.
  exists rs0; auto.
  intro. symmetry. eapply agree_reg; eauto.
  intros. 
  assert (slot_within_bounds f (function_bounds f) (Outgoing ofs ty)).
  red. simpl. omega. 
  change (4 * ofs) with (offset_of_index (make_env (function_bounds f)) (FI_arg ofs ty)).
  rewrite (offset_of_index_no_overflow f tf); auto. 
  apply get_slot_index. apply index_arg_valid. auto. 
  eapply agree_size; eauto. reflexivity. 
  eapply agree_outgoing; eauto.
  simpl. red; auto.

  (* Ltailcall *) 
  assert (WTF': wt_fundef f'). eapply find_function_well_typed; eauto.
  generalize (find_function_translated _ _ _ _ _ _ _ _ AG H). 
  intros [tf' [FIND' TRANSL']].
  generalize (restore_callee_save_correct ts _ _ TRANSL
               (shift_sp tf (Vptr stk Int.zero)) 
               (Mtailcall (Linear.funsig f') ros :: transl_code (make_env (function_bounds f)) b)
               _ m _ _ _ AG).
  intros [rs2 [A [B C]]].
  assert (FIND'': find_function tge ros rs2 = Some tf').
    rewrite <- FIND'. destruct ros; simpl; auto.
    inv WTI. rewrite C. auto. 
    simpl. intuition congruence. simpl. intuition congruence. 
  econstructor; split.
  eapply plus_right. eexact A. 
  simpl shift_sp. eapply exec_Mtailcall; eauto. traceEq.
  econstructor; eauto. 
  intros; symmetry; eapply agree_return_regs; eauto.
  intros. inv WTI. rewrite tailcall_possible_size in H4.
  rewrite H4 in H1. elimtype False. generalize (typesize_pos ty). omega.
  apply agree_callee_save_return_regs. 
 
  (* Lalloc *)
  exists (State ts tf (shift_sp tf sp) (transl_code (make_env (function_bounds f)) b)
                          (rs0#loc_alloc_result <- (Vptr blk Int.zero)) fr m'); split.
  apply plus_one; eapply exec_Malloc; eauto.
  rewrite (agree_eval_reg _ _ _ _ _ _ loc_alloc_argument AG). auto.
  econstructor; eauto with coqlib.
  apply agree_set_reg; auto.
  red. simpl. generalize (max_over_regs_of_funct_pos f int_callee_save). omega.

  (* Llabel *)
  econstructor; split.
  apply plus_one; apply exec_Mlabel.
  econstructor; eauto with coqlib.

  (* Lgoto *)
  econstructor; split.
  apply plus_one; apply exec_Mgoto.
  apply transl_find_label; eauto.
  econstructor; eauto. 
  eapply find_label_incl; eauto.

  (* Lcond, true *)
  econstructor; split.
  apply plus_one; apply exec_Mcond_true.
  rewrite <- (agree_eval_regs _ _ _ _ _ _ args AG) in H; eauto.
  apply transl_find_label; eauto.
  econstructor; eauto.
  eapply find_label_incl; eauto.

  (* Lcond, false *)
  econstructor; split.
  apply plus_one; apply exec_Mcond_false.
  rewrite <- (agree_eval_regs _ _ _ _ _ _ args AG) in H; auto.
  econstructor; eauto with coqlib.

  (* Lreturn *)
  exploit restore_callee_save_correct; eauto.
  intros [ls' [A [B C]]].
  econstructor; split.
  eapply plus_right. eauto. 
  simpl shift_sp. econstructor; eauto. traceEq.
  econstructor; eauto. 
  intros. symmetry. eapply agree_return_regs; eauto.
  apply agree_callee_save_return_regs.  

  (* internal function *)
  generalize TRANSL; clear TRANSL. 
  unfold transf_fundef, transf_partial_fundef.
  caseEq (transf_function f); simpl; try congruence.
  intros tfn TRANSL EQ. inversion EQ; clear EQ; subst tf.
  inversion WTF as [|f' WTFN]. subst f'.
  set (sp := Vptr stk Int.zero) in *.
  set (tsp := shift_sp tfn sp).
  set (fe := make_env (function_bounds f)).
  assert (fr_low (init_frame tfn) = - fe.(fe_size)).
    simpl fr_low. rewrite (unfold_transf_function _ _ TRANSL).
    reflexivity.
  assert (UNDEF: forall idx, index_valid f idx -> index_val f idx (init_frame tfn) = Vundef).
    intros.
    assert (get_slot (init_frame tfn) (type_of_index idx) (offset_of_index fe idx) Vundef).
    generalize (offset_of_index_valid _ _ H1). fold fe. intros [XX YY].
    apply slot_gi; auto. omega. 
    inv H2; auto.
  exploit save_callee_save_correct; eauto. 
  intros [fr [EXP AG]].
  econstructor; split.
  eapply plus_left.
  eapply exec_function_internal; eauto.
  rewrite (unfold_transf_function f tfn TRANSL); simpl; eexact H. 
  replace (Mach.fn_code tfn) with
          (transl_body f (make_env (function_bounds f))).    
  replace (Vptr stk (Int.repr (- fn_framesize tfn))) with tsp.
  unfold transl_body. eexact EXP.
  unfold tsp, shift_sp, sp. unfold Val.add. 
  rewrite Int.add_commut. rewrite Int.add_zero. auto.
  rewrite (unfold_transf_function f tfn TRANSL). simpl. auto.
  traceEq.
  unfold tsp. econstructor; eauto with coqlib.
  eapply agree_callee_save_agree; eauto. 

  (* external function *)
  simpl in TRANSL. inversion TRANSL; subst tf.
  inversion WTF. subst ef0.
  exploit transl_external_arguments; eauto. intro EXTARGS.
  econstructor; split.
  apply plus_one. eapply exec_function_external; eauto.
  econstructor; eauto.
  intros. unfold Regmap.set. case (RegEq.eq r (loc_result (ef_sig ef))); intro.
  rewrite e. rewrite Locmap.gss; auto. rewrite Locmap.gso; auto.
  red; auto.
  apply agree_callee_save_set_result; auto.

  (* return *)
  inv STACKS. 
  econstructor; split.
  apply plus_one. apply exec_return. 
  econstructor; eauto. simpl in AG2.  
  eapply agree_frame_agree; eauto.
Qed.

Lemma transf_initial_states:
  forall st1, Linear.initial_state prog st1 ->
  exists st2, Machabstr.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  econstructor; split.
  econstructor. 
  rewrite (transform_partial_program_main _ _ TRANSF). 
  rewrite symbols_preserved. eauto.
  eauto. 
  rewrite (Genv.init_mem_transf_partial _ _ TRANSF).
  econstructor; eauto. constructor. 
  eapply Genv.find_funct_ptr_prop; eauto.
  intros. 
  replace (size_arguments (Linear.funsig f)) with 14 in H5.
  elimtype False. generalize (typesize_pos ty). omega.
  rewrite H2; auto.
  simpl; red; auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> Linear.final_state st1 r -> Machabstr.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. econstructor. rewrite AG1; auto.
Qed.

Theorem transf_program_correct:
  forall (beh: program_behavior),
  Linear.exec_program prog beh -> Machabstr.exec_program tprog beh.
Proof.
  unfold Linear.exec_program, Machabstr.exec_program; intros.
  eapply simulation_plus_preservation; eauto.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact transf_step_correct. 
Qed.

End PRESERVATION.
