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

(** This file proves semantic preservation for the [Stacking] pass. *)

Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Op.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require LTL.
Require Import Linear.
Require Import Lineartyping.
Require Import Mach.
Require Import Machsem.
Require Import Bounds.
Require Import Conventions.
Require Import Stacklayout.
Require Import Stacking.

(** * Properties of frame offsets *)

Lemma typesize_typesize:
  forall ty, AST.typesize ty = 4 * Locations.typesize ty.
Proof.
  destruct ty; auto.
Qed.

Remark size_type_chunk:
  forall ty, size_chunk (chunk_of_type ty) = AST.typesize ty.
Proof.
  destruct ty; reflexivity.
Qed.

Section PRESERVATION.

Variable prog: Linear.program.
Variable tprog: Mach.program.
Hypothesis TRANSF: transf_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.


Section FRAME_PROPERTIES.

Variable f: Linear.function.
Let b := function_bounds f.
Let fe := make_env b.
Variable tf: Mach.function.
Hypothesis TRANSF_F: transf_function f = OK tf.

Lemma unfold_transf_function:
  tf = Mach.mkfunction
         f.(Linear.fn_sig)
         (transl_body f fe)
         fe.(fe_size)
         (Int.repr fe.(fe_ofs_link))
         (Int.repr fe.(fe_ofs_retaddr)).
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (zlt Int.max_unsigned (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros. unfold fe. unfold b. congruence.
Qed.

Lemma size_no_overflow: fe.(fe_size) <= Int.max_unsigned.
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (zlt Int.max_unsigned (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros. unfold fe. unfold b. omega.
Qed.

Remark bound_stack_data_stacksize:
  f.(Linear.fn_stacksize) <= b.(bound_stack_data).
Proof.
  unfold b, function_bounds, bound_stack_data. apply Zmax1.
Qed.  

(** A frame index is valid if it lies within the resource bounds
  of the current function. *)

Definition index_valid (idx: frame_index) :=
  match idx with
  | FI_link => True
  | FI_retaddr => True
  | FI_local x Tint => 0 <= x < b.(bound_int_local)
  | FI_local x Tfloat => 0 <= x < b.(bound_float_local)
  | FI_arg x ty => 0 <= x /\ x + typesize ty <= b.(bound_outgoing)
  | FI_saved_int x => 0 <= x < b.(bound_int_callee_save)
  | FI_saved_float x => 0 <= x < b.(bound_float_callee_save)
  end.

Definition type_of_index (idx: frame_index) :=
  match idx with
  | FI_link => Tint
  | FI_retaddr => Tint
  | FI_local x ty => ty
  | FI_arg x ty => ty
  | FI_saved_int x => Tint
  | FI_saved_float x => Tfloat
  end.

(** Non-overlap between the memory areas corresponding to two
  frame indices. *)

Definition index_diff (idx1 idx2: frame_index) : Prop :=
  match idx1, idx2 with
  | FI_link, FI_link => False
  | FI_retaddr, FI_retaddr => False
  | FI_local x1 ty1, FI_local x2 ty2 =>
      x1 <> x2 \/ ty1 <> ty2
  | FI_arg x1 ty1, FI_arg x2 ty2 =>
      x1 + typesize ty1 <= x2 \/ x2 + typesize ty2 <= x1
  | FI_saved_int x1, FI_saved_int x2 => x1 <> x2
  | FI_saved_float x1, FI_saved_float x2 => x1 <> x2
  | _, _ => True
  end.

Lemma index_diff_sym:
  forall idx1 idx2, index_diff idx1 idx2 -> index_diff idx2 idx1.
Proof.
  unfold index_diff; intros. 
  destruct idx1; destruct idx2; intuition.
Qed.

Ltac AddPosProps :=
  generalize (bound_int_local_pos b); intro;
  generalize (bound_float_local_pos b); intro;
  generalize (bound_int_callee_save_pos b); intro;
  generalize (bound_float_callee_save_pos b); intro;
  generalize (bound_outgoing_pos b); intro;
  generalize (bound_stack_data_pos b); intro.

Lemma size_pos: 0 <= fe.(fe_size).
Proof.
  generalize (frame_env_separated b). intuition.
  AddPosProps.
  unfold fe. omega.
Qed.

Opaque function_bounds.

Lemma offset_of_index_disj:
  forall idx1 idx2,
  index_valid idx1 -> index_valid idx2 ->
  index_diff idx1 idx2 ->
  offset_of_index fe idx1 + AST.typesize (type_of_index idx1) <= offset_of_index fe idx2 \/
  offset_of_index fe idx2 + AST.typesize (type_of_index idx2) <= offset_of_index fe idx1.
Proof.
  intros idx1 idx2 V1 V2 DIFF.
  generalize (frame_env_separated b). intuition. fold fe in H.
  AddPosProps.
  destruct idx1; destruct idx2;
  try (destruct t); try (destruct t0);
  unfold offset_of_index, type_of_index, AST.typesize;
  simpl in V1; simpl in V2; simpl in DIFF;
  try omega.
  assert (z <> z0). intuition auto. omega.
  assert (z <> z0). intuition auto. omega.
Qed.

Lemma offset_of_index_disj_stack_data_1:
  forall idx,
  index_valid idx ->
  offset_of_index fe idx + AST.typesize (type_of_index idx) <= fe.(fe_stack_data)
  \/ fe.(fe_stack_data) + b.(bound_stack_data) <= offset_of_index fe idx.
Proof.
  intros idx V.
  generalize (frame_env_separated b). intuition. fold fe in H.
  AddPosProps.
  destruct idx; try (destruct t);
  unfold offset_of_index, type_of_index, AST.typesize;
  simpl in V;
  omega.
Qed.

Lemma offset_of_index_disj_stack_data_2:
  forall idx,
  index_valid idx ->
  offset_of_index fe idx + AST.typesize (type_of_index idx) <= fe.(fe_stack_data)
  \/ fe.(fe_stack_data) + f.(Linear.fn_stacksize) <= offset_of_index fe idx.
Proof.
  intros. 
  exploit offset_of_index_disj_stack_data_1; eauto.
  generalize bound_stack_data_stacksize. 
  omega.
Qed.

(** Alignment properties *)

Remark aligned_4_4x: forall x, (4 | 4 * x).
Proof. intro. exists x; ring. Qed.

Remark aligned_4_8x: forall x, (4 | 8 * x).
Proof. intro. exists (x * 2); ring. Qed.

Remark aligned_8_4:
  forall x, (8 | x) -> (4 | x).
Proof. intros. apply Zdivides_trans with 8; auto. exists 2; auto. Qed.

Hint Resolve Zdivide_0 Zdivide_refl Zdivide_plus_r 
             aligned_4_4x aligned_4_8x aligned_8_4: align_4.
Hint Extern 4 (?X | ?Y) => (exists (Y/X); reflexivity) : align_4.

Lemma offset_of_index_aligned:
  forall idx, (4 | offset_of_index fe idx).
Proof.
  intros.
  generalize (frame_env_aligned b). intuition. fold fe in H. intuition.
  destruct idx; try (destruct t);
  unfold offset_of_index, type_of_index, AST.typesize;
  auto with align_4.
Qed.

Lemma fe_stack_data_aligned:
  (8 | fe_stack_data fe).
Proof.
  intros.
  generalize (frame_env_aligned b). intuition. fold fe in H. intuition.
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
  0 <= offset_of_index fe idx /\
  offset_of_index fe idx + AST.typesize (type_of_index idx) <= fe.(fe_size).
Proof.
  intros idx V.
  generalize (frame_env_separated b). intros [A B]. fold fe in A. fold fe in B.
  AddPosProps.
  destruct idx; try (destruct t);
  unfold offset_of_index, type_of_index, AST.typesize;
  simpl in V;
  omega.
Qed.

(** The image of the Linear stack data block lies within the bounds of the frame. *)

Lemma stack_data_offset_valid:
  0 <= fe.(fe_stack_data) /\ fe.(fe_stack_data) + b.(bound_stack_data) <= fe.(fe_size).
Proof.
  generalize (frame_env_separated b). intros [A B]. fold fe in A. fold fe in B.
  AddPosProps.
  omega.
Qed.

(** Offsets for valid index are representable as signed machine integers
  without loss of precision. *)

Lemma offset_of_index_no_overflow:
  forall idx,
  index_valid idx ->
  Int.unsigned (Int.repr (offset_of_index fe idx)) = offset_of_index fe idx.
Proof.
  intros.
  generalize (offset_of_index_valid idx H). intros [A B].
  apply Int.unsigned_repr.
  generalize (AST.typesize_pos (type_of_index idx)).
  generalize size_no_overflow. 
  omega.
Qed.

(** Likewise, for offsets within the Linear stack slot, after shifting. *)

Lemma shifted_stack_offset_no_overflow:
  forall ofs,
  0 <= Int.unsigned ofs < Linear.fn_stacksize f ->
  Int.unsigned (Int.add ofs (Int.repr fe.(fe_stack_data))) 
  = Int.unsigned ofs + fe.(fe_stack_data).
Proof.
  intros. unfold Int.add.
  generalize size_no_overflow stack_data_offset_valid bound_stack_data_stacksize; intros.
  AddPosProps.
  replace (Int.unsigned (Int.repr (fe_stack_data fe))) with (fe_stack_data fe).
  apply Int.unsigned_repr. omega. 
  symmetry. apply Int.unsigned_repr. omega.
Qed.

(** * Contents of frame slots *)

Inductive index_contains (m: mem) (sp: block) (idx: frame_index) (v: val) : Prop :=
  | index_contains_intro:
      index_valid idx ->
      Mem.load (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) = Some v ->
      index_contains m sp idx v.

Lemma index_contains_load_stack:
  forall m sp idx v,
  index_contains m sp idx v ->
  load_stack m (Vptr sp Int.zero) (type_of_index idx)
              (Int.repr (offset_of_index fe idx)) = Some v.
Proof.
  intros. inv H. 
  unfold load_stack, Mem.loadv, Val.add. rewrite Int.add_commut. rewrite Int.add_zero.
  rewrite offset_of_index_no_overflow; auto.
Qed.

(** Good variable properties for [index_contains] *)

Lemma gss_index_contains_base:
  forall idx m m' sp v,
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  index_valid idx ->
  exists v',
     index_contains m' sp idx v'
  /\ decode_encode_val v (chunk_of_type (type_of_index idx)) (chunk_of_type (type_of_index idx)) v'.
Proof.
  intros. 
  exploit Mem.load_store_similar. eauto. reflexivity. omega. 
  intros [v' [A B]].
  exists v'; split; auto. constructor; auto.
Qed.

Lemma gss_index_contains:
  forall idx m m' sp v,
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  index_valid idx ->
  Val.has_type v (type_of_index idx) ->
  index_contains m' sp idx v.
Proof.
  intros. exploit gss_index_contains_base; eauto. intros [v' [A B]].
  assert (v' = v).
    destruct v; destruct (type_of_index idx); simpl in *; intuition congruence.
  subst v'. auto.
Qed.

Lemma gso_index_contains:
  forall idx m m' sp v idx' v',
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  index_valid idx ->
  index_contains m sp idx' v' ->
  index_diff idx idx' ->
  index_contains m' sp idx' v'.
Proof.
  intros. inv H1. constructor; auto. 
  rewrite <- H4. eapply Mem.load_store_other; eauto.
  right. repeat rewrite size_type_chunk. 
  apply offset_of_index_disj; auto. apply index_diff_sym; auto.
Qed.

Lemma store_other_index_contains:
  forall chunk m blk ofs v' m' sp idx v,
  Mem.store chunk m blk ofs v' = Some m' ->
  blk <> sp \/
    (fe.(fe_stack_data) <= ofs /\ ofs + size_chunk chunk <= fe.(fe_stack_data) + f.(Linear.fn_stacksize)) ->
  index_contains m sp idx v ->
  index_contains m' sp idx v.
Proof.
  intros. inv H1. constructor; auto. rewrite <- H3. 
  eapply Mem.load_store_other; eauto. 
  destruct H0. auto. right. 
  exploit offset_of_index_disj_stack_data_2; eauto. intros.
  rewrite size_type_chunk.
  omega.
Qed.

Definition frame_perm_freeable (m: mem) (sp: block): Prop :=
  forall ofs,
  0 <= ofs < fe.(fe_size) ->
  ofs < fe.(fe_stack_data) \/ fe.(fe_stack_data) + f.(Linear.fn_stacksize) <= ofs ->
  Mem.perm m sp ofs Cur Freeable.

Lemma offset_of_index_perm:
  forall m sp idx,
  index_valid idx ->
  frame_perm_freeable m sp ->
  Mem.range_perm m sp (offset_of_index fe idx) (offset_of_index fe idx + AST.typesize (type_of_index idx)) Cur Freeable.
Proof.
  intros.
  exploit offset_of_index_valid; eauto. intros [A B].
  exploit offset_of_index_disj_stack_data_2; eauto. intros.
  red; intros. apply H0. omega. omega.
Qed.

Lemma store_index_succeeds:
  forall m sp idx v,
  index_valid idx ->
  frame_perm_freeable m sp ->
  exists m',
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m'.
Proof.
  intros.
  destruct (Mem.valid_access_store m (chunk_of_type (type_of_index idx)) sp (offset_of_index fe idx) v) as [m' ST].
  constructor.
  rewrite size_type_chunk. 
  apply Mem.range_perm_implies with Freeable; auto with mem.
  apply offset_of_index_perm; auto.
  replace (align_chunk (chunk_of_type (type_of_index idx))) with 4.
  apply offset_of_index_aligned; auto.
  destruct (type_of_index idx); auto.
  exists m'; auto.
Qed.

Lemma store_stack_succeeds:
  forall m sp idx v m',
  index_valid idx ->
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  store_stack m (Vptr sp Int.zero) (type_of_index idx) (Int.repr (offset_of_index fe idx)) v = Some m'.
Proof.
  intros. unfold store_stack, Mem.storev, Val.add.
  rewrite Int.add_commut. rewrite Int.add_zero.
  rewrite offset_of_index_no_overflow; auto.
Qed.

(** A variant of [index_contains], up to a memory injection. *)

Definition index_contains_inj (j: meminj) (m: mem) (sp: block) (idx: frame_index) (v: val) : Prop :=
  exists v', index_contains m sp idx v' /\ val_inject j v v'.

Lemma gss_index_contains_inj:
  forall j idx m m' sp v v',
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v' = Some m' ->
  index_valid idx ->
  Val.has_type v (type_of_index idx) ->
  val_inject j v v' ->
  index_contains_inj j m' sp idx v.
Proof.
  intros. exploit gss_index_contains_base; eauto. intros [v'' [A B]].
  exists v''; split; auto.
  inv H2; destruct (type_of_index idx); simpl in *; try contradiction; subst; auto.
  econstructor; eauto.
Qed.

Lemma gso_index_contains_inj:
  forall j idx m m' sp v idx' v',
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  index_valid idx ->
  index_contains_inj j m sp idx' v' ->
  index_diff idx idx' ->
  index_contains_inj j m' sp idx' v'.
Proof.
  intros. destruct H1 as [v'' [A B]]. exists v''; split; auto.
  eapply gso_index_contains; eauto.
Qed.

Lemma store_other_index_contains_inj:
  forall j chunk m b ofs v' m' sp idx v,
  Mem.store chunk m b ofs v' = Some m' ->
  b <> sp \/
    (fe.(fe_stack_data) <= ofs /\ ofs + size_chunk chunk <= fe.(fe_stack_data) + f.(Linear.fn_stacksize)) ->
  index_contains_inj j m sp idx v ->
  index_contains_inj j m' sp idx v.
Proof.
  intros. destruct H1 as [v'' [A B]]. exists v''; split; auto.
  eapply store_other_index_contains; eauto.
Qed.

Lemma index_contains_inj_incr:
  forall j m sp idx v j',
  index_contains_inj j m sp idx v ->
  inject_incr j j' ->
  index_contains_inj j' m sp idx v.
Proof.
  intros. destruct H as [v'' [A B]]. exists v''; split; auto. eauto. 
Qed.

Lemma index_contains_inj_undef:
  forall j m sp idx,
  index_valid idx ->
  frame_perm_freeable m sp ->
  index_contains_inj j m sp idx Vundef.
Proof.
  intros. 
  exploit (Mem.valid_access_load m (chunk_of_type (type_of_index idx)) sp (offset_of_index fe idx)).
  constructor. 
  rewrite size_type_chunk.
  apply Mem.range_perm_implies with Freeable; auto with mem.
  apply offset_of_index_perm; auto. 
  replace (align_chunk (chunk_of_type (type_of_index idx))) with 4. 
  apply offset_of_index_aligned. destruct (type_of_index idx); auto.
  intros [v C]. 
  exists v; split; auto. constructor; auto. 
Qed.

Hint Resolve store_other_index_contains_inj index_contains_inj_incr: stacking.

(** * Agreement between location sets and Mach states *)

(** Agreement with Mach register states *)

Definition agree_regs (j: meminj) (ls: locset) (rs: regset) : Prop :=
  forall r, val_inject j (ls (R r)) (rs r).

(** Agreement over data stored in memory *)

Record agree_frame (j: meminj) (ls ls0: locset)
                   (m: mem) (sp: block)
                   (m': mem) (sp': block)
                   (parent retaddr: val) : Prop :=
  mk_agree_frame {

    (** Unused registers have the same value as in the caller *)
    agree_unused_reg:
       forall r, ~(mreg_within_bounds b r) -> ls (R r) = ls0 (R r);

    (** Local and outgoing stack slots (on the Linear side) have
        the same values as the one loaded from the current Mach frame 
        at the corresponding offsets. *)
    agree_locals:
      forall ofs ty, 
      slot_within_bounds f b (Local ofs ty) ->
      index_contains_inj j m' sp' (FI_local ofs ty) (ls (S (Local ofs ty)));
    agree_outgoing:
      forall ofs ty, 
      slot_within_bounds f b (Outgoing ofs ty) ->
      index_contains_inj j m' sp' (FI_arg ofs ty) (ls (S (Outgoing ofs ty)));

    (** Incoming stack slots have the same value as the
        corresponding Outgoing stack slots in the caller *)
    agree_incoming:
       forall ofs ty, 
       In (S (Incoming ofs ty)) (loc_parameters f.(Linear.fn_sig)) ->
       ls (S (Incoming ofs ty)) = ls0 (S (Outgoing ofs ty));

    (** The back link and return address slots of the Mach frame contain
        the [parent] and [retaddr] values, respectively. *)
    agree_link:
      index_contains m' sp' FI_link parent;
    agree_retaddr:
      index_contains m' sp' FI_retaddr retaddr;

    (** The areas of the frame reserved for saving used callee-save
        registers always contain the values that those registers had
        in the caller. *)
    agree_saved_int:
      forall r,
      In r int_callee_save_regs ->
      index_int_callee_save r < b.(bound_int_callee_save) ->
      index_contains_inj j m' sp' (FI_saved_int (index_int_callee_save r)) (ls0 (R r));
    agree_saved_float:
      forall r,
      In r float_callee_save_regs ->
      index_float_callee_save r < b.(bound_float_callee_save) ->
      index_contains_inj j m' sp' (FI_saved_float (index_float_callee_save r)) (ls0 (R r));

    (** Mapping between the Linear stack pointer and the Mach stack pointer *)
    agree_inj:
      j sp = Some(sp', fe.(fe_stack_data));
    agree_inj_unique:
      forall b delta, j b = Some(sp', delta) -> b = sp /\ delta = fe.(fe_stack_data);

    (** The Linear and Mach stack pointers are valid *)
    agree_valid_linear:
      Mem.valid_block m sp;
    agree_valid_mach:
      Mem.valid_block m' sp';

    (** Bounds of the Linear stack data block *)
    agree_bounds:
      forall ofs p, Mem.perm m sp ofs Max p -> 0 <= ofs < f.(Linear.fn_stacksize);

    (** Permissions on the frame part of the Mach stack block *)
    agree_perm:
      frame_perm_freeable m' sp';

    (** Current locset is well-typed *)
    agree_wt_ls:
      wt_locset ls
  }.

Hint Resolve agree_unused_reg agree_locals agree_outgoing agree_incoming
             agree_link agree_retaddr agree_saved_int agree_saved_float
             agree_valid_linear agree_valid_mach agree_perm
             agree_wt_ls: stacking.

(** Auxiliary predicate used at call points *)

Definition agree_callee_save (ls ls0: locset) : Prop :=
  forall l,
  match l with
  | R r => In r int_callee_save_regs \/ In r float_callee_save_regs
  | S s => True
  end ->
  ls l = ls0 l.

(** ** Properties of [agree_regs]. *)

(** Values of registers *)

Lemma agree_reg:
  forall j ls rs r,
  agree_regs j ls rs -> val_inject j (ls (R r)) (rs r).
Proof.
  intros. auto. 
Qed.

Lemma agree_reglist:
  forall j ls rs rl,
  agree_regs j ls rs -> val_list_inject j (reglist ls rl) (rs##rl).
Proof.
  induction rl; simpl; intros.
  auto. constructor. eauto with stacking. auto. 
Qed.

Hint Resolve agree_reg agree_reglist: stacking.

(** Preservation under assignments of machine registers. *)

Lemma agree_regs_set_reg:
  forall j ls rs r v v',
  agree_regs j ls rs ->
  val_inject j v v' ->
  agree_regs j (Locmap.set (R r) v ls) (Regmap.set r v' rs).
Proof.
  intros; red; intros. 
  unfold Regmap.set. destruct (RegEq.eq r0 r). subst r0. 
  rewrite Locmap.gss; auto.
  rewrite Locmap.gso; auto. red. auto.
Qed.

Lemma agree_regs_exten:
  forall j ls rs ls' rs',
  agree_regs j ls rs ->
  (forall r, ls' (R r) = Vundef \/ ls' (R r) = ls (R r) /\ rs' r = rs r) ->
  agree_regs j ls' rs'.
Proof.
  intros; red; intros.
  destruct (H0 r) as [A | [A B]]. 
  rewrite A. constructor. 
  rewrite A; rewrite B; auto.
Qed.

Lemma agree_regs_undef_list:
  forall j rl ls rs,
  agree_regs j ls rs ->
  agree_regs j (Locmap.undef (List.map R rl) ls) (undef_regs rl rs).
Proof.
  induction rl; simpl; intros.
  auto. 
  apply IHrl. apply agree_regs_set_reg; auto. 
Qed.

Lemma agree_regs_undef_temps:
  forall j ls rs,
  agree_regs j ls rs ->
  agree_regs j (LTL.undef_temps ls) (undef_temps rs).
Proof.
  unfold LTL.undef_temps, undef_temps, temporaries.
  intros; apply agree_regs_undef_list; auto.
Qed.

Lemma agree_regs_undef_setstack:
  forall j ls rs,
  agree_regs j ls rs ->
  agree_regs j (Linear.undef_setstack ls) (undef_setstack rs).
Proof.
  intros. unfold Linear.undef_setstack, undef_setstack, destroyed_at_move.
  apply agree_regs_undef_list; auto.
Qed.

Lemma agree_regs_undef_op:
  forall op j ls rs,
  agree_regs j ls rs ->
  agree_regs j (Linear.undef_op op ls) (undef_op (transl_op fe op) rs).
Proof.
  intros. generalize (agree_regs_undef_temps _ _ _ H); intro A.
Opaque destroyed_at_move_regs.
  destruct op; auto; simpl; apply agree_regs_undef_setstack; auto.
Qed.

(** Preservation under assignment of stack slot *)

Lemma agree_regs_set_slot:
  forall j ls rs ss v,
  agree_regs j ls rs ->
  agree_regs j (Locmap.set (S ss) v ls) rs.
Proof.
  intros; red; intros. rewrite Locmap.gso; auto. red. destruct ss; auto.
Qed.

(** Preservation by increasing memory injections *)

Lemma agree_regs_inject_incr:
  forall j ls rs j',
  agree_regs j ls rs -> inject_incr j j' -> agree_regs j' ls rs.
Proof.
  intros; red; intros; eauto with stacking.
Qed.

(** Preservation at function entry. *)

Lemma agree_regs_call_regs:
  forall j ls rs,
  agree_regs j ls rs ->
  agree_regs j (call_regs ls) (undef_temps rs).
Proof.
  intros. 
  assert (agree_regs j (LTL.undef_temps ls) (undef_temps rs)).
    apply agree_regs_undef_temps; auto.
  unfold call_regs; intros; red; intros.
  destruct (in_dec Loc.eq (R r) temporaries).
  auto.
  generalize (H0 r). unfold LTL.undef_temps. rewrite Locmap.guo. auto.
  apply Loc.reg_notin; auto.
Qed.

(** ** Properties of [agree_frame] *)

(** Preservation under assignment of machine register. *)

Lemma agree_frame_set_reg:
  forall j ls ls0 m sp m' sp' parent ra r v,
  agree_frame j ls ls0 m sp m' sp' parent ra ->
  mreg_within_bounds b r ->
   Val.has_type v (Loc.type (R r)) ->
  agree_frame j (Locmap.set (R r) v ls) ls0 m sp m' sp' parent ra.
Proof.
  intros. inv H; constructor; auto; intros.
  rewrite Locmap.gso. auto. red. intuition congruence.
  rewrite Locmap.gso; auto. red; auto.
  rewrite Locmap.gso; auto. red; auto.
  rewrite Locmap.gso; auto. red; auto.
  apply wt_setloc; auto.
Qed.

Remark temporary_within_bounds:
  forall r, In (R r) temporaries -> mreg_within_bounds b r.
Proof.
  intros; red. destruct (mreg_type r). 
  destruct (zlt (index_int_callee_save r) 0). 
  generalize (bound_int_callee_save_pos b). omega.
  exploit int_callee_save_not_destroyed. 
  left. eauto with coqlib. apply index_int_callee_save_pos2; auto.
  contradiction.
  destruct (zlt (index_float_callee_save r) 0). 
  generalize (bound_float_callee_save_pos b). omega.
  exploit float_callee_save_not_destroyed. 
  left. eauto with coqlib. apply index_float_callee_save_pos2; auto.
  contradiction.
Qed.

Lemma agree_frame_undef_locs:
  forall j ls0 m sp m' sp' parent ra regs ls,
  agree_frame j ls ls0 m sp m' sp' parent ra ->
  incl (List.map R regs) temporaries ->
  agree_frame j (Locmap.undef (List.map R regs) ls) ls0 m sp m' sp' parent ra.
Proof.
  induction regs; simpl; intros.
  auto.
  apply IHregs; eauto with coqlib.
  apply agree_frame_set_reg; auto. 
  apply temporary_within_bounds; eauto with coqlib.
  red; auto.
Qed.

Lemma agree_frame_undef_temps:
  forall j ls ls0 m sp m' sp' parent ra,
  agree_frame j ls ls0 m sp m' sp' parent ra ->
  agree_frame j (LTL.undef_temps ls) ls0 m sp m' sp' parent ra.
Proof.
  intros. unfold temporaries. apply agree_frame_undef_locs; auto. apply incl_refl. 
Qed.

Lemma agree_frame_undef_setstack:
  forall j ls ls0 m sp m' sp' parent ra,
  agree_frame j ls ls0 m sp m' sp' parent ra ->
  agree_frame j (Linear.undef_setstack ls) ls0 m sp m' sp' parent ra.
Proof.
  intros. unfold Linear.undef_setstack, destroyed_at_move. 
  apply agree_frame_undef_locs; auto.
  red; simpl; tauto.
Qed.

Lemma agree_frame_undef_op:
  forall j ls ls0 m sp m' sp' parent ra op,
  agree_frame j ls ls0 m sp m' sp' parent ra ->
  agree_frame j (Linear.undef_op op ls) ls0 m sp m' sp' parent ra.
Proof.
  intros. 
  exploit agree_frame_undef_temps; eauto.
  destruct op; simpl; auto; intros; apply agree_frame_undef_setstack; auto. 
Qed.

(** Preservation by assignment to local slot *)

Lemma agree_frame_set_local:
  forall j ls ls0 m sp m' sp' parent retaddr ofs ty v v' m'',
  agree_frame j ls ls0 m sp m' sp' parent retaddr ->
  slot_within_bounds f b (Local ofs ty) ->
  val_inject j v v' ->
  Val.has_type v ty ->
  Mem.store (chunk_of_type ty) m' sp' (offset_of_index fe (FI_local ofs ty)) v' = Some m'' ->
  agree_frame j (Locmap.set (S (Local ofs ty)) v ls) ls0 m sp m'' sp' parent retaddr.
Proof.
  intros. inv H. 
  change (chunk_of_type ty) with (chunk_of_type (type_of_index (FI_local ofs ty))) in H3.
  constructor; auto; intros.
(* unused *)
  rewrite Locmap.gso; auto. red; auto.
(* local *)
  unfold Locmap.set. simpl. destruct (Loc.eq (S (Local ofs ty)) (S (Local ofs0 ty0))).
  inv e. eapply gss_index_contains_inj; eauto. 
  eapply gso_index_contains_inj. eauto. simpl; auto. eauto with stacking.
  simpl. destruct (zeq ofs ofs0); auto. destruct (typ_eq ty ty0); auto. congruence.
(* outgoing *)
  rewrite Locmap.gso. eapply gso_index_contains_inj; eauto with stacking.
  simpl; auto. red; auto.
(* incoming *)
  rewrite Locmap.gso; auto. red; auto.
(* parent *)
  eapply gso_index_contains; eauto. red; auto.
(* retaddr *)
  eapply gso_index_contains; eauto. red; auto.
(* int callee save *)
  eapply gso_index_contains_inj; eauto. simpl; auto. 
(* float callee save *)
  eapply gso_index_contains_inj; eauto. simpl; auto.
(* valid *)
  eauto with mem.
(* perm *)
  red; intros. eapply Mem.perm_store_1; eauto.
(* wt *)
  apply wt_setloc; auto. 
Qed.

(** Preservation by assignment to outgoing slot *)

Lemma agree_frame_set_outgoing:
  forall j ls ls0 m sp m' sp' parent retaddr ofs ty v v' m'',
  agree_frame j ls ls0 m sp m' sp' parent retaddr ->
  slot_within_bounds f b (Outgoing ofs ty) ->
  val_inject j v v' ->
  Val.has_type v ty ->
  Mem.store (chunk_of_type ty) m' sp' (offset_of_index fe (FI_arg ofs ty)) v' = Some m'' ->
  agree_frame j (Locmap.set (S (Outgoing ofs ty)) v ls) ls0 m sp m'' sp' parent retaddr.
Proof.
  intros. inv H. 
  change (chunk_of_type ty) with (chunk_of_type (type_of_index (FI_arg ofs ty))) in H3.
  constructor; auto; intros.
(* unused *)
  rewrite Locmap.gso; auto. red; auto.
(* local *)
  rewrite Locmap.gso. eapply gso_index_contains_inj; eauto. simpl; auto. red; auto.
(* outgoing *)
  unfold Locmap.set. simpl. destruct (Loc.eq (S (Outgoing ofs ty)) (S (Outgoing ofs0 ty0))).
  inv e. eapply gss_index_contains_inj; eauto.
  case_eq (Loc.overlap_aux ty ofs ofs0 || Loc.overlap_aux ty0 ofs0 ofs); intros.
  apply index_contains_inj_undef. auto.
  red; intros. eapply Mem.perm_store_1; eauto.
  eapply gso_index_contains_inj; eauto.
  red. eapply Loc.overlap_aux_false_1; eauto.
(* incoming *)
  rewrite Locmap.gso; auto. red; auto.
(* parent *)
  eapply gso_index_contains; eauto with stacking. red; auto.
(* retaddr *)
  eapply gso_index_contains; eauto with stacking. red; auto.
(* int callee save *)
  eapply gso_index_contains_inj; eauto with stacking. simpl; auto. 
(* float callee save *)
  eapply gso_index_contains_inj; eauto with stacking. simpl; auto.
(* valid *)
  eauto with mem stacking.
(* perm *)
  red; intros. eapply Mem.perm_store_1; eauto.
(* wt *)
  apply wt_setloc; auto. 
Qed.

(** General invariance property with respect to memory changes. *)

Lemma agree_frame_invariant:
  forall j ls ls0 m sp m' sp' parent retaddr m1 m1',
  agree_frame j ls ls0 m sp m' sp' parent retaddr ->
  (Mem.valid_block m sp -> Mem.valid_block m1 sp) ->
  (forall ofs p, Mem.perm m1 sp ofs Max p -> Mem.perm m sp ofs Max p) ->
  (Mem.valid_block m' sp' -> Mem.valid_block m1' sp') ->
  (forall chunk ofs v,
     ofs + size_chunk chunk <= fe.(fe_stack_data) \/
     fe.(fe_stack_data) + f.(Linear.fn_stacksize) <= ofs ->
     Mem.load chunk m' sp' ofs = Some v ->
     Mem.load chunk m1' sp' ofs = Some v) ->
  (forall ofs k p,
     ofs < fe.(fe_stack_data) \/ fe.(fe_stack_data) + f.(Linear.fn_stacksize) <= ofs ->
     Mem.perm m' sp' ofs k p -> Mem.perm m1' sp' ofs k p) ->
  agree_frame j ls ls0 m1 sp m1' sp' parent retaddr.
Proof.
  intros.
  assert (IC: forall idx v,
              index_contains m' sp' idx v -> index_contains m1' sp' idx v).
    intros. inv H5.
    exploit offset_of_index_disj_stack_data_2; eauto. intros. 
    constructor; eauto. apply H3; auto. rewrite size_type_chunk; auto.
  assert (ICI: forall idx v,
              index_contains_inj j m' sp' idx v -> index_contains_inj j m1' sp' idx v).
    intros. destruct H5 as [v' [A B]]. exists v'; split; auto. 
  inv H; constructor; auto; intros.
  eauto.
  red; intros. apply H4; auto.
Qed.

(** A variant of the latter, for use with external calls *)

Lemma agree_frame_extcall_invariant:
  forall j ls ls0 m sp m' sp' parent retaddr m1 m1',
  agree_frame j ls ls0 m sp m' sp' parent retaddr ->
  (Mem.valid_block m sp -> Mem.valid_block m1 sp) ->
  (forall ofs p, Mem.perm m1 sp ofs Max p -> Mem.perm m sp ofs Max p) ->
  (Mem.valid_block m' sp' -> Mem.valid_block m1' sp') ->
  mem_unchanged_on (loc_out_of_reach j m) m' m1' ->
  agree_frame j ls ls0 m1 sp m1' sp' parent retaddr.
Proof.
  intros.
  assert (REACH: forall ofs,
     ofs < fe.(fe_stack_data) \/ fe.(fe_stack_data) + f.(Linear.fn_stacksize) <= ofs ->
    loc_out_of_reach j m sp' ofs).
  intros; red; intros. exploit agree_inj_unique; eauto. intros [EQ1 EQ2]; subst.
  red; intros. exploit agree_bounds; eauto. omega. 
  eapply agree_frame_invariant; eauto.
  intros. apply H3. intros. apply REACH. omega. auto. 
  intros. apply H3; auto. 
Qed.

(** Preservation by parallel stores in the Linear and Mach codes *)

Lemma agree_frame_parallel_stores:
  forall j ls ls0 m sp m' sp' parent retaddr chunk addr addr' v v' m1 m1',
  agree_frame j ls ls0 m sp m' sp' parent retaddr ->
  Mem.inject j m m' ->
  val_inject j addr addr' ->
  Mem.storev chunk m addr v = Some m1 ->
  Mem.storev chunk m' addr' v' = Some m1' ->
  agree_frame j ls ls0 m1 sp m1' sp' parent retaddr.
Proof.
Opaque Int.add.
  intros until m1'. intros AG MINJ VINJ STORE1 STORE2.
  inv VINJ; simpl in *; try discriminate.
  eapply agree_frame_invariant; eauto.
  eauto with mem.
  eauto with mem.
  eauto with mem.
  intros. rewrite <- H1. eapply Mem.load_store_other; eauto. 
    destruct (zeq sp' b2); auto.
    subst b2. right.
    exploit agree_inj_unique; eauto. intros [P Q]. subst b1 delta.
    exploit Mem.store_valid_access_3. eexact STORE1. intros [A B].
    rewrite shifted_stack_offset_no_overflow.
    exploit agree_bounds. eauto. apply Mem.perm_cur_max. apply A. 
    instantiate (1 := Int.unsigned ofs1). generalize (size_chunk_pos chunk). omega.
    intros C.
    exploit agree_bounds. eauto. apply Mem.perm_cur_max. apply A. 
    instantiate (1 := Int.unsigned ofs1 + size_chunk chunk - 1). generalize (size_chunk_pos chunk). omega.
    intros D.
    omega.
    eapply agree_bounds. eauto. apply Mem.perm_cur_max. apply A. 
    generalize (size_chunk_pos chunk). omega.
  intros; eauto with mem.
Qed.

(** Preservation by increasing memory injections (allocations and external calls) *)

Lemma agree_frame_inject_incr:
  forall j ls ls0 m sp m' sp' parent retaddr m1 m1' j',
  agree_frame j ls ls0 m sp m' sp' parent retaddr ->
  inject_incr j j' -> inject_separated j j' m1 m1' ->
  Mem.valid_block m1' sp' ->
  agree_frame j' ls ls0 m sp m' sp' parent retaddr.
Proof.
  intros. inv H. constructor; auto; intros; eauto with stacking.
  case_eq (j b0). 
  intros [b' delta'] EQ. rewrite (H0 _ _ _ EQ) in H. inv H. auto. 
  intros EQ. exploit H1. eauto. eauto. intros [A B]. contradiction.
Qed.

Remark inject_alloc_separated:
  forall j m1 m2 j' b1 b2 delta,
  inject_incr j j' ->
  j' b1 = Some(b2, delta) ->
  (forall b, b <> b1 -> j' b = j b) ->
  ~Mem.valid_block m1 b1 -> ~Mem.valid_block m2 b2 ->
  inject_separated j j' m1 m2.
Proof.
  intros. red. intros.
  destruct (eq_block b0 b1). subst b0. rewrite H0 in H5; inv H5. tauto.
  rewrite H1 in H5. congruence. auto.
Qed.

(** Preservation at return points (when [ls] is changed but not [ls0]). *)

Remark mreg_not_within_bounds_callee_save:
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

Lemma agree_frame_return:
  forall j ls ls0 m sp m' sp' parent retaddr ls',
  agree_frame j ls ls0 m sp m' sp' parent retaddr ->
  agree_callee_save ls' ls ->
  wt_locset ls' ->
  agree_frame j ls' ls0 m sp m' sp' parent retaddr.
Proof.
  intros. red in H0. inv H; constructor; auto; intros.
  rewrite H0; auto. apply mreg_not_within_bounds_callee_save; auto. 
  rewrite H0; auto.
  rewrite H0; auto.
  rewrite H0; auto.
Qed.

(** Preservation at tailcalls (when [ls0] is changed but not [ls]). *)

Lemma agree_frame_tailcall:
  forall j ls ls0 m sp m' sp' parent retaddr ls0',
  agree_frame j ls ls0 m sp m' sp' parent retaddr ->
  agree_callee_save ls0 ls0' ->
  agree_frame j ls ls0' m sp m' sp' parent retaddr.
Proof.
  intros. red in H0. inv H; constructor; auto; intros.
  rewrite <- H0; auto. apply mreg_not_within_bounds_callee_save; auto. 
  rewrite <- H0; auto.
  rewrite <- H0; auto.
  rewrite <- H0; auto.
Qed.


(** Properties of [agree_callee_save]. *)

Lemma agree_callee_save_return_regs:
  forall ls1 ls2,
  agree_callee_save (return_regs ls1 ls2) ls1.
Proof.
  intros; red; intros.
  unfold return_regs. destruct l; auto.
  generalize (int_callee_save_not_destroyed m); intro.
  generalize (float_callee_save_not_destroyed m); intro.
  destruct (In_dec Loc.eq (R m) temporaries). tauto.
  destruct (In_dec Loc.eq (R m) destroyed_at_call). tauto.
  auto.
Qed.

Lemma agree_callee_save_set_result:
  forall ls1 ls2 v sg,
  agree_callee_save ls1 ls2 ->
  agree_callee_save (Locmap.set (R (loc_result sg)) v ls1) ls2.
Proof.
  intros; red; intros. rewrite <- H; auto. 
  apply Locmap.gso. destruct l; simpl; auto.
  red; intro. subst m. elim (loc_result_not_callee_save _ H0).
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
Variable j: meminj.
Variable cs: list stackframe.
Variable fb: block.
Variable sp: block.
Variable csregs: list mreg.
Variable ls: locset.

Inductive stores_in_frame: mem -> mem -> Prop :=
  | stores_in_frame_refl: forall m,
      stores_in_frame m m
  | stores_in_frame_step: forall m1 chunk ofs v m2 m3,
       ofs + size_chunk chunk <= fe.(fe_stack_data)
       \/ fe.(fe_stack_data) + f.(Linear.fn_stacksize) <= ofs ->
       Mem.store chunk m1 sp ofs v = Some m2 ->
       stores_in_frame m2 m3 ->
       stores_in_frame m1 m3.

Remark stores_in_frame_trans:
  forall m1 m2, stores_in_frame m1 m2 ->
  forall m3, stores_in_frame m2 m3 -> stores_in_frame m1 m3.
Proof.
  induction 1; intros. auto. econstructor; eauto.
Qed.

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
Hypothesis csregs_typ:
  forall r, In r csregs -> mreg_type r = ty.

Hypothesis ls_temp_undef:
  forall r, In r destroyed_at_move_regs -> ls (R r) = Vundef.

Hypothesis wt_ls: wt_locset ls.

Lemma save_callee_save_regs_correct:
  forall l k rs m,
  incl l csregs ->
  list_norepet l ->
  frame_perm_freeable m sp ->
  agree_regs j ls rs ->
  exists rs', exists m',
    star step tge 
       (State cs fb (Vptr sp Int.zero)
         (save_callee_save_regs bound number mkindex ty fe l k) rs m)
    E0 (State cs fb (Vptr sp Int.zero) k rs' m')
  /\ (forall r,
       In r l -> number r < bound fe ->
       index_contains_inj j m' sp (mkindex (number r)) (ls (R r)))
  /\ (forall idx v,
       index_valid idx ->
       (forall r,
         In r l -> number r < bound fe -> idx <> mkindex (number r)) ->
       index_contains m sp idx v ->
       index_contains m' sp idx v)
  /\ stores_in_frame m m'
  /\ frame_perm_freeable m' sp
  /\ agree_regs j ls rs'.
Proof.
  induction l; intros; simpl save_callee_save_regs.
  (* base case *)
  exists rs; exists m. split. apply star_refl. 
  split. intros. elim H3.
  split. auto.
  split. constructor.
  auto.
  (* inductive case *)
  assert (R1: incl l csregs). eauto with coqlib.
  assert (R2: list_norepet l). inversion H0; auto.
  unfold save_callee_save_reg.
  destruct (zlt (number a) (bound fe)).
  (* a store takes place *)
  exploit store_index_succeeds. apply (mkindex_valid a); auto with coqlib. 
  eauto. instantiate (1 := rs a). intros [m1 ST].
  exploit (IHl k (undef_setstack rs) m1).  auto with coqlib. auto. 
  red; eauto with mem.
  apply agree_regs_exten with ls rs. auto.
  intros. destruct (In_dec mreg_eq r destroyed_at_move_regs). 
  left. apply ls_temp_undef; auto. 
  right; split. auto. unfold undef_setstack, undef_move. apply undef_regs_other; auto.
  intros [rs' [m' [A [B [C [D [E F]]]]]]].
  exists rs'; exists m'. 
  split. eapply star_left; eauto. econstructor. 
  rewrite <- (mkindex_typ (number a)). 
  apply store_stack_succeeds; auto with coqlib.
  traceEq.
  split; intros.
  simpl in H3. destruct (mreg_eq a r). subst r.
  assert (index_contains_inj j m1 sp (mkindex (number a)) (ls (R a))).
    eapply gss_index_contains_inj; eauto.
    rewrite mkindex_typ. rewrite <- (csregs_typ a). apply wt_ls. auto with coqlib.
  destruct H5 as [v' [P Q]].
  exists v'; split; auto. apply C; auto. 
  intros. apply mkindex_inj. apply number_inj; auto with coqlib. 
  inv H0. intuition congruence.
  apply B; auto with coqlib. 
  intuition congruence.
  split. intros.
  apply C; auto with coqlib.
  eapply gso_index_contains; eauto with coqlib. 
  split. econstructor; eauto.
  rewrite size_type_chunk. apply offset_of_index_disj_stack_data_2; eauto with coqlib.
  auto.
  (* no store takes place *)
  exploit (IHl k rs m); auto with coqlib. 
  intros [rs' [m' [A [B [C [D [E F]]]]]]].
  exists rs'; exists m'; intuition. 
  simpl in H3. destruct H3. subst r. omegaContradiction. apply B; auto.
  apply C; auto with coqlib.
  intros. eapply H4; eauto. auto with coqlib.
Qed.

End SAVE_CALLEE_SAVE.

Lemma save_callee_save_correct:
  forall j ls rs sp cs fb k m,
  agree_regs j (call_regs ls) rs -> wt_locset (call_regs ls) ->
  frame_perm_freeable m sp ->
  exists rs', exists m',
    star step tge 
       (State cs fb (Vptr sp Int.zero) (save_callee_save fe k) rs m)
    E0 (State cs fb (Vptr sp Int.zero) k rs' m')
  /\ (forall r,
       In r int_callee_save_regs -> index_int_callee_save r < b.(bound_int_callee_save) ->
       index_contains_inj j m' sp (FI_saved_int (index_int_callee_save r)) (call_regs ls (R r)))
  /\ (forall r,
       In r float_callee_save_regs -> index_float_callee_save r < b.(bound_float_callee_save) ->
       index_contains_inj j m' sp (FI_saved_float (index_float_callee_save r)) (call_regs ls (R r)))
  /\ (forall idx v,
       index_valid idx ->
       match idx with FI_saved_int _ => False | FI_saved_float _ => False | _ => True end ->
       index_contains m sp idx v ->
       index_contains m' sp idx v)
  /\ stores_in_frame sp m m'
  /\ frame_perm_freeable m' sp
  /\ agree_regs j (call_regs ls) rs'.
Proof.
  intros.
  assert (ls_temp_undef: forall r, In r destroyed_at_move_regs -> call_regs ls (R r) = Vundef).
    intros; unfold call_regs. apply pred_dec_true.
Transparent destroyed_at_move_regs.
    simpl in *; intuition congruence.
  exploit (save_callee_save_regs_correct 
             fe_num_int_callee_save
             index_int_callee_save
             FI_saved_int Tint
             j cs fb sp int_callee_save_regs (call_regs ls)).
  intros. apply index_int_callee_save_inj; auto. 
  intros. simpl. split. apply Zge_le. apply index_int_callee_save_pos; auto. assumption.
  auto.
  intros; congruence.
  intros; simpl. destruct idx; auto. congruence.
  intros. apply int_callee_save_type. auto.
  auto.
  auto.
  apply incl_refl. 
  apply int_callee_save_norepet.
  eauto.
  eauto.
  intros [rs1 [m1 [A [B [C [D [E F]]]]]]].
  exploit (save_callee_save_regs_correct 
             fe_num_float_callee_save
             index_float_callee_save
             FI_saved_float Tfloat
             j cs fb sp float_callee_save_regs (call_regs ls)).
  intros. apply index_float_callee_save_inj; auto. 
  intros. simpl. split. apply Zge_le. apply index_float_callee_save_pos; auto. assumption.
  simpl; auto.
  intros; congruence.
  intros; simpl. destruct idx; auto. congruence.
  intros. apply float_callee_save_type. auto.
  auto. 
  auto.
  apply incl_refl. 
  apply float_callee_save_norepet.
  eexact E.
  eexact F.
  intros [rs2 [m2 [P [Q [R [S [T U]]]]]]].
  exists rs2; exists m2.
  split. unfold save_callee_save, save_callee_save_int, save_callee_save_float.
  eapply star_trans; eauto. 
  split; intros.
  destruct (B r H2 H3) as [v [X Y]]. exists v; split; auto. apply R.
  apply index_saved_int_valid; auto. 
  intros. congruence.
  auto.
  split. intros. apply Q; auto.
  split. intros. apply R. auto.
  intros. destruct idx; contradiction||congruence.
  apply C. auto. 
  intros. destruct idx; contradiction||congruence.
  auto.
  split. eapply stores_in_frame_trans; eauto.
  auto.
Qed.

(** Properties of sequences of stores in the frame. *)

Lemma stores_in_frame_inject:
  forall j sp sp' m,
  (forall b delta, j b = Some(sp', delta) -> b = sp /\ delta = fe.(fe_stack_data)) ->
  (forall ofs k p, Mem.perm m sp ofs k p -> 0 <= ofs < f.(Linear.fn_stacksize)) ->
  forall m1 m2, stores_in_frame sp' m1 m2 -> Mem.inject j m m1 -> Mem.inject j m m2.
Proof.
  induction 3; intros.
  auto.
  apply IHstores_in_frame.
  intros. eapply Mem.store_outside_inject; eauto.
  intros. exploit H; eauto. intros [A B]; subst.
  exploit H0; eauto. omega. 
Qed.

Lemma stores_in_frame_valid:
  forall b sp m m', stores_in_frame sp m m' -> Mem.valid_block m b -> Mem.valid_block m' b.
Proof.
  induction 1; intros. auto. apply IHstores_in_frame. eauto with mem.
Qed.

Lemma stores_in_frame_perm:
  forall b ofs k p sp m m', stores_in_frame sp m m' -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p.
Proof.
  induction 1; intros. auto. apply IHstores_in_frame. eauto with mem.
Qed.

Lemma stores_in_frame_contents:
  forall chunk b ofs sp, b < sp ->
  forall m m', stores_in_frame sp m m' -> 
  Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  induction 2. auto. 
  rewrite IHstores_in_frame. eapply Mem.load_store_other; eauto.
  left; unfold block; omega.
Qed.

(** As a corollary of the previous lemmas, we obtain the following
  correctness theorem for the execution of a function prologue
  (allocation of the frame + saving of the link and return address +
  saving of the used callee-save registers). *)

Lemma function_prologue_correct:
  forall j ls ls0 rs m1 m1' m2 sp parent ra cs fb k,
  agree_regs j ls rs ->
  agree_callee_save ls ls0 ->
  wt_locset ls ->
  Mem.inject j m1 m1' ->
  Mem.alloc m1 0 f.(Linear.fn_stacksize) = (m2, sp) ->
  Val.has_type parent Tint -> Val.has_type ra Tint ->
  exists j', exists rs', exists m2', exists sp', exists m3', exists m4', exists m5',
     Mem.alloc m1' 0 tf.(fn_stacksize) = (m2', sp')
  /\ store_stack m2' (Vptr sp' Int.zero) Tint tf.(fn_link_ofs) parent = Some m3'
  /\ store_stack m3' (Vptr sp' Int.zero) Tint tf.(fn_retaddr_ofs) ra = Some m4'
  /\ star step tge 
         (State cs fb (Vptr sp' Int.zero) (save_callee_save fe k) (undef_temps rs) m4')
      E0 (State cs fb (Vptr sp' Int.zero) k rs' m5')
  /\ agree_regs j' (call_regs ls) rs'
  /\ agree_frame j' (call_regs ls) ls0 m2 sp m5' sp' parent ra
  /\ inject_incr j j'
  /\ inject_separated j j' m1 m1'
  /\ Mem.inject j' m2 m5'
  /\ stores_in_frame sp' m2' m5'.
Proof.
  intros until k; intros AGREGS AGCS WTREGS INJ1 ALLOC TYPAR TYRA.
  rewrite unfold_transf_function.
  unfold fn_stacksize, fn_link_ofs, fn_retaddr_ofs.
  (* Allocation step *)
  caseEq (Mem.alloc m1' 0 (fe_size fe)). intros m2' sp' ALLOC'.
  exploit Mem.alloc_left_mapped_inject.
    eapply Mem.alloc_right_inject; eauto.
    eauto.
    instantiate (1 := sp'). eauto with mem.
    instantiate (1 := fe_stack_data fe).
    generalize stack_data_offset_valid (bound_stack_data_pos b) size_no_overflow; omega.
    intros; right. 
    exploit Mem.perm_alloc_inv. eexact ALLOC'. eauto. rewrite zeq_true. 
    generalize size_no_overflow. omega. 
    intros. apply Mem.perm_implies with Freeable; auto with mem. 
    eapply Mem.perm_alloc_2; eauto.
    generalize stack_data_offset_valid bound_stack_data_stacksize; omega.
    red. intros. apply Zdivides_trans with 8. 
    destruct chunk; simpl; auto with align_4.
    apply fe_stack_data_aligned.
    intros.
      assert (Mem.valid_block m1' sp'). eapply Mem.valid_block_inject_2; eauto.
      assert (~Mem.valid_block m1' sp') by eauto with mem.
      contradiction.
  intros [j' [INJ2 [INCR [MAP1 MAP2]]]].
  assert (PERM: frame_perm_freeable m2' sp').
    red; intros. eapply Mem.perm_alloc_2; eauto.
  (* Store of parent *)
  exploit (store_index_succeeds m2' sp' FI_link parent). red; auto. auto. 
  intros [m3' STORE2].
  (* Store of retaddr *)
  exploit (store_index_succeeds m3' sp' FI_retaddr ra). red; auto. red; eauto with mem.
  intros [m4' STORE3].
  (* Saving callee-save registers *)
  assert (PERM4: frame_perm_freeable m4' sp').
    red; intros. eauto with mem. 
  exploit save_callee_save_correct. 
    apply agree_regs_call_regs. eapply agree_regs_inject_incr; eauto.
    apply wt_call_regs. auto.
    eexact PERM4.
  intros [rs' [m5' [STEPS [ICS [FCS [OTHERS [STORES [PERM5 AGREGS']]]]]]]].
  (* stores in frames *)
  assert (SIF: stores_in_frame sp' m2' m5').
    econstructor; eauto. 
    rewrite size_type_chunk. apply offset_of_index_disj_stack_data_2; auto. red; auto.
    econstructor; eauto.
    rewrite size_type_chunk. apply offset_of_index_disj_stack_data_2; auto. red; auto.
  (* separation *)
  assert (SEP: forall b0 delta, j' b0 = Some(sp', delta) -> b0 = sp /\ delta = fe_stack_data fe).
    intros. destruct (zeq b0 sp). 
    subst b0. rewrite MAP1 in H; inv H; auto.
    rewrite MAP2 in H; auto. 
    assert (Mem.valid_block m1' sp'). eapply Mem.valid_block_inject_2; eauto.
    assert (~Mem.valid_block m1' sp') by eauto with mem.
    contradiction.
  (* Conclusions *)
  exists j'; exists rs'; exists m2'; exists sp'; exists m3'; exists m4'; exists m5'.
  split. auto.
  (* store parent *)
  split. change Tint with (type_of_index FI_link). 
  change (fe_ofs_link fe) with (offset_of_index fe FI_link).
  apply store_stack_succeeds; auto. red; auto.
  (* store retaddr *)
  split. change Tint with (type_of_index FI_retaddr). 
  change (fe_ofs_retaddr fe) with (offset_of_index fe FI_retaddr).
  apply store_stack_succeeds; auto. red; auto.
  (* saving of registers *)
  split. eexact STEPS.
  (* agree_regs *)
  split. auto.
  (* agree frame *)
  split. constructor; intros.
    (* unused regs *)
    unfold call_regs. destruct (in_dec Loc.eq (R r) temporaries).
    elim H. apply temporary_within_bounds; auto.
    apply AGCS. apply mreg_not_within_bounds_callee_save; auto.
    (* locals *)
    simpl. apply index_contains_inj_undef; auto.
    (* outgoing *)
    simpl. apply index_contains_inj_undef; auto.
    (* incoming *)
    unfold call_regs. apply AGCS. auto.
    (* parent *)
    apply OTHERS; auto. red; auto.
    eapply gso_index_contains; eauto. red; auto.
    eapply gss_index_contains; eauto. red; auto.
    red; auto.
    (* retaddr *)
    apply OTHERS; auto. red; auto.
    eapply gss_index_contains; eauto. red; auto.
    (* int callee save *)
    rewrite <- AGCS. replace (ls (R r)) with (call_regs ls (R r)).
    apply ICS; auto.
    unfold call_regs. apply pred_dec_false.
    red; intros; exploit int_callee_save_not_destroyed; eauto. 
    auto.
    (* float callee save *)
    rewrite <- AGCS. replace (ls (R r)) with (call_regs ls (R r)).
    apply FCS; auto.
    unfold call_regs. apply pred_dec_false.
    red; intros; exploit float_callee_save_not_destroyed; eauto. 
    auto.
    (* inj *)
    auto.
    (* inj_unique *)
    auto.
    (* valid sp *)
    eauto with mem.
    (* valid sp' *)
    eapply stores_in_frame_valid with (m := m2'); eauto with mem.
    (* bounds *)
    exploit Mem.perm_alloc_inv. eexact ALLOC. eauto. rewrite zeq_true. auto.
    (* perms *)
    auto.
    (* wt *)
    apply wt_call_regs; auto.
  (* incr *)
  split. auto.
  (* separated *)
  split. eapply inject_alloc_separated; eauto with mem.
  (* inject *)
  split. eapply stores_in_frame_inject; eauto.
  intros. exploit Mem.perm_alloc_inv. eexact ALLOC. eauto. rewrite zeq_true. auto.
  (* stores in frame *)
  auto.
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
Variable csregs: list mreg.
Variable j: meminj.
Variable cs: list stackframe.
Variable fb: block.
Variable sp: block.
Variable ls0: locset.
Variable m: mem.

Hypothesis mkindex_valid:
  forall r, In r csregs -> number r < bound fe -> index_valid (mkindex (number r)).
Hypothesis mkindex_typ:
  forall z, type_of_index (mkindex z) = ty.
Hypothesis number_within_bounds:
  forall r, In r csregs ->
  (number r < bound fe <-> mreg_within_bounds b r).
Hypothesis mkindex_val:
  forall r,
  In r csregs -> number r < bound fe ->
  index_contains_inj j m sp (mkindex (number r)) (ls0 (R r)).

Definition agree_unused (ls0: locset) (rs: regset) : Prop :=
  forall r, ~(mreg_within_bounds b r) -> val_inject j (ls0 (R r)) (rs r).

Lemma restore_callee_save_regs_correct:
  forall l rs k,
  incl l csregs ->
  list_norepet l -> 
  agree_unused ls0 rs ->
  exists rs',
    star step tge
      (State cs fb (Vptr sp Int.zero)
        (restore_callee_save_regs bound number mkindex ty fe l k) rs m)
   E0 (State cs fb (Vptr sp Int.zero) k rs' m)
  /\ (forall r, In r l -> val_inject j (ls0 (R r)) (rs' r))
  /\ (forall r, ~(In r l) -> rs' r = rs r)
  /\ agree_unused ls0 rs'.
Proof.
  induction l; intros; simpl restore_callee_save_regs.
  (* base case *)
  exists rs. intuition. apply star_refl.
  (* inductive case *)
  assert (R0: In a csregs). apply H; auto with coqlib.
  assert (R1: incl l csregs). eauto with coqlib.
  assert (R2: list_norepet l). inversion H0; auto.
  unfold restore_callee_save_reg.
  destruct (zlt (number a) (bound fe)).
  exploit (mkindex_val a); auto. intros [v [X Y]].
  set (rs1 := Regmap.set a v rs).
  exploit (IHl rs1 k); eauto.
    red; intros. unfold rs1. unfold Regmap.set. destruct (RegEq.eq r a).
    subst r. auto.
    auto.
  intros [rs' [A [B [C D]]]].
  exists rs'. split. 
  eapply star_left. 
  constructor. rewrite <- (mkindex_typ (number a)). apply index_contains_load_stack. eauto.   
  eauto. traceEq.
  split. intros. destruct H2.
  subst r. rewrite C. unfold rs1. rewrite Regmap.gss. auto. inv H0; auto.
  auto.
  split. intros. simpl in H2. rewrite C. unfold rs1. apply Regmap.gso.
  apply sym_not_eq; tauto. tauto.
  auto.
  (* no load takes place *)
  exploit (IHl rs k); auto.
  intros [rs' [A [B [C D]]]].
  exists rs'. split. assumption.
  split. intros. destruct H2.
  subst r. apply D. 
  rewrite <- number_within_bounds. auto. auto. auto.
  split. intros. simpl in H2. apply C. tauto.
  auto.
Qed.

End RESTORE_CALLEE_SAVE.

Lemma restore_callee_save_correct:
  forall j ls ls0 m sp m' sp' pa ra cs fb rs k,
  agree_frame j ls ls0 m sp m' sp' pa ra ->
  agree_unused j ls0 rs ->
  exists rs',
    star step tge
       (State cs fb (Vptr sp' Int.zero) (restore_callee_save fe k) rs m')
    E0 (State cs fb (Vptr sp' Int.zero) k rs' m')
  /\ (forall r, 
        In r int_callee_save_regs \/ In r float_callee_save_regs -> 
        val_inject j (ls0 (R r)) (rs' r))
  /\ (forall r, 
        ~(In r int_callee_save_regs) ->
        ~(In r float_callee_save_regs) ->
        rs' r = rs r).
Proof.
  intros. 
    exploit (restore_callee_save_regs_correct 
             fe_num_int_callee_save
             index_int_callee_save
             FI_saved_int
             Tint
             int_callee_save_regs
             j cs fb sp' ls0 m'); auto.
  intros. unfold mreg_within_bounds. rewrite (int_callee_save_type r H1). tauto.
  eapply agree_saved_int; eauto. 
  apply incl_refl.
  apply int_callee_save_norepet.
  eauto.
  intros [rs1 [A [B [C D]]]].
  exploit (restore_callee_save_regs_correct 
             fe_num_float_callee_save
             index_float_callee_save
             FI_saved_float
             Tfloat
             float_callee_save_regs
             j cs fb sp' ls0 m'); auto.
  intros. unfold mreg_within_bounds. rewrite (float_callee_save_type r H1). tauto.
  eapply agree_saved_float; eauto. 
  apply incl_refl.
  apply float_callee_save_norepet.
  eexact D.
  intros [rs2 [P [Q [R S]]]].
  exists rs2.
  split. unfold restore_callee_save. eapply star_trans; eauto.
  split. intros. destruct H1.
    rewrite R. apply B; auto. red; intros. exploit int_float_callee_save_disjoint; eauto.
    apply Q; auto.
  intros. rewrite R; auto.
Qed.

(** As a corollary, we obtain the following correctness result for
  the execution of a function epilogue (reloading of used callee-save
  registers + reloading of the link and return address + freeing
  of the frame). *)

Lemma function_epilogue_correct:
  forall j ls ls0 m sp m' sp' pa ra cs fb rs k m1,
  agree_regs j ls rs ->
  agree_frame j ls ls0 m sp m' sp' pa ra ->
  Mem.inject j m m' ->
  Mem.free m sp 0 f.(Linear.fn_stacksize) = Some m1 ->
  exists rs1, exists m1',
     load_stack m' (Vptr sp' Int.zero) Tint tf.(fn_link_ofs) = Some pa
  /\ load_stack m' (Vptr sp' Int.zero) Tint tf.(fn_retaddr_ofs) = Some ra
  /\ Mem.free m' sp' 0 tf.(fn_stacksize) = Some m1'
  /\ star step tge
       (State cs fb (Vptr sp' Int.zero) (restore_callee_save fe k) rs m')
    E0 (State cs fb (Vptr sp' Int.zero) k rs1 m')
  /\ agree_regs j (return_regs ls0 ls) rs1
  /\ agree_callee_save (return_regs ls0 ls) ls0
  /\ rs1 IT1 = rs IT1
  /\ Mem.inject j m1 m1'.
Proof.
  intros.
  (* can free *)
  destruct (Mem.range_perm_free m' sp' 0 (fn_stacksize tf)) as [m1' FREE].
  rewrite unfold_transf_function; unfold fn_stacksize. red; intros.
  assert (EITHER: fe_stack_data fe <= ofs < fe_stack_data fe + Linear.fn_stacksize f
              \/ (ofs < fe_stack_data fe \/ fe_stack_data fe + Linear.fn_stacksize f <= ofs))
  by omega.
  destruct EITHER.
  replace ofs with ((ofs - fe_stack_data fe) + fe_stack_data fe) by omega.
  eapply Mem.perm_inject with (f := j). eapply agree_inj; eauto. eauto. 
  eapply Mem.free_range_perm; eauto. omega.
  eapply agree_perm; eauto. 
  (* inject after free *)
  assert (INJ1: Mem.inject j m1 m1').
  eapply Mem.free_inject with (l := (sp, 0, f.(Linear.fn_stacksize)) :: nil); eauto.
  simpl. rewrite H2. auto.
  intros. exploit agree_inj_unique; eauto. intros [P Q]; subst b1 delta.
  exists 0; exists (Linear.fn_stacksize f); split. auto with coqlib.
  eapply agree_bounds. eauto. eapply Mem.perm_max. eauto.  
  (* can execute epilogue *)
  exploit restore_callee_save_correct; eauto.
    instantiate (1 := rs). red; intros. 
    rewrite <- (agree_unused_reg _ _ _ _ _ _ _ _ _ H0). auto. auto. 
  intros [rs1 [A [B C]]].
  (* conclusions *)
  exists rs1; exists m1'.
  split. rewrite unfold_transf_function; unfold fn_link_ofs. 
    eapply index_contains_load_stack with (idx := FI_link); eauto with stacking.
  split. rewrite unfold_transf_function; unfold fn_retaddr_ofs. 
    eapply index_contains_load_stack with (idx := FI_retaddr); eauto with stacking.
  split. auto.
  split. eexact A.
  split. red;intros. unfold return_regs. 
    generalize (register_classification r) (int_callee_save_not_destroyed r) (float_callee_save_not_destroyed r); intros.
    destruct (in_dec Loc.eq (R r) temporaries).
    rewrite C; auto. 
    destruct (in_dec Loc.eq (R r) destroyed_at_call).
    rewrite C; auto.
    intuition.
  split. apply agree_callee_save_return_regs.
  split. apply C. apply int_callee_save_not_destroyed. left; simpl; auto. 
  apply float_callee_save_not_destroyed. left; simpl; auto.
  auto.
Qed.

End FRAME_PROPERTIES.

(** * Call stack invariant *)

Inductive match_globalenvs (j: meminj) (bound: Z) : Prop :=
  | match_globalenvs_intro
      (POS: bound > 0)
      (DOMAIN: forall b, b < bound -> j b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, j b1 = Some(b2, delta) -> b2 < bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> b < bound)
      (INFOS: forall b gv, Genv.find_var_info ge b = Some gv -> b < bound).

Inductive match_stacks (j: meminj) (m m': mem): 
       list Linear.stackframe -> list stackframe -> signature -> Z -> Z -> Prop :=
  | match_stacks_empty: forall sg hi bound bound',
      hi <= bound -> hi <= bound' -> match_globalenvs j hi ->
      tailcall_possible sg ->
      match_stacks j m m' nil nil sg bound bound'
  | match_stacks_cons: forall f sp ls c cs fb sp' ra c' cs' sg bound bound' trf
        (TAIL: is_tail c (Linear.fn_code f))
        (WTF: wt_function f)
        (FINDF: Genv.find_funct_ptr tge fb = Some (Internal trf))
        (TRF: transf_function f = OK trf)
        (TRC: transl_code (make_env (function_bounds f)) c = c')
        (TY_RA: Val.has_type ra Tint)
        (FRM: agree_frame f j ls (parent_locset cs) m sp m' sp' (parent_sp cs') (parent_ra cs'))
        (ARGS: forall ofs ty,
             In (S (Outgoing ofs ty)) (loc_arguments sg) ->
             slot_within_bounds f (function_bounds f) (Outgoing ofs ty))
        (STK: match_stacks j m m' cs cs' (Linear.fn_sig f) sp sp')
        (BELOW: sp < bound)
        (BELOW': sp' < bound'),
      match_stacks j m m'
                   (Linear.Stackframe f (Vptr sp Int.zero) ls c :: cs)
                   (Stackframe fb (Vptr sp' Int.zero) ra c' :: cs')
                   sg bound bound'.

(** Invariance with respect to change of bounds. *)

Lemma match_stacks_change_bounds:
  forall j m1 m' cs cs' sg bound bound',
  match_stacks j m1 m' cs cs' sg bound bound' ->
  forall xbound xbound',
  bound <= xbound -> bound' <= xbound' ->
  match_stacks j m1 m' cs cs' sg xbound xbound'.
Proof.
  induction 1; intros. 
  apply match_stacks_empty with hi; auto. omega. omega.
  econstructor; eauto. omega. omega.
Qed.

(** Invariance with respect to change of [m]. *)

Lemma match_stacks_change_linear_mem:
  forall j m1 m2 m' cs cs' sg bound bound',
  match_stacks j m1 m' cs cs' sg bound bound' ->
  (forall b, b < bound -> Mem.valid_block m1 b -> Mem.valid_block m2 b) ->
  (forall b ofs p, b < bound -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  match_stacks j m2 m' cs cs' sg bound bound'.
Proof.
  induction 1; intros.
  econstructor; eauto.
  econstructor; eauto.
  eapply agree_frame_invariant; eauto. 
  apply IHmatch_stacks.
  intros. apply H0; auto. omega.
  intros. apply H1. omega. auto.
Qed.

(** Invariance with respect to change of [m']. *)

Lemma match_stacks_change_mach_mem:
  forall j m m1' m2' cs cs' sg bound bound',
  match_stacks j m m1' cs cs' sg bound bound' ->
  (forall b, b < bound' -> Mem.valid_block m1' b -> Mem.valid_block m2' b) ->
  (forall b ofs k p, b < bound' -> Mem.perm m1' b ofs k p -> Mem.perm m2' b ofs k p) ->
  (forall chunk b ofs v, b < bound' -> Mem.load chunk m1' b ofs = Some v -> Mem.load chunk m2' b ofs = Some v) ->
  match_stacks j m m2' cs cs' sg bound bound'.
Proof.
  induction 1; intros.
  econstructor; eauto.
  econstructor; eauto.
  eapply agree_frame_invariant; eauto. 
  apply IHmatch_stacks. 
  intros; apply H0; auto; omega.
  intros; apply H1; auto; omega.
  intros; apply H2; auto. omega.
Qed.

(** A variant of the latter, for use with external calls *)

Lemma match_stacks_change_mem_extcall:
  forall j m1 m2 m1' m2' cs cs' sg bound bound',
  match_stacks j m1 m1' cs cs' sg bound bound' ->
  (forall b, b < bound -> Mem.valid_block m1 b -> Mem.valid_block m2 b) ->
  (forall b ofs p, b < bound -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  (forall b, b < bound' -> Mem.valid_block m1' b -> Mem.valid_block m2' b) ->
  mem_unchanged_on (loc_out_of_reach j m1) m1' m2' ->
  match_stacks j m2 m2' cs cs' sg bound bound'.
Proof.
  induction 1; intros.
  econstructor; eauto.
  econstructor; eauto.
  eapply agree_frame_extcall_invariant; eauto.
  apply IHmatch_stacks. 
  intros; apply H0; auto; omega.
  intros; apply H1. omega. auto.
  intros; apply H2; auto; omega.
  auto.
Qed.

(** Invariance with respect to change of [j]. *)

Lemma match_stacks_change_meminj:
  forall j j' m m' m1 m1',
  inject_incr j j' ->
  inject_separated j j' m1 m1' ->
  forall cs cs' sg bound bound',
  match_stacks j m m' cs cs' sg bound bound' ->
  bound' <= Mem.nextblock m1' ->
  match_stacks j' m m' cs cs' sg bound bound'.
Proof.
  induction 3; intros.
  apply match_stacks_empty with hi; auto.
  inv H3. constructor; auto.
  intros. red in H0. case_eq (j b1).
  intros [b' delta'] EQ. rewrite (H _ _ _ EQ) in H3. inv H3. eauto.
  intros EQ. exploit H0; eauto. intros [A B]. elim B. red. omega. 
  econstructor; eauto. 
  eapply agree_frame_inject_incr; eauto. red; omega. 
  apply IHmatch_stacks. omega.
Qed.

(** Preservation by parallel stores in Linear and Mach. *)

Lemma match_stacks_parallel_stores:
  forall j m m' chunk addr addr' v v' m1 m1',
  Mem.inject j m m' ->
  val_inject j addr addr' ->
  Mem.storev chunk m addr v = Some m1 ->
  Mem.storev chunk m' addr' v' = Some m1' ->
  forall cs cs' sg bound bound',
  match_stacks j m m' cs cs' sg bound bound' ->
  match_stacks j m1 m1' cs cs' sg bound bound'.
Proof.
  intros until m1'. intros MINJ VINJ STORE1 STORE2.
  induction 1.
  econstructor; eauto.
  econstructor; eauto.
  eapply agree_frame_parallel_stores; eauto.
Qed.

(** Invariance by external calls. *)

Lemma match_stack_change_extcall:
  forall ec args m1 res t m2 args' m1' res' t' m2' j j',
  external_call ec ge args m1 t res m2 ->
  external_call ec ge args' m1' t' res' m2' ->
  inject_incr j j' ->
  inject_separated j j' m1 m1' ->
  mem_unchanged_on (loc_out_of_reach j m1) m1' m2' ->
  forall cs cs' sg bound bound',
  match_stacks j m1 m1' cs cs' sg bound bound' ->
  bound <= Mem.nextblock m1 -> bound' <= Mem.nextblock m1' ->
  match_stacks j' m2 m2' cs cs' sg bound bound'.
Proof.
  intros. 
  eapply match_stacks_change_meminj; eauto. 
  eapply match_stacks_change_mem_extcall; eauto.
  intros; eapply external_call_valid_block; eauto.
  intros; eapply external_call_max_perm; eauto. red; omega.
  intros; eapply external_call_valid_block; eauto.
Qed.

(** Invariance with respect to change of signature *)

Lemma match_stacks_change_sig:
  forall sg1 j m m' cs cs' sg bound bound',
  match_stacks j m m' cs cs' sg bound bound' ->
  tailcall_possible sg1 ->
  match_stacks j m m' cs cs' sg1 bound bound'.
Proof.
  induction 1; intros. econstructor; eauto. econstructor; eauto. 
  intros. elim (H0 _ H1). 
Qed.

(** [match_stacks] implies [match_globalenvs], which implies [meminj_preserves_globals]. *)

Lemma match_stacks_globalenvs:
  forall j m m' cs cs' sg bound bound',
  match_stacks j m m' cs cs' sg bound bound' ->
  exists hi, match_globalenvs j hi.
Proof.
  induction 1. exists hi; auto. auto.
Qed.

Lemma match_stacks_preserves_globals:
  forall j m m' cs cs' sg bound bound',
  match_stacks j m m' cs cs' sg bound bound' ->
  meminj_preserves_globals ge j.
Proof.
  intros. exploit match_stacks_globalenvs; eauto. intros [hi MG]. inv MG.
  split. eauto. split. eauto. intros. symmetry. eauto. 
Qed.

(** Typing properties of [match_stacks]. *)

Lemma match_stacks_wt_locset:
  forall j m m' cs cs' sg bound bound',
  match_stacks j m m' cs cs' sg bound bound' ->
  wt_locset (parent_locset cs).
Proof.
  induction 1; simpl.
  unfold Locmap.init; red; intros; red; auto.
  inv FRM; auto.
Qed.

Lemma match_stacks_type_sp:
  forall j m m' cs cs' sg bound bound',
  match_stacks j m m' cs cs' sg bound bound' ->
  Val.has_type (parent_sp cs') Tint.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma match_stacks_type_retaddr:
  forall j m m' cs cs' sg bound bound',
  match_stacks j m m' cs cs' sg bound bound' ->
  Val.has_type (parent_ra cs') Tint.
Proof.
  induction 1; simpl; auto.
Qed.

(** * Syntactic properties of the translation *)

(** Preservation of code labels through the translation. *)

Section LABELS.

Remark find_label_fold_right:
  forall (A: Type) (fn: A -> Mach.code -> Mach.code) lbl,
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

(** Code tail property for Linear executions. *)

Lemma find_label_tail:
  forall lbl c c', 
  Linear.find_label lbl c = Some c' -> is_tail c' c.
Proof.
  induction c; simpl.
  intros; discriminate.
  intro c'. case (Linear.is_label lbl a); intros.
  injection H; intro; subst c'. auto with coqlib.
  auto with coqlib.
Qed.

(** Code tail property for translations *)

Lemma is_tail_save_callee_save_regs:
  forall bound number mkindex ty fe csl k,
  is_tail k (save_callee_save_regs bound number mkindex ty fe csl k).
Proof.
  induction csl; intros; simpl. auto with coqlib.
  unfold save_callee_save_reg. destruct (zlt (number a) (bound fe)). 
  constructor; auto. auto.
Qed.

Lemma is_tail_save_callee_save:
  forall fe k,
  is_tail k (save_callee_save fe k).
Proof.
  intros. unfold save_callee_save, save_callee_save_int, save_callee_save_float.
  eapply is_tail_trans; apply is_tail_save_callee_save_regs.
Qed.

Lemma is_tail_restore_callee_save_regs:
  forall bound number mkindex ty fe csl k,
  is_tail k (restore_callee_save_regs bound number mkindex ty fe csl k).
Proof.
  induction csl; intros; simpl. auto with coqlib.
  unfold restore_callee_save_reg. destruct (zlt (number a) (bound fe)). 
  constructor; auto. auto.
Qed.

Lemma is_tail_restore_callee_save:
  forall fe k,
  is_tail k (restore_callee_save fe k).
Proof.
  intros. unfold restore_callee_save, restore_callee_save_int, restore_callee_save_float.
  eapply is_tail_trans; apply is_tail_restore_callee_save_regs.
Qed.

Lemma is_tail_transl_instr:
  forall fe i k,
  is_tail k (transl_instr fe i k).
Proof.
  intros. destruct i; unfold transl_instr; auto with coqlib.
  destruct s; auto with coqlib.
  destruct s; auto with coqlib.
  eapply is_tail_trans. 2: apply is_tail_restore_callee_save. auto with coqlib.
  eapply is_tail_trans. 2: apply is_tail_restore_callee_save. auto with coqlib.
Qed.

Lemma is_tail_transl_code:
  forall fe c1 c2, is_tail c1 c2 -> is_tail (transl_code fe c1) (transl_code fe c2).
Proof.
  induction 1; simpl. auto with coqlib. 
  eapply is_tail_trans. eauto. apply is_tail_transl_instr.
Qed.

Lemma is_tail_transf_function:
  forall f tf c,
  transf_function f = OK tf ->
  is_tail c (Linear.fn_code f) ->
  is_tail (transl_code (make_env (function_bounds f)) c) (fn_code tf).
Proof.
  intros. rewrite (unfold_transf_function _ _ H). simpl. 
  unfold transl_body. eapply is_tail_trans. 2: apply is_tail_save_callee_save.
  apply is_tail_transl_code; auto.
Qed.

(** * Semantic preservation *)

(** Preservation / translation of global symbols and functions. *)

Lemma symbols_preserved:
  forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_symbol_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_var_info_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof
  (Genv.find_funct_transf_partial transf_fundef _ TRANSF).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  exists tf,
  Genv.find_funct_ptr tge v = Some tf /\ transf_fundef f = OK tf.
Proof
  (Genv.find_funct_ptr_transf_partial transf_fundef _ TRANSF).

Lemma sig_preserved:
  forall f tf, transf_fundef f = OK tf -> Mach.funsig tf = Linear.funsig f.
Proof.
  intros until tf; unfold transf_fundef, transf_partial_fundef.
  destruct f; intros; monadInv H.
  rewrite (unfold_transf_function _ _ EQ). auto. 
  auto.
Qed.

Lemma find_function_translated:
  forall j ls rs m m' cs cs' sg bound bound' ros f,
  agree_regs j ls rs ->
  match_stacks j m m' cs cs' sg bound bound' ->
  Linear.find_function ge ros ls = Some f ->
  exists bf, exists tf,
     find_function_ptr tge ros rs = Some bf
  /\ Genv.find_funct_ptr tge bf = Some tf
  /\ transf_fundef f = OK tf.
Proof.
  intros until f; intros AG MS FF.
  exploit match_stacks_globalenvs; eauto. intros [hi MG]. 
  destruct ros; simpl in FF.
  exploit Genv.find_funct_inv; eauto. intros [b EQ]. rewrite EQ in FF. 
  rewrite Genv.find_funct_find_funct_ptr in FF. 
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists b; exists tf; split; auto. simpl.
  generalize (AG m0). rewrite EQ. intro INJ. inv INJ.
  exploit Genv.find_funct_ptr_negative. unfold ge in FF; eexact FF. intros. 
  inv MG. rewrite (DOMAIN b) in H2. inv H2. auto. omega. 
  revert FF. case_eq (Genv.find_symbol ge i); intros; try discriminate. 
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists b; exists tf; split; auto. simpl. 
  rewrite symbols_preserved. auto.
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

(** Preservation of the arguments to an external call. *)

Section EXTERNAL_ARGUMENTS.

Variable j: meminj.
Variables m m': mem.
Variable cs: list Linear.stackframe.
Variable cs': list stackframe.
Variable sg: signature.
Variables bound bound': Z.
Hypothesis MS: match_stacks j m m' cs cs' sg bound bound'.
Variable ls: locset.
Variable rs: regset.
Hypothesis AGR: agree_regs j ls rs.
Hypothesis AGCS: agree_callee_save ls (parent_locset cs).

Lemma transl_external_argument:
  forall l,
  In l (loc_arguments sg) ->
  exists v, extcall_arg rs m' (parent_sp cs') l v /\ val_inject j (ls l) v.
Proof.
  intros.
  assert (loc_argument_acceptable l). apply loc_arguments_acceptable with sg; auto.
  destruct l; red in H0.
  exists (rs m0); split. constructor. auto. 
  destruct s; try contradiction.
  inv MS. 
  elim (H4 _ H).
  unfold parent_sp. 
  exploit agree_outgoing; eauto. intros [v [A B]].
  exists v; split.
  constructor. 
  eapply index_contains_load_stack with (idx := FI_arg z t); eauto. 
  red in AGCS. rewrite AGCS; auto.
Qed.

Lemma transl_external_arguments_rec:
  forall locs,
  incl locs (loc_arguments sg) ->
  exists vl,
  list_forall2 (extcall_arg rs m' (parent_sp cs')) locs vl /\ val_list_inject j ls##locs vl.
Proof.
  induction locs; simpl; intros.
  exists (@nil val); split. constructor. constructor.
  exploit transl_external_argument; eauto with coqlib. intros [v [A B]].
  exploit IHlocs; eauto with coqlib. intros [vl [C D]].
  exists (v :: vl); split; constructor; auto.
Qed.

Lemma transl_external_arguments:
  exists vl,
  extcall_arguments rs m' (parent_sp cs') sg vl /\
  val_list_inject j (ls ## (loc_arguments sg)) vl.
Proof.
  unfold extcall_arguments. 
  apply transl_external_arguments_rec.
  auto with coqlib.
Qed.

End EXTERNAL_ARGUMENTS.

(** Preservation of the arguments to an annotation. *)

Section ANNOT_ARGUMENTS.

Variable f: Linear.function.
Let b := function_bounds f.
Let fe := make_env b.
Variable j: meminj.
Variables m m': mem.
Variables ls ls0: locset.
Variable rs: regset.
Variables sp sp': block.
Variables parent retaddr: val.
Hypothesis AGR: agree_regs j ls rs.
Hypothesis AGF: agree_frame f j ls ls0 m sp m' sp' parent retaddr.

Lemma transl_annot_param_correct:
  forall l,
  loc_acceptable l -> 
  match l with S s => slot_within_bounds f b s | _ => True end ->
  exists v, annot_arg rs m' (Vptr sp' Int.zero) (transl_annot_param fe l) v
         /\ val_inject j (ls l) v.
Proof.
  intros. destruct l; red in H. 
(* reg *)
  exists (rs m0); split. constructor. auto.
(* stack *) 
  destruct s; try contradiction.
  exploit agree_locals; eauto. intros [v [A B]]. inv A. 
  exists v; split. constructor. rewrite Zplus_0_l. auto. auto.
Qed.

Lemma transl_annot_params_correct:
  forall ll,
  locs_acceptable ll ->
  (forall s, In (S s) ll -> slot_within_bounds f b s) ->
  exists vl,
     annot_arguments rs m' (Vptr sp' Int.zero) (map (transl_annot_param fe) ll) vl
  /\ val_list_inject j (map ls ll) vl.
Proof.
  induction ll; intros. 
  exists (@nil val); split; constructor.
  exploit (transl_annot_param_correct a). 
    apply H; auto with coqlib.
    destruct a; auto with coqlib.
  intros [v1 [A B]].
  exploit IHll.
    red; intros; apply H; auto with coqlib.
    intros; apply H0; auto with coqlib.
  intros [vl [C D]].
  exists (v1 :: vl); split; constructor; auto.
Qed.

End ANNOT_ARGUMENTS.

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
  and on the Mach side the register set [rs] and the contents of
  the memory area corresponding to the stack frame.
- The Linear code [c] is a suffix of the code of the
  function [f] being executed.
- Memory injection between the Linear and the Mach memory states.
- Well-typedness of [f].
*)

Inductive match_states: Linear.state -> Machsem.state -> Prop :=
  | match_states_intro:
      forall cs f sp c ls m cs' fb sp' rs m' j tf
        (MINJ: Mem.inject j m m')
        (STACKS: match_stacks j m m' cs cs' f.(Linear.fn_sig) sp sp')
        (TRANSL: transf_function f = OK tf)
        (FIND: Genv.find_funct_ptr tge fb = Some (Internal tf))
        (WTF: wt_function f)
        (AGREGS: agree_regs j ls rs)
        (AGFRAME: agree_frame f j ls (parent_locset cs) m sp m' sp' (parent_sp cs') (parent_ra cs'))
        (TAIL: is_tail c (Linear.fn_code f)),
      match_states (Linear.State cs f (Vptr sp Int.zero) c ls m)
                  (Machsem.State cs' fb (Vptr sp' Int.zero) (transl_code (make_env (function_bounds f)) c) rs m')
  | match_states_call:
      forall cs f ls m cs' fb rs m' j tf
        (MINJ: Mem.inject j m m')
        (STACKS: match_stacks j m m' cs cs' (Linear.funsig f) (Mem.nextblock m) (Mem.nextblock m'))
        (TRANSL: transf_fundef f = OK tf)
        (FIND: Genv.find_funct_ptr tge fb = Some tf)
        (WTF: wt_fundef f)
        (WTLS: wt_locset ls)
        (AGREGS: agree_regs j ls rs)
        (AGLOCS: agree_callee_save ls (parent_locset cs)),
      match_states (Linear.Callstate cs f ls m)
                  (Machsem.Callstate cs' fb rs m')
  | match_states_return:
      forall cs ls m cs' rs m' j sg 
        (MINJ: Mem.inject j m m')
        (STACKS: match_stacks j m m' cs cs' sg (Mem.nextblock m) (Mem.nextblock m'))
        (WTLS: wt_locset ls)
        (AGREGS: agree_regs j ls rs)
        (AGLOCS: agree_callee_save ls (parent_locset cs)),
      match_states (Linear.Returnstate cs ls m)
                  (Machsem.Returnstate cs' rs m').

Theorem transf_step_correct:
  forall s1 t s2, Linear.step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2', plus Machsem.step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  assert (RED: forall f i c,
          transl_code (make_env (function_bounds f)) (i :: c) = 
          transl_instr (make_env (function_bounds f)) i
                       (transl_code (make_env (function_bounds f)) c)).
    intros. reflexivity.
  induction 1; intros;
  try inv MS;
  try rewrite RED;
  try (generalize (WTF _ (is_tail_in TAIL)); intro WTI);
  try (generalize (function_is_within_bounds f WTF _ (is_tail_in TAIL));
       intro BOUND; simpl in BOUND);
  unfold transl_instr.

  (* Lgetstack *)
  inv WTI. destruct BOUND. unfold undef_getstack; destruct sl.
  (* Lgetstack, local *)
  exploit agree_locals; eauto. intros [v [A B]].
  econstructor; split.
  apply plus_one. apply exec_Mgetstack. 
  eapply index_contains_load_stack; eauto.
  econstructor; eauto with coqlib.
  apply agree_regs_set_reg; auto.
  apply agree_frame_set_reg; auto. simpl; rewrite <- H1. eapply agree_wt_ls; eauto.
  (* Lgetstack, incoming *)
  red in H2. exploit incoming_slot_in_parameters; eauto. intros IN_ARGS.
  inv STACKS. elim (H6 _ IN_ARGS). 
  exploit agree_outgoing. eexact FRM. eapply ARGS; eauto.
  intros [v [A B]].
  econstructor; split.
  apply plus_one. eapply exec_Mgetparam; eauto. 
  rewrite (unfold_transf_function _ _ TRANSL). unfold fn_link_ofs. 
  eapply index_contains_load_stack with (idx := FI_link). eauto. eapply agree_link; eauto. 
  simpl parent_sp.
  change (offset_of_index (make_env (function_bounds f)) (FI_arg z t))
    with (offset_of_index (make_env (function_bounds f0)) (FI_arg z t)).
  eapply index_contains_load_stack with (idx := FI_arg z t). eauto. eauto.
  exploit agree_incoming; eauto. intros EQ; simpl in EQ.
  econstructor; eauto with coqlib. econstructor; eauto.
  apply agree_regs_set_reg. apply agree_regs_set_reg. auto. auto. congruence. 
  eapply agree_frame_set_reg; eauto. eapply agree_frame_set_reg; eauto. 
  apply temporary_within_bounds. simpl; auto. 
  simpl; auto. simpl; rewrite <- H1. eapply agree_wt_ls; eauto.
  (* Lgetstack, outgoing *)
  exploit agree_outgoing; eauto. intros [v [A B]].
  econstructor; split.
  apply plus_one. apply exec_Mgetstack. 
  eapply index_contains_load_stack; eauto.
  econstructor; eauto with coqlib.
  apply agree_regs_set_reg; auto.
  apply agree_frame_set_reg; auto. simpl; rewrite <- H1; eapply agree_wt_ls; eauto.

  (* Lsetstack *)
  inv WTI.
  set (idx := match sl with
              | Local ofs ty => FI_local ofs ty
              | Incoming ofs ty => FI_link (*dummy*)
              | Outgoing ofs ty => FI_arg ofs ty
              end).
  assert (index_valid f idx).
    unfold idx; destruct sl.
    apply index_local_valid; auto.
    red; auto.
    apply index_arg_valid; auto.
  exploit store_index_succeeds; eauto. eapply agree_perm; eauto.
  instantiate (1 := rs0 r). intros [m1' STORE].
  econstructor; split.
  apply plus_one. destruct sl; simpl in H3.
    econstructor. eapply store_stack_succeeds with (idx := idx); eauto. 
    contradiction.
    econstructor. eapply store_stack_succeeds with (idx := idx); eauto. 
  econstructor; eauto with coqlib.
  eapply Mem.store_outside_inject; eauto. 
    intros. exploit agree_inj_unique; eauto. intros [EQ1 EQ2]; subst b' delta.
    rewrite size_type_chunk in H5.
    exploit offset_of_index_disj_stack_data_2; eauto.
    exploit agree_bounds. eauto. apply Mem.perm_cur_max. eauto. 
    omega.
  apply match_stacks_change_mach_mem with m'; auto.
  eauto with mem. eauto with mem. intros. rewrite <- H4; eapply Mem.load_store_other; eauto. left; unfold block; omega.
  apply agree_regs_set_slot. apply agree_regs_undef_setstack; auto. 
  destruct sl.
    eapply agree_frame_set_local. eapply agree_frame_undef_setstack; eauto. auto. auto.
    simpl in H1; rewrite H1; eapply agree_wt_ls; eauto. auto.
    simpl in H3; contradiction.
    eapply agree_frame_set_outgoing. apply agree_frame_undef_setstack; eauto. auto. auto.
    simpl in H1; rewrite H1; eapply agree_wt_ls; eauto. auto.

  (* Lop *)
  assert (Val.has_type v (mreg_type res)).
    inv WTI. simpl in H. inv H. rewrite <- H1. eapply agree_wt_ls; eauto. 
    replace (mreg_type res) with (snd (type_of_operation op)).
    eapply type_of_operation_sound; eauto. 
    rewrite <- H4; auto.
  assert (exists v',
          eval_operation ge (Vptr sp' Int.zero) (transl_op (make_env (function_bounds f)) op) rs0##args m' = Some v'
       /\ val_inject j v v').
  eapply eval_operation_inject; eauto.
  eapply match_stacks_preserves_globals; eauto.
  eapply agree_inj; eauto. eapply agree_reglist; eauto.
  destruct H1 as [v' [A B]].
  econstructor; split. 
  apply plus_one. constructor. 
  instantiate (1 := v'). rewrite <- A. apply eval_operation_preserved. 
  exact symbols_preserved.
  econstructor; eauto with coqlib.
  apply agree_regs_set_reg; auto. apply agree_regs_undef_op; auto. 
  apply agree_frame_set_reg; auto. apply agree_frame_undef_op; auto.

  (* Lload *)
  assert (exists a',
          eval_addressing ge (Vptr sp' Int.zero) (transl_addr (make_env (function_bounds f)) addr) rs0##args = Some a'
       /\ val_inject j a a').
  eapply eval_addressing_inject; eauto. 
  eapply match_stacks_preserves_globals; eauto.
  eapply agree_inj; eauto. eapply agree_reglist; eauto.
  destruct H1 as [a' [A B]].
  exploit Mem.loadv_inject; eauto. intros [v' [C D]].
  econstructor; split. 
  apply plus_one. econstructor. 
  instantiate (1 := a'). rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved.
  eexact C.
  econstructor; eauto with coqlib.
  apply agree_regs_set_reg; auto. apply agree_regs_undef_temps; auto. 
  apply agree_frame_set_reg; auto. apply agree_frame_undef_temps; auto.
  simpl. inv WTI. rewrite H6. 
  inv B; simpl in H0; try discriminate. eapply Mem.load_type; eauto.

  (* Lstore *)
  assert (exists a',
          eval_addressing ge (Vptr sp' Int.zero) (transl_addr (make_env (function_bounds f)) addr) rs0##args = Some a'
       /\ val_inject j a a').
  eapply eval_addressing_inject; eauto. 
  eapply match_stacks_preserves_globals; eauto.
  eapply agree_inj; eauto. eapply agree_reglist; eauto.
  destruct H1 as [a' [A B]].
  exploit Mem.storev_mapped_inject; eauto. intros [m1' [C D]].
  econstructor; split. 
  apply plus_one. econstructor. 
  instantiate (1 := a'). rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved.
  eexact C.
  econstructor; eauto with coqlib.
  eapply match_stacks_parallel_stores. eexact MINJ. eexact B. eauto. eauto. auto. 
  apply agree_regs_undef_temps; auto. 
  apply agree_frame_undef_temps; auto.
  eapply agree_frame_parallel_stores; eauto.

  (* Lcall *)
  exploit find_function_translated; eauto. intros [bf [tf' [A [B C]]]].
  exploit is_tail_transf_function; eauto. intros IST. simpl in IST.
  exploit Asmgenretaddr.return_address_exists. eexact IST.
  intros [ra D].
  econstructor; split.
  apply plus_one. econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto with coqlib.
  simpl; auto.
  intros; red. split.
    generalize (loc_arguments_acceptable _ _ H0). simpl. omega.
    apply Zle_trans with (size_arguments (Linear.funsig f')); auto.
    apply loc_arguments_bounded; auto.
  eapply agree_valid_linear; eauto.
  eapply agree_valid_mach; eauto.
  eapply find_function_well_typed; eauto.
  eapply agree_wt_ls; eauto. 
  simpl; red; auto.

  (* Ltailcall *)
  exploit find_function_translated; eauto. intros [bf [tf' [A [B C]]]].
  exploit function_epilogue_correct; eauto.
  intros [rs1 [m1' [P [Q [R [S [T [U [V W]]]]]]]]].
  econstructor; split.
  eapply plus_right. eexact S. econstructor; eauto.
  replace (find_function_ptr tge ros rs1)
     with (find_function_ptr tge ros rs0). eauto.
  destruct ros; simpl; auto. inv WTI. rewrite V; auto. 
  traceEq.
  econstructor; eauto.
  inv WTI. apply match_stacks_change_sig with (Linear.fn_sig f); auto.
  apply match_stacks_change_bounds with stk sp'.
  apply match_stacks_change_linear_mem with m. 
  apply match_stacks_change_mach_mem with m'0.
  auto. 
  eauto with mem. intros. eapply Mem.perm_free_1; eauto. left; unfold block; omega. 
  intros. rewrite <- H2. eapply Mem.load_free; eauto. left; unfold block; omega.
  eauto with mem. intros. eapply Mem.perm_free_3; eauto. 
  apply Zlt_le_weak. change (Mem.valid_block m' stk). eapply Mem.valid_block_free_1; eauto. eapply agree_valid_linear; eauto. 
  apply Zlt_le_weak. change (Mem.valid_block m1' sp'). eapply Mem.valid_block_free_1; eauto. eapply agree_valid_mach; eauto. 
  eapply find_function_well_typed; eauto.
  apply wt_return_regs; auto. eapply match_stacks_wt_locset; eauto. eapply agree_wt_ls; eauto.

  (* Lbuiltin *)
  exploit external_call_mem_inject; eauto. 
    eapply match_stacks_preserves_globals; eauto.
    eapply agree_reglist; eauto. 
  intros [j' [res' [m1' [A [B [C [D [E [F G]]]]]]]]].
  econstructor; split.
  apply plus_one. econstructor; eauto. 
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto with coqlib.
  eapply match_stack_change_extcall; eauto.
  apply Zlt_le_weak. change (Mem.valid_block m sp0). eapply agree_valid_linear; eauto.
  apply Zlt_le_weak. change (Mem.valid_block m'0 sp'). eapply agree_valid_mach; eauto.
  apply agree_regs_set_reg; auto. apply agree_regs_undef_temps; auto. eapply agree_regs_inject_incr; eauto.
  apply agree_frame_set_reg; auto. apply agree_frame_undef_temps; auto.
  eapply agree_frame_inject_incr; eauto. 
  apply agree_frame_extcall_invariant with m m'0; auto.
  eapply external_call_valid_block; eauto.
  intros. eapply external_call_max_perm; eauto. eapply agree_valid_linear; eauto.
  eapply external_call_valid_block; eauto.
  eapply agree_valid_mach; eauto.
  inv WTI. simpl; rewrite H4. eapply external_call_well_typed; eauto.

  (* Lannot *)
  inv WTI.
  exploit transl_annot_params_correct; eauto.
  intros [vargs' [P Q]]. 
  exploit external_call_mem_inject; eauto. 
    eapply match_stacks_preserves_globals; eauto.
  intros [j' [res' [m1' [A [B [C [D [E [F G]]]]]]]]].
  econstructor; split.
  apply plus_one. econstructor; eauto. 
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto with coqlib.
  eapply match_stack_change_extcall; eauto.
  apply Zlt_le_weak. change (Mem.valid_block m sp0). eapply agree_valid_linear; eauto.
  apply Zlt_le_weak. change (Mem.valid_block m'0 sp'). eapply agree_valid_mach; eauto.
  eapply agree_regs_inject_incr; eauto.
  eapply agree_frame_inject_incr; eauto. 
  apply agree_frame_extcall_invariant with m m'0; auto.
  eapply external_call_valid_block; eauto.
  intros. eapply external_call_max_perm; eauto. eapply agree_valid_linear; eauto.
  eapply external_call_valid_block; eauto.
  eapply agree_valid_mach; eauto.

  (* Llabel *)
  econstructor; split.
  apply plus_one; apply exec_Mlabel.
  econstructor; eauto with coqlib.

  (* Lgoto *)
  econstructor; split.
  apply plus_one; eapply exec_Mgoto; eauto.
  apply transl_find_label; eauto.
  econstructor; eauto. 
  eapply find_label_tail; eauto.

  (* Lcond, true *)
  econstructor; split.
  apply plus_one. eapply exec_Mcond_true; eauto.
  eapply eval_condition_inject; eauto. eapply agree_reglist; eauto.
  eapply transl_find_label; eauto. 
  econstructor; eauto with coqlib.
  apply agree_regs_undef_temps; auto.
  apply agree_frame_undef_temps; auto.
  eapply find_label_tail; eauto.

  (* Lcond, false *)
  econstructor; split.
  apply plus_one. eapply exec_Mcond_false; eauto.
  eapply eval_condition_inject; eauto. eapply agree_reglist; eauto.
  econstructor; eauto with coqlib.
  apply agree_regs_undef_temps; auto.
  apply agree_frame_undef_temps; auto.

  (* Ljumptable *)
  assert (rs0 arg = Vint n).
    generalize (AGREGS arg). rewrite H. intro IJ; inv IJ; auto.
  econstructor; split.
  apply plus_one; eapply exec_Mjumptable; eauto. 
  apply transl_find_label; eauto.
  econstructor; eauto.
  apply agree_regs_undef_temps; auto.
  apply agree_frame_undef_temps; auto.
  eapply find_label_tail; eauto.

  (* Lreturn *)
  exploit function_epilogue_correct; eauto.
  intros [rs1 [m1' [P [Q [R [S [T [U [V W]]]]]]]]].
  econstructor; split.
  eapply plus_right. eexact S. econstructor; eauto.
  traceEq.
  econstructor; eauto.
  apply match_stacks_change_bounds with stk sp'.
  apply match_stacks_change_linear_mem with m. 
  apply match_stacks_change_mach_mem with m'0.
  eauto. 
  eauto with mem. intros. eapply Mem.perm_free_1; eauto. left; unfold block; omega. 
  intros. rewrite <- H1. eapply Mem.load_free; eauto. left; unfold block; omega.
  eauto with mem. intros. eapply Mem.perm_free_3; eauto. 
  apply Zlt_le_weak. change (Mem.valid_block m' stk). eapply Mem.valid_block_free_1; eauto. eapply agree_valid_linear; eauto. 
  apply Zlt_le_weak. change (Mem.valid_block m1' sp'). eapply Mem.valid_block_free_1; eauto. eapply agree_valid_mach; eauto. 
  apply wt_return_regs; auto. eapply match_stacks_wt_locset; eauto. eapply agree_wt_ls; eauto.

  (* internal function *)
  revert TRANSL. unfold transf_fundef, transf_partial_fundef.
  caseEq (transf_function f); simpl; try congruence.
  intros tfn TRANSL EQ. inversion EQ; clear EQ; subst tf.
  inversion WTF as [|f' WTFN]. subst f'.
  exploit function_prologue_correct; eauto.
  eapply match_stacks_type_sp; eauto. 
  eapply match_stacks_type_retaddr; eauto.
  intros [j' [rs' [m2' [sp' [m3' [m4' [m5' [A [B [C [D [E [F [G [J [K L]]]]]]]]]]]]]]]].
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  rewrite (unfold_transf_function _ _ TRANSL). unfold fn_code. unfold transl_body. 
  eexact D. traceEq.
  generalize (Mem.alloc_result _ _ _ _ _ H). intro SP_EQ. 
  generalize (Mem.alloc_result _ _ _ _ _ A). intro SP'_EQ.
  econstructor; eauto. 
  apply match_stacks_change_mach_mem with m'0.
  apply match_stacks_change_linear_mem with m.
  rewrite SP_EQ; rewrite SP'_EQ.
  eapply match_stacks_change_meminj; eauto. omega.
  eauto with mem. intros. exploit Mem.perm_alloc_inv. eexact H. eauto. 
  rewrite zeq_false. auto. omega. 
  intros. eapply stores_in_frame_valid; eauto with mem. 
  intros. eapply stores_in_frame_perm; eauto with mem.
  intros. rewrite <- H1. transitivity (Mem.load chunk m2' b ofs). eapply stores_in_frame_contents; eauto.
  eapply Mem.load_alloc_unchanged; eauto. red. congruence.
  auto with coqlib.

  (* external function *)
  simpl in TRANSL. inversion TRANSL; subst tf.
  inversion WTF. subst ef0.
  exploit transl_external_arguments; eauto. intros [vl [ARGS VINJ]].
  exploit external_call_mem_inject; eauto. 
  eapply match_stacks_preserves_globals; eauto.
  intros [j' [res' [m1' [A [B [C [D [E [F G]]]]]]]]].
  econstructor; split.
  apply plus_one. eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.
  apply match_stacks_change_bounds with (Mem.nextblock m) (Mem.nextblock m'0).
  eapply match_stack_change_extcall; eauto. omega. omega.
  exploit external_call_valid_block. eexact H. 
    instantiate (1 := (Mem.nextblock m - 1)). red; omega. unfold Mem.valid_block; omega.
  exploit external_call_valid_block. eexact A. 
    instantiate (1 := (Mem.nextblock m'0 - 1)). red; omega. unfold Mem.valid_block; omega.
  apply wt_setloc; auto. simpl. rewrite loc_result_type.
  change (Val.has_type res (proj_sig_res (ef_sig ef))). 
  eapply external_call_well_typed; eauto. 
  apply agree_regs_set_reg; auto. apply agree_regs_inject_incr with j; auto. 
  apply agree_callee_save_set_result; auto. 

  (* return *)
  inv STACKS. simpl in AGLOCS.  
  econstructor; split.
  apply plus_one. apply exec_return. 
  econstructor; eauto.
  apply agree_frame_return with rs0; auto. 
Qed.

Lemma transf_initial_states:
  forall st1, Linear.initial_state prog st1 ->
  exists st2, Machsem.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  econstructor; split.
  econstructor. 
  eapply Genv.init_mem_transf_partial; eauto.
  rewrite (transform_partial_program_main _ _ TRANSF). 
  rewrite symbols_preserved. eauto.
  econstructor; eauto.
  eapply Genv.initmem_inject; eauto.
  apply match_stacks_empty with (Mem.nextblock m0). omega. omega.
  constructor.
    apply Mem.nextblock_pos.
    intros. unfold Mem.flat_inj. apply zlt_true; auto.
    unfold Mem.flat_inj; intros. destruct (zlt b1 (Mem.nextblock m0)); congruence.
    intros. change (Mem.valid_block m0 b0). eapply Genv.find_symbol_not_fresh; eauto.
    intros. change (Mem.valid_block m0 b0). eapply Genv.find_var_info_not_fresh; eauto.
  rewrite H3. red; intros. contradiction.
  eapply Genv.find_funct_ptr_prop. eexact wt_prog. 
  fold ge0; eauto.
  apply wt_init.
  unfold Locmap.init. red; intros; auto.
  unfold parent_locset. red; auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> Linear.final_state st1 r -> Machsem.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS.
  constructor.
  set (rres := loc_result {| sig_args := nil; sig_res := Some Tint |}) in *.
  generalize (AGREGS rres). rewrite H1. intros IJ; inv IJ. auto.
Qed.

Theorem transf_program_correct:
  forward_simulation (Linear.semantics prog) (Machsem.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  eexact symbols_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact transf_step_correct. 
Qed.

End PRESERVATION.
