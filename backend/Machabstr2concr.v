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

(** Simulation between the two semantics for the Mach language. *)

Require Import Axioms.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import Machtyping.
Require Import Machabstr.
Require Import Machconcr.
Require Import Conventions.
Require Import Asmgenretaddr.

(** Two semantics were defined for the Mach intermediate language:
- The concrete semantics (file [Mach]), where the whole activation
  record resides in memory and the [Mgetstack], [Msetstack] and
  [Mgetparent] are interpreted as [sp]-relative memory accesses.
- The abstract semantics (file [Machabstr]), where the activation
  record is split in two parts: the Cminor stack data, resident in
  memory, and the frame information, residing not in memory but
  in additional evaluation environments.

  In this file, we show a simulation result between these
  semantics: if a program executes with some behaviour [beh] in the
  abstract semantics, it also executes with the same behaviour in
  the concrete semantics.  This result bridges the correctness proof
  in file [Stackingproof] (which uses the abstract Mach semantics
  as output) and that in file [Asmgenproof] (which uses the concrete
  Mach semantics as input).
*)

Remark size_type_chunk:
  forall ty, size_chunk (chunk_of_type ty) = AST.typesize ty.
Proof.
  destruct ty; reflexivity.
Qed.

(** * Agreement between frames and memory-resident activation records *)

(** ** Agreement for one frame *)

Section FRAME_MATCH.

Variable f: function.
Hypothesis wt_f: wt_function f.

(** The core idea of the simulation proof is that for all active
  functions, the memory-allocated activation record, in the concrete 
  semantics, contains the same data as the Cminor stack block
  (at positive offsets) and the frame of the function (at negative
  offsets) in the abstract semantics

  This intuition (activation record = Cminor stack data + frame)
  is formalized by the following predicate [frame_match fr sp base mm ms].
  [fr] is a frame and [mm] the current memory state in the abstract
  semantics. [ms] is the current memory state in the concrete semantics.
  The stack pointer is [Vptr sp base] in both semantics. *)

Record frame_match (fr: frame)
                   (sp: block) (base: int) 
                   (mm ms: mem) : Prop :=
  mk_frame_match {
    fm_valid_1: 
      Mem.valid_block mm sp;
    fm_valid_2: 
      Mem.valid_block ms sp;
    fm_base:
      base = Int.repr(- f.(fn_framesize));
    fm_stackdata_pos: 
      Mem.low_bound mm sp = 0;
    fm_write_perm:
      Mem.range_perm ms sp (-f.(fn_framesize)) 0 Freeable;
    fm_contents_match:
      forall ty ofs,
      -f.(fn_framesize) <= ofs -> ofs + AST.typesize ty <= 0 -> (4 | ofs) ->
      exists v,
        Mem.load (chunk_of_type ty) ms sp ofs = Some v
        /\ Val.lessdef (fr ty ofs) v
  }.

(** The following two innocuous-looking lemmas are the key results
  showing that [sp]-relative memory accesses in the concrete
  semantics behave like the direct frame accesses in the abstract
  semantics.  First, a value [v] that has type [ty] is preserved
  when stored in memory with chunk [chunk_of_type ty], then read
  back with the same chunk.  The typing hypothesis is crucial here:
  for instance, a float value is not preserved when stored
  and loaded with chunk [Mint32]. *)

Lemma load_result_ty:
  forall v ty,
  Val.has_type v ty -> Val.load_result (chunk_of_type ty) v = v.
Proof.
  destruct v; destruct ty; simpl; contradiction || reflexivity.
Qed.

(** Second, computations of [sp]-relative offsets using machine
  arithmetic (as done in the concrete semantics) never overflows
  and behaves identically to the offset computations using exact
  arithmetic (as done in the abstract semantics). *)

Lemma int_add_no_overflow:
  forall x y,
  Int.min_signed <= Int.signed x + Int.signed y <= Int.max_signed ->
  Int.signed (Int.add x y) = Int.signed x + Int.signed y.
Proof.
  intros. rewrite Int.add_signed. rewrite Int.signed_repr. auto. auto.
Qed.

(** Given matching frames and activation records, loading from the
  activation record (in the concrete semantics) behaves identically
  to reading the corresponding slot from the frame
  (in the abstract semantics).  *)

Lemma frame_match_load_stack:
  forall fr sp base mm ms ty ofs,
  frame_match fr sp base mm ms ->
  0 <= Int.signed ofs /\ Int.signed ofs + AST.typesize ty <= f.(fn_framesize) ->
  (4 | Int.signed ofs) ->
  exists v,
     load_stack ms (Vptr sp base) ty ofs = Some v
  /\ Val.lessdef (fr ty (Int.signed ofs - f.(fn_framesize))) v.
Proof.
  intros. inv H. inv wt_f.
  unfold load_stack, Val.add, Mem.loadv.
  replace (Int.signed (Int.add (Int.repr (- fn_framesize f)) ofs))
     with (Int.signed ofs - fn_framesize f).
  apply fm_contents_match0. omega. omega.
  apply Zdivide_minus_l; auto. 
  assert (Int.signed (Int.repr (-fn_framesize f)) = -fn_framesize f).
    apply Int.signed_repr.
    assert (0 <= Int.max_signed). compute; congruence. omega.
  rewrite int_add_no_overflow. rewrite H. omega.
  rewrite H. split. omega.
  apply Zle_trans with 0. generalize (AST.typesize_pos ty). omega. 
  compute; congruence.
Qed.

Lemma frame_match_get_slot:
  forall fr sp base mm ms ty ofs v,
  frame_match fr sp base mm ms ->
  get_slot f fr ty (Int.signed ofs) v ->
  exists v', load_stack ms (Vptr sp base) ty ofs = Some v' /\ Val.lessdef v v'.
Proof.
  intros. inv H0. inv H1. eapply frame_match_load_stack; eauto.
Qed.

(** Assigning a value to a frame slot (in the abstract semantics)
  corresponds to storing this value in the activation record
  (in the concrete semantics).  Moreover, agreement between frames
  and activation records is preserved. *)

Lemma frame_match_store_stack:
  forall fr sp base mm ms ty ofs v v',
  frame_match fr sp base mm ms ->
  0 <= Int.signed ofs -> Int.signed ofs + AST.typesize ty <= f.(fn_framesize) ->
  (4 | Int.signed ofs) ->
  Val.has_type v ty ->
  Val.lessdef v v' ->
  Mem.extends mm ms ->
  exists ms',
    store_stack ms (Vptr sp base) ty ofs v' = Some ms' /\
    frame_match (update ty (Int.signed ofs - f.(fn_framesize)) v fr) sp base mm ms' /\
    Mem.extends mm ms'.
Proof.
  intros. inv H. inv wt_f.
  unfold store_stack, Val.add, Mem.storev.
  assert (Int.signed (Int.add (Int.repr (- fn_framesize f)) ofs) =
          Int.signed ofs - fn_framesize f).
  assert (Int.signed (Int.repr (-fn_framesize f)) = -fn_framesize f).
    apply Int.signed_repr. 
    assert (0 <= Int.max_signed). compute; congruence. omega.
  rewrite int_add_no_overflow. rewrite H. omega.
  rewrite H. split. omega.
  apply Zle_trans with 0. generalize (AST.typesize_pos ty). omega. 
  compute; congruence.
  rewrite H.
  assert ({ ms' | Mem.store (chunk_of_type ty) ms sp (Int.signed ofs - fn_framesize f) v' = Some ms'}).
    apply Mem.valid_access_store. constructor.
    apply Mem.range_perm_implies with Freeable; auto with mem.
    red; intros; apply fm_write_perm0.
    rewrite <- size_type_chunk in H1.
    generalize (size_chunk_pos (chunk_of_type ty)).
    omega.
    replace (align_chunk (chunk_of_type ty)) with 4.
    apply Zdivide_minus_l; auto.
    destruct ty; auto.
  destruct X as [ms' STORE].
  exists ms'. 
  split. exact STORE.
  (* frame match *)
  split. constructor.
  (* valid *)
  eauto with mem.
  eauto with mem.
  (* base *)
  auto.
  (* stackdata_pos *)
  auto.
  (* write_perm *)
  red; intros; eauto with mem.
  (* contents *)
  intros. 
  exploit fm_contents_match0; eauto. intros [v0 [LOAD0 VLD0]]. 
  assert (exists v1, Mem.load (chunk_of_type ty0) ms' sp ofs0 = Some v1).
    apply Mem.valid_access_load; eauto with mem. 
  destruct H9 as [v1 LOAD1].
  exists v1; split; auto.
  unfold update. 
  destruct (zeq (Int.signed ofs - fn_framesize f) ofs0). subst ofs0.
    destruct (typ_eq ty ty0). subst ty0.
    (* same *)
    inv H4. 
    assert (Some v1 = Some (Val.load_result (chunk_of_type ty) v')).
      rewrite <- LOAD1. eapply Mem.load_store_same; eauto.
      destruct ty; auto.
    inv H4. rewrite load_result_ty; auto. 
    auto.
    (* mismatch *)
    auto.
    destruct (zle (ofs0 + AST.typesize ty0) (Int.signed ofs - fn_framesize f)).
    (* disjoint *)
    assert (Some v1 = Some v0).
      rewrite <- LOAD0; rewrite <- LOAD1. 
      eapply Mem.load_store_other; eauto.
      right; left. rewrite size_type_chunk; auto.
    inv H9. auto.
    destruct (zle (Int.signed ofs - fn_framesize f + AST.typesize ty)).
    assert (Some v1 = Some v0).
      rewrite <- LOAD0; rewrite <- LOAD1. 
      eapply Mem.load_store_other; eauto.
      right; right. rewrite size_type_chunk; auto.
    inv H9. auto.
    (* overlap *)
    auto.
  (* extends *)
  eapply Mem.store_outside_extends; eauto.
  left. rewrite fm_stackdata_pos0. 
  rewrite size_type_chunk. omega.
Qed.

Lemma frame_match_set_slot:
  forall fr sp base mm ms ty ofs v fr' v',
  frame_match fr sp base mm ms ->
  set_slot f fr ty (Int.signed ofs) v fr' ->
  Val.has_type v ty ->
  Val.lessdef v v' ->
  Mem.extends mm ms ->
  exists ms',
    store_stack ms (Vptr sp base) ty ofs v' = Some ms' /\
    frame_match fr' sp base mm ms' /\
    Mem.extends mm ms'.
Proof.
  intros. inv H0. inv H4. eapply frame_match_store_stack; eauto. 
Qed.

(** Agreement is preserved by stores within blocks other than the
  one pointed to by [sp]. *)

Lemma frame_match_store_other:
  forall fr sp base mm ms chunk b ofs v ms',
  frame_match fr sp base mm ms ->
  Mem.store chunk ms b ofs v = Some ms' ->
  sp <> b ->
  frame_match fr sp base mm ms'.
Proof.
  intros. inv H. constructor; auto.
  eauto with mem.
  red; intros; eauto with mem. 
  intros. exploit fm_contents_match0; eauto. intros [v0 [LOAD LD]].
  exists v0; split; auto. rewrite <- LOAD. eapply Mem.load_store_other; eauto.
Qed.

(** Agreement is preserved by parallel stores in the Machabstr
  and the Machconcr semantics. *)

Lemma frame_match_store:
  forall fr sp base mm ms chunk b ofs v mm' v' ms',
  frame_match fr sp base mm ms ->
  Mem.store chunk mm b ofs v = Some mm' ->
  Mem.store chunk ms b ofs v' = Some ms' ->
  frame_match fr sp base mm' ms'.
Proof.
  intros. inv H. constructor; auto.
  eauto with mem.
  eauto with mem.
  rewrite (Mem.bounds_store _ _ _ _ _ _ H0). auto.
  red; intros; eauto with mem.
  intros. exploit fm_contents_match0; eauto. intros [v0 [LOAD LD]].
  exists v0; split; auto. rewrite <- LOAD. eapply Mem.load_store_other; eauto.
  destruct (zeq sp b); auto. subst b. right. 
  rewrite size_type_chunk. 
  assert (Mem.valid_access mm chunk sp ofs Nonempty) by eauto with mem.
  exploit Mem.store_valid_access_3. eexact H0. intro. 
  exploit Mem.valid_access_in_bounds. eauto. rewrite fm_stackdata_pos0. 
  omega.
Qed.

(** Memory allocation of the Cminor stack data block (in the abstract
  semantics) and of the whole activation record (in the concrete
  semantics) return memory states that agree according to [frame_match].
  Moreover, [frame_match] relations over already allocated blocks
  remain true. *)

Lemma frame_match_new:
  forall mm ms mm' ms' sp,
  Mem.alloc mm 0 f.(fn_stacksize) = (mm', sp) ->
  Mem.alloc ms (- f.(fn_framesize)) f.(fn_stacksize) = (ms', sp) ->
  frame_match empty_frame sp (Int.repr (-f.(fn_framesize))) mm' ms'.
Proof.
  intros. 
  inv wt_f.
  constructor; simpl; eauto with mem.
  rewrite (Mem.bounds_alloc_same _ _ _ _ _ H). auto.
  red; intros. eapply Mem.perm_alloc_2; eauto. omega.
  intros. exists Vundef; split.
  eapply Mem.load_alloc_same'; eauto. 
  rewrite size_type_chunk. omega.
  replace (align_chunk (chunk_of_type ty)) with 4; auto.
  destruct ty; auto.
  unfold empty_frame. auto.
Qed.

Lemma frame_match_alloc:
  forall mm ms fr sp base lom him los his mm' ms' b,
  frame_match fr sp base mm ms ->
  Mem.alloc mm lom him = (mm', b) ->
  Mem.alloc ms los his = (ms', b) ->
  frame_match fr sp base mm' ms'.
Proof.
  intros. inversion H.
  assert (sp <> b). 
    apply Mem.valid_not_valid_diff with ms; eauto with mem.
  constructor; auto.
  eauto with mem.
  eauto with mem.
  rewrite (Mem.bounds_alloc_other _ _ _ _ _ H0); auto.
  red; intros; eauto with mem.
  intros. exploit fm_contents_match0; eauto. intros [v [LOAD LD]].
  exists v; split; auto. eapply Mem.load_alloc_other; eauto. 
Qed.

(** [frame_match] relations are preserved by freeing a block
  other than the one pointed to by [sp]. *)

Lemma frame_match_free:
  forall fr sp base mm ms b lom him los his mm' ms',
  frame_match fr sp base mm ms ->
  sp <> b ->
  Mem.free mm b lom him = Some mm' ->
  Mem.free ms b los his = Some ms' ->
  frame_match fr sp base mm' ms'.
Proof.
  intros. inversion H. constructor; auto.
  eauto with mem.
  eauto with mem.
  rewrite (Mem.bounds_free _ _ _ _ _ H1). auto.
  red; intros; eauto with mem. 
  intros. rewrite (Mem.load_free _ _ _ _ _ H2); auto.
Qed.

Lemma frame_match_delete:
  forall fr sp base mm ms mm',
  frame_match fr sp base mm ms ->
  Mem.free mm sp 0 f.(fn_stacksize) = Some mm' ->
  Mem.extends mm ms ->
  exists ms',
  Mem.free ms sp (-f.(fn_framesize)) f.(fn_stacksize) = Some ms'
  /\ Mem.extends mm' ms'.
Proof.
  intros. inversion H.
  assert (Mem.range_perm mm sp 0 (fn_stacksize f) Freeable).
    eapply Mem.free_range_perm; eauto. 
  assert ({ ms' | Mem.free ms sp (-f.(fn_framesize)) f.(fn_stacksize) = Some ms' }).
  apply Mem.range_perm_free. 
  red; intros. destruct (zlt ofs 0). 
  apply fm_write_perm0. omega. 
  eapply Mem.perm_extends; eauto. apply H2. omega.
  destruct X as [ms' FREE]. exists ms'; split; auto.
  eapply Mem.free_right_extends; eauto. 
  eapply Mem.free_left_extends; eauto.
  intros; red; intros.
  exploit Mem.perm_in_bounds; eauto. 
  rewrite (Mem.bounds_free _ _ _ _ _ H0). rewrite fm_stackdata_pos0; intro. 
  exploit Mem.perm_free_2. eexact H0. instantiate (1 := ofs); omega. eauto. 
  auto.
Qed.

(** [frame_match] is preserved by external calls. *)

Lemma frame_match_external_call:
  forall (ge: genv) fr sp base mm ms mm' ms' ef vargs vres t vargs' vres',
  frame_match fr sp base mm ms ->
  Mem.extends mm ms ->
  external_call ef ge vargs mm t vres mm' ->
  Mem.extends mm' ms' ->
  external_call ef ge vargs' ms t vres' ms' ->
  mem_unchanged_on (loc_out_of_bounds mm) ms ms' ->
  frame_match fr sp base mm' ms'.
Proof.
  intros. destruct H4 as [A B]. inversion H. constructor.
  eapply external_call_valid_block; eauto.
  eapply external_call_valid_block; eauto.
  auto.
  rewrite (external_call_bounds _ _ _ _ _ _ H1); auto.
  red; intros. apply A; auto. red. omega.
  intros. exploit fm_contents_match0; eauto. intros [v [C D]].
  exists v; split; auto.
  apply B; auto. 
  rewrite size_type_chunk; intros; red. omega.
Qed.

End FRAME_MATCH.

(** ** Accounting for the return address and back link *)

Section EXTEND_FRAME.

Variable f: function.
Hypothesis wt_f: wt_function f.
Variable cs: list Machconcr.stackframe.

Definition extend_frame (fr: frame) : frame :=
  update Tint (Int.signed f.(fn_retaddr_ofs) - f.(fn_framesize)) (parent_ra cs)
    (update Tint (Int.signed f.(fn_link_ofs) - f.(fn_framesize)) (parent_sp cs)
      fr).

Lemma get_slot_extends:
  forall fr ty ofs v,
  get_slot f fr ty ofs v ->
  get_slot f (extend_frame fr) ty ofs v.
Proof.
  intros. inv H. constructor. auto.
  inv H0. inv wt_f. generalize (AST.typesize_pos ty); intro.
  unfold extend_frame. rewrite update_other. rewrite update_other. auto.
  simpl; omega. simpl; omega.
Qed.

Lemma update_commut:
  forall ty1 ofs1 v1 ty2 ofs2 v2 fr,
  ofs1 + AST.typesize ty1 <= ofs2 \/
  ofs2 + AST.typesize ty2 <= ofs1 ->
  update ty1 ofs1 v1 (update ty2 ofs2 v2 fr) =
  update ty2 ofs2 v2 (update ty1 ofs1 v1 fr).
Proof.
  intros. unfold frame.
  apply extensionality. intro ty. apply extensionality. intro ofs.
  generalize (AST.typesize_pos ty1).
  generalize (AST.typesize_pos ty2).
  generalize (AST.typesize_pos ty); intros.
  unfold update.
  set (sz1 := AST.typesize ty1) in *.
  set (sz2 := AST.typesize ty2) in *.
  set (sz := AST.typesize ty) in *.
  destruct (zeq ofs1 ofs).
  rewrite zeq_false. 
  destruct (zle (ofs + sz) ofs2). auto.
  destruct (zle (ofs2 + sz2) ofs). auto.
  destruct (typ_eq ty1 ty); auto.
  replace sz with sz1 in z. omegaContradiction. unfold sz1, sz; congruence.
  omega.

  destruct (zle (ofs + sz) ofs1).
  auto.
  destruct (zle (ofs1 + sz1) ofs).
  auto.

  destruct (zeq ofs2 ofs).
  destruct (typ_eq ty2 ty); auto.
  replace sz with sz2 in z. omegaContradiction. unfold sz2, sz; congruence.
  destruct (zle (ofs + sz) ofs2); auto.
  destruct (zle (ofs2 + sz2) ofs); auto.
Qed.

Lemma set_slot_extends:
  forall fr ty ofs v fr',
  set_slot f fr ty ofs v fr' ->
  set_slot f (extend_frame fr) ty ofs v (extend_frame fr').
Proof.
  intros. inv H. constructor. auto.
  inv H0. inv wt_f. generalize (AST.typesize_pos ty); intro.
  unfold extend_frame. 
  rewrite (update_commut ty). rewrite (update_commut ty). auto.
  simpl. omega. 
  simpl. omega.
Qed.

Definition is_pointer_or_int (v: val) : Prop :=
  match v with
  | Vint _ => True
  | Vptr _ _ => True
  | _ => False
  end.

Remark is_pointer_has_type:
  forall v, is_pointer_or_int v -> Val.has_type v Tint.
Proof.
  intros; destruct v; elim H; exact I. 
Qed.

Lemma frame_match_load_stack_pointer:
  forall fr sp base mm ms ty ofs,
  frame_match f fr sp base mm ms ->
  0 <= Int.signed ofs /\ Int.signed ofs + AST.typesize ty <= f.(fn_framesize) ->
  (4 | Int.signed ofs) ->
  is_pointer_or_int (fr ty (Int.signed ofs - f.(fn_framesize))) ->
  load_stack ms (Vptr sp base) ty ofs = Some (fr ty (Int.signed ofs - f.(fn_framesize))).
Proof.
  intros. exploit frame_match_load_stack; eauto. 
  intros [v [LOAD LD]]. 
  inv LD. auto. rewrite <- H4 in H2. elim H2.
Qed.

Lemma frame_match_load_link:
  forall fr sp base mm ms,
  frame_match f (extend_frame fr) sp base mm ms ->
  is_pointer_or_int (parent_sp cs) ->
  load_stack ms (Vptr sp base) Tint f.(fn_link_ofs) = Some(parent_sp cs).
Proof.
  intros. inversion wt_f.
  assert (parent_sp cs =
    extend_frame fr Tint (Int.signed f.(fn_link_ofs) - f.(fn_framesize))).
  unfold extend_frame. rewrite update_other. rewrite update_same. auto. 
  simpl. omega.
  rewrite H1; eapply frame_match_load_stack_pointer; eauto.
  rewrite <- H1; auto.
Qed.

Lemma frame_match_load_retaddr:
  forall fr sp base mm ms,
  frame_match f (extend_frame fr) sp base mm ms ->
  is_pointer_or_int (parent_ra cs) ->
  load_stack ms (Vptr sp base) Tint f.(fn_retaddr_ofs) = Some(parent_ra cs).
Proof.
  intros. inversion wt_f.
  assert (parent_ra cs =
    extend_frame fr Tint (Int.signed f.(fn_retaddr_ofs) - f.(fn_framesize))).
  unfold extend_frame. rewrite update_same. auto. 
  rewrite H1; eapply frame_match_load_stack_pointer; eauto.
  rewrite <- H1; auto.
Qed.

Lemma frame_match_function_entry:
  forall mm ms mm' sp,
  Mem.extends mm ms ->
  Mem.alloc mm 0 f.(fn_stacksize) = (mm', sp) ->
  is_pointer_or_int (parent_sp cs) ->
  is_pointer_or_int (parent_ra cs) ->
  let base := Int.repr (-f.(fn_framesize)) in
  exists ms1, exists ms2, exists ms3,
  Mem.alloc ms (- f.(fn_framesize)) f.(fn_stacksize) = (ms1, sp) /\
  store_stack ms1 (Vptr sp base) Tint f.(fn_link_ofs) (parent_sp cs) = Some ms2 /\
  store_stack ms2 (Vptr sp base) Tint f.(fn_retaddr_ofs) (parent_ra cs) = Some ms3 /\
  frame_match f (extend_frame empty_frame) sp base mm' ms3 /\
  Mem.extends mm' ms3.
Proof.
  intros. inversion wt_f.
  exploit Mem.alloc_extends; eauto.
  instantiate (1 := -f.(fn_framesize)). omega.
  instantiate (1 := f.(fn_stacksize)). omega.
  intros [ms1 [A EXT0]].
  exploit frame_match_new; eauto. fold base. intros FM0.
  exploit frame_match_store_stack. eauto. eexact FM0. 
  instantiate (1 := fn_link_ofs f); omega.
  instantiate (1 := Tint). simpl; omega.
  auto. apply is_pointer_has_type. eexact H1. constructor. auto.
  intros [ms2 [STORE1 [FM1 EXT1]]].
  exploit frame_match_store_stack. eauto. eexact FM1. 
  instantiate (1 := fn_retaddr_ofs f); omega.
  instantiate (1 := Tint). simpl; omega.
  auto. apply is_pointer_has_type. eexact H2. constructor. auto.
  intros [ms3 [STORE2 [FM2 EXT2]]].
  exists ms1; exists ms2; exists ms3; auto.
Qed.

End EXTEND_FRAME.

(** ** The ``less defined than'' relation between register states. *)

Definition regset_lessdef (rs1 rs2: regset) : Prop :=
  forall r, Val.lessdef (rs1 r) (rs2 r).

Lemma regset_lessdef_list:
  forall rs1 rs2, regset_lessdef rs1 rs2 ->
  forall rl, Val.lessdef_list (rs1##rl) (rs2##rl).
Proof.
  induction rl; simpl.
  constructor.
  constructor; auto.
Qed.

Lemma regset_lessdef_set:
  forall rs1 rs2 r v1 v2,
  regset_lessdef rs1 rs2 -> Val.lessdef v1 v2 ->
  regset_lessdef (rs1#r <- v1) (rs2#r <- v2).
Proof.
  intros; red; intros. unfold Regmap.set.
  destruct (RegEq.eq r0 r); auto. 
Qed.

Lemma regset_lessdef_undef_temps:
  forall rs1 rs2,
  regset_lessdef rs1 rs2 -> regset_lessdef (undef_temps rs1) (undef_temps rs2).
Proof.
  unfold undef_temps. 
  generalize (int_temporaries ++ float_temporaries).
  induction l; simpl; intros. auto. apply IHl. apply regset_lessdef_set; auto.
Qed.

Lemma regset_lessdef_undef_op:
  forall op rs1 rs2,
  regset_lessdef rs1 rs2 -> regset_lessdef (undef_op op rs1) (undef_op op rs2).
Proof.
  intros. set (D := regset_lessdef_undef_temps _ _ H). 
  destruct op; simpl; auto.
Qed.

Lemma regset_lessdef_find_function_ptr:
  forall ge ros rs1 rs2 fb,
  find_function_ptr ge ros rs1 = Some fb ->
  regset_lessdef rs1 rs2 ->
  find_function_ptr ge ros rs2 = Some fb.
Proof.
  unfold find_function_ptr; intros; destruct ros; simpl in *.
  generalize (H0 m); intro LD; inv LD. auto. rewrite <- H2 in H. congruence.
  auto.
Qed.

(** ** Invariant for stacks *)

Section SIMULATION.

Variable p: program.
Let ge := Genv.globalenv p.

(** The [match_stacks] predicate relates a Machabstr call stack
  with the corresponding Machconcr stack.  In addition to enforcing
  the [frame_match] predicate for each stack frame, we also enforce:
- Proper chaining of activation record on the Machconcr side.
- Preservation of the return address stored at the bottom of the
  activation record.
- Separation between the memory blocks holding the activation records:
  their addresses increase strictly from caller to callee.
*)

Definition stack_below (ts: list Machconcr.stackframe) (b: block) : Prop :=
  match parent_sp ts with
  | Vptr sp base' => sp < b
  | _ => False
  end.

Inductive match_stacks: 
      list Machabstr.stackframe -> list Machconcr.stackframe ->
      mem -> mem -> Prop :=
  | match_stacks_nil: forall mm ms,
      match_stacks nil nil mm ms
  | match_stacks_cons: forall fb sp base c fr s f ra ts mm ms,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      wt_function f ->
      frame_match f (extend_frame f ts fr) sp base mm ms ->
      stack_below ts sp ->
      is_pointer_or_int ra ->
      match_stacks s ts mm ms ->
      match_stacks (Machabstr.Stackframe f (Vptr sp base) c fr :: s)
                   (Machconcr.Stackframe fb (Vptr sp base) ra c :: ts)
                   mm ms.

Lemma match_stacks_parent_sp_pointer:
  forall s ts mm ms,
  match_stacks s ts mm ms -> is_pointer_or_int (Machconcr.parent_sp ts).
Proof.
  induction 1; simpl; auto.
Qed.

Lemma match_stacks_parent_ra_pointer:
  forall s ts mm ms,
  match_stacks s ts mm ms -> is_pointer_or_int (Machconcr.parent_ra ts).
Proof.
  induction 1; simpl; auto.
Qed.

(** If [match_stacks] holds, a lookup in the parent frame in the
  Machabstr semantics corresponds to two memory loads in the
  Machconcr semantics, one to load the pointer to the parent's
  activation record, the second to read within this record. *)

Lemma match_stacks_get_parent:
  forall s ts mm ms ty ofs v,
  match_stacks s ts mm ms ->
  get_slot (parent_function s) (parent_frame s) ty (Int.signed ofs) v ->
  exists v',
     load_stack ms (Machconcr.parent_sp ts) ty ofs = Some v'
  /\ Val.lessdef v v'.
Proof.
  intros. inv H; simpl in H0. 
  inv H0. inv H. simpl in H1. elimtype False. generalize (AST.typesize_pos ty). omega.
  simpl. eapply frame_match_get_slot; eauto.
  eapply get_slot_extends; eauto. 
Qed.

(** Preservation of the [match_stacks] invariant
    by various kinds of memory operations. *)

Remark stack_below_trans:
  forall ts b b', 
  stack_below ts b -> b <= b' -> stack_below ts b'.
Proof.
  unfold stack_below; intros. 
  destruct (parent_sp ts); auto. omega.
Qed.

Lemma match_stacks_store_other:
  forall s ts ms mm,
  match_stacks s ts mm ms ->
  forall chunk b ofs v ms',
  Mem.store chunk ms b ofs v = Some ms' ->
  stack_below ts b ->
  match_stacks s ts mm ms'.
Proof.
  induction 1; intros.
  constructor.
  red in H6; simpl in H6. 
  econstructor; eauto.
  eapply frame_match_store_other; eauto.
  unfold block; omega.
  eapply IHmatch_stacks; eauto.
  eapply stack_below_trans; eauto. omega.
Qed.

Lemma match_stacks_store_slot:
  forall s ts ms mm,
  match_stacks s ts mm ms ->
  forall ty ofs v ms' b i,
  stack_below ts b ->
  store_stack ms (Vptr b i) ty ofs v = Some ms' ->
  match_stacks s ts mm ms'.
Proof.
  intros.
  unfold store_stack in H1. simpl in H1.
  inv H.
  constructor.
  red in H0; simpl in H0.
  econstructor; eauto.
  eapply frame_match_store_other; eauto.
  unfold block; omega.
  eapply match_stacks_store_other; eauto. 
  eapply stack_below_trans; eauto. omega.
Qed.

Lemma match_stacks_store:
  forall s ts ms mm,
  match_stacks s ts mm ms ->
  forall chunk b ofs v mm' v' ms',
  Mem.store chunk mm b ofs v = Some mm' ->
  Mem.store chunk ms b ofs v' = Some ms' ->
  match_stacks s ts mm' ms'.
Proof.
  induction 1; intros.
  constructor.
  econstructor; eauto.
  eapply frame_match_store; eauto.
Qed.

Lemma match_stacks_alloc:
  forall s ts ms mm,
  match_stacks s ts mm ms ->
  forall lom him mm' b los his ms',
  Mem.alloc mm lom him = (mm', b) ->
  Mem.alloc ms los his = (ms', b) ->
  match_stacks s ts mm' ms'.
Proof.
  induction 1; intros.
  constructor.
  econstructor; eauto. eapply frame_match_alloc; eauto.
Qed.

Lemma match_stacks_free:
  forall s ts ms mm,
  match_stacks s ts mm ms ->
  forall b lom him los his mm' ms',
  Mem.free mm b lom him = Some mm' ->
  Mem.free ms b los his = Some ms' ->
  stack_below ts b ->
  match_stacks s ts mm' ms'.
Proof.
  induction 1; intros.
  constructor.
  red in H7; simpl in H7.
  econstructor; eauto.
  eapply frame_match_free; eauto. unfold block; omega.
  eapply IHmatch_stacks; eauto.
  eapply stack_below_trans; eauto. omega.
Qed.

Lemma match_stacks_function_entry:
  forall s ts ms mm,
  match_stacks s ts mm ms ->
  forall lom him mm' stk los his ms',
  Mem.alloc mm lom him = (mm', stk) ->
  Mem.alloc ms los his = (ms', stk) ->
  match_stacks s ts mm' ms' /\ stack_below ts stk.
Proof.
  intros.
  assert (stk = Mem.nextblock mm) by eauto with mem.
  split. eapply match_stacks_alloc; eauto.
  red. inv H; simpl.
  unfold Mem.nullptr. apply Zgt_lt. apply Mem.nextblock_pos.
  inv H5. auto. 
Qed.

Lemma match_stacks_external_call:
  forall s ts mm ms,
  match_stacks s ts mm ms ->
  forall ef vargs t vres mm' ms' vargs' vres',
  Mem.extends mm ms ->
  external_call ef ge vargs mm t vres mm' ->
  Mem.extends mm' ms' ->
  external_call ef ge vargs' ms t vres' ms' ->
  mem_unchanged_on (loc_out_of_bounds mm) ms ms' ->
  match_stacks s ts mm' ms'.
Proof.
  induction 1; intros.
  constructor.
  econstructor; eauto. 
  eapply frame_match_external_call; eauto. 
Qed.

(** ** Invariant between states. *)

(** The [match_state] predicate relates a Machabstr state with
  a Machconcr state.  In addition to [match_stacks] between the
  stacks, we ask that
- The Machabstr frame is properly stored in the activation record,
  as characterized by [frame_match].
- The Machconcr memory state extends the Machabstr memory state,
  in the sense of the [Mem.extends] relation defined in module [Mem]. *)

Inductive match_states:
            Machabstr.state -> Machconcr.state -> Prop :=
  | match_states_intro:
      forall s f sp base c rs fr mm ts trs fb ms
        (STACKS: match_stacks s ts mm ms)
        (FM: frame_match f (extend_frame f ts fr) sp base mm ms)
        (BELOW: stack_below ts sp)
        (RLD: regset_lessdef rs trs)
        (MEXT: Mem.extends mm ms)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f)),
      match_states (Machabstr.State s f (Vptr sp base) c rs fr mm)
                   (Machconcr.State ts fb (Vptr sp base) c trs ms)
  | match_states_call:
      forall s f rs mm ts trs fb ms
        (STACKS: match_stacks s ts mm ms)
        (MEXT: Mem.extends mm ms)
        (RLD: regset_lessdef rs trs)
        (FIND: Genv.find_funct_ptr ge fb = Some f),
      match_states (Machabstr.Callstate s f rs mm)
                   (Machconcr.Callstate ts fb trs ms)
  | match_states_return:
      forall s rs mm ts trs ms
        (STACKS: match_stacks s ts mm ms)
        (MEXT: Mem.extends mm ms)
        (RLD: regset_lessdef rs trs),
      match_states (Machabstr.Returnstate s rs mm)
                   (Machconcr.Returnstate ts trs ms).

(** * The proof of simulation *)

(** The proof of simulation relies on diagrams of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                   |t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The precondition is matching between the initial states [st1] and
  [st2], as usual, plus the fact that [st1] is well-typed
  in the sense of predicate [wt_state] from module [Machtyping].
  The postcondition is matching between the final states [st1']
  and [st2'].  The well-typedness of [st2] is not part of the
  postcondition, since it follows from that of [st1] if the
  program is well-typed.  (See the subject reduction property
  in module [Machtyping].)
*)

Lemma find_function_find_function_ptr:
  forall ros rs f',
  find_function ge ros rs = Some f' ->
  exists fb', Genv.find_funct_ptr ge fb' = Some f' /\ find_function_ptr ge ros rs = Some fb'.
Proof.
  intros until f'. destruct ros; simpl.
  intro. exploit Genv.find_funct_inv; eauto. intros [fb' EQ].
  rewrite EQ in H. rewrite Genv.find_funct_find_funct_ptr in H.
  exists fb'; split. auto. rewrite EQ. simpl. auto.
  destruct (Genv.find_symbol ge i); intro.
  exists b; auto. congruence.
Qed.

(** Preservation of arguments to external functions. *)

Lemma transl_extcall_arguments:
  forall rs s sg args ts trs m ms,
  Machabstr.extcall_arguments (parent_function s) rs (parent_frame s) sg args ->
  regset_lessdef rs trs ->
  match_stacks s ts m ms ->
  exists targs,
     extcall_arguments trs ms (parent_sp ts) sg targs
  /\ Val.lessdef_list args targs.
Proof.
  unfold Machabstr.extcall_arguments, extcall_arguments; intros.
  generalize (loc_arguments sg) args H.
  induction l; intros; inv H2.
  exists (@nil val); split; constructor.
  exploit IHl; eauto. intros [targs [A B]].
  inv H7. exists (trs r :: targs); split.
  constructor; auto. constructor. 
  constructor; auto.
  exploit match_stacks_get_parent; eauto. intros [targ [C D]]. 
  exists (targ :: targs); split. 
  constructor; auto. constructor; auto. 
  constructor; auto.
Qed.

Hypothesis wt_prog: wt_program p.

Theorem step_equiv:
  forall s1 t s2, Machabstr.step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1') (WTS: wt_state s1),
  exists s2', Machconcr.step ge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros; inv MS.

  (* Mlabel *)
  econstructor; split.
  apply exec_Mlabel; auto.
  econstructor; eauto with coqlib.

  (* Mgetstack *)
  assert (WTF: wt_function f) by (inv WTS; auto).
  exploit frame_match_get_slot; eauto. eapply get_slot_extends; eauto. 
  intros [v' [A B]]. 
  exists (State ts fb (Vptr sp0 base) c (trs#dst <- v') ms); split.
  constructor; auto.
  econstructor; eauto with coqlib. eapply regset_lessdef_set; eauto. 

  (* Msetstack *)
  assert (WTF: wt_function f) by (inv WTS; auto).
  assert (Val.has_type (rs src) ty).
    inv WTS. 
    generalize (wt_function_instrs _ WTF _ (is_tail_in TAIL)); intro WTI.
    inv WTI. apply WTRS.
  exploit frame_match_set_slot. eauto. eauto. 
    eapply set_slot_extends; eauto.
    auto. apply RLD. auto. 
  intros [ms' [STORE [FM' EXT']]].
  exists (State ts fb (Vptr sp0 base) c trs ms'); split.
  apply exec_Msetstack; auto.
  econstructor; eauto.
  eapply match_stacks_store_slot; eauto.

  (* Mgetparam *)
  assert (WTF: wt_function f) by (inv WTS; auto).
  exploit match_stacks_get_parent; eauto. intros [v' [A B]].
  exists (State ts fb (Vptr sp0 base) c (trs # IT1 <- Vundef # dst <- v') ms); split.
  eapply exec_Mgetparam; eauto.
    eapply frame_match_load_link; eauto.
    eapply match_stacks_parent_sp_pointer; eauto.
  econstructor; eauto with coqlib.
  apply regset_lessdef_set; eauto. apply regset_lessdef_set; eauto.  
 
  (* Mop *)
  exploit eval_operation_lessdef. 2: eauto.
  eapply regset_lessdef_list; eauto. 
  intros [v' [A B]].
  exists (State ts fb (Vptr sp0 base) c ((undef_op op trs)#res <- v') ms); split.
  apply exec_Mop; auto.
  econstructor; eauto with coqlib. apply regset_lessdef_set; eauto.
  apply regset_lessdef_undef_op; auto.

  (* Mload *)
  exploit eval_addressing_lessdef. 2: eauto. eapply regset_lessdef_list; eauto.
  intros [a' [A B]].
  exploit Mem.loadv_extends. eauto. eauto. eexact B. 
  intros [v' [C D]].
  exists (State ts fb (Vptr sp0 base) c ((undef_temps trs)#dst <- v') ms); split.
  eapply exec_Mload; eauto.
  econstructor; eauto with coqlib. apply regset_lessdef_set; eauto.
  apply regset_lessdef_undef_temps; auto.

  (* Mstore *)
  exploit eval_addressing_lessdef. 2: eauto. eapply regset_lessdef_list; eauto.
  intros [a' [A B]].
  exploit Mem.storev_extends. eauto. eauto. eexact B. apply RLD. 
  intros [ms' [C D]].
  exists (State ts fb (Vptr sp0 base) c (undef_temps trs) ms'); split.
  eapply exec_Mstore; eauto.
  destruct a; simpl in H0; try congruence. inv B. simpl in C. 
  econstructor; eauto with coqlib.
  eapply match_stacks_store. eauto. eexact H0. eexact C.
  eapply frame_match_store; eauto.
  apply regset_lessdef_undef_temps; auto.

  (* Mcall *)
  exploit find_function_find_function_ptr; eauto. 
  intros [fb' [FIND' FINDFUNCT]].
  assert (exists ra', return_address_offset f c ra').
    apply return_address_exists.
    inv WTS. eapply is_tail_cons_left; eauto.
  destruct H0 as [ra' RETADDR].
  econstructor; split.
  eapply exec_Mcall; eauto. eapply regset_lessdef_find_function_ptr; eauto. 
  econstructor; eauto. 
  econstructor; eauto. inv WTS; auto. exact I.

  (* Mtailcall *)
  assert (WTF: wt_function f) by (inv WTS; auto).
  exploit find_function_find_function_ptr; eauto. 
  intros [fb' [FIND' FINDFUNCT]].
  exploit frame_match_delete; eauto. intros [ms' [A B]].
  econstructor; split.
  eapply exec_Mtailcall; eauto.
    eapply regset_lessdef_find_function_ptr; eauto. 
    eapply frame_match_load_link; eauto. eapply match_stacks_parent_sp_pointer; eauto.
    eapply frame_match_load_retaddr; eauto. eapply match_stacks_parent_ra_pointer; eauto.
  econstructor; eauto. eapply match_stacks_free; eauto.

  (* Mbuiltin *)
  exploit external_call_mem_extends; eauto. eapply regset_lessdef_list; eauto. 
  intros [v' [ms' [A [B [C D]]]]].
  econstructor; split.
  eapply exec_Mbuiltin. eauto. 
  econstructor; eauto with coqlib.
  eapply match_stacks_external_call; eauto. 
  eapply frame_match_external_call; eauto. 
  apply regset_lessdef_set; eauto. apply regset_lessdef_undef_temps; auto.

  (* Mgoto *)
  econstructor; split.
  eapply exec_Mgoto; eauto.
  econstructor; eauto.

  (* Mcond *)
  econstructor; split.
  eapply exec_Mcond_true; eauto.
  eapply eval_condition_lessdef; eauto. apply regset_lessdef_list; auto.
  econstructor; eauto. apply regset_lessdef_undef_temps; auto.
  econstructor; split.
  eapply exec_Mcond_false; eauto.
  eapply eval_condition_lessdef; eauto. apply regset_lessdef_list; auto.
  econstructor; eauto. apply regset_lessdef_undef_temps; auto.

  (* Mjumptable *)
  econstructor; split.
  eapply exec_Mjumptable; eauto.
  generalize (RLD arg); intro LD. rewrite H in LD. inv LD. auto.  
  econstructor; eauto. apply regset_lessdef_undef_temps; auto.

  (* Mreturn *)
  assert (WTF: wt_function f) by (inv WTS; auto).
  exploit frame_match_delete; eauto. intros [ms' [A B]].
  econstructor; split.
  eapply exec_Mreturn; eauto.
    eapply frame_match_load_link; eauto. eapply match_stacks_parent_sp_pointer; eauto.
    eapply frame_match_load_retaddr; eauto. eapply match_stacks_parent_ra_pointer; eauto.
  econstructor; eauto. eapply match_stacks_free; eauto.   

  (* internal function *)
  assert (WTF: wt_function f). inv WTS. inv H5. auto.
  exploit frame_match_function_entry. eauto. eauto. eauto. 
  instantiate (1 := ts). eapply match_stacks_parent_sp_pointer; eauto.
  eapply match_stacks_parent_ra_pointer; eauto.
  intros [ms1 [ms2 [ms3 [ALLOC [STORE1 [STORE2 [FM MEXT']]]]]]].
  econstructor; split.
  eapply exec_function_internal; eauto.
  exploit match_stacks_function_entry; eauto. intros [STACKS' BELOW].
  econstructor; eauto.
  eapply match_stacks_store_slot with (ms := ms2); eauto.
  eapply match_stacks_store_slot with (ms := ms1); eauto.

  (* external function *)
  exploit transl_extcall_arguments; eauto. intros [targs [A B]].
  exploit external_call_mem_extends; eauto. 
  intros [tres [ms' [C [D [E F]]]]]. 
  econstructor; split.
  eapply exec_function_external. eauto. eexact C. eexact A. reflexivity.  
  econstructor; eauto.
  eapply match_stacks_external_call; eauto. 
  apply regset_lessdef_set; auto. 

  (* return *)
  inv STACKS.
  econstructor; split.
  eapply exec_return. 
  econstructor; eauto.
Qed.

Lemma equiv_initial_states:
  forall st1, Machabstr.initial_state p st1 ->
  exists st2, Machconcr.initial_state p st2 /\ match_states st1 st2 /\ wt_state st1.
Proof.
  intros. inversion H.
  econstructor; split.
  econstructor. eauto. eauto. 
  split. econstructor. constructor. apply Mem.extends_refl.
  unfold Regmap.init; red; intros. constructor.
  auto.
  econstructor. simpl; intros; contradiction.
  eapply Genv.find_funct_ptr_prop; eauto.
  red; intros; exact I.
Qed.

Lemma equiv_final_states:
  forall st1 st2 r, 
  match_states st1 st2 /\ wt_state st1 -> Machabstr.final_state st1 r -> Machconcr.final_state st2 r.
Proof.
  intros. inv H0. destruct H. inv H. inv STACKS.
  constructor. 
  generalize (RLD (loc_result (mksignature nil (Some Tint)))).
  rewrite H1. intro LD. inv LD. auto. 
Qed.

Theorem exec_program_equiv:
  forall (beh: program_behavior), not_wrong beh ->
  Machabstr.exec_program p beh -> Machconcr.exec_program p beh.
Proof.
  unfold Machconcr.exec_program, Machabstr.exec_program; intros.
  eapply simulation_step_preservation with
    (step1 := Machabstr.step)
    (step2 := Machconcr.step)
    (match_states := fun st1 st2 => match_states st1 st2 /\ wt_state st1).
  eexact equiv_initial_states.
  eexact equiv_final_states.
  intros. destruct H2. exploit step_equiv; eauto.
  intros [st2' [A B]]. exists st2'; split. auto. split. auto.
  eapply Machtyping.subject_reduction; eauto. 
  auto. auto.
Qed.

End SIMULATION.
