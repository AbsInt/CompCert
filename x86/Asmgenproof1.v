(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                  Xavier Leroy, INRIA Paris                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for x86-64 generation: auxiliary results. *)

Require Import Coqlib.
Require Import AST Errors Integers Floats Values Memory Globalenvs.
Require Import Op Locations Conventions Mach Asm.
Require Import Asmgen Asmgenproof0.

Local Open Scope error_monad_scope.

(** * Correspondence between Mach registers and x86 registers *)

Lemma agree_nextinstr_nf:
  forall ms sp rs,
  agree ms sp rs -> agree ms sp (nextinstr_nf rs).
Proof.
  intros. unfold nextinstr_nf. apply agree_nextinstr.
  apply agree_undef_nondata_regs. auto.
  simpl; intros. intuition (subst r; auto).
Qed.

(** Useful properties of the PC register. *)

Lemma nextinstr_nf_inv:
  forall r rs,
  match r with PC => False | CR _ => False | _ => True end ->
  (nextinstr_nf rs)#r = rs#r.
Proof.
  intros. unfold nextinstr_nf. rewrite nextinstr_inv.
  simpl. repeat rewrite Pregmap.gso; auto;
  red; intro; subst; contradiction.
  red; intro; subst; contradiction.
Qed.

Lemma nextinstr_nf_inv1:
  forall r rs,
  data_preg r = true -> (nextinstr_nf rs)#r = rs#r.
Proof.
  intros. apply nextinstr_nf_inv. destruct r; auto || discriminate.
Qed.

Lemma nextinstr_nf_set_preg:
  forall rs m v,
  (nextinstr_nf (rs#(preg_of m) <- v))#PC = Val.offset_ptr rs#PC Ptrofs.one.
Proof.
  intros. unfold nextinstr_nf.
  transitivity (nextinstr (rs#(preg_of m) <- v) PC). auto.
  apply nextinstr_set_preg.
Qed.

(** Useful simplification tactic *)

Ltac Simplif :=
  match goal with
  | [ |- nextinstr_nf _ _ = _ ] =>
      ((rewrite nextinstr_nf_inv by auto with asmgen)
       || (rewrite nextinstr_nf_inv1 by auto with asmgen)); auto
  | [ |- nextinstr _ _ = _ ] =>
      ((rewrite nextinstr_inv by auto with asmgen)
       || (rewrite nextinstr_inv1 by auto with asmgen)); auto
  | [ |- Pregmap.get ?x (Pregmap.set ?x _ _) = _ ] =>
      rewrite Pregmap.gss; auto
  | [ |- Pregmap.set ?x _ _ ?x = _ ] =>
      rewrite Pregmap.gss; auto
  | [ |- Pregmap.get _ (Pregmap.set _ _ _) = _ ] =>
      rewrite Pregmap.gso by (auto with asmgen); auto
  | [ |- Pregmap.set _ _ _ _ = _ ] =>
      rewrite Pregmap.gso by (auto with asmgen); auto
  end.

Ltac Simplifs := repeat Simplif.

(** * Correctness of x86-64 constructor functions *)

Section CONSTRUCTORS.

Variable ge: genv.
Variable fn: function.

(** Smart constructor for moves. *)

Lemma mk_mov_correct:
  forall rd rs k c rs1 m,
  mk_mov rd rs k = OK c ->
  exists rs2,
     exec_straight ge fn c rs1 m k rs2 m
  /\ rs2#rd = rs1#rs
  /\ forall r, data_preg r = true -> r <> rd -> rs2#r = rs1#r.
Proof.
  unfold mk_mov; intros.
  destruct rd; try (monadInv H); destruct rs; monadInv H.
(* mov *)
  econstructor. split. apply exec_straight_one. simpl. eauto. auto.
  split. Simplifs. intros; Simplifs.
(* movsd *)
  econstructor. split. apply exec_straight_one. simpl. eauto. auto.
  split. Simplifs. intros; Simplifs.
Qed.

(** Properties of division *)

Lemma divu_modu_exists:
  forall v1 v2,
  Val.divu v1 v2 <> None \/ Val.modu v1 v2 <> None ->
  exists n d q r,
     v1 = Vint n /\ v2 = Vint d
  /\ Int.divmodu2 Int.zero n d = Some(q, r)
  /\ Val.divu v1 v2 = Some (Vint q) /\ Val.modu v1 v2 = Some (Vint r).
Proof.
  intros v1 v2; unfold Val.divu, Val.modu.
  destruct v1; try (intuition discriminate).
  destruct v2; try (intuition discriminate).
  predSpec Int.eq Int.eq_spec i0 Int.zero ; try (intuition discriminate).
  intros _. exists i, i0, (Int.divu i i0), (Int.modu i i0); intuition auto.
  apply Int.divmodu2_divu_modu; auto.
Qed.

Lemma divs_mods_exists:
  forall v1 v2,
  Val.divs v1 v2 <> None \/ Val.mods v1 v2 <> None ->
  exists nh nl d q r,
     Val.shr v1 (Vint (Int.repr 31)) = Vint nh /\ v1 = Vint nl /\ v2 = Vint d
  /\ Int.divmods2 nh nl d = Some(q, r)
  /\ Val.divs v1 v2 = Some (Vint q) /\ Val.mods v1 v2 = Some (Vint r).
Proof.
  intros v1 v2; unfold Val.divs, Val.mods.
  destruct v1; try (intuition discriminate).
  destruct v2; try (intuition discriminate).
  destruct (Int.eq i0 Int.zero
            || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone) eqn:OK;
  try (intuition discriminate).
  intros _.
  InvBooleans.
  exists (Int.shr i (Int.repr 31)), i, i0, (Int.divs i i0), (Int.mods i i0); intuition auto.
  rewrite Int.shr_lt_zero. apply Int.divmods2_divs_mods.
  red; intros; subst i0; rewrite Int.eq_true in H; discriminate.
  revert H0. predSpec Int.eq Int.eq_spec i (Int.repr Int.min_signed); auto.
  predSpec Int.eq Int.eq_spec i0 Int.mone; auto.
  discriminate.
Qed.

Lemma divlu_modlu_exists:
  forall v1 v2,
  Val.divlu v1 v2 <> None \/ Val.modlu v1 v2 <> None ->
  exists n d q r,
     v1 = Vlong n /\ v2 = Vlong d
  /\ Int64.divmodu2 Int64.zero n d = Some(q, r)
  /\ Val.divlu v1 v2 = Some (Vlong q) /\ Val.modlu v1 v2 = Some (Vlong r).
Proof.
  intros v1 v2; unfold Val.divlu, Val.modlu.
  destruct v1; try (intuition discriminate).
  destruct v2; try (intuition discriminate).
  predSpec Int64.eq Int64.eq_spec i0 Int64.zero ; try (intuition discriminate).
  intros _. exists i, i0, (Int64.divu i i0), (Int64.modu i i0); intuition auto.
  apply Int64.divmodu2_divu_modu; auto.
Qed.

Lemma divls_modls_exists:
  forall v1 v2,
  Val.divls v1 v2 <> None \/ Val.modls v1 v2 <> None ->
  exists nh nl d q r,
     Val.shrl v1 (Vint (Int.repr 63)) = Vlong nh /\ v1 = Vlong nl /\ v2 = Vlong d
  /\ Int64.divmods2 nh nl d = Some(q, r)
  /\ Val.divls v1 v2 = Some (Vlong q) /\ Val.modls v1 v2 = Some (Vlong r).
Proof.
  intros v1 v2; unfold Val.divls, Val.modls.
  destruct v1; try (intuition discriminate).
  destruct v2; try (intuition discriminate).
  destruct (Int64.eq i0 Int64.zero
            || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone) eqn:OK;
  try (intuition discriminate).
  intros _.
  InvBooleans.
  exists (Int64.shr i (Int64.repr 63)), i, i0, (Int64.divs i i0), (Int64.mods i i0); intuition auto.
  rewrite Int64.shr_lt_zero. apply Int64.divmods2_divs_mods.
  red; intros; subst i0; rewrite Int64.eq_true in H; discriminate.
  revert H0. predSpec Int64.eq Int64.eq_spec i (Int64.repr Int64.min_signed); auto.
  predSpec Int64.eq Int64.eq_spec i0 Int64.mone; auto.
  discriminate.
Qed.

(** Smart constructor for [shrx] *)

Lemma mk_shrximm_correct:
  forall n k c (rs1: regset) v m,
  mk_shrximm n k = OK c ->
  Val.shrx (rs1#RAX) (Vint n) = Some v ->
  exists rs2,
     exec_straight ge fn c rs1 m k rs2 m
  /\ rs2#RAX = v
  /\ forall r, data_preg r = true -> r <> RAX -> r <> RCX -> rs2#r = rs1#r.
Proof.
  unfold mk_shrximm; intros. inv H.
  exploit Val.shrx_shr; eauto. intros [x [y [A [B C]]]].
  inversion B; clear B; subst y; subst v; clear H0.
  set (tnm1 := Int.sub (Int.shl Int.one n) Int.one).
  set (x' := Int.add x tnm1).
  set (rs2 := nextinstr (compare_ints (Vint x) (Vint Int.zero) rs1 m)).
  set (rs3 := nextinstr (rs2#RCX <- (Vint x'))).
  set (rs4 := nextinstr (if Int.lt x Int.zero then rs3#RAX <- (Vint x') else rs3)).
  set (rs5 := nextinstr_nf (rs4#RAX <- (Val.shr rs4#RAX (Vint n)))).
  assert (rs3#RAX = Vint x). unfold rs3. Simplifs.
  assert (rs3#RCX = Vint x'). unfold rs3. Simplifs.
  exists rs5. split.
  apply exec_straight_step with rs2 m. simpl. rewrite A. simpl. rewrite Int.and_idem. auto. auto.
  apply exec_straight_step with rs3 m. simpl.
  change (rs2 RAX) with (rs1 RAX). rewrite A. simpl.
  rewrite Int.repr_unsigned. rewrite Int.add_zero_l. auto. auto.
  apply exec_straight_step with rs4 m. simpl.
  rewrite Int.lt_sub_overflow. unfold rs4. destruct (Int.lt x Int.zero); simpl; auto.
  unfold rs4. destruct (Int.lt x Int.zero); simpl; auto.
  apply exec_straight_one. auto. auto.
  split. unfold rs5. Simplifs. unfold rs4. rewrite nextinstr_inv; auto with asmgen.
  destruct (Int.lt x Int.zero). rewrite Pregmap.gss. rewrite A; auto. rewrite A; rewrite H; auto.
  intros. unfold rs5. Simplifs. unfold rs4. Simplifs.
  transitivity (rs3#r). destruct (Int.lt x Int.zero). Simplifs. auto.
  unfold rs3. Simplifs. unfold rs2. Simplifs.
  unfold compare_ints. Simplifs.
Qed.

(** Smart constructor for [shrxl] *)

Lemma mk_shrxlimm_correct:
  forall n k c (rs1: regset) v m,
  mk_shrxlimm n k = OK c ->
  Val.shrxl (rs1#RAX) (Vint n) = Some v ->
  exists rs2,
     exec_straight ge fn c rs1 m k rs2 m
  /\ rs2#RAX = v
  /\ forall r, data_preg r = true -> r <> RAX -> r <> RDX -> rs2#r = rs1#r.
Proof.
  unfold mk_shrxlimm; intros. exploit Val.shrxl_shrl_2; eauto. intros EQ.
  destruct (Int.eq n Int.zero); inv H.
- econstructor; split. apply exec_straight_one. simpl; reflexivity. auto.
  split. Simplifs. intros; Simplifs.
- set (v1 := Val.shrl (rs1 RAX) (Vint (Int.repr 63))) in *.
  set (v2 := Val.shrlu v1 (Vint (Int.sub (Int.repr 64) n))) in *.
  set (v3 := Val.addl (rs1 RAX) v2) in *.
  set (v4 := Val.shrl v3 (Vint n)) in *.
  set (rs2 := nextinstr_nf (rs1#RDX <- v1)).
  set (rs3 := nextinstr_nf (rs2#RDX <- v2)).
  set (rs4 := nextinstr (rs3#RAX <- v3)).
  set (rs5 := nextinstr_nf (rs4#RAX <- v4)).
  assert (X: forall v1 v2,
             Val.addl v1 (Val.addl v2 (Vlong Int64.zero)) = Val.addl v1 v2).
  { intros. unfold Val.addl; destruct Archi.ptr64 eqn:SF, v0; auto; destruct v5; auto.
    rewrite Int64.add_zero; auto.
    rewrite Ptrofs.add_zero; auto.
    rewrite Int64.add_zero; auto.
    rewrite Int64.add_zero; auto. }
  exists rs5; split.
  eapply exec_straight_trans with (rs2 := rs3).
  eapply exec_straight_two with (rs2 := rs2); reflexivity.
  eapply exec_straight_two with (rs2 := rs4).
  simpl. rewrite X. reflexivity. reflexivity. reflexivity. reflexivity.
  split. unfold rs5; Simplifs.
  intros. unfold rs5; Simplifs. unfold rs4; Simplifs. unfold rs3; Simplifs. unfold rs2; Simplifs.
Qed.

(** Smart constructor for integer conversions *)

Lemma mk_intconv_correct:
  forall mk sem rd rs k c rs1 m,
  mk_intconv mk rd rs k = OK c ->
  (forall c rd rs r m,
   exec_instr ge c (mk rd rs) r m = Next (nextinstr (r#rd <- (sem r#rs))) m) ->
  exists rs2,
     exec_straight ge fn c rs1 m k rs2 m
  /\ rs2#rd = sem rs1#rs
  /\ forall r, data_preg r = true -> r <> rd -> r <> RAX -> rs2#r = rs1#r.
Proof.
  unfold mk_intconv; intros. destruct (Archi.ptr64 || low_ireg rs); monadInv H.
  econstructor. split. apply exec_straight_one. rewrite H0. eauto. auto.
  split. Simplifs. intros. Simplifs.
  econstructor. split. eapply exec_straight_two.
  simpl. eauto. apply H0. auto. auto.
  split. Simplifs. intros. Simplifs.
Qed.

(** Smart constructor for small stores *)

Lemma addressing_mentions_correct:
  forall a r (rs1 rs2: regset),
  (forall (r': ireg), r' <> r -> rs1 r' = rs2 r') ->
  addressing_mentions a r = false ->
  eval_addrmode32 ge a rs1 = eval_addrmode32 ge a rs2.
Proof.
  intros until rs2; intro AG. unfold addressing_mentions, eval_addrmode32.
  destruct a. intros. destruct (orb_false_elim _ _ H). unfold proj_sumbool in *.
  decEq. destruct base; auto. apply AG. destruct (ireg_eq r i); congruence.
  decEq. destruct ofs as [[r' sc] | ]; auto. rewrite AG; auto. destruct (ireg_eq r r'); congruence.
Qed.

Lemma mk_storebyte_correct:
  forall addr r k c rs1 m1 m2,
  mk_storebyte addr r k = OK c ->
  Mem.storev Mint8unsigned m1 (eval_addrmode ge addr rs1) (rs1 r) = Some m2 ->
  exists rs2,
     exec_straight ge fn c rs1 m1 k rs2 m2
  /\ forall r, data_preg r = true -> preg_notin r (if Archi.ptr64 then nil else AX :: CX :: nil) -> rs2#r = rs1#r.
Proof.
  unfold mk_storebyte; intros.
  destruct (Archi.ptr64 || low_ireg r) eqn:E.
(* low reg *)
  monadInv H. econstructor; split. apply exec_straight_one.
  simpl. unfold exec_store. rewrite H0. eauto. auto.
  intros; Simplifs.
(* high reg *)
  InvBooleans. rewrite H1; simpl. destruct (addressing_mentions addr RAX) eqn:E; monadInv H.
(* RAX is mentioned. *)
  assert (r <> RCX). { red; intros; subst r; discriminate H2. }
  set (rs2 := nextinstr (rs1#RCX <- (eval_addrmode32 ge addr rs1))).
  set (rs3 := nextinstr (rs2#RAX <- (rs1 r))).
  econstructor; split.
  apply exec_straight_three with rs2 m1 rs3 m1.
  simpl. auto.
  simpl. replace (rs2 r) with (rs1 r). auto. symmetry. unfold rs2; Simplifs.
  simpl. unfold exec_store. unfold eval_addrmode; rewrite H1; simpl. rewrite Int.add_zero.
  change (rs3 RAX) with (rs1 r).
  change (rs3 RCX) with (eval_addrmode32 ge addr rs1).
  replace (Val.add (eval_addrmode32 ge addr rs1) (Vint Int.zero))
     with (eval_addrmode ge addr rs1).
  rewrite H0. eauto.
  unfold eval_addrmode in *; rewrite H1 in *.
  destruct (eval_addrmode32 ge addr rs1); simpl in H0; try discriminate H0.
  simpl. rewrite H1. rewrite Ptrofs.add_zero; auto.
  auto. auto. auto.
  intros. destruct H4. Simplifs. unfold rs3; Simplifs. unfold rs2; Simplifs.
(* RAX is not mentioned *)
  set (rs2 := nextinstr (rs1#RAX <- (rs1 r))).
  econstructor; split.
  apply exec_straight_two with rs2 m1.
  simpl. auto.
  simpl. unfold exec_store. unfold eval_addrmode in *; rewrite H1 in *.
  rewrite (addressing_mentions_correct addr RAX rs2 rs1); auto.
  change (rs2 RAX) with (rs1 r). rewrite H0. eauto.
  intros. unfold rs2; Simplifs.
  auto. auto.
  intros. destruct H3. simpl. Simplifs. unfold rs2; Simplifs.
Qed.

(** Accessing slots in the stack frame *)

Remark eval_addrmode_indexed:
  forall (base: ireg) ofs (rs: regset),
  match rs#base with Vptr _ _ => True | _ => False end ->
  eval_addrmode ge (Addrmode (Some base) None (inl _ (Ptrofs.unsigned ofs))) rs = Val.offset_ptr rs#base ofs.
Proof.
  intros. destruct (rs#base) eqn:BASE; try contradiction.
  intros; unfold eval_addrmode; destruct Archi.ptr64 eqn:SF; simpl; rewrite BASE; simpl; rewrite SF; simpl.
- apply f_equal. apply f_equal. rewrite Int64.add_zero_l. rewrite <- (Ptrofs.repr_unsigned ofs) at 2. auto with ptrofs.
-  apply f_equal. apply f_equal. rewrite Int.add_zero_l. rewrite <- (Ptrofs.repr_unsigned ofs) at 2. auto with ptrofs.
Qed.

Ltac loadind_correct_solve :=
  match goal with
  | H: Error _ = OK _ |- _ => discriminate H
  | H: OK _ = OK _ |- _ => inv H
  | H: match ?x with _ => _ end = OK _ |- _ => destruct x eqn:?; loadind_correct_solve
  | _ => idtac
  end.

Lemma loadind_correct:
  forall (base: ireg) ofs ty dst k (rs: regset) c m v,
  loadind base ofs ty dst k = OK c ->
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, data_preg r = true -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  unfold loadind; intros.
  set (addr := Addrmode (Some base) None (inl (ident * ptrofs) (Ptrofs.unsigned ofs))) in *.
  assert (eval_addrmode ge addr rs = Val.offset_ptr rs#base ofs).
  { apply eval_addrmode_indexed. destruct (rs base); auto || discriminate. }
  rewrite <- H1 in H0.
  exists (nextinstr_nf (rs#(preg_of dst) <- v)); split.
- loadind_correct_solve; apply exec_straight_one; auto; simpl in *; unfold exec_load; rewrite ?Heqb, ?H0; auto.
- intuition Simplifs.
Qed.

Lemma storeind_correct:
  forall (base: ireg) ofs ty src k (rs: regset) c m m',
  storeind src base ofs ty k = OK c ->
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr rs#base ofs) (rs#(preg_of src)) = Some m' ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, data_preg r = true -> preg_notin r (destroyed_by_setstack ty) -> rs'#r = rs#r.
Proof.
  unfold storeind; intros.
  set (addr := Addrmode (Some base) None (inl (ident * ptrofs) (Ptrofs.unsigned ofs))) in *.
  assert (eval_addrmode ge addr rs = Val.offset_ptr rs#base ofs).
  { apply eval_addrmode_indexed. destruct (rs base); auto || discriminate. }
  rewrite <- H1 in H0.
  loadind_correct_solve; simpl in H0;
  (econstructor; split;
  [apply exec_straight_one; [simpl; unfold exec_store; rewrite ?Heqb, H0;eauto|auto]
  |simpl; intros; unfold undef_regs; repeat Simplifs]).
Qed.

(** Translation of addressing modes *)

Lemma transl_addressing_mode_32_correct:
  forall addr args am (rs: regset) v,
  transl_addressing addr args = OK am ->
  eval_addressing32 ge (rs RSP) addr (List.map rs (List.map preg_of args)) = Some v ->
  Val.lessdef v (eval_addrmode32 ge am rs).
Proof.
  assert (A: forall id ofs, Archi.ptr64 = false ->
          Val.add (Vint Int.zero) (Genv.symbol_address ge id ofs) = Genv.symbol_address ge id ofs).
  { intros. unfold Val.add; rewrite H. unfold Genv.symbol_address.
    destruct (Genv.find_symbol ge id); auto. rewrite Ptrofs.add_zero; auto. }
  assert (C: forall v i,
    Val.lessdef (Val.mul v (Vint (Int.repr i)))
               (if zeq i 1 then v else Val.mul v (Vint (Int.repr i)))).
  { intros. destruct (zeq i 1); subst; auto.
    destruct v; simpl; auto. rewrite Int.mul_one; auto. }
  unfold transl_addressing; intros.
  destruct addr; repeat (destruct args; try discriminate H); simpl in H0; FuncInv;
  monadInv H; try (erewrite ! ireg_of_eq by eauto); unfold eval_addrmode32.
- simpl; rewrite Int.add_zero_l; auto.
- rewrite Val.add_assoc. apply Val.add_lessdef; auto.
- rewrite Val.add_permut. apply Val.add_lessdef; auto. simpl; rewrite Int.add_zero_l; auto.
- apply Val.add_lessdef; auto. apply Val.add_lessdef; auto.
- rewrite ! A by auto. auto.
- rewrite Val.add_commut. rewrite A by auto. auto.
- rewrite Val.add_permut. rewrite Val.add_commut. apply Val.add_lessdef; auto. rewrite A; auto.
- simpl. unfold Val.add; rewrite Heqb.
  destruct (rs RSP); simpl; auto.
  rewrite Int.add_zero_l. apply Val.lessdef_same; f_equal; f_equal.
  symmetry. transitivity (Ptrofs.repr (Ptrofs.signed i)). auto with ptrofs. auto with ints.
Qed.

Lemma transl_addressing_mode_64_correct:
  forall addr args am (rs: regset) v,
  transl_addressing addr args = OK am ->
  eval_addressing64 ge (rs RSP) addr (List.map rs (List.map preg_of args)) = Some v ->
  Val.lessdef v (eval_addrmode64 ge am rs).
Proof.
  assert (A: forall id ofs, Archi.ptr64 = true ->
          Val.addl (Vlong Int64.zero) (Genv.symbol_address ge id ofs) = Genv.symbol_address ge id ofs).
  { intros. unfold Val.addl; rewrite H. unfold Genv.symbol_address.
    destruct (Genv.find_symbol ge id); auto. rewrite Ptrofs.add_zero; auto. }
  assert (C: forall v i,
    Val.lessdef (Val.mull v (Vlong (Int64.repr i)))
               (if zeq i 1 then v else Val.mull v (Vlong (Int64.repr i)))).
  { intros. destruct (zeq i 1); subst; auto.
    destruct v; simpl; auto. rewrite Int64.mul_one; auto. }
  unfold transl_addressing; intros.
  destruct addr; repeat (destruct args; try discriminate H); simpl in H0; FuncInv;
  monadInv H; try (erewrite ! ireg_of_eq by eauto); unfold eval_addrmode64.
- simpl; rewrite Int64.add_zero_l; auto.
- rewrite Val.addl_assoc. apply Val.addl_lessdef; auto.
- rewrite Val.addl_permut. apply Val.addl_lessdef; auto. simpl; rewrite Int64.add_zero_l; auto.
- apply Val.addl_lessdef; auto. apply Val.addl_lessdef; auto.
- rewrite ! A by auto. auto.
- unfold Val.addl; rewrite Heqb. destruct (rs RSP); auto. simpl.
  rewrite Int64.add_zero_l. apply Val.lessdef_same; f_equal; f_equal.
  symmetry. transitivity (Ptrofs.repr (Ptrofs.signed i)). auto with ptrofs. auto with ints.
Qed.

Lemma transl_addressing_mode_correct:
  forall addr args am (rs: regset) v,
  transl_addressing addr args = OK am ->
  eval_addressing ge (rs RSP) addr (List.map rs (List.map preg_of args)) = Some v ->
  Val.lessdef v (eval_addrmode ge am rs).
Proof.
  unfold eval_addressing, eval_addrmode; intros. destruct Archi.ptr64.
  eapply transl_addressing_mode_64_correct; eauto.
  eapply transl_addressing_mode_32_correct; eauto.
Qed.

Lemma normalize_addrmode_32_correct:
  forall am rs, eval_addrmode32 ge (normalize_addrmode_32 am) rs = eval_addrmode32 ge am rs.
Proof.
  intros; destruct am as [base ofs [n|r]]; simpl; auto. rewrite Int.repr_signed. auto.
Qed.

Lemma normalize_addrmode_64_correct:
  forall am rs,
  eval_addrmode64 ge am rs =
  match normalize_addrmode_64 am with
  | (am', None) => eval_addrmode64 ge am' rs
  | (am', Some delta) => Val.addl (eval_addrmode64 ge am' rs) (Vlong delta)
  end.
Proof.
  intros; destruct am as [base ofs [n|[id delta]]]; simpl.
- destruct (offset_in_range n); auto; simpl.
  rewrite ! Val.addl_assoc. apply f_equal. apply f_equal. simpl. rewrite Int64.add_zero_l; auto.
- destruct Archi.ptr64 eqn:SF; auto; simpl;
  destruct (ptroffset_in_range delta); auto. simpl.
  rewrite ! Val.addl_assoc. apply f_equal. apply f_equal.
  rewrite <- Genv.shift_symbol_address_64 by auto.
  f_equal. rewrite Ptrofs.add_zero_l, Ptrofs.of_int64_to_int64 by auto. auto.
Qed.

(** Processor conditions and comparisons *)

Lemma compare_ints_spec:
  forall rs v1 v2 m,
  let rs' := nextinstr (compare_ints v1 v2 rs m) in
     rs'#ZF = Val.cmpu (Mem.valid_pointer m) Ceq v1 v2
  /\ rs'#CF = Val.cmpu (Mem.valid_pointer m) Clt v1 v2
  /\ rs'#SF = Val.negative (Val.sub v1 v2)
  /\ rs'#OF = Val.sub_overflow v1 v2
  /\ (forall r, data_preg r = true -> rs'#r = rs#r).
Proof.
  intros. unfold rs'; unfold compare_ints.
  split. auto.
  split. auto.
  split. auto.
  split. auto.
  intros. Simplifs.
Qed.

Lemma testcond_for_signed_comparison_32_correct:
  forall c v1 v2 rs m b,
  Val.cmp_bool c v1 v2 = Some b ->
  eval_testcond (testcond_for_signed_comparison c)
                (nextinstr (compare_ints v1 v2 rs m)) = Some b.
Proof.
  intros. generalize (compare_ints_spec rs v1 v2 m).
  set (rs' := nextinstr (compare_ints v1 v2 rs m)).
  intros [A [B [C [D E]]]].
  destruct v1; destruct v2; simpl in H; inv H.
  unfold eval_testcond. rewrite A; rewrite B; rewrite C; rewrite D.
  simpl. unfold Val.cmp, Val.cmpu.
  rewrite Int.lt_sub_overflow.
  destruct c; simpl.
  destruct (Int.eq i i0); auto.
  destruct (Int.eq i i0); auto.
  destruct (Int.lt i i0); auto.
  rewrite Int.not_lt. destruct (Int.lt i i0); simpl; destruct (Int.eq i i0); auto.
  rewrite (Int.lt_not i i0). destruct (Int.lt i i0); destruct (Int.eq i i0); reflexivity.
  destruct (Int.lt i i0); reflexivity.
Qed.

Lemma testcond_for_unsigned_comparison_32_correct:
  forall c v1 v2 rs m b,
  Val.cmpu_bool (Mem.valid_pointer m) c v1 v2 = Some b ->
  eval_testcond (testcond_for_unsigned_comparison c)
                (nextinstr (compare_ints v1 v2 rs m)) = Some b.
Proof.
  intros. generalize (compare_ints_spec rs v1 v2 m).
  set (rs' := nextinstr (compare_ints v1 v2 rs m)).
  intros [A [B [C [D E]]]].
  unfold eval_testcond. rewrite A; rewrite B. unfold Val.cmpu, Val.cmp.
  destruct v1; destruct v2; simpl in H; FuncInv; subst.
- (* int int *)
  destruct c; simpl; auto.
  destruct (Int.eq i i0); reflexivity.
  destruct (Int.eq i i0); auto.
  destruct (Int.ltu i i0); auto.
  rewrite Int.not_ltu. destruct (Int.ltu i i0); simpl; destruct (Int.eq i i0); auto.
  rewrite (Int.ltu_not i i0). destruct (Int.ltu i i0); destruct (Int.eq i i0); reflexivity.
  destruct (Int.ltu i i0); reflexivity.
- (* int ptr *)
  unfold Val.cmpu_bool; rewrite Heqb1.
  destruct (Int.eq i Int.zero &&
    (Mem.valid_pointer m b0 (Ptrofs.unsigned i0) || Mem.valid_pointer m b0 (Ptrofs.unsigned i0 - 1))); try discriminate H.
  destruct c; simpl in *; inv H; reflexivity.
- (* ptr int *)
  unfold Val.cmpu_bool; rewrite Heqb1.
  destruct (Int.eq i0 Int.zero &&
    (Mem.valid_pointer m b0 (Ptrofs.unsigned i) || Mem.valid_pointer m b0 (Ptrofs.unsigned i - 1))); try discriminate H.
  destruct c; simpl in *; inv H; reflexivity.
- (* ptr ptr *)
  unfold Val.cmpu_bool; rewrite Heqb2.
  fold (Mem.weak_valid_pointer m b0 (Ptrofs.unsigned i)) in *.
  fold (Mem.weak_valid_pointer m b1 (Ptrofs.unsigned i0)) in *.
  destruct (eq_block b0 b1).
  destruct (Mem.weak_valid_pointer m b0 (Ptrofs.unsigned i) &&
            Mem.weak_valid_pointer m b1 (Ptrofs.unsigned i0)); inv H.
  destruct c; simpl; auto.
  destruct (Ptrofs.eq i i0); auto.
  destruct (Ptrofs.eq i i0); auto.
  destruct (Ptrofs.ltu i i0); auto.
  rewrite Ptrofs.not_ltu. destruct (Ptrofs.ltu i i0); simpl; destruct (Ptrofs.eq i i0); auto.
  rewrite (Ptrofs.ltu_not i i0). destruct (Ptrofs.ltu i i0); destruct (Ptrofs.eq i i0); reflexivity.
  destruct (Ptrofs.ltu i i0); reflexivity.
  destruct (Mem.valid_pointer m b0 (Ptrofs.unsigned i) &&
            Mem.valid_pointer m b1 (Ptrofs.unsigned i0)); try discriminate H.
  destruct c; simpl in *; inv H; reflexivity.
Qed.

Lemma compare_longs_spec:
  forall rs v1 v2 m,
  let rs' := nextinstr (compare_longs v1 v2 rs m) in
     rs'#ZF = Val.maketotal (Val.cmplu (Mem.valid_pointer m) Ceq v1 v2)
  /\ rs'#CF = Val.maketotal (Val.cmplu (Mem.valid_pointer m) Clt v1 v2)
  /\ rs'#SF = Val.negativel (Val.subl v1 v2)
  /\ rs'#OF = Val.subl_overflow v1 v2
  /\ (forall r, data_preg r = true -> rs'#r = rs#r).
Proof.
  intros. unfold rs'; unfold compare_longs.
  split. auto.
  split. auto.
  split. auto.
  split. auto.
  intros. Simplifs.
Qed.

Lemma int64_sub_overflow:
  forall x y,
  Int.xor (Int.repr (Int64.unsigned (Int64.sub_overflow x y Int64.zero)))
          (Int.repr (Int64.unsigned (Int64.negative (Int64.sub x y)))) =
  (if Int64.lt x y then Int.one else Int.zero).
Proof.
  intros.
  transitivity (Int.repr (Int64.unsigned (if Int64.lt x y then Int64.one else Int64.zero))).
  rewrite <- (Int64.lt_sub_overflow x y).
  unfold Int64.sub_overflow, Int64.negative.
  set (s := Int64.signed x - Int64.signed y - Int64.signed Int64.zero).
  destruct (zle Int64.min_signed s && zle s Int64.max_signed);
  destruct (Int64.lt (Int64.sub x y) Int64.zero);
  auto.
  destruct (Int64.lt x y); auto.
Qed.

Lemma testcond_for_signed_comparison_64_correct:
  forall c v1 v2 rs m b,
  Val.cmpl_bool c v1 v2 = Some b ->
  eval_testcond (testcond_for_signed_comparison c)
                (nextinstr (compare_longs v1 v2 rs m)) = Some b.
Proof.
  intros. generalize (compare_longs_spec rs v1 v2 m).
  set (rs' := nextinstr (compare_longs v1 v2 rs m)).
  intros [A [B [C [D E]]]].
  destruct v1; destruct v2; simpl in H; inv H.
  unfold eval_testcond. rewrite A; rewrite B; rewrite C; rewrite D.
  simpl; rewrite int64_sub_overflow.
  destruct c; simpl.
  destruct (Int64.eq i i0); auto.
  destruct (Int64.eq i i0); auto.
  destruct (Int64.lt i i0); auto.
  rewrite Int64.not_lt. destruct (Int64.lt i i0); simpl; destruct (Int64.eq i i0); auto.
  rewrite (Int64.lt_not i i0). destruct (Int64.lt i i0); destruct (Int64.eq i i0); reflexivity.
  destruct (Int64.lt i i0); reflexivity.
Qed.

Lemma testcond_for_unsigned_comparison_64_correct:
  forall c v1 v2 rs m b,
  Val.cmplu_bool (Mem.valid_pointer m) c v1 v2 = Some b ->
  eval_testcond (testcond_for_unsigned_comparison c)
                (nextinstr (compare_longs v1 v2 rs m)) = Some b.
Proof.
  intros. generalize (compare_longs_spec rs v1 v2 m).
  set (rs' := nextinstr (compare_longs v1 v2 rs m)).
  intros [A [B [C [D E]]]].
  unfold eval_testcond. rewrite A; rewrite B.
  destruct v1; destruct v2; simpl in H; FuncInv; subst.
- (* int int *)
  destruct c; simpl; auto.
  destruct (Int64.eq i i0); reflexivity.
  destruct (Int64.eq i i0); auto.
  destruct (Int64.ltu i i0); auto.
  rewrite Int64.not_ltu. destruct (Int64.ltu i i0); simpl; destruct (Int64.eq i i0); auto.
  rewrite (Int64.ltu_not i i0). destruct (Int64.ltu i i0); destruct (Int64.eq i i0); reflexivity.
  destruct (Int64.ltu i i0); reflexivity.
- (* int ptr *)
  unfold Val.cmplu; simpl; destruct Archi.ptr64; try discriminate.
  destruct (Int64.eq i Int64.zero &&
    (Mem.valid_pointer m b0 (Ptrofs.unsigned i0) || Mem.valid_pointer m b0 (Ptrofs.unsigned i0 - 1))) eqn:?; try discriminate H.
  destruct c; simpl in *; inv H; auto.
- (* ptr int *)
  unfold Val.cmplu; simpl; destruct Archi.ptr64; try discriminate.
  destruct (Int64.eq i0 Int64.zero &&
    (Mem.valid_pointer m b0 (Ptrofs.unsigned i) || Mem.valid_pointer m b0 (Ptrofs.unsigned i - 1))) eqn:?; try discriminate H.
  destruct c; simpl in *; inv H; auto.
- (* ptr ptr *)
  unfold Val.cmplu; simpl; destruct Archi.ptr64; try discriminate H.
  fold (Mem.weak_valid_pointer m b0 (Ptrofs.unsigned i)) in *.
  fold (Mem.weak_valid_pointer m b1 (Ptrofs.unsigned i0)) in *.
  destruct (eq_block b0 b1).
  destruct (Mem.weak_valid_pointer m b0 (Ptrofs.unsigned i) &&
            Mem.weak_valid_pointer m b1 (Ptrofs.unsigned i0)); inv H.
  destruct c; simpl; auto.
  destruct (Ptrofs.eq i i0); auto.
  destruct (Ptrofs.eq i i0); auto.
  destruct (Ptrofs.ltu i i0); auto.
  rewrite Ptrofs.not_ltu. destruct (Ptrofs.ltu i i0); simpl; destruct (Ptrofs.eq i i0); auto.
  rewrite (Ptrofs.ltu_not i i0). destruct (Ptrofs.ltu i i0); destruct (Ptrofs.eq i i0); reflexivity.
  destruct (Ptrofs.ltu i i0); reflexivity.
  destruct (Mem.valid_pointer m b0 (Ptrofs.unsigned i) &&
            Mem.valid_pointer m b1 (Ptrofs.unsigned i0)); try discriminate H.
  destruct c; simpl in *; inv H; reflexivity.
Qed.

Lemma compare_floats_spec:
  forall rs n1 n2,
  let rs' := nextinstr (compare_floats (Vfloat n1) (Vfloat n2) rs) in
     rs'#ZF = Val.of_bool (Float.cmp Ceq n1 n2 || negb (Float.ordered n1 n2))
  /\ rs'#CF = Val.of_bool (negb (Float.cmp Cge n1 n2))
  /\ rs'#PF = Val.of_bool (negb (Float.ordered n1 n2))
  /\ (forall r, data_preg r = true -> rs'#r = rs#r).
Proof.
  intros. unfold rs'; unfold compare_floats.
  split. auto.
  split. auto.
  split. auto.
  intros. Simplifs.
Qed.

Lemma compare_floats32_spec:
  forall rs n1 n2,
  let rs' := nextinstr (compare_floats32 (Vsingle n1) (Vsingle n2) rs) in
     rs'#ZF = Val.of_bool (Float32.cmp Ceq n1 n2 || negb (Float32.ordered n1 n2))
  /\ rs'#CF = Val.of_bool (negb (Float32.cmp Cge n1 n2))
  /\ rs'#PF = Val.of_bool (negb (Float32.ordered n1 n2))
  /\ (forall r, data_preg r = true -> rs'#r = rs#r).
Proof.
  intros. unfold rs'; unfold compare_floats32.
  split. auto.
  split. auto.
  split. auto.
  intros. Simplifs.
Qed.

Definition eval_extcond (xc: extcond) (rs: regset) : option bool :=
  match xc with
  | Cond_base c =>
      eval_testcond c rs
  | Cond_and c1 c2 =>
      match eval_testcond c1 rs, eval_testcond c2 rs with
      | Some b1, Some b2 => Some (b1 && b2)
      | _, _ => None
      end
  | Cond_or c1 c2 =>
      match eval_testcond c1 rs, eval_testcond c2 rs with
      | Some b1, Some b2 => Some (b1 || b2)
      | _, _ => None
      end
  end.

Definition swap_floats {A: Type} (c: comparison) (n1 n2: A) : A :=
  match c with
  | Clt | Cle => n2
  | Ceq | Cne | Cgt | Cge => n1
  end.

Lemma testcond_for_float_comparison_correct:
  forall c n1 n2 rs,
  eval_extcond (testcond_for_condition (Ccompf c))
               (nextinstr (compare_floats (Vfloat (swap_floats c n1 n2))
                                          (Vfloat (swap_floats c n2 n1)) rs)) =
  Some(Float.cmp c n1 n2).
Proof.
  intros.
  generalize (compare_floats_spec rs (swap_floats c n1 n2) (swap_floats c n2 n1)).
  set (rs' := nextinstr (compare_floats (Vfloat (swap_floats c n1 n2))
                                        (Vfloat (swap_floats c n2 n1)) rs)).
  intros [A [B [C D]]].
  unfold eval_extcond, eval_testcond. rewrite A; rewrite B; rewrite C.
  destruct c; simpl.
- (* eq *)
Transparent Float.cmp Float.ordered.
  unfold Float.ordered, Float.cmp; destruct (Float.compare n1 n2) as [[]|]; reflexivity.
- (* ne *)
  unfold Float.ordered, Float.cmp; destruct (Float.compare n1 n2) as [[]|]; reflexivity.
- (* lt *)
  rewrite <- (Float.cmp_swap Clt n2 n1). simpl. unfold Float.ordered. 
  destruct (Float.compare n2 n1) as [[]|]; reflexivity.
- (* le *)
  rewrite <- (Float.cmp_swap Cge n1 n2). simpl.
  destruct (Float.compare n1 n2) as [[]|]; auto.
- (* gt *)
 unfold Float.ordered, Float.cmp; destruct (Float.compare n1 n2) as [[]|]; reflexivity.
- (* ge *)
  destruct (Float.cmp Cge n1 n2); auto.
Opaque Float.cmp Float.ordered.
Qed.

Lemma testcond_for_neg_float_comparison_correct:
  forall c n1 n2 rs,
  eval_extcond (testcond_for_condition (Cnotcompf c))
               (nextinstr (compare_floats (Vfloat (swap_floats c n1 n2))
                                          (Vfloat (swap_floats c n2 n1)) rs)) =
  Some(negb(Float.cmp c n1 n2)).
Proof.
  intros.
  generalize (compare_floats_spec rs (swap_floats c n1 n2) (swap_floats c n2 n1)).
  set (rs' := nextinstr (compare_floats (Vfloat (swap_floats c n1 n2))
                                        (Vfloat (swap_floats c n2 n1)) rs)).
  intros [A [B [C D]]].
  unfold eval_extcond, eval_testcond. rewrite A; rewrite B; rewrite C.
  destruct c; simpl.
- (* eq *)
Transparent Float.cmp Float.ordered.
  unfold Float.ordered, Float.cmp; destruct (Float.compare n1 n2) as [[]|]; reflexivity.
- (* ne *)
  unfold Float.ordered, Float.cmp; destruct (Float.compare n1 n2) as [[]|]; reflexivity.
- (* lt *)
  rewrite <- (Float.cmp_swap Clt n2 n1). simpl. unfold Float.ordered. 
  destruct (Float.compare n2 n1) as [[]|]; reflexivity.
- (* le *)
  rewrite <- (Float.cmp_swap Cge n1 n2). simpl.
  destruct (Float.compare n1 n2) as [[]|]; auto.
- (* gt *)
 unfold Float.ordered, Float.cmp; destruct (Float.compare n1 n2) as [[]|]; reflexivity.
- (* ge *)
  destruct (Float.cmp Cge n1 n2); auto.
Opaque Float.cmp Float.ordered.
Qed.

Lemma testcond_for_float32_comparison_correct:
  forall c n1 n2 rs,
  eval_extcond (testcond_for_condition (Ccompfs c))
               (nextinstr (compare_floats32 (Vsingle (swap_floats c n1 n2))
                                            (Vsingle (swap_floats c n2 n1)) rs)) =
  Some(Float32.cmp c n1 n2).
Proof.
  intros.
  generalize (compare_floats32_spec rs (swap_floats c n1 n2) (swap_floats c n2 n1)).
  set (rs' := nextinstr (compare_floats32 (Vsingle (swap_floats c n1 n2))
                                        (Vsingle (swap_floats c n2 n1)) rs)).
  intros [A [B [C D]]].
  unfold eval_extcond, eval_testcond. rewrite A; rewrite B; rewrite C.
  destruct c; simpl.
- (* eq *)
Transparent Float32.cmp Float32.ordered.
  unfold Float32.ordered, Float32.cmp; destruct (Float32.compare n1 n2) as [[]|]; reflexivity.
- (* ne *)
  unfold Float32.ordered, Float32.cmp; destruct (Float32.compare n1 n2) as [[]|]; reflexivity.
- (* lt *)
  rewrite <- (Float32.cmp_swap Clt n2 n1). simpl. unfold Float32.ordered. 
  destruct (Float32.compare n2 n1) as [[]|]; reflexivity.
- (* le *)
  rewrite <- (Float32.cmp_swap Cge n1 n2). simpl.
  destruct (Float32.compare n1 n2) as [[]|]; auto.
- (* gt *)
 unfold Float32.ordered, Float32.cmp; destruct (Float32.compare n1 n2) as [[]|]; reflexivity.
- (* ge *)
  destruct (Float32.cmp Cge n1 n2); auto.
Opaque Float32.cmp Float32.ordered.
Qed.

Lemma testcond_for_neg_float32_comparison_correct:
  forall c n1 n2 rs,
  eval_extcond (testcond_for_condition (Cnotcompfs c))
               (nextinstr (compare_floats32 (Vsingle (swap_floats c n1 n2))
                                            (Vsingle (swap_floats c n2 n1)) rs)) =
  Some(negb(Float32.cmp c n1 n2)).
Proof.
  intros.
  generalize (compare_floats32_spec rs (swap_floats c n1 n2) (swap_floats c n2 n1)).
  set (rs' := nextinstr (compare_floats32 (Vsingle (swap_floats c n1 n2))
                                          (Vsingle (swap_floats c n2 n1)) rs)).
  intros [A [B [C D]]].
  unfold eval_extcond, eval_testcond. rewrite A; rewrite B; rewrite C.
  destruct c; simpl.
- (* eq *)
Transparent Float32.cmp Float32.ordered.
  unfold Float32.ordered, Float32.cmp; destruct (Float32.compare n1 n2) as [[]|]; reflexivity.
- (* ne *)
  unfold Float32.ordered, Float32.cmp; destruct (Float32.compare n1 n2) as [[]|]; reflexivity.
- (* lt *)
  rewrite <- (Float32.cmp_swap Clt n2 n1). simpl. unfold Float32.ordered. 
  destruct (Float32.compare n2 n1) as [[]|]; reflexivity.
- (* le *)
  rewrite <- (Float32.cmp_swap Cge n1 n2). simpl.
  destruct (Float32.compare n1 n2) as [[]|]; auto.
- (* gt *)
 unfold Float32.ordered, Float32.cmp; destruct (Float32.compare n1 n2) as [[]|]; reflexivity.
- (* ge *)
  destruct (Float32.cmp Cge n1 n2); auto.
Opaque Float32.cmp Float32.ordered.
Qed.

Remark swap_floats_commut:
  forall (A B: Type) c (f: A -> B) x y, swap_floats c (f x) (f y) = f (swap_floats c x y).
Proof.
  intros. destruct c; auto.
Qed.

Remark compare_floats_inv:
  forall vx vy rs r,
  r <> CR ZF -> r <> CR CF -> r <> CR PF -> r <> CR SF -> r <> CR OF ->
  compare_floats vx vy rs r = rs r.
Proof.
  intros.
  assert (DFL: undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs r = rs r).
    simpl. Simplifs.
  unfold compare_floats; destruct vx; destruct vy; auto. Simplifs.
Qed.

Remark compare_floats32_inv:
  forall vx vy rs r,
  r <> CR ZF -> r <> CR CF -> r <> CR PF -> r <> CR SF -> r <> CR OF ->
  compare_floats32 vx vy rs r = rs r.
Proof.
  intros.
  assert (DFL: undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs r = rs r).
    simpl. Simplifs.
  unfold compare_floats32; destruct vx; destruct vy; auto. Simplifs.
Qed.

Lemma transl_cond_correct:
  forall cond args k c rs m,
  transl_cond cond args k = OK c ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ match eval_condition cond (map rs (map preg_of args)) m with
     | None => True
     | Some b => eval_extcond (testcond_for_condition cond) rs' = Some b
     end
  /\ forall r, data_preg r = true -> rs'#r = rs r.
Proof.
  unfold transl_cond; intros.
  destruct cond; repeat (destruct args; try discriminate); monadInv H.
- (* comp *)
  simpl. rewrite (ireg_of_eq _ _ EQ). rewrite (ireg_of_eq _ _ EQ1).
  econstructor. split. apply exec_straight_one. simpl. eauto. auto.
  split. destruct (Val.cmp_bool c0 (rs x) (rs x0)) eqn:?; auto.
  eapply testcond_for_signed_comparison_32_correct; eauto.
  intros. unfold compare_ints. Simplifs.
- (* compu *)
  simpl. rewrite (ireg_of_eq _ _ EQ). rewrite (ireg_of_eq _ _ EQ1).
  econstructor. split. apply exec_straight_one. simpl. eauto. auto.
  split. destruct (Val.cmpu_bool (Mem.valid_pointer m) c0 (rs x) (rs x0)) eqn:?; auto.
  eapply testcond_for_unsigned_comparison_32_correct; eauto.
  intros. unfold compare_ints. Simplifs.
- (* compimm *)
  simpl. rewrite (ireg_of_eq _ _ EQ). destruct (Int.eq_dec n Int.zero).
  econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split. destruct (rs x); simpl; auto. subst. rewrite Int.and_idem.
  eapply testcond_for_signed_comparison_32_correct; eauto.
  intros. unfold compare_ints. Simplifs.
  econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split. destruct (Val.cmp_bool c0 (rs x) (Vint n)) eqn:?; auto.
  eapply testcond_for_signed_comparison_32_correct; eauto.
  intros. unfold compare_ints. Simplifs.
- (* compuimm *)
  simpl. rewrite (ireg_of_eq _ _ EQ).
  econstructor. split. apply exec_straight_one. simpl. eauto. auto.
  split. destruct (Val.cmpu_bool (Mem.valid_pointer m) c0 (rs x) (Vint n)) eqn:?; auto.
  eapply testcond_for_unsigned_comparison_32_correct; eauto.
  intros. unfold compare_ints. Simplifs.
- (* compl *)
  simpl. rewrite (ireg_of_eq _ _ EQ). rewrite (ireg_of_eq _ _ EQ1).
  econstructor. split. apply exec_straight_one. simpl. eauto. auto.
  split. destruct (Val.cmpl_bool c0 (rs x) (rs x0)) eqn:?; auto.
  eapply testcond_for_signed_comparison_64_correct; eauto.
  intros. unfold compare_longs. Simplifs.
- (* complu *)
  simpl. rewrite (ireg_of_eq _ _ EQ). rewrite (ireg_of_eq _ _ EQ1).
  econstructor. split. apply exec_straight_one. simpl. eauto. auto.
  split. destruct (Val.cmplu_bool (Mem.valid_pointer m) c0 (rs x) (rs x0)) eqn:?; auto.
  eapply testcond_for_unsigned_comparison_64_correct; eauto.
  intros. unfold compare_longs. Simplifs.
- (* compimm *)
  simpl. rewrite (ireg_of_eq _ _ EQ). destruct (Int64.eq_dec n Int64.zero).
  econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split. destruct (rs x); simpl; auto. subst. rewrite Int64.and_idem.
  eapply testcond_for_signed_comparison_64_correct; eauto.
  intros. unfold compare_longs. Simplifs.
  econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split. destruct (Val.cmpl_bool c0 (rs x) (Vlong n)) eqn:?; auto.
  eapply testcond_for_signed_comparison_64_correct; eauto.
  intros. unfold compare_longs. Simplifs.
- (* compuimm *)
  simpl. rewrite (ireg_of_eq _ _ EQ).
  econstructor. split. apply exec_straight_one. simpl. eauto. auto.
  split. destruct (Val.cmplu_bool (Mem.valid_pointer m) c0 (rs x) (Vlong n)) eqn:?; auto.
  eapply testcond_for_unsigned_comparison_64_correct; eauto.
  intros. unfold compare_longs. Simplifs.
- (* compf *)
  simpl. rewrite (freg_of_eq _ _ EQ). rewrite (freg_of_eq _ _ EQ1).
  exists (nextinstr (compare_floats (swap_floats c0 (rs x) (rs x0)) (swap_floats c0 (rs x0) (rs x)) rs)).
  split. apply exec_straight_one.
  destruct c0; simpl; auto.
  unfold nextinstr. rewrite Pregmap.gss. rewrite compare_floats_inv; auto with asmgen.
  split. destruct (rs x); destruct (rs x0); simpl; auto.
  repeat rewrite swap_floats_commut. apply testcond_for_float_comparison_correct.
  intros. Simplifs. apply compare_floats_inv; auto with asmgen.
- (* notcompf *)
  simpl. rewrite (freg_of_eq _ _ EQ). rewrite (freg_of_eq _ _ EQ1).
  exists (nextinstr (compare_floats (swap_floats c0 (rs x) (rs x0)) (swap_floats c0 (rs x0) (rs x)) rs)).
  split. apply exec_straight_one.
  destruct c0; simpl; auto.
  unfold nextinstr. rewrite Pregmap.gss. rewrite compare_floats_inv; auto with asmgen.
  split. destruct (rs x); destruct (rs x0); simpl; auto.
  repeat rewrite swap_floats_commut. apply testcond_for_neg_float_comparison_correct.
  intros. Simplifs. apply compare_floats_inv; auto with asmgen.
- (* compfs *)
  simpl. rewrite (freg_of_eq _ _ EQ). rewrite (freg_of_eq _ _ EQ1).
  exists (nextinstr (compare_floats32 (swap_floats c0 (rs x) (rs x0)) (swap_floats c0 (rs x0) (rs x)) rs)).
  split. apply exec_straight_one.
  destruct c0; simpl; auto.
  unfold nextinstr. rewrite Pregmap.gss. rewrite compare_floats32_inv; auto with asmgen.
  split. destruct (rs x); destruct (rs x0); simpl; auto.
  repeat rewrite swap_floats_commut. apply testcond_for_float32_comparison_correct.
  intros. Simplifs. apply compare_floats32_inv; auto with asmgen.
- (* notcompfs *)
  simpl. rewrite (freg_of_eq _ _ EQ). rewrite (freg_of_eq _ _ EQ1).
  exists (nextinstr (compare_floats32 (swap_floats c0 (rs x) (rs x0)) (swap_floats c0 (rs x0) (rs x)) rs)).
  split. apply exec_straight_one.
  destruct c0; simpl; auto.
  unfold nextinstr. rewrite Pregmap.gss. rewrite compare_floats32_inv; auto with asmgen.
  split. destruct (rs x); destruct (rs x0); simpl; auto.
  repeat rewrite swap_floats_commut. apply testcond_for_neg_float32_comparison_correct.
  intros. Simplifs. apply compare_floats32_inv; auto with asmgen.
- (* maskzero *)
  simpl. rewrite (ireg_of_eq _ _ EQ).
  econstructor. split. apply exec_straight_one. simpl; eauto. auto.
  split. destruct (rs x); simpl; auto.
  generalize (compare_ints_spec rs (Vint (Int.and i n)) Vzero m).
  intros [A B]. rewrite A. unfold Val.cmpu; simpl. destruct (Int.eq (Int.and i n) Int.zero); auto.
  intros. unfold compare_ints. Simplifs.
- (* masknotzero *)
  simpl. rewrite (ireg_of_eq _ _ EQ).
  econstructor. split. apply exec_straight_one. simpl; eauto. auto.
  split. destruct (rs x); simpl; auto.
  generalize (compare_ints_spec rs (Vint (Int.and i n)) Vzero m).
  intros [A B]. rewrite A. unfold Val.cmpu; simpl. destruct (Int.eq (Int.and i n) Int.zero); auto.
  intros. unfold compare_ints. Simplifs.
Qed.

Remark eval_testcond_nextinstr:
  forall c rs, eval_testcond c (nextinstr rs) = eval_testcond c rs.
Proof.
  intros. unfold eval_testcond. repeat rewrite nextinstr_inv; auto with asmgen.
Qed.

Remark eval_testcond_set_ireg:
  forall c rs r v, eval_testcond c (rs#(IR r) <- v) = eval_testcond c rs.
Proof.
  intros. unfold eval_testcond. repeat rewrite Pregmap.gso; auto with asmgen.
Qed.

Lemma mk_setcc_base_correct:
  forall cond rd k rs1 m,
  exists rs2,
  exec_straight ge fn (mk_setcc_base cond rd k) rs1 m k rs2 m
  /\ rs2#rd = Val.of_optbool(eval_extcond cond rs1)
  /\ forall r, data_preg r = true -> r <> RAX /\ r <> RCX -> r <> rd -> rs2#r = rs1#r.
Proof.
  intros. destruct cond; simpl in *.
- (* base *)
  econstructor; split.
  apply exec_straight_one. simpl; eauto. auto.
  split. Simplifs. intros; Simplifs.
- (* or *)
  assert (Val.of_optbool
    match eval_testcond c1 rs1 with
    | Some b1 =>
        match eval_testcond c2 rs1 with
        | Some b2 => Some (b1 || b2)
        | None => None
        end
    | None => None
    end =
    Val.or (Val.of_optbool (eval_testcond c1 rs1)) (Val.of_optbool (eval_testcond c2 rs1))).
  destruct (eval_testcond c1 rs1). destruct (eval_testcond c2 rs1).
  destruct b; destruct b0; auto.
  destruct b; auto.
  auto.
  rewrite H; clear H.
  destruct (ireg_eq rd RAX).
  subst rd. econstructor; split.
  eapply exec_straight_three.
  simpl; eauto.
  simpl. rewrite eval_testcond_nextinstr. repeat rewrite eval_testcond_set_ireg. eauto.
  simpl; eauto.
  auto. auto. auto.
  intuition Simplifs.
  econstructor; split.
  eapply exec_straight_three.
  simpl; eauto.
  simpl. rewrite eval_testcond_nextinstr. repeat rewrite eval_testcond_set_ireg. eauto.
  simpl. eauto.
  auto. auto. auto.
  split. Simplifs. rewrite Val.or_commut. decEq; Simplifs.
  intros. destruct H0; Simplifs.
- (* and *)
  assert (Val.of_optbool
    match eval_testcond c1 rs1 with
    | Some b1 =>
        match eval_testcond c2 rs1 with
        | Some b2 => Some (b1 && b2)
        | None => None
        end
    | None => None
    end =
    Val.and (Val.of_optbool (eval_testcond c1 rs1)) (Val.of_optbool (eval_testcond c2 rs1))).
  {
    destruct (eval_testcond c1 rs1). destruct (eval_testcond c2 rs1).
    destruct b; destruct b0; auto.
    destruct b; auto.
    auto.
  }
  rewrite H; clear H.
  destruct (ireg_eq rd RAX).
  subst rd. econstructor; split.
  eapply exec_straight_three.
  simpl; eauto.
  simpl. rewrite eval_testcond_nextinstr. repeat rewrite eval_testcond_set_ireg. eauto.
  simpl; eauto.
  auto. auto. auto.
  intuition Simplifs.
  econstructor; split.
  eapply exec_straight_three.
  simpl; eauto.
  simpl. rewrite eval_testcond_nextinstr. repeat rewrite eval_testcond_set_ireg. eauto.
  simpl. eauto.
  auto. auto. auto.
  split. Simplifs. rewrite Val.and_commut. decEq; Simplifs.
  intros. destruct H0; Simplifs.
Qed.

Lemma mk_setcc_correct:
  forall cond rd k rs1 m,
  exists rs2,
  exec_straight ge fn (mk_setcc cond rd k) rs1 m k rs2 m
  /\ rs2#rd = Val.of_optbool(eval_extcond cond rs1)
  /\ forall r, data_preg r = true -> r <> RAX /\ r <> RCX -> r <> rd -> rs2#r = rs1#r.
Proof.
  intros. unfold mk_setcc. destruct (Archi.ptr64 || low_ireg rd).
- apply mk_setcc_base_correct.
- exploit mk_setcc_base_correct. intros [rs2 [A [B C]]].
  econstructor; split. eapply exec_straight_trans. eexact A. apply exec_straight_one.
    simpl. eauto. simpl. auto.
  intuition Simplifs.
Qed.

(** Translation of arithmetic operations. *)

Ltac ArgsInv :=
  match goal with
  | [ H: Error _ = OK _ |- _ ] => discriminate
  | [ H: match ?args with nil => _ | _ :: _ => _ end = OK _ |- _ ] => destruct args; ArgsInv
  | [ H: bind _ _ = OK _ |- _ ] => monadInv H; ArgsInv
  | [ H: match _ with left _ => _ | right _ => assertion_failed end = OK _ |- _ ] => monadInv H; ArgsInv
  | [ H: match _ with true => _ | false => assertion_failed end = OK _ |- _ ] => monadInv H; ArgsInv
  | [ H: ireg_of _ = OK _ |- _ ] => simpl in *; rewrite (ireg_of_eq _ _ H) in *; clear H; ArgsInv
  | [ H: freg_of _ = OK _ |- _ ] => simpl in *; rewrite (freg_of_eq _ _ H) in *; clear H; ArgsInv
  | _ => idtac
  end.

Ltac TranslOp :=
  econstructor; split;
  [ apply exec_straight_one; [ simpl; eauto | auto ]
  | split; [ Simplifs | intros; Simplifs ]].

Lemma transl_op_correct:
  forall op args res k c (rs: regset) m v,
  transl_op op args res k = OK c ->
  eval_operation ge (rs#RSP) op (map rs (map preg_of args)) m = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef v rs'#(preg_of res)
  /\ forall r, data_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs' r = rs r.
Proof.
Transparent destroyed_by_op.
  intros until v; intros TR EV.
  assert (SAME:
  (exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of res) = v
  /\ forall r, data_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs' r = rs r) ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef v rs'#(preg_of res)
  /\ forall r, data_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs' r = rs r).
  {
    intros [rs' [A [B C]]]. subst v. exists rs'; auto.
  }

  destruct op; simpl in TR; ArgsInv; simpl in EV; try (inv EV); try (apply SAME; TranslOp; fail).
(* move *)
  exploit mk_mov_correct; eauto. intros [rs2 [A [B C]]].
  apply SAME. exists rs2. eauto.
(* intconst *)
  apply SAME. destruct (Int.eq_dec n Int.zero). subst n. TranslOp. TranslOp.
(* longconst *)
  apply SAME. destruct (Int64.eq_dec n Int64.zero). subst n. TranslOp. TranslOp.
(* floatconst *)
  apply SAME. destruct (Float.eq_dec n Float.zero). subst n. TranslOp. TranslOp.
(* singleconst *)
  apply SAME. destruct (Float32.eq_dec n Float32.zero). subst n. TranslOp. TranslOp.
(* cast8signed *)
  apply SAME. eapply mk_intconv_correct; eauto.
(* cast8unsigned *)
  apply SAME. eapply mk_intconv_correct; eauto.
(* mulhs *)
  apply SAME. TranslOp. destruct H1. Simplifs.
(* mulhu *)
  apply SAME. TranslOp. destruct H1. Simplifs.
(* div *)
  apply SAME.
  exploit (divs_mods_exists (rs RAX) (rs RCX)). left; congruence.
  intros (nh & nl & d & q & r & A & B & C & D & E & F).
  set (rs1 := nextinstr_nf (rs#RDX <- (Vint nh))).
  econstructor; split.
  eapply exec_straight_two with (rs2 := rs1). simpl. rewrite A. reflexivity.
  simpl. change (rs1 RAX) with (rs RAX); rewrite B.
  change (rs1 RCX) with (rs RCX); rewrite C.
  rewrite D. reflexivity. auto. auto.
  split. change (Vint q = v). congruence.
  simpl; intros. destruct H2. unfold rs1; Simplifs.
(* divu *)
  apply SAME.
  exploit (divu_modu_exists (rs RAX) (rs RCX)). left; congruence.
  intros (n & d & q & r & B & C & D & E & F).
  set (rs1 := nextinstr_nf (rs#RDX <- Vzero)).
  econstructor; split.
  eapply exec_straight_two with (rs2 := rs1). reflexivity.
  simpl. change (rs1 RAX) with (rs RAX); rewrite B.
  change (rs1 RCX) with (rs RCX); rewrite C.
  rewrite D. reflexivity. auto. auto.
  split. change (Vint q = v). congruence.
  simpl; intros. destruct H2. unfold rs1; Simplifs.
(* mod *)
  apply SAME.
  exploit (divs_mods_exists (rs RAX) (rs RCX)). right; congruence.
  intros (nh & nl & d & q & r & A & B & C & D & E & F).
  set (rs1 := nextinstr_nf (rs#RDX <- (Vint nh))).
  econstructor; split.
  eapply exec_straight_two with (rs2 := rs1). simpl. rewrite A. reflexivity.
  simpl. change (rs1 RAX) with (rs RAX); rewrite B.
  change (rs1 RCX) with (rs RCX); rewrite C.
  rewrite D. reflexivity. auto. auto.
  split. change (Vint r = v). congruence.
  simpl; intros. destruct H2. unfold rs1; Simplifs.
(* modu *)
  apply SAME.
  exploit (divu_modu_exists (rs RAX) (rs RCX)). right; congruence.
  intros (n & d & q & r & B & C & D & E & F).
  set (rs1 := nextinstr_nf (rs#RDX <- Vzero)).
  econstructor; split.
  eapply exec_straight_two with (rs2 := rs1). reflexivity.
  simpl. change (rs1 RAX) with (rs RAX); rewrite B.
  change (rs1 RCX) with (rs RCX); rewrite C.
  rewrite D. reflexivity. auto. auto.
  split. change (Vint r = v). congruence.
  simpl; intros. destruct H2. unfold rs1; Simplifs.
(* shrximm *)
  apply SAME. eapply mk_shrximm_correct; eauto.
(* lea *)
  exploit transl_addressing_mode_32_correct; eauto. intros EA.
  TranslOp. rewrite nextinstr_inv; auto with asmgen. rewrite Pregmap.gss. rewrite normalize_addrmode_32_correct; auto.
(* mullhs *)
  apply SAME. TranslOp. destruct H1. Simplifs.
(* mullhu *)
  apply SAME. TranslOp. destruct H1. Simplifs.
(* divl *)
  apply SAME.
  exploit (divls_modls_exists (rs RAX) (rs RCX)). left; congruence.
  intros (nh & nl & d & q & r & A & B & C & D & E & F).
  set (rs1 := nextinstr_nf (rs#RDX <- (Vlong nh))).
  econstructor; split.
  eapply exec_straight_two with (rs2 := rs1). simpl. rewrite A. reflexivity.
  simpl. change (rs1 RAX) with (rs RAX); rewrite B.
  change (rs1 RCX) with (rs RCX); rewrite C.
  rewrite D. reflexivity. auto. auto.
  split. change (Vlong q = v). congruence.
  simpl; intros. destruct H2. unfold rs1; Simplifs.
(* divlu *)
  apply SAME.
  exploit (divlu_modlu_exists (rs RAX) (rs RCX)). left; congruence.
  intros (n & d & q & r & B & C & D & E & F).
  set (rs1 := nextinstr_nf (rs#RDX <- (Vlong Int64.zero))).
  econstructor; split.
  eapply exec_straight_two with (rs2 := rs1). reflexivity.
  simpl. change (rs1 RAX) with (rs RAX); rewrite B.
  change (rs1 RCX) with (rs RCX); rewrite C.
  rewrite D. reflexivity. auto. auto.
  split. change (Vlong q = v). congruence.
  simpl; intros. destruct H2. unfold rs1; Simplifs.
(* modl *)
  apply SAME.
  exploit (divls_modls_exists (rs RAX) (rs RCX)). right; congruence.
  intros (nh & nl & d & q & r & A & B & C & D & E & F).
  set (rs1 := nextinstr_nf (rs#RDX <- (Vlong nh))).
  econstructor; split.
  eapply exec_straight_two with (rs2 := rs1). simpl. rewrite A. reflexivity.
  simpl. change (rs1 RAX) with (rs RAX); rewrite B.
  change (rs1 RCX) with (rs RCX); rewrite C.
  rewrite D. reflexivity. auto. auto.
  split. change (Vlong r = v). congruence.
  simpl; intros. destruct H2. unfold rs1; Simplifs.
(* modlu *)
  apply SAME.
  exploit (divlu_modlu_exists (rs RAX) (rs RCX)). right; congruence.
  intros (n & d & q & r & B & C & D & E & F).
  set (rs1 := nextinstr_nf (rs#RDX <- (Vlong Int64.zero))).
  econstructor; split.
  eapply exec_straight_two with (rs2 := rs1). reflexivity.
  simpl. change (rs1 RAX) with (rs RAX); rewrite B.
  change (rs1 RCX) with (rs RCX); rewrite C.
  rewrite D. reflexivity. auto. auto.
  split. change (Vlong r = v). congruence.
  simpl; intros. destruct H2. unfold rs1; Simplifs.
(* shrxlimm *)
  apply SAME. eapply mk_shrxlimm_correct; eauto.
(* leal *)
  exploit transl_addressing_mode_64_correct; eauto. intros EA.
  generalize (normalize_addrmode_64_correct x rs). destruct (normalize_addrmode_64 x) as [am' [delta|]]; intros EV.
  econstructor; split. eapply exec_straight_two.
  simpl. reflexivity.  simpl. reflexivity. auto. auto.
  split. rewrite nextinstr_nf_inv by auto. rewrite Pregmap.gss. rewrite nextinstr_inv by auto with asmgen.
  rewrite Pregmap.gss. rewrite <- EV; auto.
  intros; Simplifs.
  TranslOp. rewrite nextinstr_inv; auto with asmgen. rewrite Pregmap.gss; auto. rewrite <- EV; auto.
(* intoffloat *)
  apply SAME. TranslOp. rewrite H0; auto.
(* floatofint *)
  apply SAME. TranslOp. rewrite H0; auto.
(* intofsingle *)
  apply SAME. TranslOp. rewrite H0; auto.
(* singleofint *)
  apply SAME. TranslOp. rewrite H0; auto.
(* longoffloat *)
  apply SAME. TranslOp. rewrite H0; auto.
(* floatoflong *)
  apply SAME. TranslOp. rewrite H0; auto.
(* longofsingle *)
  apply SAME. TranslOp. rewrite H0; auto.
(* singleoflong *)
  apply SAME. TranslOp. rewrite H0; auto.
(* condition *)
  exploit transl_cond_correct; eauto. intros [rs2 [P [Q R]]].
  exploit mk_setcc_correct; eauto. intros [rs3 [S [T U]]].
  exists rs3.
  split. eapply exec_straight_trans. eexact P. eexact S.
  split. rewrite T. destruct (eval_condition cond rs ## (preg_of ## args) m).
  rewrite Q. auto.
  simpl; auto.
  intros. transitivity (rs2 r); auto.
Qed.

(** Translation of memory loads. *)

Lemma transl_load_correct:
  forall chunk addr args dest k c (rs: regset) m a v,
  transl_load chunk addr args dest k = OK c ->
  eval_addressing ge (rs#RSP) addr (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dest) = v
  /\ forall r, data_preg r = true -> r <> preg_of dest -> rs'#r = rs#r.
Proof.
  unfold transl_load; intros. monadInv H.
  exploit transl_addressing_mode_correct; eauto. intro EA.
  assert (EA': eval_addrmode ge x rs = a). destruct a; simpl in H1; try discriminate; inv EA; auto.
  set (rs2 := nextinstr_nf (rs#(preg_of dest) <- v)).
  assert (exec_load ge chunk m x rs (preg_of dest) = Next rs2 m).
    unfold exec_load. rewrite EA'. rewrite H1. auto.
  assert (rs2 PC = Val.offset_ptr (rs PC) Ptrofs.one).
    transitivity (Val.offset_ptr ((rs#(preg_of dest) <- v) PC) Ptrofs.one).
    auto. decEq. apply Pregmap.gso; auto with asmgen.
  exists rs2. split.
  destruct chunk; ArgsInv; apply exec_straight_one; auto.
  split. unfold rs2. rewrite nextinstr_nf_inv1. Simplifs. apply preg_of_data.
  intros. unfold rs2. Simplifs.
Qed.

Lemma transl_store_correct:
  forall chunk addr args src k c (rs: regset) m a m',
  transl_store chunk addr args src k = OK c ->
  eval_addressing ge (rs#RSP) addr (map rs (map preg_of args)) = Some a ->
  Mem.storev chunk m a (rs (preg_of src)) = Some m' ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, data_preg r = true -> preg_notin r (destroyed_by_store chunk addr) -> rs'#r = rs#r.
Proof.
  unfold transl_store; intros. monadInv H.
  exploit transl_addressing_mode_correct; eauto. intro EA.
  assert (EA': eval_addrmode ge x rs = a). destruct a; simpl in H1; try discriminate; inv EA; auto.
  rewrite <- EA' in H1. destruct chunk; ArgsInv.
(* int8signed *)
  eapply mk_storebyte_correct; eauto.
  destruct (eval_addrmode ge x rs); simpl; auto. rewrite <- Mem.store_signed_unsigned_8; auto.
(* int8unsigned *)
  eapply mk_storebyte_correct; eauto.
(* int16signed *)
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_store.
  replace (Mem.storev Mint16unsigned m (eval_addrmode ge x rs) (rs x0))
     with (Mem.storev Mint16signed m (eval_addrmode ge x rs) (rs x0)).
  rewrite H1. eauto.
  destruct (eval_addrmode ge x rs); simpl; auto. rewrite Mem.store_signed_unsigned_16; auto.
  auto.
  intros. Simplifs.
(* int16unsigned *)
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_store. rewrite H1. eauto. auto.
  intros. Simplifs.
(* int32 *)
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_store. rewrite H1. eauto. auto.
  intros. Simplifs.
(* int64 *)
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_store. rewrite H1. eauto. auto.
  intros. Simplifs.
(* float32 *)
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_store. rewrite H1. eauto. auto.
  intros. Transparent destroyed_by_store. simpl in H2. simpl. Simplifs.
(* float64 *)
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_store. rewrite H1. eauto. auto.
  intros. Simplifs.
Qed.

End CONSTRUCTORS.
