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

(** Correctness proof for IA32 generation: auxiliary results. *)

Require Import Coqlib.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import Asm.
Require Import Asmgen.
Require Import Asmgenproof0.
Require Import Conventions.

Open Local Scope error_monad_scope.

(** * Correspondence between Mach registers and IA32 registers *)

Lemma agree_nextinstr_nf:
  forall ms sp rs,
  agree ms sp rs -> agree ms sp (nextinstr_nf rs).
Proof.
  intros. unfold nextinstr_nf. apply agree_nextinstr. 
  apply agree_undef_nondata_regs. auto.
  intro. simpl. ElimOrEq; auto. 
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
  (nextinstr_nf (rs#(preg_of m) <- v))#PC = Val.add rs#PC Vone.
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

(** * Correctness of IA32 constructor functions *)

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
(* movd *)
  econstructor. split. apply exec_straight_one. simpl. eauto. auto. 
  split. Simplifs. intros; Simplifs.
Qed.

(** Properties of division *)

Remark divs_mods_exist:
  forall v1 v2,
  match Val.divs v1 v2, Val.mods v1 v2 with
  | Some _, Some _ => True
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros. unfold Val.divs, Val.mods. destruct v1; auto. destruct v2; auto.
  destruct (Int.eq i0 Int.zero || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); auto. 
Qed.

Remark divu_modu_exist:
  forall v1 v2,
  match Val.divu v1 v2, Val.modu v1 v2 with
  | Some _, Some _ => True
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros. unfold Val.divu, Val.modu. destruct v1; auto. destruct v2; auto.
  destruct (Int.eq i0 Int.zero); auto. 
Qed.

(** Smart constructor for [shrx] *)

Lemma mk_shrximm_correct:
  forall n k c (rs1: regset) v m,
  mk_shrximm n k = OK c ->
  Val.shrx (rs1#EAX) (Vint n) = Some v ->
  exists rs2,
     exec_straight ge fn c rs1 m k rs2 m
  /\ rs2#EAX = v
  /\ forall r, data_preg r = true -> r <> EAX -> r <> ECX -> rs2#r = rs1#r.
Proof.
  unfold mk_shrximm; intros. inv H.
  exploit Val.shrx_shr; eauto. intros [x [y [A [B C]]]].
  inversion B; clear B; subst y; subst v; clear H0.
  set (tnm1 := Int.sub (Int.shl Int.one n) Int.one).
  set (x' := Int.add x tnm1).
  set (rs2 := nextinstr (compare_ints (Vint x) (Vint Int.zero) rs1 m)).
  set (rs3 := nextinstr (rs2#ECX <- (Vint x'))).
  set (rs4 := nextinstr (if Int.lt x Int.zero then rs3#EAX <- (Vint x') else rs3)).
  set (rs5 := nextinstr_nf (rs4#EAX <- (Val.shr rs4#EAX (Vint n)))).
  assert (rs3#EAX = Vint x). unfold rs3. Simplifs.
  assert (rs3#ECX = Vint x'). unfold rs3. Simplifs.
  exists rs5. split. 
  apply exec_straight_step with rs2 m. simpl. rewrite A. simpl. rewrite Int.and_idem. auto. auto.
  apply exec_straight_step with rs3 m. simpl. 
  change (rs2 EAX) with (rs1 EAX). rewrite A. simpl. 
  rewrite (Int.add_commut Int.zero tnm1). rewrite Int.add_zero. auto. auto.
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

(** Smart constructor for integer conversions *)

Lemma mk_intconv_correct:
  forall mk sem rd rs k c rs1 m,
  mk_intconv mk rd rs k = OK c ->
  (forall c rd rs r m,
   exec_instr ge c (mk rd rs) r m = Next (nextinstr (r#rd <- (sem r#rs))) m) ->
  exists rs2,
     exec_straight ge fn c rs1 m k rs2 m
  /\ rs2#rd = sem rs1#rs
  /\ forall r, data_preg r = true -> r <> rd -> r <> EAX -> rs2#r = rs1#r.
Proof.
  unfold mk_intconv; intros. destruct (low_ireg rs); monadInv H.
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
  eval_addrmode ge a rs1 = eval_addrmode ge a rs2.
Proof.
  intros until rs2; intro AG. unfold addressing_mentions, eval_addrmode.
  destruct a. intros. destruct (orb_false_elim _ _ H). unfold proj_sumbool in *.
  decEq. destruct base; auto. apply AG. destruct (ireg_eq r i); congruence.
  decEq. destruct ofs as [[r' sc] | ]; auto. rewrite AG; auto. destruct (ireg_eq r r'); congruence.
Qed.

Lemma mk_smallstore_correct:
  forall chunk sto addr r k c rs1 m1 m2,
  mk_smallstore sto addr r k = OK c ->
  Mem.storev chunk m1 (eval_addrmode ge addr rs1) (rs1 r) = Some m2 ->
  (forall c r addr rs m,
   exec_instr ge c (sto addr r) rs m = exec_store ge chunk m addr rs r nil) ->
  exists rs2,
     exec_straight ge fn c rs1 m1 k rs2 m2
  /\ forall r, data_preg r = true -> r <> EAX /\ r <> ECX -> rs2#r = rs1#r.
Proof.
  unfold mk_smallstore; intros. 
  remember (low_ireg r) as low. destruct low.
(* low reg *)
  monadInv H. econstructor; split. apply exec_straight_one. rewrite H1. 
  unfold exec_store. rewrite H0. eauto. auto.
  intros; Simplifs.
(* high reg *)
   remember (addressing_mentions addr EAX) as mentions. destruct mentions; monadInv H.
(* EAX is mentioned. *)
  assert (r <> ECX). red; intros; subst r; discriminate. 
  set (rs2 := nextinstr (rs1#ECX <- (eval_addrmode ge addr rs1))).
  set (rs3 := nextinstr (rs2#EAX <- (rs1 r))).
  econstructor; split.
  apply exec_straight_three with rs2 m1 rs3 m1. 
  simpl. auto. 
  simpl. replace (rs2 r) with (rs1 r). auto. symmetry. unfold rs2; Simplifs. 
  rewrite H1. unfold exec_store. simpl. rewrite Int.add_zero. 
  change (rs3 EAX) with (rs1 r).
  change (rs3 ECX) with (eval_addrmode ge addr rs1).
  replace (Val.add (eval_addrmode ge addr rs1) (Vint Int.zero))
     with (eval_addrmode ge addr rs1).
  rewrite H0. eauto.
  destruct (eval_addrmode ge addr rs1); simpl in H0; try discriminate.
  simpl. rewrite Int.add_zero; auto. 
  auto. auto. auto. 
  intros. destruct H3. Simplifs. unfold rs3; Simplifs. unfold rs2; Simplifs. 
(* EAX is not mentioned *)
  set (rs2 := nextinstr (rs1#EAX <- (rs1 r))).
  econstructor; split.
  apply exec_straight_two with rs2 m1.
  simpl. auto.
  rewrite H1. unfold exec_store. 
  rewrite (addressing_mentions_correct addr EAX rs2 rs1); auto.
  change (rs2 EAX) with (rs1 r). rewrite H0. eauto. 
  intros. unfold rs2; Simplifs.
  auto. auto.
  intros. destruct H2. simpl. Simplifs. unfold rs2; Simplifs.
Qed.

(** Accessing slots in the stack frame *)

Lemma loadind_correct:
  forall (base: ireg) ofs ty dst k (rs: regset) c m v,
  loadind base ofs ty dst k = OK c ->
  Mem.loadv (chunk_of_type ty) m (Val.add rs#base (Vint ofs)) = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, data_preg r = true -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  unfold loadind; intros.
  set (addr := Addrmode (Some base) None (inl (ident * int) ofs)) in *.
  assert (eval_addrmode ge addr rs = Val.add rs#base (Vint ofs)).
    unfold addr. simpl. rewrite Int.add_commut; rewrite Int.add_zero; auto. 
  exists (nextinstr_nf (rs#(preg_of dst) <- v)); split.
- destruct ty; try discriminate; destruct (preg_of dst); inv H; simpl in H0;
  apply exec_straight_one; auto; simpl; unfold exec_load; rewrite H1, H0; auto.
- intuition Simplifs.
Qed.

Lemma storeind_correct:
  forall (base: ireg) ofs ty src k (rs: regset) c m m',
  storeind src base ofs ty k = OK c ->
  Mem.storev (chunk_of_type ty) m (Val.add rs#base (Vint ofs)) (rs#(preg_of src)) = Some m' ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, data_preg r = true -> preg_notin r (destroyed_by_setstack ty) -> rs'#r = rs#r.
Proof.
Local Transparent destroyed_by_setstack.
  unfold storeind; intros.
  set (addr := Addrmode (Some base) None (inl (ident * int) ofs)) in *.
  assert (eval_addrmode ge addr rs = Val.add rs#base (Vint ofs)).
    unfold addr. simpl. rewrite Int.add_commut; rewrite Int.add_zero; auto. 
  destruct ty; try discriminate; destruct (preg_of src); inv H; simpl in H0;
  (econstructor; split;
  [apply exec_straight_one; [simpl; unfold exec_store; rewrite H1, H0; eauto|auto]
  |simpl; intros; unfold undef_regs; repeat Simplifs]).
Qed.

(** Translation of addressing modes *)

Lemma transl_addressing_mode_correct:
  forall addr args am (rs: regset) v,
  transl_addressing addr args = OK am ->
  eval_addressing ge (rs ESP) addr (List.map rs (List.map preg_of args)) = Some v ->
  Val.lessdef v (eval_addrmode ge am rs).
Proof.
  assert (A: forall n, Int.add Int.zero n = n). 
    intros. rewrite Int.add_commut. apply Int.add_zero.
  assert (B: forall n i, (if Int.eq i Int.one then Vint n else Vint (Int.mul n i)) = Vint (Int.mul n i)).
    intros. predSpec Int.eq Int.eq_spec i Int.one. 
    subst i. rewrite Int.mul_one. auto. auto.
  assert (C: forall v i,
    Val.lessdef (Val.mul v (Vint i))
               (if Int.eq i Int.one then v else Val.mul v (Vint i))).
    intros. predSpec Int.eq Int.eq_spec i Int.one.
    subst i. destruct v; simpl; auto. rewrite Int.mul_one; auto.
    destruct v; simpl; auto.
  unfold transl_addressing; intros.
  destruct addr; repeat (destruct args; try discriminate); simpl in H0; inv H0.
(* indexed *)
  monadInv H. rewrite (ireg_of_eq _ _ EQ). simpl. rewrite A; auto.
(* indexed2 *)
  monadInv H. rewrite (ireg_of_eq _ _ EQ); rewrite (ireg_of_eq _ _ EQ1). simpl.
  rewrite Val.add_assoc; auto. 
(* scaled *)
  monadInv H. rewrite (ireg_of_eq _ _ EQ). unfold eval_addrmode. 
  rewrite Val.add_permut. simpl. rewrite A. apply Val.add_lessdef; auto. 
(* indexed2scaled *)
  monadInv H. rewrite (ireg_of_eq _ _ EQ); rewrite (ireg_of_eq _ _ EQ1); simpl.
  apply Val.add_lessdef; auto. apply Val.add_lessdef; auto. 
(* global *)
  inv H. simpl. unfold Genv.symbol_address.
  destruct (Genv.find_symbol ge i); simpl; auto. repeat rewrite Int.add_zero. auto.
(* based *)
  monadInv H. rewrite (ireg_of_eq _ _ EQ). simpl.
  unfold Genv.symbol_address. destruct (Genv.find_symbol ge i); simpl; auto.
  rewrite Int.add_zero. rewrite Val.add_commut. auto. 
(* basedscaled *)
  monadInv H. rewrite (ireg_of_eq _ _ EQ). unfold eval_addrmode. 
  rewrite (Val.add_commut Vzero). rewrite Val.add_assoc. rewrite Val.add_permut.
  apply Val.add_lessdef; auto. destruct (rs x); simpl; auto. rewrite B. simpl.
  rewrite Int.add_zero. auto.
(* instack *)
  inv H; simpl. rewrite A; auto.
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

Lemma int_signed_eq:
  forall x y, Int.eq x y = zeq (Int.signed x) (Int.signed y).
Proof.
  intros. unfold Int.eq. unfold proj_sumbool. 
  destruct (zeq (Int.unsigned x) (Int.unsigned y));
  destruct (zeq (Int.signed x) (Int.signed y)); auto.
  elim n. unfold Int.signed. rewrite e; auto.
  elim n. apply Int.eqm_small_eq; auto with ints. 
  eapply Int.eqm_trans. apply Int.eqm_sym. apply Int.eqm_signed_unsigned.
  rewrite e. apply Int.eqm_signed_unsigned. 
Qed.

Lemma int_not_lt:
  forall x y, negb (Int.lt y x) = (Int.lt x y || Int.eq x y).
Proof.
  intros. unfold Int.lt. rewrite int_signed_eq. unfold proj_sumbool.
  destruct (zlt (Int.signed y) (Int.signed x)).
  rewrite zlt_false. rewrite zeq_false. auto. omega. omega.
  destruct (zeq (Int.signed x) (Int.signed y)). 
  rewrite zlt_false. auto. omega. 
  rewrite zlt_true. auto. omega.
Qed.

Lemma int_lt_not:
  forall x y, Int.lt y x = negb (Int.lt x y) && negb (Int.eq x y).
Proof.
  intros. rewrite <- negb_orb. rewrite <- int_not_lt. rewrite negb_involutive. auto.
Qed.

Lemma int_not_ltu:
  forall x y, negb (Int.ltu y x) = (Int.ltu x y || Int.eq x y).
Proof.
  intros. unfold Int.ltu, Int.eq.
  destruct (zlt (Int.unsigned y) (Int.unsigned x)).
  rewrite zlt_false. rewrite zeq_false. auto. omega. omega.
  destruct (zeq (Int.unsigned x) (Int.unsigned y)). 
  rewrite zlt_false. auto. omega. 
  rewrite zlt_true. auto. omega.
Qed.

Lemma int_ltu_not:
  forall x y, Int.ltu y x = negb (Int.ltu x y) && negb (Int.eq x y).
Proof.
  intros. rewrite <- negb_orb. rewrite <- int_not_ltu. rewrite negb_involutive. auto.
Qed.

Lemma testcond_for_signed_comparison_correct:
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
  rewrite int_not_lt. destruct (Int.lt i i0); simpl; destruct (Int.eq i i0); auto.
  rewrite (int_lt_not i i0). destruct (Int.lt i i0); destruct (Int.eq i i0); reflexivity.
  destruct (Int.lt i i0); reflexivity.
Qed.

Lemma testcond_for_unsigned_comparison_correct:
  forall c v1 v2 rs m b,
  Val.cmpu_bool (Mem.valid_pointer m) c v1 v2 = Some b ->
  eval_testcond (testcond_for_unsigned_comparison c)
                (nextinstr (compare_ints v1 v2 rs m)) = Some b.
Proof.
  intros. generalize (compare_ints_spec rs v1 v2 m).
  set (rs' := nextinstr (compare_ints v1 v2 rs m)).
  intros [A [B [C [D E]]]].
  unfold eval_testcond. rewrite A; rewrite B. unfold Val.cmpu, Val.cmp.
  destruct v1; destruct v2; simpl in H; inv H.
(* int int *)
  destruct c; simpl; auto.
  destruct (Int.eq i i0); reflexivity.
  destruct (Int.eq i i0); auto.
  destruct (Int.ltu i i0); auto.
  rewrite int_not_ltu. destruct (Int.ltu i i0); simpl; destruct (Int.eq i i0); auto.
  rewrite (int_ltu_not i i0). destruct (Int.ltu i i0); destruct (Int.eq i i0); reflexivity.
  destruct (Int.ltu i i0); reflexivity.
(* int ptr *)
  destruct (Int.eq i Int.zero) eqn:?; try discriminate.
  destruct c; simpl in *; inv H1.
  rewrite Heqb1; reflexivity. 
  rewrite Heqb1; reflexivity.
(* ptr int *)
  destruct (Int.eq i0 Int.zero) eqn:?; try discriminate.
  destruct c; simpl in *; inv H1.
  rewrite Heqb1; reflexivity. 
  rewrite Heqb1; reflexivity.
(* ptr ptr *)
  simpl. 
  fold (Mem.weak_valid_pointer m b0 (Int.unsigned i)) in *.
  fold (Mem.weak_valid_pointer m b1 (Int.unsigned i0)) in *.
  destruct (eq_block b0 b1).
  destruct (Mem.weak_valid_pointer m b0 (Int.unsigned i) &&
            Mem.weak_valid_pointer m b1 (Int.unsigned i0)); inversion H1.
  destruct c; simpl; auto.
  destruct (Int.eq i i0); reflexivity.
  destruct (Int.eq i i0); auto.
  destruct (Int.ltu i i0); auto.
  rewrite int_not_ltu. destruct (Int.ltu i i0); simpl; destruct (Int.eq i i0); auto.
  rewrite (int_ltu_not i i0). destruct (Int.ltu i i0); destruct (Int.eq i i0); reflexivity.
  destruct (Int.ltu i i0); reflexivity.
  destruct (Mem.valid_pointer m b0 (Int.unsigned i) &&
            Mem.valid_pointer m b1 (Int.unsigned i0)); try discriminate.
  destruct c; simpl in *; inv H1; reflexivity.
Qed.

Lemma compare_floats_spec:
  forall rs n1 n2,
  let rs' := nextinstr (compare_floats (Vfloat n1) (Vfloat n2) rs) in
     rs'#ZF = Val.of_bool (negb (Float.cmp Cne n1 n2))
  /\ rs'#CF = Val.of_bool (negb (Float.cmp Cge n1 n2))
  /\ rs'#PF = Val.of_bool (negb (Float.cmp Ceq n1 n2 || Float.cmp Clt n1 n2 || Float.cmp Cgt n1 n2))
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
     rs'#ZF = Val.of_bool (negb (Float32.cmp Cne n1 n2))
  /\ rs'#CF = Val.of_bool (negb (Float32.cmp Cge n1 n2))
  /\ rs'#PF = Val.of_bool (negb (Float32.cmp Ceq n1 n2 || Float32.cmp Clt n1 n2 || Float32.cmp Cgt n1 n2))
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
(* eq *)
  rewrite Float.cmp_ne_eq.
  caseEq (Float.cmp Ceq n1 n2); intros.
  auto.
  simpl. destruct (Float.cmp Clt n1 n2 || Float.cmp Cgt n1 n2); auto.
(* ne *)
  rewrite Float.cmp_ne_eq.
  caseEq (Float.cmp Ceq n1 n2); intros.
  auto.
  simpl. destruct (Float.cmp Clt n1 n2 || Float.cmp Cgt n1 n2); auto.
(* lt *)
  rewrite <- (Float.cmp_swap Cge n1 n2).
  rewrite <- (Float.cmp_swap Cne n1 n2).
  simpl.
  rewrite Float.cmp_ne_eq. rewrite Float.cmp_le_lt_eq.
  caseEq (Float.cmp Clt n1 n2); intros; simpl.
  caseEq (Float.cmp Ceq n1 n2); intros; simpl. 
  elimtype False. eapply Float.cmp_lt_eq_false; eauto. 
  auto. 
  destruct (Float.cmp Ceq n1 n2); auto.
(* le *)
  rewrite <- (Float.cmp_swap Cge n1 n2). simpl.
  destruct (Float.cmp Cle n1 n2); auto.
(* gt *)
  rewrite Float.cmp_ne_eq. rewrite Float.cmp_ge_gt_eq. 
  caseEq (Float.cmp Cgt n1 n2); intros; simpl.
  caseEq (Float.cmp Ceq n1 n2); intros; simpl. 
  elimtype False. eapply Float.cmp_gt_eq_false; eauto. 
  auto. 
  destruct (Float.cmp Ceq n1 n2); auto.
(* ge *)
  destruct (Float.cmp Cge n1 n2); auto.
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
(* eq *)
  rewrite Float.cmp_ne_eq.
  caseEq (Float.cmp Ceq n1 n2); intros.
  auto.
  simpl. destruct (Float.cmp Clt n1 n2 || Float.cmp Cgt n1 n2); auto.
(* ne *)
  rewrite Float.cmp_ne_eq.
  caseEq (Float.cmp Ceq n1 n2); intros.
  auto.
  simpl. destruct (Float.cmp Clt n1 n2 || Float.cmp Cgt n1 n2); auto.
(* lt *)
  rewrite <- (Float.cmp_swap Cge n1 n2).
  rewrite <- (Float.cmp_swap Cne n1 n2).
  simpl.
  rewrite Float.cmp_ne_eq. rewrite Float.cmp_le_lt_eq.
  caseEq (Float.cmp Clt n1 n2); intros; simpl.
  caseEq (Float.cmp Ceq n1 n2); intros; simpl. 
  elimtype False. eapply Float.cmp_lt_eq_false; eauto.
  auto. 
  destruct (Float.cmp Ceq n1 n2); auto.
(* le *)
  rewrite <- (Float.cmp_swap Cge n1 n2). simpl.
  destruct (Float.cmp Cle n1 n2); auto.
(* gt *)
  rewrite Float.cmp_ne_eq. rewrite Float.cmp_ge_gt_eq. 
  caseEq (Float.cmp Cgt n1 n2); intros; simpl.
  caseEq (Float.cmp Ceq n1 n2); intros; simpl. 
  elimtype False. eapply Float.cmp_gt_eq_false; eauto. 
  auto. 
  destruct (Float.cmp Ceq n1 n2); auto.
(* ge *)
  destruct (Float.cmp Cge n1 n2); auto.
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
(* eq *)
  rewrite Float32.cmp_ne_eq.
  caseEq (Float32.cmp Ceq n1 n2); intros.
  auto.
  simpl. destruct (Float32.cmp Clt n1 n2 || Float32.cmp Cgt n1 n2); auto.
(* ne *)
  rewrite Float32.cmp_ne_eq.
  caseEq (Float32.cmp Ceq n1 n2); intros.
  auto.
  simpl. destruct (Float32.cmp Clt n1 n2 || Float32.cmp Cgt n1 n2); auto.
(* lt *)
  rewrite <- (Float32.cmp_swap Cge n1 n2).
  rewrite <- (Float32.cmp_swap Cne n1 n2).
  simpl.
  rewrite Float32.cmp_ne_eq. rewrite Float32.cmp_le_lt_eq.
  caseEq (Float32.cmp Clt n1 n2); intros; simpl.
  caseEq (Float32.cmp Ceq n1 n2); intros; simpl. 
  elimtype False. eapply Float32.cmp_lt_eq_false; eauto. 
  auto. 
  destruct (Float32.cmp Ceq n1 n2); auto.
(* le *)
  rewrite <- (Float32.cmp_swap Cge n1 n2). simpl.
  destruct (Float32.cmp Cle n1 n2); auto.
(* gt *)
  rewrite Float32.cmp_ne_eq. rewrite Float32.cmp_ge_gt_eq. 
  caseEq (Float32.cmp Cgt n1 n2); intros; simpl.
  caseEq (Float32.cmp Ceq n1 n2); intros; simpl. 
  elimtype False. eapply Float32.cmp_gt_eq_false; eauto. 
  auto. 
  destruct (Float32.cmp Ceq n1 n2); auto.
(* ge *)
  destruct (Float32.cmp Cge n1 n2); auto.
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
(* eq *)
  rewrite Float32.cmp_ne_eq.
  caseEq (Float32.cmp Ceq n1 n2); intros.
  auto.
  simpl. destruct (Float32.cmp Clt n1 n2 || Float32.cmp Cgt n1 n2); auto.
(* ne *)
  rewrite Float32.cmp_ne_eq.
  caseEq (Float32.cmp Ceq n1 n2); intros.
  auto.
  simpl. destruct (Float32.cmp Clt n1 n2 || Float32.cmp Cgt n1 n2); auto.
(* lt *)
  rewrite <- (Float32.cmp_swap Cge n1 n2).
  rewrite <- (Float32.cmp_swap Cne n1 n2).
  simpl.
  rewrite Float32.cmp_ne_eq. rewrite Float32.cmp_le_lt_eq.
  caseEq (Float32.cmp Clt n1 n2); intros; simpl.
  caseEq (Float32.cmp Ceq n1 n2); intros; simpl. 
  elimtype False. eapply Float32.cmp_lt_eq_false; eauto.
  auto. 
  destruct (Float32.cmp Ceq n1 n2); auto.
(* le *)
  rewrite <- (Float32.cmp_swap Cge n1 n2). simpl.
  destruct (Float32.cmp Cle n1 n2); auto.
(* gt *)
  rewrite Float32.cmp_ne_eq. rewrite Float32.cmp_ge_gt_eq. 
  caseEq (Float32.cmp Cgt n1 n2); intros; simpl.
  caseEq (Float32.cmp Ceq n1 n2); intros; simpl. 
  elimtype False. eapply Float32.cmp_gt_eq_false; eauto. 
  auto. 
  destruct (Float32.cmp Ceq n1 n2); auto.
(* ge *)
  destruct (Float32.cmp Cge n1 n2); auto.
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
(* comp *)
  simpl. rewrite (ireg_of_eq _ _ EQ). rewrite (ireg_of_eq _ _ EQ1).
  econstructor. split. apply exec_straight_one. simpl. eauto. auto.
  split. destruct (Val.cmp_bool c0 (rs x) (rs x0)) eqn:?; auto.
  eapply testcond_for_signed_comparison_correct; eauto. 
  intros. unfold compare_ints. Simplifs.
(* compu *)
  simpl. rewrite (ireg_of_eq _ _ EQ). rewrite (ireg_of_eq _ _ EQ1).
  econstructor. split. apply exec_straight_one. simpl. eauto. auto.
  split. destruct (Val.cmpu_bool (Mem.valid_pointer m) c0 (rs x) (rs x0)) eqn:?; auto.
  eapply testcond_for_unsigned_comparison_correct; eauto. 
  intros. unfold compare_ints. Simplifs.
(* compimm *)
  simpl. rewrite (ireg_of_eq _ _ EQ). destruct (Int.eq_dec i Int.zero).
  econstructor; split. apply exec_straight_one. simpl; eauto. auto. 
  split. destruct (rs x); simpl; auto. subst. rewrite Int.and_idem.
  eapply testcond_for_signed_comparison_correct; eauto. 
  intros. unfold compare_ints. Simplifs.
  econstructor; split. apply exec_straight_one. simpl; eauto. auto. 
  split. destruct (Val.cmp_bool c0 (rs x) (Vint i)) eqn:?; auto.
  eapply testcond_for_signed_comparison_correct; eauto. 
  intros. unfold compare_ints. Simplifs.
(* compuimm *)
  simpl. rewrite (ireg_of_eq _ _ EQ).
  econstructor. split. apply exec_straight_one. simpl. eauto. auto.
  split. destruct (Val.cmpu_bool (Mem.valid_pointer m) c0 (rs x) (Vint i)) eqn:?; auto.
  eapply testcond_for_unsigned_comparison_correct; eauto. 
  intros. unfold compare_ints. Simplifs.
(* compf *)
  simpl. rewrite (freg_of_eq _ _ EQ). rewrite (freg_of_eq _ _ EQ1).
  exists (nextinstr (compare_floats (swap_floats c0 (rs x) (rs x0)) (swap_floats c0 (rs x0) (rs x)) rs)).
  split. apply exec_straight_one. 
  destruct c0; simpl; auto.
  unfold nextinstr. rewrite Pregmap.gss. rewrite compare_floats_inv; auto with asmgen. 
  split. destruct (rs x); destruct (rs x0); simpl; auto.
  repeat rewrite swap_floats_commut. apply testcond_for_float_comparison_correct.
  intros. Simplifs. apply compare_floats_inv; auto with asmgen. 
(* notcompf *)
  simpl. rewrite (freg_of_eq _ _ EQ). rewrite (freg_of_eq _ _ EQ1).
  exists (nextinstr (compare_floats (swap_floats c0 (rs x) (rs x0)) (swap_floats c0 (rs x0) (rs x)) rs)).
  split. apply exec_straight_one. 
  destruct c0; simpl; auto.
  unfold nextinstr. rewrite Pregmap.gss. rewrite compare_floats_inv; auto with asmgen. 
  split. destruct (rs x); destruct (rs x0); simpl; auto.
  repeat rewrite swap_floats_commut. apply testcond_for_neg_float_comparison_correct.
  intros. Simplifs. apply compare_floats_inv; auto with asmgen. 
(* compfs *)
  simpl. rewrite (freg_of_eq _ _ EQ). rewrite (freg_of_eq _ _ EQ1).
  exists (nextinstr (compare_floats32 (swap_floats c0 (rs x) (rs x0)) (swap_floats c0 (rs x0) (rs x)) rs)).
  split. apply exec_straight_one. 
  destruct c0; simpl; auto.
  unfold nextinstr. rewrite Pregmap.gss. rewrite compare_floats32_inv; auto with asmgen. 
  split. destruct (rs x); destruct (rs x0); simpl; auto.
  repeat rewrite swap_floats_commut. apply testcond_for_float32_comparison_correct.
  intros. Simplifs. apply compare_floats32_inv; auto with asmgen. 
(* notcompfs *)
  simpl. rewrite (freg_of_eq _ _ EQ). rewrite (freg_of_eq _ _ EQ1).
  exists (nextinstr (compare_floats32 (swap_floats c0 (rs x) (rs x0)) (swap_floats c0 (rs x0) (rs x)) rs)).
  split. apply exec_straight_one. 
  destruct c0; simpl; auto.
  unfold nextinstr. rewrite Pregmap.gss. rewrite compare_floats32_inv; auto with asmgen. 
  split. destruct (rs x); destruct (rs x0); simpl; auto.
  repeat rewrite swap_floats_commut. apply testcond_for_neg_float32_comparison_correct.
  intros. Simplifs. apply compare_floats32_inv; auto with asmgen. 
(* maskzero *)
  simpl. rewrite (ireg_of_eq _ _ EQ).
  econstructor. split. apply exec_straight_one. simpl; eauto. auto.
  split. destruct (rs x); simpl; auto. 
  generalize (compare_ints_spec rs (Vint (Int.and i0 i)) Vzero m).
  intros [A B]. rewrite A. unfold Val.cmpu; simpl. destruct (Int.eq (Int.and i0 i) Int.zero); auto.
  intros. unfold compare_ints. Simplifs.
(* masknotzero *)
  simpl. rewrite (ireg_of_eq _ _ EQ).
  econstructor. split. apply exec_straight_one. simpl; eauto. auto.
  split. destruct (rs x); simpl; auto. 
  generalize (compare_ints_spec rs (Vint (Int.and i0 i)) Vzero m).
  intros [A B]. rewrite A. unfold Val.cmpu; simpl. destruct (Int.eq (Int.and i0 i) Int.zero); auto.
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
  /\ forall r, data_preg r = true -> r <> EAX /\ r <> ECX -> r <> rd -> rs2#r = rs1#r.
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
  destruct (ireg_eq rd EAX).
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
  destruct (ireg_eq rd EAX).
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
  /\ forall r, data_preg r = true -> r <> EAX /\ r <> ECX -> r <> rd -> rs2#r = rs1#r.
Proof.
  intros. unfold mk_setcc. destruct (low_ireg rd).
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
  eval_operation ge (rs#ESP) op (map rs (map preg_of args)) m = Some v ->
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
  apply SAME. destruct (Int.eq_dec i Int.zero). subst i. TranslOp. TranslOp.
(* floatconst *)
  apply SAME. destruct (Float.eq_dec f Float.zero). subst f. TranslOp. TranslOp.
(* singleconst *)
  apply SAME. destruct (Float32.eq_dec f Float32.zero). subst f. TranslOp. TranslOp.
(* cast8signed *)
  apply SAME. eapply mk_intconv_correct; eauto.
(* cast8unsigned *)
  apply SAME. eapply mk_intconv_correct; eauto. 
(* cast16signed *)
  apply SAME. eapply mk_intconv_correct; eauto.
(* cast16unsigned *)
  apply SAME. eapply mk_intconv_correct; eauto.
(* mulhs *)
  apply SAME. TranslOp. destruct H1. Simplifs. 
(* mulhu *)
  apply SAME. TranslOp. destruct H1. Simplifs. 
(* div *)
  apply SAME.
  specialize (divs_mods_exist (rs EAX) (rs ECX)). rewrite H0. 
  destruct (Val.mods (rs EAX) (rs ECX)) as [vr|] eqn:?; intros; try contradiction.
  TranslOp. change (rs#EDX<-Vundef ECX) with (rs#ECX). rewrite H0; rewrite Heqo. eauto.
  auto. auto.
  simpl in H3. destruct H3; Simplifs.
(* divu *)
  apply SAME.
  specialize (divu_modu_exist (rs EAX) (rs ECX)). rewrite H0. 
  destruct (Val.modu (rs EAX) (rs ECX)) as [vr|] eqn:?; intros; try contradiction.
  TranslOp. change (rs#EDX<-Vundef ECX) with (rs#ECX). rewrite H0; rewrite Heqo. eauto.
  auto. auto.
  simpl in H3. destruct H3; Simplifs.
(* mod *)
  apply SAME.
  specialize (divs_mods_exist (rs EAX) (rs ECX)). rewrite H0. 
  destruct (Val.divs (rs EAX) (rs ECX)) as [vr|] eqn:?; intros; try contradiction.
  TranslOp. change (rs#EDX<-Vundef ECX) with (rs#ECX). rewrite H0; rewrite Heqo. eauto.
  auto. auto.
  simpl in H3. destruct H3; Simplifs.
(* modu *)
  apply SAME.
  specialize (divu_modu_exist (rs EAX) (rs ECX)). rewrite H0. 
  destruct (Val.divu (rs EAX) (rs ECX)) as [vr|] eqn:?; intros; try contradiction.
  TranslOp. change (rs#EDX<-Vundef ECX) with (rs#ECX). rewrite H0; rewrite Heqo. eauto.
  auto. auto.
  simpl in H3. destruct H3; Simplifs.
(* shrximm *)
  apply SAME. eapply mk_shrximm_correct; eauto.
(* lea *)
  exploit transl_addressing_mode_correct; eauto. intros EA.
  TranslOp. rewrite nextinstr_inv; auto with asmgen. rewrite Pregmap.gss; auto.
(* intoffloat *)
  apply SAME. TranslOp. rewrite H0; auto.
(* floatofint *)
  apply SAME. TranslOp. rewrite H0; auto.
(* intofsingle *)
  apply SAME. TranslOp. rewrite H0; auto.
(* singleofint *)
  apply SAME. TranslOp. rewrite H0; auto.
(* condition *)
  exploit transl_cond_correct; eauto. intros [rs2 [P [Q R]]].
  exploit mk_setcc_correct; eauto. intros [rs3 [S [T U]]].
  exists rs3.
  split. eapply exec_straight_trans. eexact P. eexact S.
  split. rewrite T. destruct (eval_condition c0 rs ## (preg_of ## args) m).
  rewrite Q. auto.
  simpl; auto.
  intros. transitivity (rs2 r); auto.
Qed.

(** Translation of memory loads. *)

Lemma transl_load_correct:
  forall chunk addr args dest k c (rs: regset) m a v,
  transl_load chunk addr args dest k = OK c ->
  eval_addressing ge (rs#ESP) addr (map rs (map preg_of args)) = Some a ->
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
  assert (rs2 PC = Val.add (rs PC) Vone).
    transitivity (Val.add ((rs#(preg_of dest) <- v) PC) Vone).
    auto. decEq. apply Pregmap.gso; auto with asmgen.
  exists rs2. split. 
  destruct chunk; ArgsInv; apply exec_straight_one; auto.
  split. unfold rs2. rewrite nextinstr_nf_inv1. Simplifs. apply preg_of_data.
  intros. unfold rs2. Simplifs. 
Qed.

Lemma transl_store_correct:
  forall chunk addr args src k c (rs: regset) m a m',
  transl_store chunk addr args src k = OK c ->
  eval_addressing ge (rs#ESP) addr (map rs (map preg_of args)) = Some a ->
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
  eapply mk_smallstore_correct; eauto.
  intros. simpl. unfold exec_store.
  destruct (eval_addrmode ge addr0 rs0); simpl; auto. rewrite Mem.store_signed_unsigned_8; auto.
(* int8unsigned *)
  eapply mk_smallstore_correct; eauto.
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


