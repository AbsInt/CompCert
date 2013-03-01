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

(** Correctness proof for Asm generation: machine-independent framework *)

Require Import Coqlib.
Require Intv.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Locations.
Require Import Mach.
Require Import Asm.
Require Import Asmgen.
Require Import Conventions.

(** * Processor registers and register states *)

Hint Extern 2 (_ <> _) => congruence: asmgen.

Lemma ireg_of_eq:
  forall r r', ireg_of r = OK r' -> preg_of r = IR r'.
Proof.
  unfold ireg_of; intros. destruct (preg_of r); inv H; auto.
Qed.

Lemma freg_of_eq:
  forall r r', freg_of r = OK r' -> preg_of r = FR r'.
Proof.
  unfold freg_of; intros. destruct (preg_of r); inv H; auto.
Qed.

Lemma preg_of_injective:
  forall r1 r2, preg_of r1 = preg_of r2 -> r1 = r2.
Proof.
  destruct r1; destruct r2; simpl; intros; reflexivity || discriminate.
Qed.

Lemma preg_of_data:
  forall r, data_preg (preg_of r) = true.
Proof.
  intros. destruct r; reflexivity.
Qed.
Hint Resolve preg_of_data: asmgen.

Lemma data_diff:
  forall r r',
  data_preg r = true -> data_preg r' = false -> r <> r'.
Proof.
  congruence.
Qed.
Hint Resolve data_diff: asmgen.

Lemma preg_of_not_SP:
  forall r, preg_of r <> SP.
Proof.
  intros. unfold preg_of; destruct r; simpl; congruence. 
Qed.

Lemma preg_of_not_PC:
  forall r, preg_of r <> PC.
Proof.
  intros. apply data_diff; auto with asmgen.
Qed.

Hint Resolve preg_of_not_SP preg_of_not_PC: asmgen.

Lemma nontemp_diff:
  forall r r',
  nontemp_preg r = true -> nontemp_preg r' = false -> r <> r'.
Proof.
  congruence.
Qed.
Hint Resolve nontemp_diff: asmgen.

Lemma temporaries_temp_preg:
  forall r, In r temporary_regs -> nontemp_preg (preg_of r) = false.
Proof.
  assert (List.forallb (fun r => negb (nontemp_preg (preg_of r))) temporary_regs = true) by reflexivity.
  rewrite List.forallb_forall in H. intros. generalize (H r H0). 
  destruct (nontemp_preg (preg_of r)); simpl; congruence.
Qed.

Lemma nontemp_data_preg:
  forall r, nontemp_preg r = true -> data_preg r = true.
Proof.
  destruct r; try (destruct i); try (destruct f); simpl; congruence.
Qed.
Hint Resolve nontemp_data_preg: asmgen.

Lemma nextinstr_pc:
  forall rs, (nextinstr rs)#PC = Val.add rs#PC Vone.
Proof.
  intros. apply Pregmap.gss. 
Qed.

Lemma nextinstr_inv:
  forall r rs, r <> PC -> (nextinstr rs)#r = rs#r.
Proof.
  intros. unfold nextinstr. apply Pregmap.gso. red; intro; subst. auto.
Qed.

Lemma nextinstr_inv1:
  forall r rs, data_preg r = true -> (nextinstr rs)#r = rs#r.
Proof.
  intros. apply nextinstr_inv. red; intro; subst; discriminate.
Qed.

Lemma nextinstr_inv2:
  forall r rs, nontemp_preg r = true -> (nextinstr rs)#r = rs#r.
Proof.
  intros. apply nextinstr_inv1; auto with asmgen.
Qed.

Lemma nextinstr_set_preg:
  forall rs m v,
  (nextinstr (rs#(preg_of m) <- v))#PC = Val.add rs#PC Vone.
Proof.
  intros. unfold nextinstr. rewrite Pregmap.gss. 
  rewrite Pregmap.gso. auto. apply sym_not_eq. apply preg_of_not_PC. 
Qed.

(** * Agreement between Mach registers and processor registers *)

Record agree (ms: Mach.regset) (sp: val) (rs: Asm.regset) : Prop := mkagree {
  agree_sp: rs#SP = sp;
  agree_mregs: forall r: mreg, Val.lessdef (ms r) (rs#(preg_of r))
}.

Lemma preg_val:
  forall ms sp rs r, agree ms sp rs -> Val.lessdef (ms r) rs#(preg_of r).
Proof.
  intros. destruct H. auto.
Qed.

Lemma preg_vals:
  forall ms sp rs, agree ms sp rs ->
  forall l, Val.lessdef_list (map ms l) (map rs (map preg_of l)).
Proof.
  induction l; simpl. constructor. constructor. eapply preg_val; eauto. auto.
Qed.

Lemma sp_val:
  forall ms sp rs, agree ms sp rs -> sp = rs#SP.
Proof.
  intros. destruct H; auto.
Qed.

Lemma ireg_val:
  forall ms sp rs r r',
  agree ms sp rs ->
  ireg_of r = OK r' ->
  Val.lessdef (ms r) rs#r'.
Proof.
  intros. rewrite <- (ireg_of_eq _ _ H0). eapply preg_val; eauto.
Qed.

Lemma freg_val:
  forall ms sp rs r r',
  agree ms sp rs ->
  freg_of r = OK r' ->
  Val.lessdef (ms r) (rs#r').
Proof.
  intros. rewrite <- (freg_of_eq _ _ H0). eapply preg_val; eauto.
Qed.

Lemma agree_exten:
  forall ms sp rs rs',
  agree ms sp rs ->
  (forall r, data_preg r = true -> rs'#r = rs#r) ->
  agree ms sp rs'.
Proof.
  intros. destruct H. split. 
  rewrite H0; auto. auto.
  intros. rewrite H0; auto. apply preg_of_data.
Qed.

(** Preservation of register agreement under various assignments. *)

Lemma agree_set_mreg:
  forall ms sp rs r v rs',
  agree ms sp rs ->
  Val.lessdef v (rs'#(preg_of r)) ->
  (forall r', data_preg r' = true -> r' <> preg_of r -> rs'#r' = rs#r') ->
  agree (Regmap.set r v ms) sp rs'.
Proof.
  intros. destruct H. split.
  rewrite H1; auto. apply sym_not_equal. apply preg_of_not_SP.
  auto.
  intros. unfold Regmap.set. destruct (RegEq.eq r0 r). congruence. 
  rewrite H1. auto. apply preg_of_data.
  red; intros; elim n. eapply preg_of_injective; eauto.
Qed.

Lemma agree_set_other:
  forall ms sp rs r v,
  agree ms sp rs ->
  data_preg r = false ->
  agree ms sp (rs#r <- v).
Proof.
  intros. apply agree_exten with rs. auto.
  intros. apply Pregmap.gso. congruence.
Qed.

Lemma agree_nextinstr:
  forall ms sp rs,
  agree ms sp rs -> agree ms sp (nextinstr rs).
Proof.
  intros. unfold nextinstr. apply agree_set_other. auto. auto.
Qed.

Lemma agree_undef_regs:
  forall ms sp rl rs,
  agree ms sp rs ->
  (forall r, In r rl -> data_preg r = false) ->
  agree ms sp (undef_regs rl rs).
Proof.
  induction rl; simpl; intros. auto.
  apply IHrl. apply agree_exten with rs; auto.
  intros. apply Pregmap.gso. red; intros; subst.
  assert (data_preg a = false) by auto. congruence.
  intros. apply H0; auto.
Qed.

Lemma agree_exten_temps:
  forall ms sp rs rs',
  agree ms sp rs ->
  (forall r, nontemp_preg r = true -> rs'#r = rs#r) ->
  agree (undef_temps ms) sp rs'.
Proof.
  intros. destruct H. split. 
  rewrite H0; auto. auto. 
  intros. unfold undef_temps. 
  destruct (In_dec mreg_eq r temporary_regs).
  rewrite Mach.undef_regs_same; auto. 
  rewrite Mach.undef_regs_other; auto. rewrite H0; auto.
  simpl in n. destruct r; auto; intuition.
Qed.

Lemma agree_set_undef_mreg:
  forall ms sp rs r v rs',
  agree ms sp rs ->
  Val.lessdef v (rs'#(preg_of r)) ->
  (forall r', nontemp_preg r' = true -> r' <> preg_of r -> rs'#r' = rs#r') ->
  agree (Regmap.set r v (undef_temps ms)) sp rs'.
Proof.
  intros. apply agree_set_mreg with (rs'#(preg_of r) <- (rs#(preg_of r))); auto.
  eapply agree_exten_temps; eauto. 
  intros. unfold Pregmap.set. destruct (PregEq.eq r0 (preg_of r)). 
  congruence. auto. 
  intros. rewrite Pregmap.gso; auto. 
Qed.

Lemma agree_change_sp:
  forall ms sp rs sp',
  agree ms sp rs -> sp' <> Vundef ->
  agree ms sp' (rs#SP <- sp').
Proof.
  intros. inv H. split. apply Pregmap.gss. auto. 
  intros. rewrite Pregmap.gso; auto with asmgen.
Qed.

(** Connection between Mach and Asm calling conventions for external
    functions. *)

Lemma extcall_arg_match:
  forall ms sp rs m m' l v,
  agree ms sp rs ->
  Mem.extends m m' ->
  Mach.extcall_arg ms m sp l v ->
  exists v', Asm.extcall_arg rs m' l v' /\ Val.lessdef v v'.
Proof.
  intros. inv H1.
  exists (rs#(preg_of r)); split. constructor. eapply preg_val; eauto.
  unfold load_stack in H2.
  exploit Mem.loadv_extends; eauto. intros [v' [A B]].
  rewrite (sp_val _ _ _ H) in A.
  exists v'; split; auto.
  destruct ty; econstructor.
  reflexivity. assumption.
  reflexivity. assumption.
Qed.

Lemma extcall_args_match:
  forall ms sp rs m m', agree ms sp rs -> Mem.extends m m' ->
  forall ll vl,
  list_forall2 (Mach.extcall_arg ms m sp) ll vl ->
  exists vl', list_forall2 (Asm.extcall_arg rs m') ll vl' /\ Val.lessdef_list vl vl'.
Proof.
  induction 3; intros. 
  exists (@nil val); split. constructor. constructor.
  exploit extcall_arg_match; eauto. intros [v1' [A B]].
  destruct IHlist_forall2 as [vl' [C D]].
  exists (v1' :: vl'); split; constructor; auto.
Qed.

Lemma extcall_arguments_match:
  forall ms m m' sp rs sg args,
  agree ms sp rs -> Mem.extends m m' ->
  Mach.extcall_arguments ms m sp sg args ->
  exists args', Asm.extcall_arguments rs m' sg args' /\ Val.lessdef_list args args'.
Proof.
  unfold Mach.extcall_arguments, Asm.extcall_arguments; intros.
  eapply extcall_args_match; eauto.
Qed.

(** Translation of arguments to annotations. *)

Lemma annot_arg_match:
  forall ms sp rs m m' p v,
  agree ms sp rs ->
  Mem.extends m m' ->
  Mach.annot_arg ms m sp p v ->
  exists v', Asm.annot_arg rs m' (transl_annot_param p) v' /\ Val.lessdef v v'.
Proof.
  intros. inv H1; simpl.
(* reg *)
  exists (rs (preg_of r)); split. constructor. eapply preg_val; eauto.
(* stack *)
  exploit Mem.load_extends; eauto. intros [v' [A B]].
  exists v'; split; auto. 
  inv H. econstructor; eauto. 
Qed.

Lemma annot_arguments_match:
  forall ms sp rs m m', agree ms sp rs -> Mem.extends m m' ->
  forall pl vl,
  Mach.annot_arguments ms m sp pl vl ->
  exists vl', Asm.annot_arguments rs m' (map transl_annot_param pl) vl'
           /\ Val.lessdef_list vl vl'.
Proof.
  induction 3; intros. 
  exists (@nil val); split. constructor. constructor.
  exploit annot_arg_match; eauto. intros [v1' [A B]].
  destruct IHlist_forall2 as [vl' [C D]].
  exists (v1' :: vl'); split; constructor; auto.
Qed.

(** * Correspondence between Mach code and Asm code *)

Lemma find_instr_in:
  forall c pos i,
  find_instr pos c = Some i -> In i c.
Proof.
  induction c; simpl. intros; discriminate.
  intros until i. case (zeq pos 0); intros.
  left; congruence. right; eauto.
Qed.

(** The ``code tail'' of an instruction list [c] is the list of instructions
  starting at PC [pos]. *)

Inductive code_tail: Z -> code -> code -> Prop :=
  | code_tail_0: forall c,
      code_tail 0 c c
  | code_tail_S: forall pos i c1 c2,
      code_tail pos c1 c2 ->
      code_tail (pos + 1) (i :: c1) c2.

Lemma code_tail_pos:
  forall pos c1 c2, code_tail pos c1 c2 -> pos >= 0.
Proof.
  induction 1. omega. omega.
Qed.

Lemma find_instr_tail:
  forall c1 i c2 pos,
  code_tail pos c1 (i :: c2) ->
  find_instr pos c1 = Some i.
Proof.
  induction c1; simpl; intros.
  inv H.
  destruct (zeq pos 0). subst pos.
  inv H. auto. generalize (code_tail_pos _ _ _ H4). intro. omegaContradiction.
  inv H. congruence. replace (pos0 + 1 - 1) with pos0 by omega.
  eauto.
Qed.

Remark code_tail_bounds:
  forall fn ofs i c,
  code_tail ofs fn (i :: c) -> 0 <= ofs < list_length_z fn.
Proof.
  assert (forall ofs fn c, code_tail ofs fn c ->
          forall i c', c = i :: c' -> 0 <= ofs < list_length_z fn).
  induction 1; intros; simpl. 
  rewrite H. rewrite list_length_z_cons. generalize (list_length_z_pos c'). omega.
  rewrite list_length_z_cons. generalize (IHcode_tail _ _ H0). omega.
  eauto.
Qed.

Lemma code_tail_next:
  forall fn ofs i c,
  code_tail ofs fn (i :: c) ->
  code_tail (ofs + 1) fn c.
Proof.
  assert (forall ofs fn c, code_tail ofs fn c ->
          forall i c', c = i :: c' -> code_tail (ofs + 1) fn c').
  induction 1; intros.
  subst c. constructor. constructor.
  constructor. eauto.
  eauto.
Qed.

Lemma code_tail_next_int:
  forall fn ofs i c,
  list_length_z fn <= Int.max_unsigned ->
  code_tail (Int.unsigned ofs) fn (i :: c) ->
  code_tail (Int.unsigned (Int.add ofs Int.one)) fn c.
Proof.
  intros. rewrite Int.add_unsigned.
  change (Int.unsigned Int.one) with 1.
  rewrite Int.unsigned_repr. apply code_tail_next with i; auto.
  generalize (code_tail_bounds _ _ _ _ H0). omega. 
Qed.

(** [transl_code_at_pc pc f c ep tf tc] holds if the code pointer [pc] points
  within the Asm code generated by translating Mach function [f],
  and [tc] is the tail of the generated code at the position corresponding
  to the code pointer [pc]. *)

Inductive transl_code_at_pc (ge: Mach.genv):
    val -> Mach.function -> Mach.code -> bool -> Asm.function -> Asm.code -> Prop :=
  transl_code_at_pc_intro:
    forall b ofs f c ep tf tc,
    Genv.find_funct_ptr ge b = Some(Internal f) ->
    transf_function f = Errors.OK tf ->
    transl_code f c ep = OK tc ->
    code_tail (Int.unsigned ofs) (fn_code tf) tc ->
    transl_code_at_pc ge (Vptr b ofs) f c ep tf tc.

(** * Execution of straight-line code *)

Section STRAIGHTLINE.

Variable ge: genv.
Variable fn: function.

(** Straight-line code is composed of processor instructions that execute
  in sequence (no branches, no function calls and returns).
  The following inductive predicate relates the machine states
  before and after executing a straight-line sequence of instructions.
  Instructions are taken from the first list instead of being fetched
  from memory. *)

Inductive exec_straight: code -> regset -> mem -> 
                         code -> regset -> mem -> Prop :=
  | exec_straight_one:
      forall i1 c rs1 m1 rs2 m2,
      exec_instr ge fn i1 rs1 m1 = Next rs2 m2 ->
      rs2#PC = Val.add rs1#PC Vone ->
      exec_straight (i1 :: c) rs1 m1 c rs2 m2
  | exec_straight_step:
      forall i c rs1 m1 rs2 m2 c' rs3 m3,
      exec_instr ge fn i rs1 m1 = Next rs2 m2 ->
      rs2#PC = Val.add rs1#PC Vone ->
      exec_straight c rs2 m2 c' rs3 m3 ->
      exec_straight (i :: c) rs1 m1 c' rs3 m3.

Lemma exec_straight_trans:
  forall c1 rs1 m1 c2 rs2 m2 c3 rs3 m3,
  exec_straight c1 rs1 m1 c2 rs2 m2 ->
  exec_straight c2 rs2 m2 c3 rs3 m3 ->
  exec_straight c1 rs1 m1 c3 rs3 m3.
Proof.
  induction 1; intros.
  apply exec_straight_step with rs2 m2; auto.
  apply exec_straight_step with rs2 m2; auto.
Qed.

Lemma exec_straight_two:
  forall i1 i2 c rs1 m1 rs2 m2 rs3 m3,
  exec_instr ge fn i1 rs1 m1 = Next rs2 m2 ->
  exec_instr ge fn i2 rs2 m2 = Next rs3 m3 ->
  rs2#PC = Val.add rs1#PC Vone ->
  rs3#PC = Val.add rs2#PC Vone ->
  exec_straight (i1 :: i2 :: c) rs1 m1 c rs3 m3.
Proof.
  intros. apply exec_straight_step with rs2 m2; auto.
  apply exec_straight_one; auto.
Qed.

Lemma exec_straight_three:
  forall i1 i2 i3 c rs1 m1 rs2 m2 rs3 m3 rs4 m4,
  exec_instr ge fn i1 rs1 m1 = Next rs2 m2 ->
  exec_instr ge fn i2 rs2 m2 = Next rs3 m3 ->
  exec_instr ge fn i3 rs3 m3 = Next rs4 m4 ->
  rs2#PC = Val.add rs1#PC Vone ->
  rs3#PC = Val.add rs2#PC Vone ->
  rs4#PC = Val.add rs3#PC Vone ->
  exec_straight (i1 :: i2 :: i3 :: c) rs1 m1 c rs4 m4.
Proof.
  intros. apply exec_straight_step with rs2 m2; auto.
  eapply exec_straight_two; eauto.
Qed.

(** The following lemmas show that straight-line executions
  (predicate [exec_straight]) correspond to correct Asm executions. *)

Lemma exec_straight_steps_1:
  forall c rs m c' rs' m',
  exec_straight c rs m c' rs' m' ->
  list_length_z (fn_code fn) <= Int.max_unsigned ->
  forall b ofs,
  rs#PC = Vptr b ofs ->
  Genv.find_funct_ptr ge b = Some (Internal fn) ->
  code_tail (Int.unsigned ofs) (fn_code fn) c ->
  plus step ge (State rs m) E0 (State rs' m').
Proof.
  induction 1; intros.
  apply plus_one.
  econstructor; eauto. 
  eapply find_instr_tail. eauto.
  eapply plus_left'.
  econstructor; eauto. 
  eapply find_instr_tail. eauto.
  apply IHexec_straight with b (Int.add ofs Int.one). 
  auto. rewrite H0. rewrite H3. reflexivity.
  auto. 
  apply code_tail_next_int with i; auto.
  traceEq.
Qed.
    
Lemma exec_straight_steps_2:
  forall c rs m c' rs' m',
  exec_straight c rs m c' rs' m' ->
  list_length_z (fn_code fn) <= Int.max_unsigned ->
  forall b ofs,
  rs#PC = Vptr b ofs ->
  Genv.find_funct_ptr ge b = Some (Internal fn) ->
  code_tail (Int.unsigned ofs) (fn_code fn) c ->
  exists ofs',
     rs'#PC = Vptr b ofs'
  /\ code_tail (Int.unsigned ofs') (fn_code fn) c'.
Proof.
  induction 1; intros.
  exists (Int.add ofs Int.one). split.
  rewrite H0. rewrite H2. auto.
  apply code_tail_next_int with i1; auto.
  apply IHexec_straight with (Int.add ofs Int.one).
  auto. rewrite H0. rewrite H3. reflexivity. auto. 
  apply code_tail_next_int with i; auto.
Qed.

End STRAIGHTLINE.

(** * Stack invariants *)

(** ** Stored return addresses *)

(** [retaddr_stored_at m m' sp pos ra] holds if Asm memory [m']
  contains value [ra] (a return address) at offset [pos] in block [sp]. *)

Record retaddr_stored_at (m m': mem) (sp: block) (pos: Z) (ra: val) : Prop := {
  rsa_noperm:
    forall ofs k p, pos <= ofs < pos + 4 -> ~Mem.perm m sp ofs k p;
  rsa_allperm:
    forall ofs k p, pos <= ofs < pos + 4 -> Mem.perm m' sp ofs k p;
  rsa_contains:
    Mem.load Mint32 m' sp pos = Some ra
}.

Lemma retaddr_stored_at_invariant:
  forall m m' sp pos ra m1 m1',
  retaddr_stored_at m m' sp pos ra ->
  (forall ofs p, pos <= ofs < pos + 4 -> Mem.perm m1 sp ofs Max p -> Mem.perm m sp ofs Max p) ->
  (forall ofs k p, pos <= ofs < pos + 4 -> Mem.perm m' sp ofs k p -> Mem.perm m1' sp ofs k p) ->
  (Mem.load Mint32 m' sp pos = Some ra -> Mem.load Mint32 m1' sp pos = Some ra) ->
  retaddr_stored_at m1 m1' sp pos ra.
Proof.
  intros. inv H. constructor; intros.
  red; intros. eelim rsa_noperm0. eauto. apply H0. auto. eapply Mem.perm_max; eauto.  
  eauto.
  eauto.
Qed.

Lemma retaddr_stored_at_store:
  forall chunk m m' b ofs v v' m1 m1' sp pos ra,
  retaddr_stored_at m m' sp pos ra ->
  Mem.store chunk m b ofs v = Some m1 ->
  Mem.store chunk m' b ofs v' = Some m1' ->
  retaddr_stored_at m1 m1' sp pos ra.
Proof.
  intros. eapply retaddr_stored_at_invariant; eauto; intros.
- eapply Mem.perm_store_2; eauto.
- eapply Mem.perm_store_1; eauto.
- rewrite <- H2. eapply Mem.load_store_other; eauto.
  destruct (eq_block sp b); auto. subst b.
  right. exploit Mem.store_valid_access_3. eexact H0. intros [A B].
  apply (Intv.range_disjoint' (pos, pos + size_chunk Mint32) (ofs, ofs + size_chunk chunk)).
  red; intros; red; intros. 
  elim (rsa_noperm _ _ _ _ _ H x Cur Writable). assumption. apply A. assumption.
  simpl; omega.
  simpl; generalize (size_chunk_pos chunk); omega.
Qed.

Lemma retaddr_stored_at_storev:
  forall chunk m m' a a' v v' m1 m1' sp pos ra,
  retaddr_stored_at m m' sp pos ra ->
  Mem.storev chunk m a v = Some m1 ->
  Mem.storev chunk m' a' v' = Some m1' ->
  Val.lessdef a a' ->
  retaddr_stored_at m1 m1' sp pos ra.
Proof.
  intros. destruct a; simpl in H0; try discriminate. inv H2. simpl in H1.
  eapply retaddr_stored_at_store; eauto.
Qed.

Lemma retaddr_stored_at_valid':
  forall m m' sp pos ra,
  retaddr_stored_at m m' sp pos ra ->
  Mem.valid_block m' sp.
Proof.
  intros.
  eapply Mem.valid_access_valid_block. 
  apply Mem.valid_access_implies with Readable; auto with mem.
  eapply Mem.load_valid_access.
  eapply rsa_contains; eauto.
Qed.

Lemma retaddr_stored_at_valid:
  forall m m' sp pos ra,
  retaddr_stored_at m m' sp pos ra ->
  Mem.extends m m' ->
  Mem.valid_block m sp.
Proof.
  intros.
  erewrite Mem.valid_block_extends; eauto.
  eapply retaddr_stored_at_valid'; eauto.
Qed.

Lemma retaddr_stored_at_extcall:
  forall m1 m1' sp pos ra m2 m2',
  retaddr_stored_at m1 m1' sp pos ra ->
  (forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  mem_unchanged_on (loc_out_of_bounds m1) m1' m2' ->
  Mem.extends m1 m1' ->
  retaddr_stored_at m2 m2' sp pos ra.
Proof.
  intros.
  assert (B: forall ofs, pos <= ofs < pos + 4 -> loc_out_of_bounds m1 sp ofs).
    intros; red; intros. eapply rsa_noperm; eauto.
  eapply retaddr_stored_at_invariant; eauto. 
- intros. apply H0; auto. eapply retaddr_stored_at_valid; eauto. 
- intros. destruct H1. eauto. 
- intros. destruct H1. apply H4; auto. 
Qed.

Lemma retaddr_stored_at_can_alloc:
  forall m lo hi m1 sp pos m2 a v m3 m' m1' a' v' m2' ra,
  Mem.alloc m lo hi = (m1, sp) ->
  Mem.free m1 sp pos (pos + 4) = Some m2 ->
  Mem.storev Mint32 m2 a v = Some m3 ->
  Mem.alloc m' lo hi = (m1', sp) ->
  Mem.storev Mint32 m1' a' v' = Some m2' ->
  (4 | pos) ->
  Mem.extends m3 m2' ->
  Val.has_type ra Tint ->
  exists m3',
     Mem.store Mint32 m2' sp pos ra = Some m3'
  /\ retaddr_stored_at m3 m3' sp pos ra
  /\ Mem.extends m3 m3'.
Proof.
  intros. destruct a; simpl in H1; try discriminate. destruct a'; simpl in H3; try discriminate.
  assert (POS: forall ofs, pos <= ofs < pos + 4 -> lo <= ofs < hi).
    intros. eapply Mem.perm_alloc_3. eexact H. eapply Mem.free_range_perm; eauto.
  assert (ST: { m3' | Mem.store Mint32 m2' sp pos ra = Some m3' }).
  {
    apply Mem.valid_access_store. split.
    red; intros. eapply Mem.perm_store_1; eauto.
    apply Mem.perm_implies with Freeable; auto with mem.
    eapply Mem.perm_alloc_2; eauto.
    assumption.
  }
  destruct ST as [m3' ST]. exists m3'; split; auto.
  split. constructor.
  intros; red; intros. eelim Mem.perm_free_2; eauto. eapply Mem.perm_store_2; eauto.
  intros. eapply Mem.perm_store_1; eauto. eapply Mem.perm_store_1; eauto. 
  apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.perm_alloc_2; eauto.
  replace ra with (Val.load_result Mint32 ra). eapply Mem.load_store_same; eauto.
  destruct ra; reflexivity || contradiction.
  eapply Mem.store_outside_extends; eauto. 
  intros. eelim Mem.perm_free_2; eauto. eapply Mem.perm_store_2; eauto.  
Qed.

Lemma retaddr_stored_at_can_free:
  forall m m' sp pos ra lo m1 hi m2,
  retaddr_stored_at m m' sp pos ra ->
  Mem.free m sp lo pos = Some m1 ->
  Mem.free m1 sp (pos + 4) hi = Some m2 ->
  Mem.extends m m' ->
  exists m1', Mem.free m' sp lo hi = Some m1' /\ Mem.extends m2 m1'.
Proof.
  intros. inv H.
  assert (F: { m1' | Mem.free m' sp lo hi = Some m1' }).
  {
    apply Mem.range_perm_free. red; intros. 
    assert (EITHER: lo <= ofs < pos \/ pos <= ofs < pos + 4 \/ pos + 4 <= ofs < hi) by omega.
    destruct EITHER as [A | [A | A]].
    eapply Mem.perm_extends; eauto. eapply Mem.free_range_perm; eauto.
    auto.
    eapply Mem.perm_extends; eauto.
    eapply Mem.perm_free_3; eauto. eapply Mem.free_range_perm; eauto.
  }
  destruct F as [m1' F]. exists m1'; split; auto.
  eapply Mem.free_right_extends; eauto.
  eapply Mem.free_left_extends. eapply Mem.free_left_extends. eauto. eauto. eauto. 
  intros. 
  exploit Mem.perm_free_3. eexact H1. eauto. intros P1.
  exploit Mem.perm_free_3. eexact H0. eauto. intros P0.
  assert (EITHER: lo <= ofs < pos \/ pos <= ofs < pos + 4 \/ pos + 4 <= ofs < hi) by omega.
  destruct EITHER as [A | [A | A]].
  eelim Mem.perm_free_2. eexact H0. eexact A. eauto. 
  eelim rsa_noperm0; eauto.
  eelim Mem.perm_free_2. eexact H1. eexact A. eauto. 
Qed.

Lemma retaddr_stored_at_type:
  forall m m' sp pos ra, retaddr_stored_at m m' sp pos ra -> Val.has_type ra Tint.
Proof.
  intros. change Tint with (type_of_chunk Mint32). 
  eapply Mem.load_type. eapply rsa_contains; eauto.
Qed.

(** Matching a Mach stack against an Asm memory state. *)

Section MATCH_STACK.

Variable ge: Mach.genv.

Inductive match_stack:
           list Mach.stackframe -> mem -> mem -> val -> block -> Prop :=
  | match_stack_nil: forall m m' bound,
      match_stack nil m m' Vzero bound
  | match_stack_cons: forall f sp c s m m' ra tf tc ra' bound
      (AT: transl_code_at_pc ge ra f c false tf tc)
      (RSA: retaddr_stored_at m m' sp (Int.unsigned f.(fn_retaddr_ofs)) ra')
      (BELOW: sp < bound),
      match_stack s m m' ra' sp ->
      match_stack (Stackframe f (Vptr sp Int.zero) c :: s) m m' ra bound.

Lemma match_stack_invariant:
  forall m2 m2' s m1 m1' ra bound,
  match_stack s m1 m1' ra bound ->
  (forall b ofs p, b < bound -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  (forall b ofs k p, b < bound -> Mem.perm m1' b ofs k p -> Mem.perm m2' b ofs k p) ->
  (forall b ofs v, b < bound -> Mem.load Mint32 m1' b ofs = Some v -> Mem.load Mint32 m2' b ofs = Some v) ->
  match_stack s m2 m2' ra bound.
Proof.
  induction 1; intros; econstructor; eauto.
  eapply retaddr_stored_at_invariant; eauto.
  apply IHmatch_stack; intros. 
  eapply H0; eauto. omega.
  eapply H1; eauto. omega.
  eapply H2; eauto. omega.
Qed.

Lemma match_stack_change_bound:
  forall s m m' ra bound1 bound2,
  match_stack s m m' ra bound1 ->
  bound1 <= bound2 ->
  match_stack s m m' ra bound2.
Proof.
  intros. inv H; econstructor; eauto. omega. 
Qed.

Lemma match_stack_storev:
  forall chunk a v m1 a' v' m1' s m m' ra bound,
  match_stack s m m' ra bound ->
  Mem.storev chunk m a v = Some m1 ->
  Mem.storev chunk m' a' v' = Some m1' ->
  Val.lessdef a a' ->
  match_stack s m1 m1' ra bound.
Proof.
  induction 1; intros; econstructor; eauto. 
  eapply retaddr_stored_at_storev; eauto.
Qed.

Lemma match_stack_extcall:
  forall m2 m2' s m1 m1' ra bound,
  match_stack s m1 m1' ra bound ->
  (forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  mem_unchanged_on (loc_out_of_bounds m1) m1' m2' ->
  Mem.extends m1 m1' ->
  match_stack s m2 m2' ra bound.
Proof.
  induction 1; intros; econstructor; eauto.
  eapply retaddr_stored_at_extcall; eauto. 
Qed.

Lemma match_stack_free_left:
  forall s m m' ra bound b lo hi m1,
  match_stack s m m' ra bound ->
  Mem.free m b lo hi = Some m1 ->
  match_stack s m1 m' ra bound.
Proof.
  intros. eapply match_stack_invariant; eauto.
  intros. eapply Mem.perm_free_3; eauto. 
Qed.

Lemma match_stack_free_right:
  forall s m m' ra bound b lo hi m1',
  match_stack s m m' ra bound ->
  Mem.free m' b lo hi = Some m1' ->
  bound <= b ->
  match_stack s m m1' ra bound.
Proof.
  intros. eapply match_stack_invariant; eauto.
  intros. eapply Mem.perm_free_1; eauto. left. unfold block; omega. 
  intros. rewrite <- H3. eapply Mem.load_free; eauto. left. unfold block; omega.
Qed.

Lemma parent_sp_def:
  forall s m m' ra bound,
  match_stack s m m' ra bound -> parent_sp s <> Vundef.
Proof.
  intros. inv H; simpl; congruence.
Qed.

Lemma lessdef_parent_sp:
  forall s m m' ra bound v,
  match_stack s m m' ra bound -> Val.lessdef (parent_sp s) v -> v = parent_sp s.
Proof.
  intros. inv H0; auto. exfalso. eelim parent_sp_def; eauto.
Qed.

End MATCH_STACK.


