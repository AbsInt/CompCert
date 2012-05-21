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

(** Correctness proof for constant propagation. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Lattice.
Require Import Kildall.
Require Import ConstpropOp.
Require Import Constprop.
Require Import ConstpropOpproof.

Section PRESERVATION.

Variable prog: program.
Let tprog := transf_program prog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Let gapp := make_global_approx (PTree.empty _) prog.(prog_vars).

(** * Correctness of the static analysis *)

Section ANALYSIS.

Variable sp: val.

Definition regs_match_approx (a: D.t) (rs: regset) : Prop :=
  forall r, val_match_approx ge sp (D.get r a) rs#r.

Lemma regs_match_approx_top:
  forall rs, regs_match_approx D.top rs.
Proof.
  intros. red; intros. simpl. rewrite PTree.gempty. 
  unfold Approx.top, val_match_approx. auto.
Qed.

Lemma val_match_approx_increasing:
  forall a1 a2 v,
  Approx.ge a1 a2 -> val_match_approx ge sp a2 v -> val_match_approx ge sp a1 v.
Proof.
  intros until v.
  intros [A|[B|C]].
  subst a1. simpl. auto.
  subst a2. simpl. tauto.
  subst a2. auto.
Qed.

Lemma regs_match_approx_increasing:
  forall a1 a2 rs,
  D.ge a1 a2 -> regs_match_approx a2 rs -> regs_match_approx a1 rs.
Proof.
  unfold D.ge, regs_match_approx. intros.
  apply val_match_approx_increasing with (D.get r a2); auto.
Qed.

Lemma regs_match_approx_update:
  forall ra rs a v r,
  val_match_approx ge sp a v ->
  regs_match_approx ra rs ->
  regs_match_approx (D.set r a ra) (rs#r <- v).
Proof.
  intros; red; intros. rewrite Regmap.gsspec. 
  case (peq r0 r); intro.
  subst r0. rewrite D.gss. auto.
  rewrite D.gso; auto. 
Qed.

Lemma approx_regs_val_list:
  forall ra rs rl,
  regs_match_approx ra rs ->
  val_list_match_approx ge sp (approx_regs ra rl) rs##rl.
Proof.
  induction rl; simpl; intros.
  constructor.
  constructor. apply H. auto.
Qed.

(** The correctness of the static analysis follows from the results
  of module [ConstpropOpproof] and the fact that the result of
  the static analysis is a solution of the forward dataflow inequations. *)

Lemma analyze_correct_1:
  forall f pc rs pc' i,
  f.(fn_code)!pc = Some i ->
  In pc' (successors_instr i) ->
  regs_match_approx (transfer gapp f pc (analyze gapp f)!!pc) rs ->
  regs_match_approx (analyze gapp f)!!pc' rs.
Proof.
  intros until i. unfold analyze. 
  caseEq (DS.fixpoint (successors f) (transfer gapp f)
                      ((fn_entrypoint f, D.top) :: nil)).
  intros approxs; intros.
  apply regs_match_approx_increasing with (transfer gapp f pc approxs!!pc).
  eapply DS.fixpoint_solution; eauto.
  unfold successors_list, successors. rewrite PTree.gmap1. rewrite H0. auto.
  auto.
  intros. rewrite PMap.gi. apply regs_match_approx_top. 
Qed.

Lemma analyze_correct_3:
  forall f rs,
  regs_match_approx (analyze gapp f)!!(f.(fn_entrypoint)) rs.
Proof.
  intros. unfold analyze. 
  caseEq (DS.fixpoint (successors f) (transfer gapp f)
                      ((fn_entrypoint f, D.top) :: nil)).
  intros approxs; intros.
  apply regs_match_approx_increasing with D.top.
  eapply DS.fixpoint_entry; eauto. auto with coqlib.
  apply regs_match_approx_top. 
  intros. rewrite PMap.gi. apply regs_match_approx_top.
Qed.

(** eval_static_load *)

Definition mem_match_approx (m: mem) : Prop :=
  forall id il b,
  gapp!id = Some il -> Genv.find_symbol ge id = Some b ->
  Genv.load_store_init_data ge m b 0 il /\
  Mem.valid_block m b /\
  (forall ofs, ~Mem.perm m b ofs Max Writable).

Lemma eval_load_init_sound:
  forall chunk m b il base ofs pos v,
  Genv.load_store_init_data ge m b base il ->
  Mem.load chunk m b ofs = Some v ->
  ofs = base + pos ->
  val_match_approx ge sp (eval_load_init chunk pos il) v.
Proof.
  induction il; simpl; intros.
(* base case il = nil *)
  auto.
(* inductive case *)
  destruct a.
  (* Init_int8 *)
  destruct H. destruct (zeq pos 0). subst.  rewrite Zplus_0_r in H0.
  destruct chunk; simpl; auto.
  rewrite Mem.load_int8_signed_unsigned in H0. rewrite H in H0. simpl in H0.
  inv H0. decEq. apply Int.sign_ext_zero_ext. compute; auto. 
  congruence.
  eapply IHil; eauto. omega.
  (* Init_int16 *)
  destruct H. destruct (zeq pos 0). subst.  rewrite Zplus_0_r in H0.
  destruct chunk; simpl; auto.
  rewrite Mem.load_int16_signed_unsigned in H0. rewrite H in H0. simpl in H0.
  inv H0. decEq. apply Int.sign_ext_zero_ext. compute; auto. 
  congruence.
  eapply IHil; eauto. omega.
  (* Init_int32 *)
  destruct H. destruct (zeq pos 0). subst.  rewrite Zplus_0_r in H0.
  destruct chunk; simpl; auto.
  congruence.
  eapply IHil; eauto. omega.
  (* Init_float32 *)
  destruct H. destruct (zeq pos 0). subst.  rewrite Zplus_0_r in H0.
  destruct chunk; simpl; auto. destruct (propagate_float_constants tt); simpl; auto.
  congruence.
  eapply IHil; eauto. omega.
  (* Init_float64 *)
  destruct H. destruct (zeq pos 0). subst.  rewrite Zplus_0_r in H0.
  destruct chunk; simpl; auto. destruct (propagate_float_constants tt); simpl; auto.
  congruence.
  eapply IHil; eauto. omega.
  (* Init_space *)
  eapply IHil; eauto. omega.
  (* Init_symbol *)
  destruct H as [[b' [A B]] C].
  destruct (zeq pos 0). subst.  rewrite Zplus_0_r in H0.
  destruct chunk; simpl; auto.
  unfold symbol_address. rewrite A. congruence.
  eapply IHil; eauto. omega.
Qed.

Lemma eval_static_load_sound:
  forall chunk m addr vaddr v,
  Mem.loadv chunk m vaddr = Some v ->
  mem_match_approx m ->  
  val_match_approx ge sp addr vaddr ->
  val_match_approx ge sp (eval_static_load gapp chunk addr) v.
Proof.
  intros. unfold eval_static_load. destruct addr; simpl; auto. 
  destruct (gapp!i) as [il|]_eqn; auto.
  red in H1. subst vaddr. unfold symbol_address in H. 
  destruct (Genv.find_symbol ge i) as [b'|]_eqn; simpl in H; try discriminate.
  exploit H0; eauto. intros [A [B C]]. 
  eapply eval_load_init_sound; eauto. 
  red; auto. 
Qed.

Lemma mem_match_approx_store:
  forall chunk m addr v m',
  mem_match_approx m ->
  Mem.storev chunk m addr v = Some m' ->
  mem_match_approx m'.
Proof.
  intros; red; intros. exploit H; eauto. intros [A [B C]].
  destruct addr; simpl in H0; try discriminate.
  exploit Mem.store_valid_access_3; eauto. intros [P Q].
  split. apply Genv.load_store_init_data_invariant with m; auto. 
  intros. eapply Mem.load_store_other; eauto. left; red; intro; subst b0.
  eapply C. apply Mem.perm_cur_max. eapply P. instantiate (1 := Int.unsigned i).
  generalize (size_chunk_pos chunk). omega.
  split. eauto with mem.
  intros; red; intros. eapply C. eapply Mem.perm_store_2; eauto.
Qed.

Lemma mem_match_approx_alloc:
  forall m lo hi b m',
  mem_match_approx m ->
  Mem.alloc m lo hi = (m', b) ->
  mem_match_approx m'.
Proof.
  intros; red; intros. exploit H; eauto. intros [A [B C]].
  split. apply Genv.load_store_init_data_invariant with m; auto.
  intros. eapply Mem.load_alloc_unchanged; eauto. 
  split. eauto with mem.
  intros; red; intros. exploit Mem.perm_alloc_inv; eauto. 
  rewrite zeq_false. apply C. eapply Mem.valid_not_valid_diff; eauto with mem.
Qed.

Lemma mem_match_approx_free:
  forall m lo hi b m',
  mem_match_approx m ->
  Mem.free m b lo hi = Some m' ->
  mem_match_approx m'.
Proof.
  intros; red; intros. exploit H; eauto. intros [A [B C]].
  split. apply Genv.load_store_init_data_invariant with m; auto.
  intros. eapply Mem.load_free; eauto.
  destruct (zeq b0 b); auto. subst b0.
  right. destruct (zlt lo hi); auto. 
  elim (C lo). apply Mem.perm_cur_max. 
  exploit Mem.free_range_perm; eauto. instantiate (1 := lo); omega. 
  intros; eapply Mem.perm_implies; eauto with mem.
  split. eauto with mem.
  intros; red; intros. eapply C. eauto with mem. 
Qed.

Lemma mem_match_approx_extcall:
  forall ef vargs m t vres m',
  mem_match_approx m ->
  external_call ef ge vargs m t vres m' ->
  mem_match_approx m'.
Proof.
  intros; red; intros. exploit H; eauto. intros [A [B C]].
  split. apply Genv.load_store_init_data_invariant with m; auto.
  intros. eapply external_call_readonly; eauto. 
  split. eapply external_call_valid_block; eauto.
  intros; red; intros. elim (C ofs). eapply external_call_max_perm; eauto. 
Qed.

(* Show that mem_match_approx holds initially *)

Definition global_approx_charact (g: genv) (ga: global_approx) : Prop :=
  forall id il b,
  ga!id = Some il -> 
  Genv.find_symbol g id = Some b -> 
  Genv.find_var_info g b = Some (mkglobvar tt il true false).

Lemma make_global_approx_correct:
  forall vl g ga,
  global_approx_charact g ga ->
  global_approx_charact (Genv.add_variables g vl) (make_global_approx ga vl).
Proof.
  induction vl; simpl; intros.
  auto.
  destruct a as [id gv]. apply IHvl. 
  red; intros. 
  assert (EITHER: id0 = id /\ gv = mkglobvar tt il true false
               \/ id0 <> id /\ ga!id0 = Some il).
  destruct (gvar_readonly gv && negb (gvar_volatile gv)) as []_eqn.
  rewrite PTree.gsspec in H0. destruct (peq id0 id).
  inv H0. left. split; auto. 
  destruct gv; simpl in *. 
  destruct gvar_readonly; try discriminate.
  destruct gvar_volatile; try discriminate.
  destruct gvar_info. auto.
  right; auto.
  rewrite PTree.grspec in H0. destruct (PTree.elt_eq id0 id); try discriminate.
  right; auto.
  unfold Genv.add_variable, Genv.find_symbol, Genv.find_var_info in *;
  simpl in *.
  destruct EITHER as [[A B] | [A B]].
  subst id0. rewrite PTree.gss in H1. inv H1. rewrite ZMap.gss. auto.
  rewrite PTree.gso in H1; auto. rewrite ZMap.gso. eapply H. eauto. auto.
  exploit Genv.genv_symb_range; eauto. unfold ZIndexed.t. omega.
Qed.

Theorem mem_match_approx_init:
  forall m, Genv.init_mem prog = Some m -> mem_match_approx m.
Proof.
  intros. 
  assert (global_approx_charact ge gapp).
    unfold ge, gapp.   unfold Genv.globalenv.
    apply make_global_approx_correct.
    red; intros. rewrite PTree.gempty in H0; discriminate.
  red; intros. 
  exploit Genv.init_mem_characterization.
  unfold ge in H0. eapply H0; eauto. eauto. 
  unfold Genv.perm_globvar; simpl.
  intros [A [B C]].
  split. auto. split. eapply Genv.find_symbol_not_fresh; eauto. 
  intros; red; intros. exploit B; eauto. intros [P Q]. inv Q.
Qed.

(**********************
Definition mem_match_approx_gen (g: genv) (ga: global_approx) (m: mem) : Prop :=
  forall id il b,
  ga!id = Some il -> Genv.find_symbol g id = Some b ->
  Genv.load_store_init_data ge m b 0 il /\
  Mem.valid_block m b /\
  (forall ofs, ~Mem.perm m b ofs Max Writable).

Lemma mem_match_approx_alloc_variables:
  forall vl g ga m m',
  mem_match_approx_gen g ga m ->
  Genv.genv_nextvar g = Mem.nextblock m ->
  Genv.alloc_variables ge m vl = Some m' ->
  mem_match_approx_gen (Genv.add_variables g vl) (make_global_approx ga vl) m'.
Proof.
  induction vl; simpl; intros.
(* base case *)
  inv H1. auto.
(* inductive case *)
  destruct a as [id gv].
  set (ga1 := if gv.(gvar_readonly) && negb gv.(gvar_volatile)
        then PTree.set id gv.(gvar_init) ga
        else PTree.remove id ga).
  revert H1. unfold Genv.alloc_variable. simpl.
  set (il := gvar_init gv) in *.
  set (sz := Genv.init_data_list_size il) in *.
  destruct (Mem.alloc m 0 sz) as [m1 b]_eqn.
  destruct (Genv.store_zeros m1 b sz) as [m2|]_eqn; try congruence.
  destruct (Genv.store_init_data_list ge m2 b 0 il) as [m3|]_eqn; try congruence.
  destruct (Mem.drop_perm m3 b 0 sz (Genv.perm_globvar gv)) as [m4|]_eqn; try congruence.
  intros. 
  exploit Mem.alloc_result; eauto. intro NB. 
  assert (NB': Mem.nextblock m4 = Mem.nextblock m1).
  rewrite (Mem.nextblock_drop _ _ _ _ _ _ Heqo1).
  rewrite (Genv.store_init_data_list_nextblock _ _ _ _ _ Heqo0).
  rewrite (Genv.store_zeros_nextblock _ _ _ Heqo). 
  auto.
  apply IHvl with m4. 
  (* mem_match_approx for intermediate state *)
  red; intros.
  unfold Genv.find_symbol in H3. simpl in H3. 
  rewrite H0 in H3. rewrite <- NB in H3. 
  assert (EITHER: id0 <> id /\ ga!id0 = Some il0
       \/ id0 = id /\ il0 = il /\ gvar_readonly gv = true /\ gvar_volatile gv = false).
  unfold ga1 in H2. destruct (gvar_readonly gv && negb (gvar_volatile gv)) as []_eqn. 
  rewrite PTree.gsspec in H2. destruct (peq id0 id).
  inv H2. right. split; auto. split; auto. 
  destruct (gvar_readonly gv); simpl in Heqb1; try discriminate.
  destruct (gvar_volatile gv); simpl in Heqb1; try discriminate.
  auto. auto.
  rewrite PTree.grspec in H2. destruct (PTree.elt_eq id0 id); try discriminate.
  auto.   
  destruct EITHER as [[A B] | [A [B [C D]]]].
  (* older blocks *)
  rewrite PTree.gso in H3; auto. exploit H; eauto. intros [P [Q R]].
  assert (b0 <> b). eapply Mem.valid_not_valid_diff; eauto with mem.
  split. apply Genv.load_store_init_data_invariant with m; auto. 
  intros. transitivity (Mem.load chunk m3 b0 ofs). eapply Mem.load_drop; eauto.
  transitivity (Mem.load chunk m2 b0 ofs). eapply Genv.store_init_data_list_outside; eauto.
  transitivity (Mem.load chunk m1 b0 ofs). eapply Genv.store_zeros_outside; eauto.
  eapply Mem.load_alloc_unchanged; eauto.  
  split. red. rewrite NB'.  change (Mem.valid_block m1 b0). eauto with mem.
  intros; red; intros. elim (R ofs). 
  eapply Mem.perm_alloc_4; eauto.
  rewrite Genv.store_zeros_perm; [idtac|eauto].
  rewrite Genv.store_init_data_list_perm; [idtac|eauto].
  eapply Mem.perm_drop_4; eauto.
  (* same block *)
  subst id0 il0. rewrite PTree.gss in H3. injection H3; intro EQ; subst b0.
  unfold Genv.perm_globvar in Heqo1.
  rewrite D in Heqo1. rewrite C in Heqo1.
  split. apply Genv.load_store_init_data_invariant with m3.
  intros. eapply Mem.load_drop; eauto. do 3 right. auto with mem. 
  eapply Genv.store_init_data_list_charact; eauto. 
  split. red. rewrite NB'. change (Mem.valid_block m1 b). eauto with mem.
  intros; red; intros. 
  assert (0 <= ofs < sz).
    eapply Mem.perm_alloc_3; eauto.
    rewrite Genv.store_zeros_perm; [idtac|eauto].
    rewrite Genv.store_init_data_list_perm; [idtac|eauto].
    eapply Mem.perm_drop_4; eauto.
  assert (PO: perm_order Readable Writable).
    eapply Mem.perm_drop_2; eauto. 
  inv PO. 
  (* nextvar hyp *)
  simpl. rewrite NB'. rewrite (Mem.nextblock_alloc _ _ _ _ _ Heqp).
  unfold block in *; omega.
  (* alloc vars hyp *)
  auto.
Qed.

Theorem mem_match_approx_init:
  forall m, Genv.init_mem prog = Some m -> mem_match_approx m.
Proof.
  intros. unfold Genv.init_mem in H. 
  eapply mem_match_approx_alloc_variables; eauto.
(* mem_match_approx on empty list *)
  red; intros. rewrite PTree.gempty in H0. discriminate.
(* nextvar *)
  rewrite Genv.add_functions_nextvar. auto.
Qed.
********************************)

End ANALYSIS.

(** * Correctness of the code transformation *)

(** We now show that the transformed code after constant propagation
  has the same semantics as the original code. *)

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intros; unfold ge, tge, tprog, transf_program. 
  apply Genv.find_symbol_transf.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros; unfold ge, tge, tprog, transf_program. 
  apply Genv.find_var_info_transf.
Qed.

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef gapp f).
Proof.  
  intros.
  exact (Genv.find_funct_transf (transf_fundef gapp) _ _ H).
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (transf_fundef gapp f).
Proof.  
  intros. 
  exact (Genv.find_funct_ptr_transf (transf_fundef gapp) _ _ H).
Qed.

Lemma sig_function_translated:
  forall f,
  funsig (transf_fundef gapp f) = funsig f.
Proof.
  intros. destruct f; reflexivity.
Qed.

Definition regs_lessdef (rs1 rs2: regset) : Prop :=
  forall r, Val.lessdef (rs1#r) (rs2#r).

Lemma regs_lessdef_regs:
  forall rs1 rs2, regs_lessdef rs1 rs2 ->
  forall rl, Val.lessdef_list rs1##rl rs2##rl.
Proof.
  induction rl; constructor; auto.
Qed.

Lemma set_reg_lessdef:
  forall r v1 v2 rs1 rs2,
  Val.lessdef v1 v2 -> regs_lessdef rs1 rs2 -> regs_lessdef (rs1#r <- v1) (rs2#r <- v2).
Proof.
  intros; red; intros. repeat rewrite Regmap.gsspec. 
  destruct (peq r0 r); auto.
Qed.

Lemma init_regs_lessdef:
  forall rl vl1 vl2,
  Val.lessdef_list vl1 vl2 ->
  regs_lessdef (init_regs vl1 rl) (init_regs vl2 rl).
Proof.
  induction rl; simpl; intros.
  red; intros. rewrite Regmap.gi. auto.
  inv H. red; intros. rewrite Regmap.gi. auto.
  apply set_reg_lessdef; auto.
Qed.

Lemma transf_ros_correct:
  forall sp ros rs rs' f approx,
  regs_match_approx sp approx rs ->
  find_function ge ros rs = Some f ->
  regs_lessdef rs rs' ->
  find_function tge (transf_ros approx ros) rs' = Some (transf_fundef gapp f).
Proof.
  intros. destruct ros; simpl in *.
  generalize (H r); intro MATCH. generalize (H1 r); intro LD.
  destruct (rs#r); simpl in H0; try discriminate.
  destruct (Int.eq_dec i Int.zero); try discriminate.
  inv LD. 
  assert (find_function tge (inl _ r) rs' = Some (transf_fundef gapp f)).
    simpl. rewrite <- H4. simpl. rewrite dec_eq_true. apply function_ptr_translated. auto.
  destruct (D.get r approx); auto.
  predSpec Int.eq Int.eq_spec i0 Int.zero; intros; auto.
  simpl in *. unfold symbol_address in MATCH. rewrite symbols_preserved.
  destruct (Genv.find_symbol ge i); try discriminate. 
  inv MATCH. apply function_ptr_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i); try discriminate.
  apply function_ptr_translated; auto.
Qed.

Lemma const_for_result_correct:
  forall a op sp v m,
  const_for_result a = Some op ->
  val_match_approx ge sp a v ->
  eval_operation tge sp op nil m = Some v.
Proof.
  unfold const_for_result; intros. 
  destruct a; inv H; simpl in H0.
  simpl. congruence.
  destruct (generate_float_constants tt); inv H2.  simpl. congruence.
  simpl. subst v. unfold symbol_address. rewrite symbols_preserved. auto.
  simpl. congruence.
Qed.

(** The proof of semantic preservation is a simulation argument
  based on diagrams of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                   |t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The left vertical arrow represents a transition in the
  original RTL code.  The top horizontal bar is the [match_states]
  invariant between the initial state [st1] in the original RTL code
  and an initial state [st2] in the transformed code.
  This invariant expresses that all code fragments appearing in [st2]
  are obtained by [transf_code] transformation of the corresponding
  fragments in [st1].  Moreover, the values of registers in [st1]
  must match their compile-time approximations at the current program
  point.
  These two parts of the diagram are the hypotheses.  In conclusions,
  we want to prove the other two parts: the right vertical arrow,
  which is a transition in the transformed RTL code, and the bottom
  horizontal bar, which means that the [match_state] predicate holds
  between the final states [st1'] and [st2']. *)

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
   match_stackframe_intro:
      forall res sp pc rs f rs',
      regs_lessdef rs rs' ->
      (forall v, regs_match_approx sp (analyze gapp f)!!pc (rs#res <- v)) ->
    match_stackframes
        (Stackframe res f sp pc rs)
        (Stackframe res (transf_function gapp f) sp pc rs').

Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s sp pc rs m f s' rs' m'
           (MATCH: regs_match_approx sp (analyze gapp f)!!pc rs)
           (GMATCH: mem_match_approx m)
           (STACKS: list_forall2 match_stackframes s s')
           (REGS: regs_lessdef rs rs')
           (MEM: Mem.extends m m'),
      match_states (State s f sp pc rs m)
                   (State s' (transf_function gapp f) sp pc rs' m')
  | match_states_call:
      forall s f args m s' args' m'
           (GMATCH: mem_match_approx m)
           (STACKS: list_forall2 match_stackframes s s')
           (ARGS: Val.lessdef_list args args')
           (MEM: Mem.extends m m'),
      match_states (Callstate s f args m)
                   (Callstate s' (transf_fundef gapp f) args' m')
  | match_states_return:
      forall s v m s' v' m'
           (GMATCH: mem_match_approx m)
           (STACKS: list_forall2 match_stackframes s s')
           (RES: Val.lessdef v v')
           (MEM: Mem.extends m m'),
      list_forall2 match_stackframes s s' ->
      match_states (Returnstate s v m)
                   (Returnstate s' v' m').

Ltac TransfInstr :=
  match goal with
  | H1: (PTree.get ?pc ?c = Some ?instr), f: function |- _ =>
      cut ((transf_function gapp f).(fn_code)!pc = Some(transf_instr gapp (analyze gapp f)!!pc instr));
      [ simpl transf_instr
      | unfold transf_function, transf_code; simpl; rewrite PTree.gmap; 
        unfold option_map; rewrite H1; reflexivity ]
  end.

(** The proof of simulation proceeds by case analysis on the transition
  taken in the source code. *)

Lemma transf_step_correct:
  forall s1 t s2,
  step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2', step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros; inv MS.

  (* Inop *)
  exists (State s' (transf_function gapp f) sp pc' rs' m'); split.
  TransfInstr; intro. eapply exec_Inop; eauto.
  econstructor; eauto.
  eapply analyze_correct_1 with (pc := pc); eauto.
  simpl; auto.
  unfold transfer; rewrite H. auto.

  (* Iop *)
  TransfInstr.
  set (a := eval_static_operation op (approx_regs (analyze gapp f)#pc args)).
  assert (VMATCH: val_match_approx ge sp a v).  
    eapply eval_static_operation_correct; eauto.
    apply approx_regs_val_list; auto.
  assert (MATCH': regs_match_approx sp (analyze gapp f) # pc' rs # res <- v).
    eapply analyze_correct_1 with (pc := pc); eauto. simpl; auto.
    unfold transfer; rewrite H. 
    apply regs_match_approx_update; auto. 
  destruct (const_for_result a) as [cop|]_eqn; intros.
  (* constant is propagated *)
  exists (State s' (transf_function gapp f) sp pc' (rs'#res <- v) m'); split.
  eapply exec_Iop; eauto. 
  eapply const_for_result_correct; eauto.
  econstructor; eauto. 
  apply set_reg_lessdef; auto.
  (* operator is strength-reduced *)
  exploit op_strength_reduction_correct. eexact MATCH. reflexivity. eauto. 
  destruct (op_strength_reduction op args (approx_regs (analyze gapp f) # pc args)) as [op' args'].
  intros [v' [EV' LD']].
  assert (EV'': exists v'', eval_operation ge sp op' rs'##args' m' = Some v'' /\ Val.lessdef v' v'').
  eapply eval_operation_lessdef; eauto. eapply regs_lessdef_regs; eauto.
  destruct EV'' as [v'' [EV'' LD'']].
  exists (State s' (transf_function gapp f) sp pc' (rs'#res <- v'') m'); split.
  econstructor. eauto. rewrite <- EV''. apply eval_operation_preserved. exact symbols_preserved.
  econstructor; eauto. apply set_reg_lessdef; auto. eapply Val.lessdef_trans; eauto.

  (* Iload *)
  TransfInstr. 
  set (ap1 := eval_static_addressing addr
               (approx_regs (analyze gapp f) # pc args)).
  set (ap2 := eval_static_load gapp chunk ap1).
  assert (VM1: val_match_approx ge sp ap1 a).
    eapply eval_static_addressing_correct; eauto.
    eapply approx_regs_val_list; eauto.
  assert (VM2: val_match_approx ge sp ap2 v).
    eapply eval_static_load_sound; eauto.
  assert (MATCH': regs_match_approx sp (analyze gapp f) # pc' rs # dst <- v).
    eapply analyze_correct_1 with (pc := pc); eauto. simpl; auto.
    unfold transfer; rewrite H. 
    apply regs_match_approx_update; auto. 
  destruct (const_for_result ap2) as [cop|]_eqn; intros.
  (* constant-propagated *)
  exists (State s' (transf_function gapp f) sp pc' (rs'#dst <- v) m'); split.
  eapply exec_Iop; eauto. eapply const_for_result_correct; eauto.
  econstructor; eauto. apply set_reg_lessdef; auto.
  (* strength-reduced *)
  generalize (addr_strength_reduction_correct ge sp (analyze gapp f)!!pc rs
                  MATCH addr args (approx_regs (analyze gapp f) # pc args) (refl_equal _)).
  destruct (addr_strength_reduction addr args (approx_regs (analyze gapp f) # pc args)) as [addr' args'].
  rewrite H0. intros P.
  assert (ADDR': exists a', eval_addressing ge sp addr' rs'##args' = Some a' /\ Val.lessdef a a').
    eapply eval_addressing_lessdef; eauto. eapply regs_lessdef_regs; eauto.
  destruct ADDR' as [a' [A B]].
  assert (C: eval_addressing tge sp addr' rs'##args' = Some a').
    rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved.
  exploit Mem.loadv_extends; eauto. intros [v' [D E]].
  exists (State s' (transf_function gapp f) sp pc' (rs'#dst <- v') m'); split.
  eapply exec_Iload; eauto.
  econstructor; eauto. 
  apply set_reg_lessdef; auto. 

  (* Istore *)
  TransfInstr.
  generalize (addr_strength_reduction_correct ge sp (analyze gapp f)!!pc rs
                  MATCH addr args (approx_regs (analyze gapp f) # pc args) (refl_equal _)).
  destruct (addr_strength_reduction addr args (approx_regs (analyze gapp f) # pc args)) as [addr' args'].
  intros P Q. rewrite H0 in P.
  assert (ADDR': exists a', eval_addressing ge sp addr' rs'##args' = Some a' /\ Val.lessdef a a').
    eapply eval_addressing_lessdef; eauto. eapply regs_lessdef_regs; eauto.
  destruct ADDR' as [a' [A B]].
  assert (C: eval_addressing tge sp addr' rs'##args' = Some a').
    rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved.
  exploit Mem.storev_extends; eauto. intros [m2' [D E]].
  exists (State s' (transf_function gapp f) sp pc' rs' m2'); split.
  eapply exec_Istore; eauto.
  econstructor; eauto. 
  eapply analyze_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H. auto. 
  eapply mem_match_approx_store; eauto.

  (* Icall *)
  exploit transf_ros_correct; eauto. intro FIND'.
  TransfInstr; intro.
  econstructor; split.
  eapply exec_Icall; eauto. apply sig_function_translated; auto.
  constructor; auto. constructor; auto.
  econstructor; eauto. 
  intros. eapply analyze_correct_1; eauto. simpl; auto.
  unfold transfer; rewrite H.
  apply regs_match_approx_update; auto. simpl. auto.
  apply regs_lessdef_regs; auto. 

  (* Itailcall *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  exploit transf_ros_correct; eauto. intros FIND'.
  TransfInstr; intro.
  econstructor; split.
  eapply exec_Itailcall; eauto. apply sig_function_translated; auto.
  constructor; auto. 
  eapply mem_match_approx_free; eauto.
  apply regs_lessdef_regs; auto. 

  (* Ibuiltin *)
Opaque builtin_strength_reduction.
  destruct (builtin_strength_reduction ef args (approx_regs (analyze gapp f)#pc args)) as [ef' args']_eqn.
  generalize (builtin_strength_reduction_correct ge sp (analyze gapp f)!!pc rs
                  MATCH ef args (approx_regs (analyze gapp f) # pc args) _ _ _ _ (refl_equal _) H0).
  rewrite Heqp. intros P.
  exploit external_call_mem_extends; eauto. 
  instantiate (1 := rs'##args'). apply regs_lessdef_regs; auto.
  intros [v' [m2' [A [B [C D]]]]].
  exists (State s' (transf_function gapp f) sp pc' (rs'#res <- v') m2'); split.
  eapply exec_Ibuiltin. TransfInstr. rewrite Heqp. eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto. 
  eapply analyze_correct_1; eauto. simpl; auto. 
  unfold transfer; rewrite H. 
  apply regs_match_approx_update; auto. simpl; auto.
  eapply mem_match_approx_extcall; eauto. 
  apply set_reg_lessdef; auto.

  (* Icond *)
  TransfInstr. 
  generalize (cond_strength_reduction_correct ge sp (analyze gapp f)#pc rs m
                    MATCH cond args (approx_regs (analyze gapp f) # pc args) (refl_equal _)).
  destruct (cond_strength_reduction cond args (approx_regs (analyze gapp f) # pc args)) as [cond' args'].
  intros EV1. 
  exists (State s' (transf_function gapp f) sp (if b then ifso else ifnot) rs' m'); split. 
  destruct (eval_static_condition cond (approx_regs (analyze gapp f) # pc args)) as []_eqn.
  assert (eval_condition cond rs ## args m = Some b0).
    eapply eval_static_condition_correct; eauto. eapply approx_regs_val_list; eauto.
  assert (b = b0) by congruence. subst b0.
  destruct b; eapply exec_Inop; eauto. 
  eapply exec_Icond; eauto.
  eapply eval_condition_lessdef with (vl1 := rs##args'); eauto. eapply regs_lessdef_regs; eauto. congruence.
  econstructor; eauto. 
  eapply analyze_correct_1; eauto. destruct b; simpl; auto. 
  unfold transfer; rewrite H. auto. 

  (* Ijumptable *)
  assert (A: (fn_code (transf_function gapp f))!pc = Some(Ijumptable arg tbl)
             \/ (fn_code (transf_function gapp f))!pc = Some(Inop pc')).
  TransfInstr. destruct (approx_reg (analyze gapp f) # pc arg) as []_eqn; auto.
  generalize (MATCH arg). unfold approx_reg in Heqt. rewrite Heqt. rewrite H0. 
  simpl. intro EQ; inv EQ. rewrite H1. auto.
  assert (B: rs'#arg = Vint n).
  generalize (REGS arg); intro LD; inv LD; congruence.
  exists (State s' (transf_function gapp f) sp pc' rs' m'); split.
  destruct A. eapply exec_Ijumptable; eauto. eapply exec_Inop; eauto. 
  econstructor; eauto.
  eapply analyze_correct_1; eauto.
  simpl. eapply list_nth_z_in; eauto.
  unfold transfer; rewrite  H; auto.

  (* Ireturn *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  exists (Returnstate s' (regmap_optget or Vundef rs') m2'); split.
  eapply exec_Ireturn; eauto. TransfInstr; auto.
  constructor; auto.
  eapply mem_match_approx_free; eauto.
  destruct or; simpl; auto. 

  (* internal function *)
  exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl.
  intros [m2' [A B]].
  simpl. unfold transf_function.
  econstructor; split.
  eapply exec_function_internal; simpl; eauto.
  simpl. econstructor; eauto.
  apply analyze_correct_3; auto.
  eapply mem_match_approx_alloc; eauto.
  apply init_regs_lessdef; auto.

  (* external function *)
  exploit external_call_mem_extends; eauto. 
  intros [v' [m2' [A [B [C D]]]]].
  simpl. econstructor; split.
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto.
  eapply mem_match_approx_extcall; eauto.

  (* return *)
  inv H3. inv H1. 
  econstructor; split.
  eapply exec_return; eauto. 
  econstructor; eauto. apply set_reg_lessdef; auto. 
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto. intro FIND.
  exists (Callstate nil (transf_fundef gapp f) nil m0); split.
  econstructor; eauto.
  apply Genv.init_mem_transf; auto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  reflexivity.
  rewrite <- H3. apply sig_function_translated.
  constructor. 
  eapply mem_match_approx_init; eauto.
  constructor. constructor. apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. inv RES. constructor. 
Qed.

(** The preservation of the observable behavior of the program then
  follows. *)

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_step.
  eexact symbols_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transf_step_correct. 
Qed.

End PRESERVATION.
