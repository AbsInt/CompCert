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

(** RTL function inlining: relational specification *)

Require Import Coqlib.
Require Import Wfsimpl.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Inlining.

(** ** Soundness of function environments. *)

(** A (compile-time) function environment is compatible with a
  (run-time) global environment if the following condition holds. *)

Definition fenv_compat (ge: genv) (fenv: funenv) : Prop :=
  forall id b f,
  fenv!id = Some f -> Genv.find_symbol ge id = Some b ->
  Genv.find_funct_ptr ge b = Some (Internal f).

Remark add_fundef_compat:
  forall ge fenv idf,
  fenv_compat ge fenv ->
  fenv_compat (Genv.add_function ge idf) (Inlining.add_fundef fenv idf).
Proof.
  intros. destruct idf as [id fd]. red; simpl; intros.
  unfold Genv.find_symbol in H1; simpl in H1. 
  unfold Genv.find_funct_ptr; simpl.
  rewrite PTree.gsspec in H1. destruct (peq id0 id).
  (* same *)
  subst id0. inv H1. rewrite ZMap.gss. 
  destruct fd. destruct (should_inline id f0).
  rewrite PTree.gss in H0. inv H0; auto.
  rewrite PTree.grs in H0; discriminate.
  rewrite PTree.grs in H0; discriminate.
  (* different *)
  rewrite ZMap.gso. eapply H; eauto.
  destruct fd. destruct (should_inline id f0).
  rewrite PTree.gso in H0; auto.
  rewrite PTree.gro in H0; auto.
  rewrite PTree.gro in H0; auto.
  exploit Genv.genv_symb_range; eauto. intros [A B]. unfold ZIndexed.t; omega. 
Qed.

Remark remove_vardef_compat:
  forall ge fenv idv,
  fenv_compat ge fenv ->
  fenv_compat (Genv.add_variable ge idv) (Inlining.remove_vardef fenv idv).
Proof.
  intros. destruct idv as [id vi]. red; simpl; intros.
  unfold Genv.find_symbol in H1; simpl in H1. 
  unfold Genv.find_funct_ptr; simpl.
  unfold remove_vardef in H0; simpl in H0.
  rewrite PTree.gsspec in H1. rewrite PTree.grspec in H0. 
  unfold PTree.elt_eq in H0. destruct (peq id0 id).
  discriminate.
  eapply H; eauto.
Qed.

Lemma funenv_program_compat:
  forall p, fenv_compat (Genv.globalenv p) (funenv_program p).
Proof.
  intros.
  unfold Genv.globalenv, funenv_program.
  assert (forall funs ge fenv,
         fenv_compat ge fenv ->
         fenv_compat (Genv.add_functions ge funs) (fold_left add_fundef funs fenv)).
    unfold Genv.add_functions. induction funs; simpl; intros.
    auto. apply IHfuns. apply add_fundef_compat; auto.
  assert (forall vars ge fenv,
         fenv_compat ge fenv ->
         fenv_compat (Genv.add_variables ge vars) (fold_left remove_vardef vars fenv)).
    unfold Genv.add_variables. induction vars; simpl; intros.
    auto. apply IHvars. apply remove_vardef_compat; auto.
  apply H0. apply H. red; intros. rewrite PTree.gempty in H1; discriminate.
Qed.

(** ** Soundness of the computed bounds over function resources *)

Remark Pmax_l: forall x y, Ple x (Pmax x y).
Proof. intros; xomega. Qed.

Remark Pmax_r: forall x y, Ple y (Pmax x y).
Proof. intros; xomega. Qed.

Lemma max_pc_function_sound:
  forall f pc i, f.(fn_code)!pc = Some i -> Ple pc (max_pc_function f).
Proof.
  intros until i. unfold max_pc_function. 
  apply PTree_Properties.fold_rec with (P := fun c m => c!pc = Some i -> Ple pc m).
  (* extensionality *)
  intros. apply H0. rewrite H; auto. 
  (* base case *)
  rewrite PTree.gempty. congruence.
  (* inductive case *)
  intros. rewrite PTree.gsspec in H2. destruct (peq pc k). 
  inv H2. apply Pmax_r.
  apply Ple_trans with a. auto. apply Pmax_l.
Qed.

Lemma max_def_function_instr:
  forall f pc i, f.(fn_code)!pc = Some i -> Ple (max_def_instr i) (max_def_function f).
Proof.
  intros. unfold max_def_function. eapply Ple_trans. 2: eapply Pmax_l. 
  revert H. 
  apply PTree_Properties.fold_rec with (P := fun c m => c!pc = Some i -> Ple (max_def_instr i) m).
  (* extensionality *)
  intros. apply H0. rewrite H; auto. 
  (* base case *)
  rewrite PTree.gempty. congruence.
  (* inductive case *)
  intros. rewrite PTree.gsspec in H2. destruct (peq pc k). 
  inv H2. apply Pmax_r. 
  apply Ple_trans with a. auto. apply Pmax_l.
Qed.

Lemma max_def_function_params:
  forall f r, In r f.(fn_params) -> Ple r (max_def_function f).
Proof.
  assert (A: forall l m, Ple m (fold_left (fun m r => Pmax m r) l m)).
    induction l; simpl; intros. 
    apply Ple_refl.
    eapply Ple_trans. 2: eauto. apply Pmax_l.
  assert (B: forall l m r, In r l -> Ple r (fold_left (fun m r => Pmax m r) l m)).
    induction l; simpl; intros.
    contradiction.
    destruct H. subst a. eapply Ple_trans. 2: eapply A. apply Pmax_r. 
    eauto. 
  unfold max_def_function; intros. 
  eapply Ple_trans. 2: eapply Pmax_r. eauto. 
Qed.

(** ** Working with the state monad *)

Remark bind_inversion:
  forall (A B: Type) (f: mon A) (g: A -> mon B) 
         (y: B) (s1 s3: state) (i: sincr s1 s3),
  bind f g s1 = R y s3 i ->
  exists x, exists s2, exists i1, exists i2,
  f s1 = R x s2 i1 /\ g x s2 = R y s3 i2.
Proof.
  unfold bind; intros. destruct (f s1). exists x; exists s'; exists I.
  destruct (g x s'). inv H. exists I0; auto.
Qed.

Ltac monadInv1 H :=
  match type of H with
  | (R _ _ _ = R _ _ _) =>
      inversion H; clear H; try subst
  | (ret _ _ = R _ _ _) =>
      inversion H; clear H; try subst
  | (bind ?F ?G ?S = R ?X ?S' ?I) =>
      let x := fresh "x" in (
      let s := fresh "s" in (
      let i1 := fresh "INCR" in (
      let i2 := fresh "INCR" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion _ _ F G X S S' I H) as [x [s [i1 [i2 [EQ1 EQ2]]]]];
      clear H;
      try (monadInv1 EQ2)))))))
  end.

Ltac monadInv H :=
  match type of H with
  | (ret _ _ = R _ _ _) => monadInv1 H
  | (bind ?F ?G ?S = R ?X ?S' ?I) => monadInv1 H
  | (?F _ _ _ _ _ _ _ _ = R _ _ _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ = R _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  end.

(** ** Relational specification of the translation of moves *)

Inductive tr_moves (c: code) : node -> list reg -> list reg -> node -> Prop :=
  | tr_moves_cons: forall pc1 src srcs dst dsts pc2 pc3,
      tr_moves c pc1 srcs dsts pc2 ->
      c!pc2 = Some(Iop Omove (src :: nil) dst pc3) ->
      tr_moves c pc1 (src :: srcs) (dst :: dsts) pc3
  | tr_moves_nil: forall srcs dsts pc,
      srcs = nil \/ dsts = nil ->
      tr_moves c pc srcs dsts pc.

Lemma add_moves_unchanged:
  forall srcs dsts pc2 s pc1 s' i pc,
  add_moves srcs dsts pc2 s = R pc1 s' i ->
  Ple pc s.(st_nextnode) \/ Plt s'.(st_nextnode) pc ->
  s'.(st_code)!pc = s.(st_code)!pc.
Proof.
  induction srcs; simpl; intros. 
  monadInv H. auto.
  destruct dsts; monadInv H. auto.
  transitivity (st_code s0)!pc. eapply IHsrcs; eauto. monadInv EQ; simpl. xomega. 
  monadInv EQ; simpl. apply PTree.gso.
  inversion INCR0; simpl in *. xomega. 
Qed.

Lemma add_moves_spec:
  forall srcs dsts pc2 s pc1 s' i c,
  add_moves srcs dsts pc2 s = R pc1 s' i ->
  (forall pc, Plt s.(st_nextnode) pc -> Ple pc s'.(st_nextnode) -> c!pc = s'.(st_code)!pc) ->
  tr_moves c pc1 srcs dsts pc2.
Proof.
  induction srcs; simpl; intros. 
  monadInv H. apply tr_moves_nil; auto.
  destruct dsts; monadInv H. apply tr_moves_nil; auto. 
  apply tr_moves_cons with x. eapply IHsrcs; eauto. 
  intros. inversion INCR. apply H0; xomega.
  monadInv EQ.
  rewrite H0. erewrite add_moves_unchanged; eauto. 
  simpl. apply PTree.gss. 
  simpl. xomega. 
  xomega.
  inversion INCR; inversion INCR0; simpl in *; xomega.
Qed.

(** ** Relational specification of CFG expansion *)

Section INLINING_SPEC.

Variable fenv: funenv.

Definition context_below (ctx1 ctx2: context): Prop :=
  Ple (Pplus ctx1.(dreg) ctx1.(mreg)) ctx2.(dreg).

Definition context_stack_call (ctx1 ctx2: context): Prop :=
  ctx1.(mstk) >= 0 /\ ctx1.(dstk) + ctx1.(mstk) <= ctx2.(dstk).

Definition context_stack_tailcall (ctx1: context) (f: function) (ctx2: context) : Prop :=
  ctx2.(dstk) = align ctx1.(dstk) (min_alignment f.(fn_stacksize)).

Section INLINING_BODY_SPEC.

Variable stacksize: Z.

Inductive tr_instr: context -> node -> instruction -> code -> Prop :=
  | tr_nop: forall ctx pc c s,
      c!(spc ctx pc) = Some (Inop (spc ctx s)) ->
      tr_instr ctx pc (Inop s) c
  | tr_op: forall ctx pc c op args res s,
      Ple res ctx.(mreg) ->
      c!(spc ctx pc) = Some (Iop (sop ctx op) (sregs ctx args) (sreg ctx res) (spc ctx s)) ->
      tr_instr ctx pc (Iop op args res s) c
  | tr_load: forall ctx pc c chunk addr args res s,
      Ple res ctx.(mreg) ->
      c!(spc ctx pc) = Some (Iload chunk (saddr ctx addr) (sregs ctx args) (sreg ctx res) (spc ctx s)) ->
      tr_instr ctx pc (Iload chunk addr args res s) c
  | tr_store: forall ctx pc c chunk addr args src s,
      c!(spc ctx pc) = Some (Istore chunk (saddr ctx addr) (sregs ctx args) (sreg ctx src) (spc ctx s)) ->
      tr_instr ctx pc (Istore chunk addr args src s) c
  | tr_call: forall ctx pc c sg ros args res s,
      Ple res ctx.(mreg) ->
      c!(spc ctx pc) = Some (Icall sg (sros ctx ros) (sregs ctx args) (sreg ctx res) (spc ctx s)) ->
      tr_instr ctx pc (Icall sg ros args res s) c
  | tr_call_inlined:forall ctx pc sg id args res s c f pc1 ctx',
      Ple res ctx.(mreg) ->
      fenv!id = Some f ->
      c!(spc ctx pc) = Some(Inop pc1) ->
      tr_moves c pc1 (sregs ctx args) (sregs ctx' f.(fn_params)) (spc ctx' f.(fn_entrypoint)) ->
      tr_funbody ctx' f c ->
      ctx'.(retinfo) = Some(spc ctx s, sreg ctx res) ->
      context_below ctx ctx' ->
      context_stack_call ctx ctx' ->
      tr_instr ctx pc (Icall sg (inr _ id) args res s) c
  | tr_tailcall: forall ctx pc c sg ros args,
      c!(spc ctx pc) = Some (Itailcall sg (sros ctx ros) (sregs ctx args)) ->
      ctx.(retinfo) = None ->
      tr_instr ctx pc (Itailcall sg ros args) c
  | tr_tailcall_call: forall ctx pc c sg ros args res s,
      c!(spc ctx pc) = Some (Icall sg (sros ctx ros) (sregs ctx args) res s) ->
      ctx.(retinfo) = Some(s, res) ->
      tr_instr ctx pc (Itailcall sg ros args) c
  | tr_tailcall_inlined: forall ctx pc sg id args c f pc1 ctx',
      fenv!id = Some f ->
      c!(spc ctx pc) = Some(Inop pc1) ->
      tr_moves c pc1 (sregs ctx args) (sregs ctx' f.(fn_params)) (spc ctx' f.(fn_entrypoint)) ->
      tr_funbody ctx' f c ->
      ctx'.(retinfo) = ctx.(retinfo) ->
      context_below ctx ctx' ->
      context_stack_tailcall ctx f ctx' ->
      tr_instr ctx pc (Itailcall sg (inr _ id) args) c
  | tr_builtin: forall ctx pc c ef args res s,
      Ple res ctx.(mreg) ->
      c!(spc ctx pc) = Some (Ibuiltin ef (sregs ctx args) (sreg ctx res) (spc ctx s)) ->
      tr_instr ctx pc (Ibuiltin ef args res s) c
  | tr_cond: forall ctx pc cond args s1 s2 c,
      c!(spc ctx pc) = Some (Icond cond (sregs ctx args) (spc ctx s1) (spc ctx s2)) ->
      tr_instr ctx pc (Icond cond args s1 s2) c
  | tr_jumptable: forall ctx pc r tbl c,
      c!(spc ctx pc) = Some (Ijumptable (sreg ctx r) (List.map (spc ctx) tbl)) ->
      tr_instr ctx pc (Ijumptable r tbl) c
  | tr_return: forall ctx pc or c,
      c!(spc ctx pc) = Some (Ireturn (option_map (sreg ctx) or)) ->
      ctx.(retinfo) = None ->
      tr_instr ctx pc (Ireturn or) c
  | tr_return_inlined: forall ctx pc or c rinfo,
      c!(spc ctx pc) = Some (inline_return ctx or rinfo) ->
      ctx.(retinfo) = Some rinfo ->
      tr_instr ctx pc (Ireturn or) c

with tr_funbody: context -> function -> code -> Prop :=
  | tr_funbody_intro: forall ctx f c,
      (forall r, In r f.(fn_params) -> Ple r ctx.(mreg)) ->
      (forall pc i, f.(fn_code)!pc = Some i -> tr_instr ctx pc i c) ->
      ctx.(mstk) = Zmax f.(fn_stacksize) 0 ->
      (min_alignment f.(fn_stacksize) | ctx.(dstk)) ->
      ctx.(dstk) >= 0 -> ctx.(dstk) + ctx.(mstk) <= stacksize ->
      tr_funbody ctx f c.

Definition fenv_agree (fe: funenv) : Prop :=
  forall id f, fe!id = Some f -> fenv!id = Some f.

Section EXPAND_INSTR.

Variable fe: funenv.
Hypothesis FE: fenv_agree fe.

Variable rec: forall fe', (size_fenv fe' < size_fenv fe)%nat -> context -> function -> mon unit.

Hypothesis rec_unchanged:
  forall fe' (L: (size_fenv fe' < size_fenv fe)%nat) ctx f s x s' i pc,
  rec fe' L ctx f s = R x s' i ->
  Ple ctx.(dpc) s.(st_nextnode) ->
  Ple pc ctx.(dpc) ->
  s'.(st_code)!pc = s.(st_code)!pc.

Remark set_instr_other:
  forall pc instr s x s' i pc',
  set_instr pc instr s = R x s' i ->
  pc' <> pc ->
  s'.(st_code)!pc' = s.(st_code)!pc'.
Proof.
  intros. monadInv H; simpl. apply PTree.gso; auto.
Qed.

Remark set_instr_same:
  forall pc instr s x s' i c,
  set_instr pc instr s = R x s' i ->
  c!(pc) = s'.(st_code)!pc ->
  c!(pc) = Some instr.
Proof.
  intros. rewrite H0. monadInv H; simpl. apply PTree.gss.
Qed.

Lemma expand_instr_unchanged:
  forall ctx pc instr s x s' i pc',
  expand_instr fe rec ctx pc instr s = R x s' i ->
  Ple ctx.(dpc) s.(st_nextnode) ->
  Ple pc' s.(st_nextnode) ->
  pc' <> spc ctx pc ->
  s'.(st_code)!pc' = s.(st_code)!pc'.
Proof.
  generalize set_instr_other; intros A.
  intros. unfold expand_instr in H; destruct instr; eauto.
(* call *)
  destruct (can_inline fe s1). eauto. 
  monadInv H. unfold inline_function in EQ. monadInv EQ.
  transitivity (s2.(st_code)!pc'). eauto. 
  transitivity (s5.(st_code)!pc'). eapply add_moves_unchanged; eauto.
    left. inversion INCR5. inversion INCR3. monadInv EQ1; simpl in *. xomega. 
  transitivity (s4.(st_code)!pc'). eapply rec_unchanged; eauto. 
    simpl. monadInv EQ; simpl. monadInv EQ1; simpl. xomega.
    simpl. monadInv EQ1; simpl. auto. 
  monadInv EQ; simpl. monadInv EQ1; simpl. auto.
(* tailcall *)
  destruct (can_inline fe s1).
  destruct (retinfo ctx) as [[rpc rreg]|]; eauto.
  monadInv H. unfold inline_tail_function in EQ. monadInv EQ.
  transitivity (s2.(st_code)!pc'). eauto. 
  transitivity (s5.(st_code)!pc'). eapply add_moves_unchanged; eauto.
    left. inversion INCR5. inversion INCR3. monadInv EQ1; simpl in *. xomega. 
  transitivity (s4.(st_code)!pc'). eapply rec_unchanged; eauto. 
    simpl. monadInv EQ; simpl. monadInv EQ1; simpl. xomega.
    simpl. monadInv EQ1; simpl. auto. 
  monadInv EQ; simpl. monadInv EQ1; simpl. auto.
(* return *)
  destruct (retinfo ctx) as [[rpc rreg]|]; eauto.
Qed.

Lemma iter_expand_instr_unchanged:
  forall ctx pc l s x s' i,
  mlist_iter2 (expand_instr fe rec ctx) l s = R x s' i ->
  Ple ctx.(dpc) s.(st_nextnode) ->
  Ple pc s.(st_nextnode) ->
  ~In pc (List.map (spc ctx) (List.map (@fst _ _) l)) ->
  list_norepet (List.map (@fst _ _) l) ->
  s'.(st_code)!pc = s.(st_code)!pc.
Proof.
  induction l; simpl; intros.
  (* base case *)
  monadInv H. auto.
  (* inductive case *)
  destruct a as [pc1 instr1]; simpl in *.
  monadInv H. inv H3.
  transitivity ((st_code s0)!pc). 
  eapply IHl; eauto. destruct INCR; xomega. destruct INCR; xomega. 
  eapply expand_instr_unchanged; eauto.
Qed.

Lemma expand_cfg_rec_unchanged:
  forall ctx f s x s' i pc,
  expand_cfg_rec fe rec ctx f s = R x s' i ->
  Ple ctx.(dpc) s.(st_nextnode) ->
  Ple pc ctx.(dpc) ->
  s'.(st_code)!pc = s.(st_code)!pc.
Proof.
  intros. unfold expand_cfg_rec in H. monadInv H. inversion EQ.
  transitivity ((st_code s0)!pc).
  eapply iter_expand_instr_unchanged; eauto. 
    subst s0; auto. 
    subst s0; simpl. xomega.
    red; intros. exploit list_in_map_inv; eauto. intros [pc1 [A B]]. 
    subst pc. unfold spc in H1. xomega.
    apply PTree.elements_keys_norepet.
  subst s0; auto.
Qed.

Hypothesis rec_spec:
  forall fe' (L: (size_fenv fe' < size_fenv fe)%nat) ctx f s x s' i c,
  rec fe' L ctx f s = R x s' i ->
  fenv_agree fe' ->
  Ple (ctx.(dpc) + max_pc_function f) s.(st_nextnode) ->
  ctx.(mreg) = max_def_function f ->
  Ple (ctx.(dreg) + ctx.(mreg)) s.(st_nextreg) ->
  ctx.(mstk) >= 0 -> 
  ctx.(mstk) = Zmax (fn_stacksize f) 0 ->
  (min_alignment (fn_stacksize f) | ctx.(dstk)) ->
  ctx.(dstk) >= 0 ->
  s'.(st_stksize) <= stacksize ->
  (forall pc, Plt ctx.(dpc) pc -> Ple pc s'.(st_nextnode) -> c!pc = s'.(st_code)!pc) ->
  tr_funbody ctx f c.

Remark min_alignment_pos:
  forall sz, min_alignment sz > 0.
Proof.
  intros; unfold min_alignment.
  destruct (zle sz 1). omega. destruct (zle sz 2). omega. destruct (zle sz 4); omega.
Qed.

Ltac inv_incr :=
  match goal with
  | [ H: sincr _ _ |- _ ] => destruct H; inv_incr
  | _ => idtac
  end.

Lemma expand_instr_spec:
  forall ctx pc instr s x s' i c,
  expand_instr fe rec ctx pc instr s = R x s' i ->
  Ple (max_def_instr instr) ctx.(mreg) ->
  Ple (spc ctx pc) s.(st_nextnode) ->
  Ple (ctx.(dreg) + ctx.(mreg)) s.(st_nextreg) ->
  ctx.(mstk) >= 0 -> ctx.(dstk) >= 0 ->
  s'.(st_stksize) <= stacksize ->
  (forall pc', Plt s.(st_nextnode) pc' -> Ple pc' s'.(st_nextnode) -> c!pc' = s'.(st_code)!pc') ->
  c!(spc ctx pc) = s'.(st_code)!(spc ctx pc) ->
  tr_instr ctx pc instr c.
Proof.
  intros until c; intros EXP DEFS OPC OREG STK1 STK2 STK3 S1 S2.
  generalize set_instr_same; intros BASE.
  unfold expand_instr in EXP; destruct instr; simpl in DEFS;
  try (econstructor; eauto; fail).
(* call *)
  destruct (can_inline fe s1) as [|id f P Q].
  (* not inlined *)
  eapply tr_call; eauto. 
  (* inlined *)
  subst s1.
  monadInv EXP. unfold inline_function in EQ; monadInv EQ.
  set (ctx' := callcontext ctx x1 x2 (max_def_function f) (fn_stacksize f) n r).
  inversion EQ0; inversion EQ1; inversion EQ. inv_incr. 
  apply tr_call_inlined with (pc1 := x0) (ctx' := ctx') (f := f); auto.
  eapply BASE; eauto. 
  eapply add_moves_spec; eauto.
    intros. rewrite S1. eapply set_instr_other; eauto. unfold node; xomega. xomega. xomega.
  eapply rec_spec; eauto.
    red; intros. rewrite PTree.grspec in H. destruct (PTree.elt_eq id0 id); try discriminate. auto.
    simpl. subst s2; simpl in *; xomega.
    simpl. subst s3; simpl in *; xomega.
    simpl. xomega.
    simpl. apply align_divides. apply min_alignment_pos.
    assert (dstk ctx + mstk ctx <= dstk ctx'). simpl. apply align_le. apply min_alignment_pos. omega.
    omega.
    intros. simpl in H. rewrite S1.
    transitivity s1.(st_code)!pc0. eapply set_instr_other; eauto. unfold node in *; xomega.
    eapply add_moves_unchanged; eauto. unfold node in *; xomega. xomega. 
  red; simpl. subst s2; simpl in *; xomega.
  red; simpl. split. auto. apply align_le. apply min_alignment_pos.
(* tailcall *)
  destruct (can_inline fe s1) as [|id f P Q].
  (* not inlined *)
  destruct (retinfo ctx) as [[rpc rreg] | ]_eqn. 
  (* turned into a call *)
  eapply tr_tailcall_call; eauto. 
  (* preserved *)
  eapply tr_tailcall; eauto. 
  (* inlined *)
  subst s1.
  monadInv EXP. unfold inline_function in EQ; monadInv EQ.
  set (ctx' := tailcontext ctx x1 x2 (max_def_function f) (fn_stacksize f)) in *.
  inversion EQ0; inversion EQ1; inversion EQ. inv_incr. 
  apply tr_tailcall_inlined with (pc1 := x0) (ctx' := ctx') (f := f); auto.
  eapply BASE; eauto. 
  eapply add_moves_spec; eauto.
    intros. rewrite S1. eapply set_instr_other; eauto. unfold node; xomega. xomega. xomega.
  eapply rec_spec; eauto.
    red; intros. rewrite PTree.grspec in H. destruct (PTree.elt_eq id0 id); try discriminate. auto.
    simpl. subst s2; simpl in *; xomega.
    simpl. subst s3; simpl in *; xomega.
    simpl. xomega.
    simpl. apply align_divides. apply min_alignment_pos.
    assert (dstk ctx <= dstk ctx'). simpl. apply align_le. apply min_alignment_pos. omega.
    omega.
    intros. simpl in H. rewrite S1.
    transitivity s1.(st_code)!pc0. eapply set_instr_other; eauto. unfold node in *; xomega.
    eapply add_moves_unchanged; eauto. unfold node in *; xomega. xomega. 
  red; simpl. subst s2; simpl in *; xomega.
  red; auto.
(* return *)
  destruct (retinfo ctx) as [[rpc rreg] | ]_eqn. 
  (* inlined *)
  eapply tr_return_inlined; eauto. 
  (* unchanged *)
  eapply tr_return; eauto. 
Qed.

Lemma iter_expand_instr_spec:
  forall ctx l s x s' i c,
  mlist_iter2 (expand_instr fe rec ctx) l s = R x s' i ->
  list_norepet (List.map (@fst _ _) l) ->
  (forall pc instr, In (pc, instr) l -> Ple (max_def_instr instr) ctx.(mreg)) ->
  (forall pc instr, In (pc, instr) l -> Ple (spc ctx pc) s.(st_nextnode)) ->
  Ple (ctx.(dreg) + ctx.(mreg)) s.(st_nextreg) ->
  ctx.(mstk) >= 0 -> ctx.(dstk) >= 0 ->
  s'.(st_stksize) <= stacksize ->
  (forall pc', Plt s.(st_nextnode) pc' -> Ple pc' s'.(st_nextnode) -> c!pc' = s'.(st_code)!pc') ->
  (forall pc instr, In (pc, instr) l -> c!(spc ctx pc) = s'.(st_code)!(spc ctx pc)) ->
  forall pc instr, In (pc, instr) l -> tr_instr ctx pc instr c.
Proof.
  induction l; simpl; intros.
  (* base case *)
  contradiction.
  (* inductive case *)
  destruct a as [pc1 instr1]; simpl in *. inv H0. monadInv H. inv_incr.
  assert (A: Ple ctx.(dpc) s0.(st_nextnode)).
    assert (B: Ple (spc ctx pc) (st_nextnode s)) by eauto. unfold spc in B; xomega.
  destruct H9. inv H.
  (* same pc *)
  eapply expand_instr_spec; eauto.
  omega.
  intros.
    transitivity ((st_code s')!pc'). 
    apply H7. auto. xomega. 
    eapply iter_expand_instr_unchanged; eauto. 
    red; intros. rewrite list_map_compose in H9. exploit list_in_map_inv; eauto. 
    intros [[pc0 instr0] [P Q]]. simpl in P. 
    assert (Ple (spc ctx pc0) (st_nextnode s)) by eauto. xomega.
  transitivity ((st_code s')!(spc ctx pc)). 
    eapply H8; eauto. 
    eapply iter_expand_instr_unchanged; eauto. 
    assert (Ple (spc ctx pc) (st_nextnode s)) by eauto. xomega.
    red; intros. rewrite list_map_compose in H. exploit list_in_map_inv; eauto. 
    intros [[pc0 instr0] [P Q]]. simpl in P. unfold spc in P. 
    assert (pc = pc0) by (unfold node; xomega). subst pc0.
    elim H12. change pc with (fst (pc, instr0)). apply List.in_map; auto.
  (* older pc *)
  inv_incr. eapply IHl; eauto. 
  intros. eapply Ple_trans; eauto. 
  intros; eapply Ple_trans; eauto.
  intros. apply H7; auto. xomega.
Qed.

Lemma expand_cfg_rec_spec:
  forall ctx f s x s' i c,
  expand_cfg_rec fe rec ctx f s = R x s' i ->
  Ple (ctx.(dpc) + max_pc_function f) s.(st_nextnode) ->
  ctx.(mreg) = max_def_function f ->
  Ple (ctx.(dreg) + ctx.(mreg)) s.(st_nextreg) ->
  ctx.(mstk) >= 0 -> 
  ctx.(mstk) = Zmax (fn_stacksize f) 0 ->
  (min_alignment (fn_stacksize f) | ctx.(dstk)) ->
  ctx.(dstk) >= 0 ->
  s'.(st_stksize) <= stacksize ->
  (forall pc', Plt ctx.(dpc) pc' -> Ple pc' s'.(st_nextnode) -> c!pc' = s'.(st_code)!pc') ->
  tr_funbody ctx f c.
Proof.
  intros. unfold expand_cfg_rec in H. monadInv H. inversion EQ. 
  constructor. 
  intros. rewrite H1. eapply max_def_function_params; eauto. 
  intros. eapply iter_expand_instr_spec; eauto. 
    apply PTree.elements_keys_norepet. 
    intros. rewrite H1. eapply max_def_function_instr; eauto. 
    eapply PTree.elements_complete; eauto.
  intros.
    assert (Ple pc0 (max_pc_function f)).
      eapply max_pc_function_sound. eapply PTree.elements_complete; eauto.  
    unfold spc. subst s0; simpl; xomega.
  subst s0; simpl; auto.
  intros. apply H8; auto. subst s0; simpl in H11; xomega.
  intros. apply H8. unfold spc; xomega. 
    assert (Ple pc0 (max_pc_function f)).
      eapply max_pc_function_sound. eapply PTree.elements_complete; eauto.  
    unfold spc. inversion i; xomega.
  apply PTree.elements_correct; auto.
  auto. auto. auto.
  inversion INCR0. subst s0; simpl in STKSIZE; xomega.
Qed.

End EXPAND_INSTR.

Lemma expand_cfg_unchanged:
  forall fe ctx f s x s' i pc,
  expand_cfg fe ctx f s = R x s' i ->
  Ple ctx.(dpc) s.(st_nextnode) ->
  Ple pc ctx.(dpc) ->
  s'.(st_code)!pc = s.(st_code)!pc.
Proof.
  intros fe0; pattern fe0. apply well_founded_ind with (R := ltof _ size_fenv).
  apply well_founded_ltof.
  intros. unfold expand_cfg in H0. rewrite unroll_Fixm in H0.
  eapply expand_cfg_rec_unchanged; eauto. assumption. 
Qed.

Lemma expand_cfg_spec:
  forall fe ctx f s x s' i c,
  expand_cfg fe ctx f s = R x s' i ->
  fenv_agree fe ->  
  Ple (ctx.(dpc) + max_pc_function f) s.(st_nextnode) ->
  ctx.(mreg) = max_def_function f ->
  Ple (ctx.(dreg) + ctx.(mreg)) s.(st_nextreg) ->
  ctx.(mstk) >= 0 -> 
  ctx.(mstk) = Zmax (fn_stacksize f) 0 ->
  (min_alignment (fn_stacksize f) | ctx.(dstk)) ->
  ctx.(dstk) >= 0 ->
  s'.(st_stksize) <= stacksize ->
  (forall pc', Plt ctx.(dpc) pc' -> Ple pc' s'.(st_nextnode) -> c!pc' = s'.(st_code)!pc') ->
  tr_funbody ctx f c.
Proof.
  intros fe0; pattern fe0. apply well_founded_ind with (R := ltof _ size_fenv).
  apply well_founded_ltof.
  intros. unfold expand_cfg in H0. rewrite unroll_Fixm in H0.
  eapply expand_cfg_rec_spec; eauto. 
  simpl. intros. eapply expand_cfg_unchanged; eauto. assumption.
Qed.

End INLINING_BODY_SPEC.

(** ** Relational specification of the translation of a function *)

Inductive tr_function: function -> function -> Prop :=
  | tr_function_intro: forall f f' ctx,
      tr_funbody f'.(fn_stacksize) ctx f f'.(fn_code) ->
      ctx.(dstk) = 0 ->
      ctx.(retinfo) = None ->
      f'.(fn_sig) = f.(fn_sig) ->
      f'.(fn_params) = sregs ctx f.(fn_params) ->
      f'.(fn_entrypoint) = spc ctx f.(fn_entrypoint) ->
      0 <= fn_stacksize f' <= Int.max_unsigned ->
      tr_function f f'.

Lemma transf_function_spec:
  forall f f', transf_function fenv f = OK f' -> tr_function f f'.
Proof.
  intros. unfold transf_function in H.
  destruct (expand_function fenv f initstate) as [ctx s i]_eqn. 
  destruct (zle (st_stksize s) Int.max_unsigned); inv H.
  monadInv Heqr. set (ctx := initcontext x x0 (max_def_function f) (fn_stacksize f)) in *.
Opaque initstate.
  destruct INCR3. inversion EQ1. inversion EQ.
  apply tr_function_intro with ctx; auto.
  eapply expand_cfg_spec with (fe := fenv); eauto.
    red; auto.
    unfold ctx; rewrite <- H1; rewrite <- H2; rewrite <- H3; simpl. xomega.
    unfold ctx; rewrite <- H0; rewrite <- H1; simpl. xomega.
    simpl. xomega.
    simpl. apply Zdivide_0. 
    simpl. omega.
  simpl. omega.
  simpl. split; auto. destruct INCR2. destruct INCR1. destruct INCR0. destruct INCR. 
  simpl. change 0 with (st_stksize initstate). omega. 
Qed.

End INLINING_SPEC.
