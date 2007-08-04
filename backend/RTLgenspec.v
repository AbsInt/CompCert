(** Abstract specification of RTL generation *)

(** In this module, we define inductive predicates that specify the 
  translations from Cminor to RTL performed by the functions in module
  [RTLgen].  We then show that these functions satisfy these relational
  specifications.  The relational specifications will then be used
  instead of the actual functions to show semantic equivalence between
  the source Cminor code and the the generated RTL code
  (see module [RTLgenproof]). *)

Require Import Coqlib.
Require Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Mem.
Require Import Globalenvs.
Require Import Switch.
Require Import Op.
Require Import Registers.
Require Import CminorSel.
Require Import RTL.
Require Import RTLgen.

(** * Reasoning about monadic computations *)

(** The tactics below simplify hypotheses of the form [f ... = OK x s]
  where [f] is a monadic computation.  For instance, the hypothesis
  [(do x <- a; b) s = OK y s'] will generate the additional witnesses
  [x], [s1] and the additional hypotheses
  [a s = OK x s1] and [b x s1 = OK y s'], reflecting the fact that
  both monadic computations [a] and [b] succeeded.
*)

Remark bind_inversion:
  forall (A B: Set) (f: mon A) (g: A -> mon B) (y: B) (s1 s3: state),
  bind f g s1 = OK y s3 ->
  exists x, exists s2, f s1 = OK x s2 /\ g x s2 = OK y s3.
Proof.
  intros until s3. unfold bind. destruct (f s1); intros.
  discriminate.
  exists a; exists s; auto.
Qed.

Remark bind2_inversion:
  forall (A B C: Set) (f: mon (A*B)) (g: A -> B -> mon C)
         (z: C) (s1 s3: state),
  bind2 f g s1 = OK z s3 ->
  exists x, exists y, exists s2, f s1 = OK (x, y) s2 /\ g x y s2 = OK z s3.
Proof.
  intros until s3. unfold bind2, bind. destruct (f s1). congruence.
  destruct p as [x y]; simpl; intro. 
  exists x; exists y; exists s; auto. 
Qed.

Ltac monadInv1 H :=
  match type of H with
  | (OK _ _ = OK _ _) =>
      inversion H; clear H; try subst
  | (Error _ _ = OK _ _) =>
      discriminate
  | (ret _ _ = OK _ _) =>
      inversion H; clear H; try subst
  | (error _ _ = OK _ _) =>
      discriminate
  | (bind ?F ?G ?S = OK ?X ?S') =>
      let x := fresh "x" in (
      let s := fresh "s" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion _ _ F G X S S' H) as [x [s [EQ1 EQ2]]];
      clear H;
      try (monadInv1 EQ2)))))
  | (bind2 ?F ?G ?S = OK ?X ?S') =>
      let x1 := fresh "x" in (
      let x2 := fresh "x" in (
      let s := fresh "s" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion _ _ _ F G X S S' H) as [x1 [x2 [s [EQ1 EQ2]]]];
      clear H;
      try (monadInv1 EQ2))))))
  end.

Ltac monadInv H :=
  match type of H with
  | (ret _ _ = OK _ _) => monadInv1 H
  | (error _ _ = OK _ _) => monadInv1 H
  | (bind ?F ?G ?S = OK ?X ?S') => monadInv1 H
  | (bind2 ?F ?G ?S = OK ?X ?S') => monadInv1 H
  | (?F _ _ _ _ _ _ _ _ = OK _ _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = OK _ _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = OK _ _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = OK _ _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = OK _ _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = OK _ _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = OK _ _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ = OK _ _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  end.

(** * Monotonicity properties of the state *)

(** Operations over the global state satisfy a crucial monotonicity property:
  nodes are only added to the CFG, but never removed nor their instructions
  changed; similarly, fresh nodes and fresh registers are only consumed,
  but never reused.  This property is captured by the following predicate
  over states, which we show is a partial order. *)

Inductive state_incr: state -> state -> Prop :=
  state_incr_intro:
    forall (s1 s2: state),
    Ple s1.(st_nextnode) s2.(st_nextnode) ->
    Ple s1.(st_nextreg) s2.(st_nextreg) ->
    (forall pc, Plt pc s1.(st_nextnode) -> s2.(st_code)!pc = s1.(st_code)!pc) ->
    state_incr s1 s2.

Lemma instr_at_incr:
  forall s1 s2 n i,
  state_incr s1 s2 -> s1.(st_code)!n = Some i -> s2.(st_code)!n = Some i.
Proof.
  intros. inversion H.
  rewrite H3. auto. elim (st_wf s1 n); intro.
  assumption. congruence.
Qed.

Lemma state_incr_refl:
  forall s, state_incr s s.
Proof.
  intros. apply state_incr_intro.
  apply Ple_refl. apply Ple_refl. intros; auto.
Qed.
Hint Resolve state_incr_refl: rtlg.

Lemma state_incr_trans:
  forall s1 s2 s3, state_incr s1 s2 -> state_incr s2 s3 -> state_incr s1 s3.
Proof.
  intros. inversion H. inversion H0. apply state_incr_intro.
  apply Ple_trans with (st_nextnode s2); assumption. 
  apply Ple_trans with (st_nextreg s2); assumption.
  intros. transitivity (s2.(st_code)!pc).
  apply H8. apply Plt_Ple_trans with s1.(st_nextnode); auto.
  apply H3; auto.
Qed.
Hint Resolve state_incr_trans: rtlg.

(** The following relation between two states is a weaker version of
  [state_incr].  It permits changing the contents at an already reserved
  graph node, but only from [None] to [Some i]. *)

Definition state_extends (s1 s2: state): Prop :=
  forall pc,
  s1.(st_code)!pc = None \/ s2.(st_code)!pc = s1.(st_code)!pc.

Lemma instr_at_extends:
  forall s1 s2 pc i,
  state_extends s1 s2 -> 
  s1.(st_code)!pc = Some i -> s2.(st_code)!pc = Some i.
Proof.
  intros. elim (H pc); intro. congruence. congruence.
Qed.

Lemma state_incr_extends:
  forall s1 s2,
  state_incr s1 s2 -> state_extends s1 s2.
Proof.
  unfold state_extends; intros. inversion H.   
  case (plt pc s1.(st_nextnode)); intro.
  right; apply H2; auto.
  left. elim (s1.(st_wf) pc); intro.
  elim (n H5). auto.
Qed.
Hint Resolve state_incr_extends.

(** * Validity and freshness of registers *)

(** An RTL pseudo-register is valid in a given state if it was created
  earlier, that is, it is less than the next fresh register of the state.
  Otherwise, the pseudo-register is said to be fresh. *)

Definition reg_valid (r: reg) (s: state) : Prop := 
  Plt r s.(st_nextreg).

Definition reg_fresh (r: reg) (s: state) : Prop :=
  ~(Plt r s.(st_nextreg)).

Lemma valid_fresh_absurd:
  forall r s, reg_valid r s -> reg_fresh r s -> False.
Proof.
  intros r s. unfold reg_valid, reg_fresh; case r; tauto.
Qed.
Hint Resolve valid_fresh_absurd: rtlg.

Lemma valid_fresh_different:
  forall r1 r2 s, reg_valid r1 s -> reg_fresh r2 s -> r1 <> r2.
Proof.
  unfold not; intros. subst r2. eauto with rtlg.
Qed.
Hint Resolve valid_fresh_different: rtlg.

Lemma reg_valid_incr: 
  forall r s1 s2, state_incr s1 s2 -> reg_valid r s1 -> reg_valid r s2.
Proof.
  intros r s1 s2 INCR.
  inversion INCR.
  unfold reg_valid. intros; apply Plt_Ple_trans with (st_nextreg s1); auto.
Qed.
Hint Resolve reg_valid_incr: rtlg.

Lemma reg_fresh_decr:
  forall r s1 s2, state_incr s1 s2 -> reg_fresh r s2 -> reg_fresh r s1.
Proof.
  intros r s1 s2 INCR. inversion INCR.
  unfold reg_fresh; unfold not; intros.
  apply H4. apply Plt_Ple_trans with (st_nextreg s1); auto.
Qed. 
Hint Resolve reg_fresh_decr: rtlg.

(** Validity of a list of registers. *)

Definition regs_valid (rl: list reg) (s: state) : Prop :=
  forall r, In r rl -> reg_valid r s.

Lemma regs_valid_nil: 
  forall s, regs_valid nil s.
Proof.
  intros; red; intros. elim H.
Qed.
Hint Resolve regs_valid_nil: rtlg.

Lemma regs_valid_cons:
  forall r1 rl s,
  reg_valid r1 s -> regs_valid rl s -> regs_valid (r1 :: rl) s.
Proof.
  intros; red; intros. elim H1; intro. subst r1; auto. auto.
Qed.

Lemma regs_valid_incr:
  forall s1 s2 rl, state_incr s1 s2 -> regs_valid rl s1 -> regs_valid rl s2.
Proof.
  unfold regs_valid; intros; eauto with rtlg.
Qed.
Hint Resolve regs_valid_incr: rtlg.

(** A register is ``in'' a mapping if it is associated with a Cminor
  local or let-bound variable. *)

Definition reg_in_map (m: mapping) (r: reg) : Prop :=
  (exists id, m.(map_vars)!id = Some r) \/ In r m.(map_letvars).

(** A compilation environment (mapping) is valid in a given state if
  the registers associated with Cminor local variables and let-bound variables
  are valid in the state. *)

Definition map_valid (m: mapping) (s: state) : Prop :=
  forall r, reg_in_map m r -> reg_valid r s.

Lemma map_valid_incr:
  forall s1 s2 m,
  state_incr s1 s2 -> map_valid m s1 -> map_valid m s2.
Proof.
  unfold map_valid; intros; eauto with rtlg.
Qed.
Hint Resolve map_valid_incr: rtlg.

(** * Properties of basic operations over the state *)

(** Properties of [add_instr]. *)

Lemma add_instr_incr:
  forall s1 s2 i n,
  add_instr i s1 = OK n s2 -> state_incr s1 s2.
Proof.
  intros. monadInv H.
  apply state_incr_intro; simpl.
  apply Ple_succ.
  apply Ple_refl.
  intros. apply PTree.gso; apply Plt_ne; auto.
Qed.
Hint Resolve add_instr_incr: rtlg.

Lemma add_instr_at:
  forall s1 s2 i n,
  add_instr i s1 = OK n s2 -> s2.(st_code)!n = Some i.
Proof.
  intros. monadInv H. simpl. apply PTree.gss.
Qed.
Hint Resolve add_instr_at.

(** Properties of [reserve_instr] and [update_instr]. *)

Lemma reserve_instr_incr:
  forall s1 s2 n,
  reserve_instr s1 = OK n s2 -> state_incr s1 s2.
Proof.
  intros. monadInv H. 
  apply state_incr_intro; simpl.
  apply Ple_succ.
  apply Ple_refl.
  auto.
Qed.

Lemma update_instr_incr:
  forall s1 s2 s3 s4 i n t,
  reserve_instr s1 = OK n s2 ->
  state_incr s2 s3 ->
  update_instr n i s3 = OK t s4 ->
  state_incr s1 s4.
Proof.
  intros.
  generalize H1; clear H1; unfold update_instr.
  case (plt n (st_nextnode s3)); intros. 2: discriminate.
  inv H1. inv H0. monadInv H; simpl in *.
  apply state_incr_intro; simpl.
  eapply Ple_trans; eauto. apply Plt_Ple. apply Plt_succ.
  auto.
  intros. rewrite PTree.gso.
  apply H3. apply Plt_trans_succ; auto.
  apply Plt_ne. auto.
Qed.

Lemma update_instr_extends:
  forall s1 s2 s3 s4 i n t,
  reserve_instr s1 = OK n s2 ->
  state_incr s2 s3 ->
  update_instr n i s3 = OK t s4 ->
  state_extends s3 s4.
Proof.
  intros. injection H. intros EQ1 EQ2.  
  red; intros. 
  case (peq pc n); intro.
  subst pc. left. inversion H0. rewrite H4. rewrite <- EQ1; simpl.
  destruct (s1.(st_wf) n). rewrite <- EQ2 in H7. elim (Plt_strict _ H7).
  auto.
  rewrite <- EQ1; rewrite <- EQ2; simpl. apply Plt_succ.
  generalize H1; unfold update_instr.
  case (plt n s3.(st_nextnode)); intros; inv H2. 
  right; simpl. apply PTree.gso; auto.
Qed.

(** Properties of [new_reg]. *)

Lemma new_reg_incr:
  forall s1 s2 r, new_reg s1 = OK r s2 -> state_incr s1 s2.
Proof.
  intros. monadInv H. 
  apply state_incr_intro; simpl.
  apply Ple_refl. apply Ple_succ. auto.
Qed.
Hint Resolve new_reg_incr: rtlg.

Lemma new_reg_valid:
  forall s1 s2 r,
  new_reg s1 = OK r s2 -> reg_valid r s2.
Proof.
  intros. monadInv H.
  unfold reg_valid; simpl. apply Plt_succ.
Qed.
Hint Resolve new_reg_valid: rtlg.

Lemma new_reg_fresh:
  forall s1 s2 r,
  new_reg s1 = OK r s2 -> reg_fresh r s1.
Proof.
  intros. monadInv H.
  unfold reg_fresh; simpl.
  exact (Plt_strict _).
Qed.
Hint Resolve new_reg_fresh: rtlg.

Lemma new_reg_not_in_map:
  forall s1 s2 m r,
  new_reg s1 = OK r s2 -> map_valid m s1 -> ~(reg_in_map m r).
Proof.
  unfold not; intros; eauto with rtlg.
Qed. 
Hint Resolve new_reg_not_in_map: rtlg.

(** * Properties of operations over compilation environments *)

Lemma init_mapping_valid:
  forall s, map_valid init_mapping s.
Proof.
  unfold map_valid, init_mapping.
  intros s r [[id A] | B].  
  simpl in A. rewrite PTree.gempty in A; discriminate.
  simpl in B. tauto.
Qed.  

(** Properties of [find_var]. *)

Lemma find_var_incr:
  forall s1 s2 map name r,
  find_var map name s1 = OK r s2 -> state_incr s1 s2.
Proof.
  intros until r. unfold find_var.
  case (map_vars map)!name; intros; monadInv H. 
  auto with rtlg.
Qed.
Hint Resolve find_var_incr: rtlg.

Lemma find_var_in_map:
  forall s1 s2 map name r,
  find_var map name s1 = OK r s2 -> reg_in_map map r.
Proof.
  intros until r. unfold find_var; caseEq (map.(map_vars)!name).
  intros. inv H0. left; exists name; auto.
  intros. inv H0.
Qed.
Hint Resolve find_var_in_map: rtlg.

Lemma find_var_valid:
  forall s1 s2 map name r,
  find_var map name s1 = OK r s2 -> map_valid map s1 -> reg_valid r s1.
Proof.
  eauto with rtlg.
Qed.
Hint Resolve find_var_valid: rtlg.

(** Properties of [find_letvar]. *)

Lemma find_letvar_incr:
  forall s1 s2 map idx r,
  find_letvar map idx s1 = OK r s2 -> state_incr s1 s2.
Proof.
  intros until r. unfold find_letvar.
  case (nth_error (map_letvars map) idx); intros; monadInv H.
  auto with rtlg.
Qed.
Hint Resolve find_letvar_incr: rtlg.

Lemma find_letvar_in_map:
  forall s1 s2 map idx r,
  find_letvar map idx s1 = OK r s2 -> reg_in_map map r.
Proof.
  intros until r. unfold find_letvar.
  caseEq (nth_error (map_letvars map) idx); intros; monadInv H0.
  right; apply nth_error_in with idx; auto.
Qed.
Hint Resolve find_letvar_in_map: rtlg.

Lemma find_letvar_valid:
  forall s1 s2 map idx r,
  find_letvar map idx s1 = OK r s2 -> map_valid map s1 -> reg_valid r s1.
Proof.
  eauto with rtlg.
Qed.
Hint Resolve find_letvar_valid: rtlg.

(** Properties of [add_var]. *)

Lemma add_var_valid:
  forall s1 s2 map1 map2 name r, 
  add_var map1 name s1 = OK (r, map2) s2 ->
  map_valid map1 s1 ->
  reg_valid r s2 /\ map_valid map2 s2.
Proof.
  intros. monadInv H. 
  split. eauto with rtlg.
  inversion EQ. subst. red. intros r' [[id A] | B].
  simpl in A. rewrite PTree.gsspec in A. destruct (peq id name).
  inv A. eauto with rtlg.
  apply reg_valid_incr with s1. eauto with rtlg. 
  apply H0. left; exists id; auto.
  simpl in B. apply reg_valid_incr with s1. eauto with rtlg.
  apply H0. right; auto.
Qed.

Lemma add_var_incr:
  forall s1 s2 map name rm, 
  add_var map name s1 = OK rm s2 -> state_incr s1 s2.
Proof.
  intros. monadInv H. eauto with rtlg.
Qed.
Hint Resolve add_var_incr: rtlg.

Lemma add_var_find:
  forall s1 s2 map name r map',
  add_var map name s1 = OK (r,map') s2 -> map'.(map_vars)!name = Some r.
Proof.
  intros. monadInv H. simpl. apply PTree.gss. 
Qed.

Lemma add_vars_incr:
  forall names s1 s2 map r,
  add_vars map names s1 = OK r s2 -> state_incr s1 s2.
Proof.
  induction names; simpl; intros; monadInv H.
  auto with rtlg.
  eauto with rtlg. 
Qed.

Lemma add_vars_valid:
  forall namel s1 s2 map1 map2 rl, 
  add_vars map1 namel s1 = OK (rl, map2) s2 ->
  map_valid map1 s1 ->
  regs_valid rl s2 /\ map_valid map2 s2.
Proof.
  induction namel; simpl; intros; monadInv H.
  split. red; simpl; intros; tauto. auto.
  exploit IHnamel; eauto. intros [A B].
  exploit add_var_valid; eauto. intros [C D].
  exploit add_var_incr; eauto. intros INCR.
  split. apply regs_valid_cons; eauto with rtlg.
  auto.
Qed.

Lemma add_var_letenv:
  forall map1 i s1 r map2 s2,
  add_var map1 i s1 = OK (r, map2) s2 ->
  map2.(map_letvars) = map1.(map_letvars).
Proof.
  intros; monadInv H. reflexivity.
Qed.

Lemma add_vars_letenv:
  forall il map1 s1 rl map2 s2,
  add_vars map1 il s1 = OK (rl, map2) s2 ->
  map2.(map_letvars) = map1.(map_letvars).
Proof.
  induction il; simpl; intros; monadInv H.
  reflexivity.
  transitivity (map_letvars x0).
  eapply add_var_letenv; eauto.
  eauto.
Qed.

(** Properties of [add_letvar]. *)

Lemma add_letvar_valid:
  forall map s r,
  map_valid map s ->
  reg_valid r s ->
  map_valid (add_letvar map r) s.
Proof.
  intros; red; intros. 
  destruct H1 as [[id A]|B]. 
  simpl in A. apply H. left; exists id; auto.
  simpl in B. elim B; intro. 
  subst r0; auto. apply H. right; auto.
Qed.

(** * Properties of [alloc_reg] and [alloc_regs] *)

Lemma alloc_reg_incr:
  forall a s1 s2 map r,
  alloc_reg map a s1 = OK r s2 -> state_incr s1 s2.
Proof.
  intros until r.  unfold alloc_reg.
  case a; eauto with rtlg.
Qed.
Hint Resolve alloc_reg_incr: rtlg.

Lemma alloc_reg_valid:
  forall a s1 s2 map r,
  map_valid map s1 ->
  alloc_reg map a s1 = OK r s2 -> reg_valid r s2.
Proof.
  intros until r.  unfold alloc_reg.
  case a; eauto with rtlg.
Qed.
Hint Resolve alloc_reg_valid: rtlg.

Lemma alloc_reg_fresh_or_in_map:
  forall map a s r s',
  map_valid map s ->
  alloc_reg map a s = OK r s' ->
  reg_in_map map r \/ reg_fresh r s.
Proof.
  intros until s'. unfold alloc_reg.
  destruct a; intros; try (right; eauto with rtlg; fail).
  left; eauto with rtlg.
  left; eauto with rtlg.
Qed.

Lemma alloc_regs_incr:
  forall al s1 s2 map rl,
  alloc_regs map al s1 = OK rl s2 -> state_incr s1 s2.
Proof.
  induction al; simpl; intros; monadInv H; eauto with rtlg.
Qed.
Hint Resolve alloc_regs_incr: rtlg.

Lemma alloc_regs_valid:
  forall al s1 s2 map rl,
  map_valid map s1 ->
  alloc_regs map al s1 = OK rl s2 ->
  regs_valid rl s2.
Proof.
  induction al; simpl; intros; monadInv H0.
  apply regs_valid_nil.
  apply regs_valid_cons. eauto with rtlg. eauto with rtlg. 
Qed.
Hint Resolve alloc_regs_valid: rtlg.

Lemma alloc_regs_fresh_or_in_map:
  forall map al s rl s',
  map_valid map s ->
  alloc_regs map al s = OK rl s' ->
  forall r, In r rl -> reg_in_map map r \/ reg_fresh r s.
Proof.
  induction al; simpl; intros; monadInv H0.
  elim H1.
  elim H1; intro. 
  subst r.
  eapply alloc_reg_fresh_or_in_map; eauto.
  exploit IHal. apply map_valid_incr with s0; eauto with rtlg. eauto. eauto.
  intros [A|B]. auto. right; eauto with rtlg.
Qed.

(** A register is an adequate target for holding the value of an
  expression if
- either the register is associated with a Cminor let-bound variable
  or a Cminor local variable;
- or the register is not associated with any Cminor variable
  and does not belong to the preserved set [pr]. *)

Inductive target_reg_ok (map: mapping) (pr: list reg): expr -> reg -> Prop :=
  | target_reg_var:
      forall id r,
      map.(map_vars)!id = Some r ->
      target_reg_ok map pr (Evar id) r
  | target_reg_letvar:
      forall idx r,
      nth_error map.(map_letvars) idx = Some r ->
      target_reg_ok map pr (Eletvar idx) r
  | target_reg_other:
      forall a r,
      ~(reg_in_map map r) -> ~In r pr ->
      target_reg_ok map pr a r.

Inductive target_regs_ok (map: mapping) (pr: list reg): exprlist -> list reg -> Prop :=
  | target_regs_nil:
      target_regs_ok map pr Enil nil
  | target_regs_cons: forall a1 al r1 rl,
      target_reg_ok map pr a1 r1 ->
      target_regs_ok map (r1 :: pr) al rl ->
      target_regs_ok map pr (Econs a1 al) (r1 :: rl).

Lemma target_reg_ok_append:
  forall map pr a r,
  target_reg_ok map pr a r ->
  forall pr',
  (forall r', In r' pr' -> reg_in_map map r' \/ r' <> r) ->
  target_reg_ok map (pr' ++ pr) a r.
Proof.
  induction 1; intros.
  constructor; auto.
  constructor; auto.
  constructor; auto. red; intros. 
  elim (in_app_or _ _ _ H2); intro. 
  generalize (H1 _ H3). tauto. tauto.
Qed.

Lemma target_reg_ok_cons:
  forall map pr a r,
  target_reg_ok map pr a r ->
  forall r',
  reg_in_map map r' \/ r' <> r ->
  target_reg_ok map (r' :: pr) a r.
Proof.
  intros. change (r' :: pr) with ((r' :: nil) ++ pr).
  apply target_reg_ok_append; auto. 
  intros r'' [A|B]. subst r''; auto. contradiction.
Qed.

Lemma new_reg_target_ok:
  forall map pr s1 a r s2,
  map_valid map s1 ->
  regs_valid pr s1 ->
  new_reg s1 = OK r s2 ->
  target_reg_ok map pr a r.
Proof.
  intros. constructor. 
  red; intro. apply valid_fresh_absurd with r s1.
  eauto with rtlg. eauto with rtlg.
  red; intro. apply valid_fresh_absurd with r s1.
  auto. eauto with rtlg.
Qed.

Lemma alloc_reg_target_ok:
  forall map pr s1 a r s2,
  map_valid map s1 ->
  regs_valid pr s1 ->
  alloc_reg map a s1 = OK r s2 ->
  target_reg_ok map pr a r.
Proof.
  intros. unfold alloc_reg in H1. destruct a;
  try (eapply new_reg_target_ok; eauto; fail).
  (* Evar *)
  generalize H1; unfold find_var. caseEq (map_vars map)!i; intros.
  inv H3. constructor. auto. inv H3.
  (* Elet *)
  generalize H1; unfold find_letvar. caseEq (nth_error (map_letvars map) n); intros.
  inv H3. constructor. auto. inv H3.
Qed.

Lemma alloc_regs_target_ok:
  forall map al pr s1 rl s2,
  map_valid map s1 ->
  regs_valid pr s1 ->
  alloc_regs map al s1 = OK rl s2 ->
  target_regs_ok map pr al rl.
Proof.
  induction al; intros; monadInv H1.
  constructor.
  constructor.
  eapply alloc_reg_target_ok; eauto. 
  apply IHal with s s2; eauto with rtlg. 
  apply regs_valid_cons; eauto with rtlg.
Qed.

Hint Resolve new_reg_target_ok alloc_reg_target_ok alloc_regs_target_ok: rtlg.  

(** The following predicate is a variant of [target_reg_ok] used
  to characterize registers that are adequate for holding the return
  value of a function. *)

Inductive return_reg_ok: state -> mapping -> option reg -> Prop :=
  | return_reg_ok_none:
      forall s map,
      return_reg_ok s map None
  | return_reg_ok_some:
      forall s map r,
      ~(reg_in_map map r) -> reg_valid r s ->
      return_reg_ok s map (Some r).

Lemma return_reg_ok_incr:
  forall s map rret, return_reg_ok s map rret ->
  forall s', state_incr s s' -> return_reg_ok s' map rret.
Proof.
  induction 1; intros; econstructor; eauto with rtlg.
Qed.
Hint Resolve return_reg_ok_incr: rtlg.

Lemma new_reg_return_ok:
  forall s1 r s2 map sig,
  new_reg s1 = OK r s2 ->
  map_valid map s1 ->
  return_reg_ok s2 map (ret_reg sig r).
Proof.
  intros. unfold ret_reg. destruct (sig_res sig); constructor.
  eauto with rtlg. eauto with rtlg.  
Qed.

(** * Relational specification of the translation *)

(** We now define inductive predicates that characterize the fact that
  the control-flow graph produced by compilation of a Cminor function
  contains sub-graphs that correspond to the translation of each
  Cminor expression or statement in the original code. *)

(** [tr_move c ns rs nd rd] holds if the graph [c], between nodes [ns]
  and [nd], contains instructions that move the value of register [rs]
  to register [rd]. *)

Inductive tr_move (c: code):
       node -> reg -> node -> reg -> Prop :=
  | tr_move_0: forall n r,
      tr_move c n r n r
  | tr_move_1: forall ns rs nd rd,
      c!ns = Some (Iop Omove (rs :: nil) rd nd) ->
      tr_move c ns rs nd rd.

(** [tr_expr c map pr expr ns nd rd] holds if the graph [c],
  between nodes [ns] and [nd], contains instructions that compute the
  value of the Cminor expression [expr] and deposit this value in
  register [rd].  [map] is a mapping from Cminor variables to the
  corresponding RTL registers.  [pr] is a list of RTL registers whose
  values must be preserved during this computation.  All registers
  mentioned in [map] must also be preserved during this computation.
  To ensure this, we demand that the result registers of the instructions
  appearing on the path from [ns] to [nd] are neither in [pr] nor in [map].
*)

Inductive tr_expr (c: code): 
       mapping -> list reg -> expr -> node -> node -> reg -> Prop :=
  | tr_Evar: forall map pr id ns nd r rd,
      map.(map_vars)!id = Some r ->
      (rd = r \/ ~reg_in_map map rd /\ ~In rd pr) ->
      tr_move c ns r nd rd ->
      tr_expr c map pr (Evar id) ns nd rd
  | tr_Eop: forall map pr op al ns nd rd n1 rl,
      tr_exprlist c map pr al ns n1 rl ->
      c!n1 = Some (Iop op rl rd nd) ->
      ~reg_in_map map rd -> ~In rd pr ->
      tr_expr c map pr (Eop op al) ns nd rd
  | tr_Eload: forall map pr chunk addr al ns nd rd n1 rl,
      tr_exprlist c map pr al ns n1 rl ->
      c!n1 = Some (Iload chunk addr rl rd nd) ->
      ~reg_in_map map rd -> ~In rd pr ->
      tr_expr c map pr (Eload chunk addr al) ns nd rd
  | tr_Estore: forall map pr chunk addr al b ns nd rd n1 rl n2,
      tr_exprlist c map pr al ns n1 rl ->
      tr_expr c map (rl ++ pr) b n1 n2 rd ->
      c!n2 = Some (Istore chunk addr rl rd nd) ->
      tr_expr c map pr (Estore chunk addr al b) ns nd rd
  | tr_Ecall: forall map pr sig b cl ns nd rd n1 rf n2 rargs,
      tr_expr c map pr b ns n1 rf ->
      tr_exprlist c map (rf :: pr) cl n1 n2 rargs ->
      c!n2 = Some (Icall sig (inl _ rf) rargs rd nd) ->
      ~reg_in_map map rd -> ~In rd pr ->
      tr_expr c map pr (Ecall sig b cl) ns nd rd
  | tr_Econdition: forall map pr b ifso ifnot ns nd rd ntrue nfalse,
      tr_condition c map pr b ns ntrue nfalse ->
      tr_expr c map pr ifso ntrue nd rd ->
      tr_expr c map pr ifnot nfalse nd rd ->
      tr_expr c map pr (Econdition b ifso ifnot) ns nd rd
  | tr_Elet: forall map pr b1 b2 ns nd rd n1 r,
      ~reg_in_map map r ->
      tr_expr c map pr b1 ns n1 r ->
      tr_expr c (add_letvar map r) pr b2 n1 nd rd ->
      tr_expr c map pr (Elet b1 b2) ns nd rd
  | tr_Eletvar: forall map pr n ns nd rd r,
      List.nth_error map.(map_letvars) n = Some r ->
      (rd = r \/ ~reg_in_map map rd /\ ~In rd pr) ->
      tr_move c ns r nd rd ->
      tr_expr c map pr (Eletvar n) ns nd rd
  | tr_Ealloc: forall map pr a ns nd rd n1 r,
      tr_expr c map pr a ns n1 r ->
      c!n1 = Some (Ialloc r rd nd) ->
      ~reg_in_map map rd -> ~In rd pr ->
      tr_expr c map pr (Ealloc a) ns nd rd

(** [tr_expr c map pr cond ns ntrue nfalse rd] holds if the graph [c],
  starting at node [ns], contains instructions that compute the truth
  value of the Cminor conditional expression [cond] and terminate
  on node [ntrue] if the condition holds and on node [nfalse] otherwise. *)

with tr_condition (c: code): 
       mapping -> list reg -> condexpr -> node -> node -> node -> Prop :=
  | tr_CEtrue: forall map pr ntrue nfalse,
      tr_condition c map pr CEtrue ntrue ntrue nfalse
  | tr_CEfalse: forall map pr ntrue nfalse,
      tr_condition c map pr CEfalse nfalse ntrue nfalse
  | tr_CEcond: forall map pr cond bl ns ntrue nfalse n1 rl,
      tr_exprlist c map pr bl ns n1 rl ->
      c!n1 = Some (Icond cond rl ntrue nfalse) ->
      tr_condition c map pr (CEcond cond bl) ns ntrue nfalse
  | tr_CEcondition: forall map pr b ifso ifnot ns ntrue nfalse ntrue' nfalse',
      tr_condition c map pr b ns ntrue' nfalse' ->
      tr_condition c map pr ifso ntrue' ntrue nfalse ->
      tr_condition c map pr ifnot nfalse' ntrue nfalse ->
      tr_condition c map pr (CEcondition b ifso ifnot) ns ntrue nfalse

(** [tr_exprlist c map pr exprs ns nd rds] holds if the graph [c],
  between nodes [ns] and [nd], contains instructions that compute the values
  of the list of Cminor expression [exprlist] and deposit these values
  in registers [rds]. *)

with tr_exprlist (c: code): 
       mapping -> list reg -> exprlist -> node -> node -> list reg -> Prop :=
  | tr_Enil: forall map pr n,
      tr_exprlist c map pr Enil n n nil
  | tr_Econs: forall map pr a1 al ns nd r1 rl n1,
      tr_expr c map pr a1 ns n1 r1 ->
      tr_exprlist c map (r1 :: pr) al n1 nd rl ->
      tr_exprlist c map pr (Econs a1 al) ns nd (r1 :: rl).

(** Auxiliary for the compilation of [switch] statements. *)

Inductive tr_switch
     (c: code) (r: reg) (nexits: list node):
     comptree -> node -> Prop :=
  | tr_switch_action: forall act n,
      nth_error nexits act = Some n ->
      tr_switch c r nexits (CTaction act) n
  | tr_switch_ifeq: forall key act t' n ncont nfound,
      tr_switch c r nexits t' ncont ->
      nth_error nexits act = Some nfound ->
      c!n = Some(Icond (Ccompimm Ceq key) (r :: nil) nfound ncont) ->
      tr_switch c r nexits (CTifeq key act t') n
  | tr_switch_iflt: forall key t1 t2 n n1 n2,
      tr_switch c r nexits t1 n1 ->
      tr_switch c r nexits t2 n2 ->
      c!n = Some(Icond (Ccompuimm Clt key) (r :: nil) n1 n2) ->
      tr_switch c r nexits (CTiflt key t1 t2) n.

(** [tr_stmt c map stmt ns ncont nexits nret rret] holds if the graph [c],
  starting at node [ns], contains instructions that perform the Cminor
  statement [stmt].   These instructions branch to node [ncont] if
  the statement terminates normally, to the [n]-th node in [nexits]
  if the statement terminates prematurely on a [exit n] statement,
  and to [nret] if the statement terminates prematurely on a [return]
  statement.  Moreover, if the [return] statement has an argument,
  its value is deposited in register [rret]. *)

Inductive tr_stmt (c: code) (map: mapping):
     stmt -> node -> node -> list node -> node -> option reg -> Prop :=
  | tr_Sskip: forall ns nexits nret rret,
     tr_stmt c map Sskip ns ns nexits nret rret
  | tr_Sexpr: forall a ns nd nexits nret rret r,
     tr_expr c map nil a ns nd r ->
     tr_stmt c map (Sexpr a) ns nd nexits nret rret
  | tr_Sassign: forall id a ns nd nexits nret rret rv rt n,
     map.(map_vars)!id = Some rv ->
     tr_move c n rt nd rv ->
     tr_expr c map nil a ns n rt ->
     tr_stmt c map (Sassign id a) ns nd nexits nret rret
  | tr_Sseq: forall s1 s2 ns nd nexits nret rret n,
     tr_stmt c map s2 n nd nexits nret rret ->
     tr_stmt c map s1 ns n nexits nret rret ->
     tr_stmt c map (Sseq s1 s2) ns nd nexits nret rret
  | tr_Sifthenelse: forall a strue sfalse ns nd nexits nret rret ntrue nfalse,
     tr_stmt c map strue ntrue nd nexits nret rret ->
     tr_stmt c map sfalse nfalse nd nexits nret rret ->
     tr_condition c map nil a ns ntrue nfalse ->
     tr_stmt c map (Sifthenelse a strue sfalse) ns nd nexits nret rret
  | tr_Sloop: forall sbody ns nd nexits nret rret nloop,
     tr_stmt c map sbody ns nloop nexits nret rret ->
     c!nloop = Some(Inop ns) ->
     tr_stmt c map (Sloop sbody) ns nd nexits nret rret
  | tr_Sblock: forall sbody ns nd nexits nret rret,
     tr_stmt c map sbody ns nd (nd :: nexits) nret rret ->
     tr_stmt c map (Sblock sbody) ns nd nexits nret rret
  | tr_Sexit: forall n ns nd nexits nret rret,
     nth_error nexits n = Some ns ->
     tr_stmt c map (Sexit n) ns nd nexits nret rret
  | tr_Sswitch: forall a cases default ns nd nexits nret rret n r t,
     validate_switch default cases t = true ->
     tr_expr c map nil a ns n r ->
     tr_switch c r nexits t n ->
     tr_stmt c map (Sswitch a cases default) ns nd nexits nret rret
  | tr_Sreturn_none: forall nret nd nexits,
     tr_stmt c map (Sreturn None) nret nd nexits nret None
  | tr_Sreturn_some: forall a ns nd nexits nret rret,
     tr_expr c map nil a ns nret rret ->
     tr_stmt c map (Sreturn (Some a)) ns nd nexits nret (Some rret)
  | tr_Stailcall: forall sig b cl ns nd nexits nret rret n1 rf n2 rargs,
     tr_expr c map nil b ns n1 rf ->
     tr_exprlist c map (rf :: nil) cl n1 n2 rargs ->
     c!n2 = Some (Itailcall sig (inl _ rf) rargs) ->
     tr_stmt c map (Stailcall sig b cl) ns nd nexits nret rret.

(** [tr_function f tf] specifies the RTL function [tf] that 
  [RTLgen.transl_function] returns.  *)

Inductive tr_function: CminorSel.function -> RTL.function -> Prop :=
  | tr_function_intro:
      forall f code rparams map1 s1 rvars map2 s2 nentry nret rret orret nextnode wfcode,
      add_vars init_mapping f.(CminorSel.fn_params) init_state = OK (rparams, map1) s1 ->
      add_vars map1 f.(CminorSel.fn_vars) s1 = OK (rvars, map2) s2 ->
      orret = ret_reg f.(CminorSel.fn_sig) rret ->
      tr_stmt code map2 f.(CminorSel.fn_body) nentry nret nil nret orret ->
      code!nret = Some(Ireturn orret) -> 
      tr_function f (RTL.mkfunction
                       f.(CminorSel.fn_sig)
                       rparams
                       f.(CminorSel.fn_stackspace)
                       code
                       nentry
                       nextnode
                       wfcode).

(** * Correctness proof of the translation functions *)

(** We now show that the translation functions in module [RTLgen]
  satisfy the specifications given above as inductive predicates. *)

Scheme tr_expr_ind3 := Minimality for tr_expr Sort Prop
  with tr_condition_ind3 := Minimality for tr_condition Sort Prop
  with tr_exprlist_ind3 := Minimality for tr_exprlist Sort Prop.

Definition tr_expr_condition_exprlist_ind3
  (c: code)
  (P : mapping -> list reg -> expr -> node -> node -> reg -> Prop)
  (P0 : mapping -> list reg -> condexpr -> node -> node -> node -> Prop)
  (P1 : mapping -> list reg -> exprlist -> node -> node -> list reg -> Prop) :=
  fun a b c' d e f g h i j k l m n o =>
  conj (tr_expr_ind3 c P P0 P1 a b c' d e f g h i j k l m n o)
       (conj (tr_condition_ind3 c P P0 P1 a b c' d e f g h i j k l m n o)
             (tr_exprlist_ind3 c P P0 P1 a b c' d e f g h i j k l m n o)).

Lemma tr_move_extends:
  forall s1 s2, state_extends s1 s2 ->
  forall ns rs nd rd,
  tr_move s1.(st_code) ns rs nd rd ->
  tr_move s2.(st_code) ns rs nd rd.
Proof.
  induction 2; econstructor; eauto.
  eapply instr_at_extends; eauto.
Qed.

Lemma tr_expr_condition_exprlist_extends:
  forall s1 s2, state_extends s1 s2 ->
  (forall map pr a ns nd rd,
   tr_expr s1.(st_code) map pr a ns nd rd ->
   tr_expr s2.(st_code) map pr a ns nd rd)
/\(forall map pr a ns ntrue nfalse,
   tr_condition s1.(st_code) map pr a ns ntrue nfalse ->
   tr_condition s2.(st_code) map pr a ns ntrue nfalse)
/\(forall map pr al ns nd rl,
   tr_exprlist s1.(st_code) map pr al ns nd rl ->
   tr_exprlist s2.(st_code) map pr al ns nd rl).
Proof.
  intros s1 s2 EXT. 
  pose (AT := fun pc i => instr_at_extends s1 s2 pc i EXT).
  apply tr_expr_condition_exprlist_ind3; intros; econstructor; eauto.
  eapply tr_move_extends; eauto.
  eapply tr_move_extends; eauto.
Qed.

Lemma tr_expr_incr:
  forall s1 s2, state_incr s1 s2 ->
  forall map pr a ns nd rd,
  tr_expr s1.(st_code) map pr a ns nd rd ->
  tr_expr s2.(st_code) map pr a ns nd rd.
Proof.
  intros.
  exploit tr_expr_condition_exprlist_extends. 
  apply state_incr_extends; eauto. intros [A [B C]]. eauto.
Qed.

Lemma tr_condition_incr:
  forall s1 s2, state_incr s1 s2 ->
  forall map pr a ns ntrue nfalse,
  tr_condition s1.(st_code) map pr a ns ntrue nfalse ->
  tr_condition s2.(st_code) map pr a ns ntrue nfalse.
Proof.
  intros.
  exploit tr_expr_condition_exprlist_extends. 
  apply state_incr_extends; eauto. intros [A [B C]]. eauto.
Qed.

Lemma tr_exprlist_incr:
  forall s1 s2, state_incr s1 s2 ->
  forall map pr al ns nd rl,
  tr_exprlist s1.(st_code) map pr al ns nd rl ->
  tr_exprlist s2.(st_code) map pr al ns nd rl.
Proof.
  intros.
  exploit tr_expr_condition_exprlist_extends. 
  apply state_incr_extends; eauto. intros [A [B C]]. eauto.
Qed.

Scheme expr_ind3 := Induction for expr Sort Prop
  with condexpr_ind3 := Induction for condexpr Sort Prop
  with exprlist_ind3 := Induction for exprlist Sort Prop.

Definition expr_condexpr_exprlist_ind 
    (P1: expr -> Prop) (P2: condexpr -> Prop) (P3: exprlist -> Prop) :=
  fun a b c d e f g h i j k l m n o =>
  conj (expr_ind3 P1 P2 P3 a b c d e f g h i j k l m n o)
    (conj (condexpr_ind3 P1 P2 P3 a b c d e f g h i j k l m n o)
          (exprlist_ind3 P1 P2 P3 a b c d e f g h i j k l m n o)).

Lemma add_move_charact:
  forall s ns rs nd rd s',
  add_move rs rd nd s = OK ns s' -> 
  tr_move s'.(st_code) ns rs nd rd /\ state_incr s s'.
Proof.
  intros. unfold add_move in H. destruct (Reg.eq rs rd).
  inv H. split. constructor. auto with rtlg.
  split. constructor. eauto with rtlg. eauto with rtlg.
Qed.

Lemma transl_expr_condexpr_list_charact:
  (forall a map rd nd s ns s' pr
     (TR: transl_expr map a rd nd s = OK ns s')
     (WF: map_valid map s)
     (OK: target_reg_ok map pr a rd)
     (VALID: regs_valid pr s)
     (VALID2: reg_valid rd s),
   tr_expr s'.(st_code) map pr a ns nd rd
   /\ state_incr s s')
/\
  (forall a map ntrue nfalse s ns s' pr
     (TR: transl_condition map a ntrue nfalse s = OK ns s')
     (WF: map_valid map s)
     (VALID: regs_valid pr s),
   tr_condition s'.(st_code) map pr a ns ntrue nfalse
   /\ state_incr s s')
/\
  (forall al map rl nd s ns s' pr
     (TR: transl_exprlist map al rl nd s = OK ns s')
     (WF: map_valid map s)
     (OK: target_regs_ok map pr al rl)
     (VALID1: regs_valid pr s)
     (VALID2: regs_valid rl s),
   tr_exprlist s'.(st_code) map pr al ns nd rl
   /\ state_incr s s').
Proof.
  apply expr_condexpr_exprlist_ind; intros; try (monadInv TR).
  (* Evar *)
  generalize EQ; unfold find_var. caseEq (map_vars map)!i; intros; inv EQ1.
  exploit add_move_charact; eauto.
  intros [A B].
  split. econstructor; eauto.
    inv OK. left; congruence. right; eauto.
  auto.
  (* Eop *)
  inv OK. 
  exploit (H _ _ _ _ _ _ pr EQ2); eauto with rtlg. intros [A B].
  split. econstructor; eauto.
  eapply instr_at_incr; eauto.
  apply state_incr_trans with s1; eauto with rtlg.
  (* Eload *)
  inv OK.
  exploit (H _ _ _ _ _ _ pr EQ2); eauto with rtlg. intros [A B].
  split. econstructor; eauto.
  eapply instr_at_incr; eauto.
  apply state_incr_trans with s1; eauto with rtlg.
  (* Estore *)
  inv OK.
  assert (state_incr s s1). eauto with rtlg. 
  exploit (H0 _ _ _ _ _ _ (x ++ pr) EQ0).
  eauto with rtlg.
  apply target_reg_ok_append. constructor; auto. 
  intros. exploit alloc_regs_fresh_or_in_map; eauto.
  intros [A|B]. auto. right. apply sym_not_equal.
  eapply valid_fresh_different; eauto with rtlg. 
  red; intros. elim (in_app_or _ _ _ H4); intro. 
  exploit alloc_regs_valid; eauto with rtlg.
  generalize (VALID _ H5). eauto with rtlg. 
  eauto with rtlg. 
  intros [A B].
  exploit (H _ _ _ _ _ _ pr EQ3); eauto with rtlg. 
  intros [C D].
  split. econstructor; eauto.
  apply tr_expr_incr with s2; eauto with rtlg. 
  apply instr_at_incr with s1; eauto with rtlg. 
  eauto with rtlg.
  (* Ecall *)
  inv OK.
  assert (state_incr s0 s3).
    apply state_incr_trans with s1. eauto with rtlg.
    apply state_incr_trans with s2; eauto with rtlg.
  assert (regs_valid (x :: pr) s1).
    apply regs_valid_cons; eauto with rtlg. 
  exploit (H0 _ _ _ _ _ _ (x :: pr) EQ2).
  eauto with rtlg. 
  apply alloc_regs_target_ok with s1 s2; eauto with rtlg.
  eauto with rtlg.
  apply regs_valid_incr with s2; eauto with rtlg.
  intros [A B].
  exploit (H _ _ _ _ _ _ pr EQ4).
  eauto with rtlg.
  eauto with rtlg.
  apply regs_valid_incr with s0; eauto with rtlg.
  apply reg_valid_incr with s1; eauto with rtlg.
  intros [C D].
  split. econstructor; eauto.
  apply tr_exprlist_incr with s4; eauto.
  apply instr_at_incr with s3; eauto with rtlg. 
  eauto with rtlg.
  (* Econdition *)
  inv OK.
  exploit (H1 _ _ _ _ _ _ pr EQ); eauto with rtlg.
  constructor; auto.
  intros [A B].
  exploit (H0 _ _ _ _ _ _ pr EQ1); eauto with rtlg.
  constructor; auto.
  intros [C D].
  exploit (H _ _ _ _ _ _ pr EQ2); eauto with rtlg.
  intros [E F].
  split. econstructor; eauto. 
  apply tr_expr_incr with s1; auto.
  apply tr_expr_incr with s0; eauto with rtlg.
  apply state_incr_trans with s0; auto.
  apply state_incr_trans with s1; auto.
  (* Elet *)
  inv OK.
  exploit (H0 _ _ _ _ _ _ pr EQ1). 
  apply add_letvar_valid; eauto with rtlg. 
  constructor; auto. 
  red; unfold reg_in_map. simpl. intros [[id A] | [B | C]].
  elim H1. left; exists id; auto.
  subst x. apply valid_fresh_absurd with rd s. auto. eauto with rtlg.
  elim H1. right; auto.
  eauto with rtlg. eauto with rtlg. 
  intros [A B].
  exploit (H _ _ _ _ _ _ pr EQ2); eauto with rtlg. intros [C D].
  split. econstructor.
  eapply new_reg_not_in_map; eauto with rtlg. eauto. 
  apply tr_expr_incr with s1; auto.
  eauto with rtlg.
  (* Eletvar *)
  generalize EQ; unfold find_letvar. caseEq (nth_error (map_letvars map) n); intros; inv EQ0.
  monadInv EQ1.
  exploit add_move_charact; eauto.
  intros [A B].
  split. econstructor; eauto. 
    inv OK. left; congruence. right; eauto.
  auto.
  monadInv EQ1.
  (* Ealloc *)
  inv OK. 
  exploit (H _ _ _ _ _ _ pr EQ2); eauto with rtlg.
  intros [A B].
  split. econstructor; eauto.
  eapply instr_at_incr; eauto.
  apply state_incr_trans with s1; eauto with rtlg.

  (* CEtrue *)
  split. constructor. auto with rtlg.
  (* CEfalse *)
  split. constructor. auto with rtlg.
  (* CEcond *)
  exploit (H _ _ _ _ _ _ pr EQ2); eauto with rtlg.
  intros [A B].
  split. econstructor; eauto. 
  apply instr_at_incr with s1; eauto with rtlg. 
  eauto with rtlg.
  (* CEcondition *)
  exploit (H1 _ _ _ _ _ _ pr EQ); eauto with rtlg.
  intros [A B].
  exploit (H0 _ _ _ _ _ _ pr EQ1); eauto with rtlg.
  intros [C D].
  exploit (H _ _ _ _ _ _ pr EQ2); eauto with rtlg.
  intros [E F].
  split. econstructor; eauto. 
  apply tr_condition_incr with s1; eauto with rtlg.
  apply tr_condition_incr with s0; eauto with rtlg.
  eauto with rtlg.

  (* Enil *)
  destruct rl; inv TR. split. constructor. eauto with rtlg.
  (* Econs *)
  destruct rl; simpl in TR; monadInv TR. inv OK. 
  exploit H0; eauto.
  apply regs_valid_cons. apply VALID2. auto with coqlib. auto. 
  red; intros; apply VALID2; auto with coqlib.
  intros [A B]. 
  exploit H; eauto.
  eauto with rtlg.
  eauto with rtlg.
  generalize (VALID2 r (in_eq _ _)). eauto with rtlg.
  intros [C D].
  split. econstructor; eauto.
  apply tr_exprlist_incr with s0; auto.
  apply state_incr_trans with s0; eauto with rtlg.
Qed.

Lemma transl_expr_charact:
  forall a map rd nd s ns s'
     (TR: transl_expr map a rd nd s = OK ns s')
     (WF: map_valid map s)
     (OK: target_reg_ok map nil a rd)
     (VALID2: reg_valid rd s),
   tr_expr s'.(st_code) map nil a ns nd rd
   /\ state_incr s s'.
Proof.
  destruct transl_expr_condexpr_list_charact as [A [B C]].
  intros. eapply A; eauto with rtlg.
Qed.

Lemma transl_condexpr_charact:
  forall a map ntrue nfalse s ns s'
     (TR: transl_condition map a ntrue nfalse s = OK ns s')
     (WF: map_valid map s),
   tr_condition s'.(st_code) map nil a ns ntrue nfalse
   /\ state_incr s s'.
Proof.
  destruct transl_expr_condexpr_list_charact as [A [B C]].
  intros. eapply B; eauto with rtlg.
Qed.

Lemma tr_switch_extends:
  forall s1 s2, state_extends s1 s2 ->
  forall r nexits t ns,
  tr_switch s1.(st_code) r nexits t ns ->
  tr_switch s2.(st_code) r nexits t ns.
Proof.
  induction 2; econstructor; eauto with rtlg.
  eapply instr_at_extends; eauto.
  eapply instr_at_extends; eauto.
Qed.

Lemma tr_stmt_extends:
  forall s1 s2, state_extends s1 s2 ->
  forall map s ns nd nexits nret rret,
  tr_stmt s1.(st_code) map s ns nd nexits nret rret ->
  tr_stmt s2.(st_code) map s ns nd nexits nret rret.
Proof.
  intros s1 s2 EXT.
  destruct (tr_expr_condition_exprlist_extends s1 s2 EXT) as [A [B C]].
  pose (AT := fun pc i => instr_at_extends s1 s2 pc i EXT).
  induction 1; econstructor; eauto.
  eapply tr_move_extends; eauto.
  eapply tr_switch_extends; eauto.
Qed.

Lemma tr_stmt_incr:
  forall s1 s2, state_incr s1 s2 ->
  forall map s ns nd nexits nret rret,
  tr_stmt s1.(st_code) map s ns nd nexits nret rret ->
  tr_stmt s2.(st_code) map s ns nd nexits nret rret.
Proof.
  intros. eapply tr_stmt_extends; eauto with rtlg.
Qed.

Lemma transl_exit_charact:
  forall nexits n s ne s',
  transl_exit nexits n s = OK ne s' ->
  nth_error nexits n = Some ne /\ s' = s.
Proof.
  intros until s'. unfold transl_exit. 
  destruct (nth_error nexits n); intro; monadInv H. auto.
Qed.

Lemma transl_switch_charact:
  forall r nexits t s ns s',
  transl_switch r nexits t s = OK ns s' ->
  tr_switch s'.(st_code) r nexits t ns /\ state_incr s s'.
Proof.
  induction t; simpl; intros.
  exploit transl_exit_charact; eauto. intros [A B].
  split. econstructor; eauto. subst s'; auto with rtlg.

  monadInv H.
  exploit transl_exit_charact; eauto. intros [A B]. subst s1.
  exploit IHt; eauto. intros [C D].
  split. econstructor; eauto with rtlg. 
  apply tr_switch_extends with s0; eauto with rtlg.
  eauto with rtlg.

  monadInv H.
  exploit IHt2; eauto. intros [A B].
  exploit IHt1; eauto. intros [C D].
  split. econstructor.
  apply tr_switch_extends with s1; eauto with rtlg.
  apply tr_switch_extends with s0; eauto with rtlg.
  eauto with rtlg.
  eauto with rtlg.
Qed.
 
Lemma transl_stmt_charact:
  forall map stmt nd nexits nret rret s ns s'
    (TR: transl_stmt map stmt nd nexits nret rret s = OK ns s')
    (WF: map_valid map s)
    (OK: return_reg_ok s map rret),
  tr_stmt s'.(st_code) map stmt ns nd nexits nret rret
  /\ state_incr s s'.
Proof.
  induction stmt; intros; simpl in TR; try (monadInv TR).
  (* Sskip *)
  split. constructor. auto with rtlg.
  (* Sexpr *)
  exploit transl_expr_charact; eauto with rtlg. intros [A B].
  split. econstructor; eauto. eauto with rtlg.
  (* Sassign *)
  exploit add_move_charact; eauto. intros [A B].
  exploit transl_expr_charact; eauto with rtlg. 
    apply map_valid_incr with s; eauto with rtlg. 
  intros [C D].
  generalize EQ. unfold find_var. caseEq (map_vars map)!i; intros; inv EQ2.
  split. econstructor; eauto.
  apply tr_move_extends with s2; eauto with rtlg.
  eauto with rtlg. 
  (* Sseq *)
  exploit IHstmt2; eauto with rtlg. intros [A B].
  exploit IHstmt1; eauto with rtlg. intros [C D].
  split. econstructor; eauto. apply tr_stmt_incr with s0; eauto with rtlg.
  eauto with rtlg.
  (* Sifthenelse *)
  destruct (more_likely c stmt1 stmt2); monadInv TR.
  exploit IHstmt2; eauto. intros [A B].
  exploit IHstmt1; eauto with rtlg. intros [C D].
  exploit transl_condexpr_charact; eauto with rtlg. intros [E F].
  split. econstructor; eauto. 
  apply tr_stmt_incr with s1; eauto with rtlg.
  apply tr_stmt_incr with s0; eauto with rtlg.
  eauto with rtlg.
  exploit IHstmt1; eauto. intros [A B].
  exploit IHstmt2; eauto with rtlg. intros [C D].
  exploit transl_condexpr_charact; eauto with rtlg. intros [E F].
  split. econstructor; eauto. 
  apply tr_stmt_incr with s0; eauto with rtlg.
  apply tr_stmt_incr with s1; eauto with rtlg.
  eauto with rtlg.
  (* Sloop *)
  assert (state_incr s s0).
    eapply reserve_instr_incr; eauto.  
  exploit IHstmt; eauto with rtlg. intros [A B].
  split. econstructor. 
    apply tr_stmt_extends with s1; eauto.
    eapply update_instr_extends; eauto.
  unfold update_instr in EQ0.
  destruct (plt x (st_nextnode s1)); inv EQ0.
  simpl. apply PTree.gss. 
  eapply update_instr_incr; eauto.
  (* Sblock *)
  exploit IHstmt; eauto. intros [A B].
  split. econstructor; eauto. auto.
  (* Sexit *)
  exploit transl_exit_charact; eauto. intros [A B]. subst s'.
  split. econstructor; eauto. auto with rtlg.
  (* Sswitch *)
  generalize TR; clear TR.
  set (t := compile_switch n l).
  caseEq (validate_switch n l t); intro VALID; intros.
  monadInv TR. 
  exploit transl_switch_charact; eauto with rtlg. intros [A B].
  exploit transl_expr_charact; eauto with rtlg. intros [C D].
  split. econstructor; eauto with rtlg. 
  apply tr_switch_extends with s1; eauto with rtlg.
  eauto with rtlg.
  monadInv TR. 
  (* Sreturn *)
  destruct o; destruct rret; inv TR.
  inv OK.  
  exploit transl_expr_charact; eauto with rtlg.
  constructor. auto. simpl; tauto. 
  intros [A B].
  split. econstructor; eauto. auto.
  split. constructor. auto with rtlg.
  (* Stailcall *)
  assert (state_incr s0 s2) by eauto with rtlg.
  destruct transl_expr_condexpr_list_charact as [A [B C]].
  exploit (C _ _ _ _ _ _ _ (x ::nil) EQ2); eauto with rtlg.
  apply alloc_regs_target_ok with s1 s2; eauto with rtlg. 
  apply regs_valid_cons. eauto with rtlg. apply regs_valid_nil.
  apply regs_valid_cons. apply reg_valid_incr with s1; eauto with rtlg.
  apply regs_valid_nil.
  apply regs_valid_incr with s2; eauto with rtlg.
  intros [D E].
  exploit (A _ _ _ _ _ _ _ nil EQ4); eauto with rtlg.
  apply reg_valid_incr with s1; eauto with rtlg. 
  intros [F G].
  split. econstructor; eauto. 
  apply tr_exprlist_incr with s4; eauto.
  apply instr_at_incr with s3; eauto with rtlg.
  eauto with rtlg.  
Qed.

Lemma transl_function_charact:
  forall f tf,
  transl_function f = Errors.OK tf ->
  tr_function f tf.
Proof.
  intros until tf. unfold transl_function. 
  caseEq (transl_fun f init_state). congruence. 
  intros [nentry rparams] sfinal TR E. inv E. 
  monadInv TR.
  exploit add_vars_valid. eexact EQ. apply init_mapping_valid.
  intros [A B]. 
  exploit add_vars_valid. eexact EQ1. auto. 
  intros [C D].
  exploit transl_stmt_charact; eauto with rtlg. 
  unfold ret_reg. destruct (sig_res (CminorSel.fn_sig f)).
  constructor. eauto with rtlg. eauto with rtlg.
  constructor.
  intros [E F].
  eapply tr_function_intro; eauto with rtlg.
  apply instr_at_incr with s2; eauto with rtlg. 
Qed.
