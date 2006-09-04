(** Correctness proof for RTL generation: auxiliary results. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Mem.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import Cminor.
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

Ltac monadSimpl1 :=
  match goal with
  | [ |- (bind ?F ?G ?S = OK ?X ?S') -> _ ] =>
      unfold bind at 1;
      generalize (refl_equal (F S));
      pattern (F S) at -1 in |- *;
      case (F S);
      [ intro; intro; discriminate
      | (let s := fresh "s" in
         (let EQ := fresh "EQ" in
          (intro; intros s EQ;
           try monadSimpl1))) ]
  | [ |- (bind2 ?F ?G ?S = OK ?X ?S') -> _ ] =>
      unfold bind2 at 1; unfold bind at 1;
      generalize (refl_equal (F S));
      pattern (F S) at -1 in |- *;
      case (F S);
      [ intro; intro; discriminate
      | let xy := fresh "xy" in
        (let x := fresh "x" in
         (let y := fresh "y" in
          (let s := fresh "s" in
           (let EQ := fresh "EQ" in
           (intros xy s EQ; destruct xy as [x y]; simpl;
            try monadSimpl1))))) ]
  | [ |- (error _ _ = OK _ _) -> _ ] =>
      unfold error; monadSimpl1
  | [ |- (ret _ _ = OK _ _) -> _ ] =>
      unfold ret; monadSimpl1
  | [ |- (Error _ = OK _ _) -> _ ] =>
      intro; discriminate
  | [ |- (OK _ _ = OK _ _) -> _ ] =>
      let h := fresh "H" in
      (intro h; injection h; intro; intro; clear h)
  end.

Ltac monadSimpl :=
  match goal with
  | [ |- (bind ?F ?G ?S = OK ?X ?S') -> _ ] => monadSimpl1
  | [ |- (bind2 ?F ?G ?S = OK ?X ?S') -> _ ] => monadSimpl1
  | [ |- (error _ _ = OK _ _) -> _ ] => monadSimpl1
  | [ |- (ret _ _ = OK _ _) -> _ ] => monadSimpl1
  | [ |- (Error _ = OK _ _) -> _ ] => monadSimpl1
  | [ |- (OK _ _ = OK _ _) -> _ ] => monadSimpl1
  | [ |- (?F _ _ _ _ _ _ _ = OK _ _) -> _ ] => unfold F; monadSimpl1
  | [ |- (?F _ _ _ _ _ _ = OK _ _) -> _ ] => unfold F; monadSimpl1
  | [ |- (?F _ _ _ _ _ = OK _ _) -> _ ] => unfold F; monadSimpl1
  | [ |- (?F _ _ _ _ = OK _ _) -> _ ] => unfold F; monadSimpl1
  | [ |- (?F _ _ _ = OK _ _) -> _ ] => unfold F; monadSimpl1
  | [ |- (?F _ _ = OK _ _) -> _ ] => unfold F; monadSimpl1
  | [ |- (?F _ = OK _ _) -> _ ] => unfold F; monadSimpl1
  end.

Ltac monadInv H :=
  generalize H; monadSimpl.

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
  s1.(st_code)!n = i -> i <> None -> state_incr s1 s2 ->
  s2.(st_code)!n = i.
Proof.
  intros. inversion H1.
  rewrite <- H. apply H4. elim (st_wf s1 n); intro.
  assumption. elim H0. congruence.
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

Lemma state_incr_trans2:
  forall s1 s2 s3 s4,
  state_incr s1 s2 -> state_incr s2 s3 -> state_incr s3 s4 ->
  state_incr s1 s4.
Proof.
  intros; eauto with rtlg.
Qed.

Lemma state_incr_trans3:
  forall s1 s2 s3 s4 s5,
  state_incr s1 s2 -> state_incr s2 s3 -> state_incr s3 s4 -> state_incr s4 s5 ->
  state_incr s1 s5.
Proof.
  intros; eauto with rtlg.
Qed.

Lemma state_incr_trans4:
  forall s1 s2 s3 s4 s5 s6,
  state_incr s1 s2 -> state_incr s2 s3 -> state_incr s3 s4 ->
  state_incr s4 s5 -> state_incr s5 s6 ->
  state_incr s1 s6.
Proof.
  intros; eauto with rtlg.
Qed.

Lemma state_incr_trans5:
  forall s1 s2 s3 s4 s5 s6 s7,
  state_incr s1 s2 -> state_incr s2 s3 -> state_incr s3 s4 ->
  state_incr s4 s5 -> state_incr s5 s6 -> state_incr s6 s7 ->
  state_incr s1 s7.
Proof.
  intros; eauto 6 with rtlg.
Qed.

Lemma state_incr_trans6:
  forall s1 s2 s3 s4 s5 s6 s7 s8,
  state_incr s1 s2 -> state_incr s2 s3 -> state_incr s3 s4 ->
  state_incr s4 s5 -> state_incr s5 s6 -> state_incr s6 s7 ->
  state_incr s7 s8 -> state_incr s1 s8.
Proof.
  intros; eauto 7 with rtlg.
Qed.

(** The following relation between two states is a weaker version of
  [state_incr].  It permits changing the contents at an already reserved
  graph node, but only from [None] to [Some i]. *)

Definition state_extends (s1 s2: state): Prop :=
  forall pc,
  s1.(st_code)!pc = None \/ s2.(st_code)!pc = s1.(st_code)!pc.

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

(** A crucial property of states is the following: if an RTL execution
  is possible (does not get stuck) in the CFG of a given state [s1]
  the same execution is possible and leads to the same results in
  the CFG of any state [s2] that extends [s1] in the sense of the
  [state_extends] predicate. *)

Section EXEC_INSTR_EXTENDS.

Variable s1 s2: state.
Hypothesis EXT: state_extends s1 s2.

Lemma exec_instr_not_halt:
  forall ge c sp pc rs m t pc' rs' m',
  exec_instr ge c sp pc rs m t pc' rs' m' -> c!pc <> None.
Proof.
  induction 1; rewrite H; discriminate.
Qed.

Lemma exec_instr_in_s2:
  forall ge sp pc rs m t pc' rs' m',
  exec_instr ge s1.(st_code) sp pc rs m t pc' rs' m' ->
  s2.(st_code)!pc = s1.(st_code)!pc.
Proof.
  intros.
  elim (EXT pc); intro.
  elim (exec_instr_not_halt _ _ _ _ _ _ _ _ _ _ H H0).
  assumption.
Qed.

Lemma exec_instr_extends_rec:
  forall ge c sp pc rs m t pc' rs' m',
  exec_instr ge c sp  pc rs m t pc' rs' m' ->
  forall c', c!pc = c'!pc ->
  exec_instr ge c' sp  pc rs m t pc' rs' m'.
Proof.
  induction 1; intros.
  apply exec_Inop. congruence.
  apply exec_Iop with op args. congruence. auto.
  apply exec_Iload with chunk addr args a. congruence. auto. auto.
  apply exec_Istore with chunk addr args src a.
    congruence. auto. auto.
  apply exec_Icall with sig ros args f; auto. congruence.
  apply exec_Ialloc with arg sz; auto. congruence. 
  apply exec_Icond_true with cond args ifnot; auto. congruence.
  apply exec_Icond_false with cond args ifso; auto. congruence.
Qed.

Lemma exec_instr_extends:
  forall ge sp pc rs m t pc' rs' m',
  exec_instr ge s1.(st_code) sp pc rs m t pc' rs' m' ->
  exec_instr ge s2.(st_code) sp pc rs m t pc' rs' m'.
Proof.
  intros.
  apply exec_instr_extends_rec with (st_code s1).
  assumption.
  symmetry. eapply exec_instr_in_s2. eexact H.
Qed.

Lemma exec_instrs_extends_rec:
  forall ge c sp pc rs m t pc' rs' m',
  exec_instrs ge c sp  pc rs m t pc' rs' m' ->
  c = s1.(st_code) ->
  exec_instrs ge s2.(st_code) sp  pc rs m t pc' rs' m'.
Proof.
  induction 1; intros.
  apply exec_refl.
  apply exec_one. apply exec_instr_extends; auto. rewrite <- H0; auto.
  apply exec_trans with t1 pc2 rs2 m2 t2; auto.
Qed.

Lemma exec_instrs_extends:
  forall ge sp pc rs m t pc' rs' m',
  exec_instrs ge s1.(st_code) sp  pc rs m t pc' rs' m' ->
  exec_instrs ge s2.(st_code) sp  pc rs m t pc' rs' m'.
Proof.
  intros.
  apply exec_instrs_extends_rec with (st_code s1); auto.
Qed.

End EXEC_INSTR_EXTENDS.

(** Since [state_incr s1 s2] implies [state_extends s1 s2], we also have
  that any RTL execution possible in the CFG of [s1] is also possible
  in the CFG of [s2], provided that [state_incr s1 s2].
  In particular, any RTL execution that is possible in a partially
  constructed CFG remains possible in the final CFG obtained at
  the end of the translation of the current function. *)

Section EXEC_INSTR_INCR.

Variable s1 s2: state.
Hypothesis INCR: state_incr s1 s2.

Lemma exec_instr_incr:
  forall ge sp pc rs m t pc' rs' m',
  exec_instr ge s1.(st_code) sp  pc rs m t pc' rs' m' ->
  exec_instr ge s2.(st_code) sp  pc rs m t pc' rs' m'.
Proof.
  intros.
  apply exec_instr_extends with s1.
  apply state_incr_extends; auto.
  auto.
Qed.

Lemma exec_instrs_incr:
  forall ge sp pc rs m t pc' rs' m',
  exec_instrs ge s1.(st_code) sp  pc rs m t pc' rs' m' ->
  exec_instrs ge s2.(st_code) sp  pc rs m t pc' rs' m'.
Proof.
  intros.
  apply exec_instrs_extends with s1.
  apply state_incr_extends; auto.
  auto.
Qed.

End EXEC_INSTR_INCR.

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

(** * Well-formedness of compilation environments *)

(** A compilation environment (mapping) is well-formed in a given state if
  the following properties hold:
- The registers associated with Cminor local variables and let-bound variables
  are valid in the state.
- Two distinct Cminor local variables are mapped to distinct pseudo-registers.
- A Cminor local variable and a let-bound variable are mapped to
  distinct pseudo-registers.
*)

Record map_wf (m: mapping) (s: state) : Prop :=
  mk_map_wf {
    map_wf_var_valid:
      (forall id r, m.(map_vars)!id = Some r -> reg_valid r s);
    map_wf_letvar_valid:
      (forall r, In r m.(map_letvars) -> reg_valid r s);
    map_wf_inj:
      (forall id1 id2 r,
         m.(map_vars)!id1 = Some r -> m.(map_vars)!id2 = Some r -> id1 = id2);
     map_wf_disj:
      (forall id r,
         m.(map_vars)!id = Some r -> In r m.(map_letvars) -> False)
  }.
Hint Resolve map_wf_var_valid
             map_wf_letvar_valid
             map_wf_inj map_wf_disj: rtlg.

Lemma map_wf_incr:
  forall s1 s2 m,
  state_incr s1 s2 -> map_wf m s1 -> map_wf m s2.
Proof.
  intros. apply mk_map_wf; intros; eauto with rtlg.
Qed.
Hint Resolve map_wf_incr: rtlg.

(** A register is ``in'' a mapping if it is associated with a Cminor
  local or let-bound variable. *)

Definition reg_in_map (m: mapping) (r: reg) : Prop :=
  (exists id, m.(map_vars)!id = Some r) \/ In r m.(map_letvars).

Lemma reg_in_map_valid:
  forall m s r,
  map_wf m s -> reg_in_map m r -> reg_valid r s.
Proof.
  intros. elim H0.
  intros [id EQ]. eauto with rtlg.
  intro IN. eauto with rtlg.
Qed.
Hint Resolve reg_in_map_valid: rtlg.

(** A register is mutated if it is associated with a Cminor local variable
  that belongs to the given set of mutated variables. *)

Definition mutated_reg (map: mapping) (mut: list ident) (r: reg) : Prop :=
  exists id, In id mut /\ map.(map_vars)!id = Some r.

Lemma mutated_reg_in_map:
  forall map mut r, mutated_reg map mut r -> reg_in_map map r.
Proof.
  intros. elim H. intros id [IN EQ]. 
  left. exists id; auto.
Qed.
Hint Resolve mutated_reg_in_map: rtlg.

(** * Properties of basic operations over the state *)

(** Properties of [add_instr]. *)

Lemma add_instr_incr:
  forall s1 s2 i n,
  add_instr i s1 = OK n s2 -> state_incr s1 s2.
Proof.
  intros until n; monadSimpl.
  subst s2; apply state_incr_intro; simpl.
  apply Ple_succ.
  apply Ple_refl.
  intros. apply PTree.gso; apply Plt_ne; auto.
Qed.
Hint Resolve add_instr_incr: rtlg.

Lemma add_instr_at:
  forall s1 s2 i n,
  add_instr i s1 = OK n s2 -> s2.(st_code)!n = Some i.
Proof.
  intros until n; monadSimpl.
  subst n; subst s2; simpl. apply PTree.gss.
Qed.
Hint Resolve add_instr_at.

(** Properties of [reserve_instr] and [update_instr]. *)

Lemma reserve_instr_incr:
  forall s1 s2 n,
  reserve_instr s1 = OK n s2 -> state_incr s1 s2.
Proof.
  intros until n; monadSimpl. subst s2.
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
  monadInv H.
  generalize H1; unfold update_instr.
  case (plt n (st_nextnode s3)); intro.
  monadSimpl. inversion H0.
  subst s4; apply state_incr_intro; simpl.
  apply Plt_Ple. apply Plt_Ple_trans with (st_nextnode s2).
  subst s2; simpl; apply Plt_succ. assumption.
  rewrite <- H3 in H7; simpl in H7. assumption.
  intros. rewrite PTree.gso.
  rewrite <- H3 in H8; simpl in H8. apply H8.
  apply Plt_trans_succ; assumption.
  subst n; apply Plt_ne; assumption.
  intros; discriminate.
Qed.

Lemma update_instr_extends:
  forall s1 s2 s3 s4 i n t,
  reserve_instr s1 = OK n s2 ->
  state_incr s2 s3 ->
  update_instr n i s3 = OK t s4 ->
  state_extends s3 s4.
Proof.
  intros.
  monadInv H.
  red; intros. 
  case (peq pc n); intro.
  subst pc. left. inversion H0. rewrite H6. 
  rewrite <- H3; simpl.  
  elim (s1.(st_wf) n); intro.
  rewrite <- H4 in H9. elim (Plt_strict _ H9).
  auto.
  rewrite <- H4. rewrite <- H3; simpl. apply Plt_succ.
  generalize H1; unfold update_instr.
  case (plt n s3.(st_nextnode)); intro; monadSimpl.
  right; rewrite <- H5; simpl. apply PTree.gso; auto.
Qed.

(** Properties of [new_reg]. *)

Lemma new_reg_incr:
  forall s1 s2 r, new_reg s1 = OK r s2 -> state_incr s1 s2.
Proof.
  intros until r. monadSimpl.
  subst s2; apply state_incr_intro; simpl.
  apply Ple_refl. apply Ple_succ. auto.
Qed.
Hint Resolve new_reg_incr: rtlg.

Lemma new_reg_valid:
  forall s1 s2 r,
  new_reg s1 = OK r s2 -> reg_valid r s2.
Proof.
  intros until r. monadSimpl. subst s2; subst r.
  unfold reg_valid; unfold reg_valid; simpl.
  apply Plt_succ.
Qed.
Hint Resolve new_reg_valid: rtlg.

Lemma new_reg_fresh:
  forall s1 s2 r,
  new_reg s1 = OK r s2 -> reg_fresh r s1.
Proof.
  intros until r. monadSimpl. subst s2; subst r.
  unfold reg_fresh; simpl.
  exact (Plt_strict _).
Qed.
Hint Resolve new_reg_fresh: rtlg.

Lemma new_reg_not_in_map:
  forall s1 s2 m r,
  new_reg s1 = OK r s2 -> map_wf m s1 -> ~(reg_in_map m r).
Proof.
  unfold not; intros; eauto with rtlg.
Qed. 
Hint Resolve new_reg_not_in_map: rtlg.

Lemma new_reg_not_mutated:
  forall s1 s2 m mut r,
  new_reg s1 = OK r s2 -> map_wf m s1 -> ~(mutated_reg m mut r).
Proof.
  unfold not; intros. 
  generalize (mutated_reg_in_map _ _ _ H1); intro.
  exact (new_reg_not_in_map _ _ _ _ H H0 H2).
Qed.
Hint Resolve new_reg_not_mutated: rtlg.

(** * Properties of operations over compilation environments *)

Lemma init_mapping_wf:
  forall s, map_wf init_mapping s.
Proof.
  intro. unfold init_mapping; apply mk_map_wf; simpl; intros.
  rewrite PTree.gempty in H; discriminate.
  contradiction.
  rewrite PTree.gempty in H; discriminate.
  tauto.
Qed.  

(** Properties of [find_var]. *)

Lemma find_var_incr:
  forall s1 s2 map name r,
  find_var map name s1 = OK r s2 -> state_incr s1 s2.
Proof.
  intros until r. unfold find_var.
  case (map_vars map)!name.
  intro; monadSimpl. subst s2; auto with rtlg.
  monadSimpl.
Qed.
Hint Resolve find_var_incr: rtlg.

Lemma find_var_in_map:
  forall s1 s2 map name r,
  find_var map name s1 = OK r s2 -> map_wf map s1 -> reg_in_map map r.
Proof.
  intros until r. unfold find_var; caseEq (map.(map_vars)!name).
  intros r0 eq. monadSimpl; intros. subst r0. 
  left. exists name; auto.
  intro; monadSimpl.
Qed.
Hint Resolve find_var_in_map: rtlg.

Lemma find_var_valid:
  forall s1 s2 map name r,
  find_var map name s1 = OK r s2 -> map_wf map s1 -> reg_valid r s1.
Proof.
  eauto with rtlg.
Qed.
Hint Resolve find_var_valid: rtlg.

Lemma find_var_not_mutated:
  forall s1 s2 map name r mut,
  find_var map name s1 = OK r s2 ->
  map_wf map s1 ->
  ~(In name mut) ->
  ~(mutated_reg map mut r).
Proof.
  intros until mut. unfold find_var; caseEq (map.(map_vars)!name).
  intros r0 EQ. monadSimpl; intros; subst r0.
  red; unfold mutated_reg; intros [id [IN EQ2]]. 
  assert (name = id). eauto with rtlg.
  subst id. contradiction.
  intro; monadSimpl.
Qed.
Hint Resolve find_var_not_mutated: rtlg.

(** Properties of [find_letvar]. *)

Lemma find_letvar_incr:
  forall s1 s2 map idx r,
  find_letvar map idx s1 = OK r s2 -> state_incr s1 s2.
Proof.
  intros until r. unfold find_letvar.
  case (nth_error (map_letvars map) idx).
  intro; monadSimpl. subst s2; auto with rtlg.
  monadSimpl.
Qed.
Hint Resolve find_letvar_incr: rtlg.

Lemma find_letvar_in_map:
  forall s1 s2 map idx r,
  find_letvar map idx s1 = OK r s2 -> map_wf map s1 -> reg_in_map map r.
Proof.
  intros until r. unfold find_letvar.
  caseEq (nth_error (map_letvars map) idx).
  intros r0 EQ; monadSimpl. intros. right. 
  subst r0; apply nth_error_in with idx; auto.
  intro; monadSimpl.
Qed.
Hint Resolve find_letvar_in_map: rtlg.

Lemma find_letvar_valid:
  forall s1 s2 map idx r,
  find_letvar map idx s1 = OK r s2 -> map_wf map s1 -> reg_valid r s1.
Proof.
  eauto with rtlg.
Qed.
Hint Resolve find_letvar_valid: rtlg.

Lemma find_letvar_not_mutated:
  forall s1 s2 map idx mut r,
  find_letvar map idx s1 = OK r s2 ->
  map_wf map s1 ->
  ~(mutated_reg map mut r).
Proof.
  intros until r. unfold find_letvar.
  caseEq (nth_error (map_letvars map) idx).
  intros r' NTH. monadSimpl. unfold not; unfold mutated_reg.
  intros MWF (id, (IN, MV)). subst r'. eauto with rtlg coqlib.
  intro; monadSimpl.
Qed.
Hint Resolve find_letvar_not_mutated: rtlg.

(** Properties of [add_var]. *)

Lemma add_var_valid:
  forall s1 s2 map1 map2 name r, 
  add_var map1 name s1 = OK (r, map2) s2 -> reg_valid r s2.
Proof.
  intros until r. monadSimpl. intro. subst r0; subst s.
  eauto with rtlg.
Qed.

Lemma add_var_incr:
  forall s1 s2 map name rm, 
  add_var map name s1 = OK rm s2 -> state_incr s1 s2.
Proof.
  intros until rm; monadSimpl. subst s2. eauto with rtlg.
Qed.
Hint Resolve add_var_incr: rtlg.

Lemma add_var_wf:
  forall s1 s2 map name r map',
  add_var map name s1 = OK (r,map') s2 -> map_wf map s1 -> map_wf map' s2.
Proof.
  intros until map'; monadSimpl; intros.
  subst r0; subst s; subst map'; apply mk_map_wf; simpl.

  intros id r'. rewrite PTree.gsspec. 
  case (peq id name); intros.
  injection H; intros; subst r'. eauto with rtlg.
  eauto with rtlg.
  eauto with rtlg.

  intros id1 id2 r'.
  repeat (rewrite PTree.gsspec). 
  case (peq id1 name); case (peq id2 name); intros.
  congruence.
  rewrite <- H in H0. byContradiction; eauto with rtlg.
  rewrite <- H0 in H. byContradiction; eauto with rtlg.
  eauto with rtlg.

  intros id r'. case (peq id name); intro.
  subst id. rewrite PTree.gss. intro E; injection E; intro; subst r'.
  intro; eauto with rtlg.

  rewrite PTree.gso; auto. eauto with rtlg.
Qed.
Hint Resolve add_var_wf: rtlg.

Lemma add_var_find:
  forall s1 s2 map name r map',
  add_var map name s1 = OK (r,map') s2 -> map'.(map_vars)!name = Some r.
Proof.
  intros until map'.
  monadSimpl.
  intro; subst r0.
  subst map'; simpl in |- *.
  apply PTree.gss.
Qed.

Lemma add_vars_incr:
  forall names s1 s2 map r,
  add_vars map names s1 = OK r s2 -> state_incr s1 s2.
Proof.
  induction names; simpl. 
  intros until r; monadSimpl; intros. subst s2; eauto with rtlg.
  intros until r; monadSimpl; intros.
  subst s0; eauto with rtlg.
Qed.

Lemma add_vars_valid:
  forall namel s1 s2 map1 map2 rl, 
  add_vars map1 namel s1 = OK (rl, map2) s2 ->
  forall r, In r rl -> reg_valid r s2.
Proof.
  induction namel; simpl; intros.
  monadInv H. intro. subst rl. elim H0. 
  monadInv H. intro EQ1. subst rl; subst s0; subst y0. elim H0.
  intro; subst r. eapply add_var_valid. eexact EQ0. 
  intro. apply reg_valid_incr with s. eauto with rtlg.
  eauto.
Qed.

Lemma add_vars_wf:
  forall names s1 s2 map map' rl,
  add_vars map names s1 = OK (rl,map') s2 ->
  map_wf map s1 -> map_wf map' s2.
Proof.
  induction names; simpl.
  intros until rl; monadSimpl; intros.
  subst s2; subst map'; assumption.
  intros until rl; monadSimpl; intros. subst y0; subst s0.
  eapply add_var_wf. eexact EQ0.
  eapply IHnames. eexact EQ. auto.
Qed.
Hint Resolve add_vars_wf: rtlg.

Lemma add_var_letenv:
  forall map1 i s1 r map2 s2,
  add_var map1 i s1 = OK (r, map2) s2 ->
  map2.(map_letvars) = map1.(map_letvars).
Proof.
  intros until s2. monadSimpl. intro. subst map2; reflexivity.
Qed.

(** Properties of [add_letvar]. *)

Lemma add_letvar_wf:
  forall map s r,
  map_wf map s ->
  reg_valid r s ->
  ~(reg_in_map map r) ->
  map_wf (add_letvar map r) s.
Proof.
  intros. unfold add_letvar; apply mk_map_wf; simpl.
  exact (map_wf_var_valid map s H).
  intros r' [EQ| IN].
    subst r'; assumption.
    eapply map_wf_letvar_valid; eauto.
  exact (map_wf_inj map s H).
  intros. elim H3; intro.
   subst r0. apply H1. left. exists id; auto.
   eapply map_wf_disj; eauto.
Qed.

(** * Properties of [alloc_reg] and [alloc_regs] *)

Lemma alloc_reg_incr:
  forall a s1 s2 map mut r,
  alloc_reg map mut a s1 = OK r s2 -> state_incr s1 s2.
Proof.
  intros until r.  unfold alloc_reg.
  case a; eauto with rtlg.
  intro i; case (In_dec ident_eq i mut); eauto with rtlg.
Qed.
Hint Resolve alloc_reg_incr: rtlg.

Lemma alloc_reg_valid:
  forall a s1 s2 map mut r,
  map_wf map s1 ->
  alloc_reg map mut a s1 = OK r s2 -> reg_valid r s2.
Proof.
  intros until r.  unfold alloc_reg.
  case a; eauto with rtlg.
  intro i; case (In_dec ident_eq i mut); eauto with rtlg.
Qed.
Hint Resolve alloc_reg_valid: rtlg.

Lemma alloc_reg_fresh_or_in_map:
  forall map mut a s r s',
  map_wf map s ->
  alloc_reg map mut a s = OK r s' ->
  reg_in_map map r \/ reg_fresh r s.
Proof.
  intros until s'. unfold alloc_reg.
  destruct a; try (right; eauto with rtlg; fail).
  case (In_dec ident_eq i mut); intros.
  right; eauto with rtlg.
  left; eauto with rtlg.
  intros; left; eauto with rtlg.
Qed.

Lemma add_vars_letenv:
  forall il map1 s1 rl map2 s2,
  add_vars map1 il s1 = OK (rl, map2) s2 ->
  map2.(map_letvars) = map1.(map_letvars).
Proof.
  induction il; simpl; intros.
   monadInv H. intro. subst map2; reflexivity.
   monadInv H. intro EQ1. transitivity (map_letvars y).
   subst y0. eapply add_var_letenv; eauto.
   eauto.
Qed.

(** A register is an adequate target for holding the value of an
  expression if
- either the register is associated with a Cminor let-bound variable
  or a Cminor local variable that is not modified;
- or the register is valid and not associated with any Cminor variable. *)

Inductive target_reg_ok: state -> mapping -> list ident -> expr -> reg -> Prop :=
  | target_reg_immut_var:
      forall s map mut id r,
      ~(In id mut) -> map.(map_vars)!id = Some r ->
      target_reg_ok s map mut (Evar id) r
  | target_reg_letvar:
      forall s map mut idx r,
      nth_error map.(map_letvars) idx = Some r ->
      target_reg_ok s map mut (Eletvar idx) r
  | target_reg_other:
      forall s map mut a r,
      ~(reg_in_map map r) ->
      reg_valid r s ->
      target_reg_ok s map mut a r.

Lemma target_reg_ok_incr:
  forall s1 s2 map mut e r,
  state_incr s1 s2 ->
  target_reg_ok s1 map mut e r ->
  target_reg_ok s2 map mut e r.
Proof.
  intros. inversion H0. 
  apply target_reg_immut_var; auto.
  apply target_reg_letvar; auto.
  apply target_reg_other; eauto with rtlg.
Qed.
Hint Resolve target_reg_ok_incr: rtlg.

Lemma target_reg_valid:
  forall s map mut e r,
  map_wf map s ->
  target_reg_ok s map mut e r ->
  reg_valid r s.
Proof.
  intros. inversion H0; eauto with rtlg coqlib.
Qed.
Hint Resolve target_reg_valid: rtlg.

Lemma target_reg_not_mutated:
  forall s map mut e r,
  map_wf map s ->
  target_reg_ok s map mut e r ->
  ~(mutated_reg map mut r).
Proof.
  unfold not; unfold mutated_reg; intros until r.
  intros MWF TRG [id [IN MV]].
  inversion TRG.
  assert (id = id0); eauto with rtlg. subst id0. contradiction.
  assert (In r (map_letvars map)). eauto with coqlib. eauto with rtlg.
  apply H. red. left; exists id; assumption.
Qed.
Hint Resolve target_reg_not_mutated: rtlg.

Lemma alloc_reg_target_ok:
  forall a s1 s2 map mut r,
  map_wf map s1 ->
  alloc_reg map mut a s1 = OK r s2 ->
  target_reg_ok s2 map mut a r.
Proof.
  intros until r; intro MWF. unfold alloc_reg.
  case a; intros; try (eapply target_reg_other; eauto with rtlg; fail).
  generalize H; case (In_dec ident_eq i mut); intros.
  apply target_reg_other; eauto with rtlg.
  apply target_reg_immut_var; auto.
  generalize H0; unfold find_var. 
  case (map_vars map)!i.
  intro. monadSimpl. congruence.
  monadSimpl.
  apply target_reg_letvar. 
  generalize H. unfold find_letvar. 
  case (nth_error (map_letvars map) n).
  intro; monadSimpl; congruence.
  monadSimpl.
Qed.
Hint Resolve alloc_reg_target_ok: rtlg.

Lemma alloc_regs_incr:
  forall al s1 s2 map mut rl,
  alloc_regs map mut al s1 = OK rl s2 -> state_incr s1 s2.
Proof.
  induction al; simpl; intros.
  monadInv H. subst s2. eauto with rtlg.
  monadInv H. subst s2. eauto with rtlg.
Qed.
Hint Resolve alloc_regs_incr: rtlg.

Lemma alloc_regs_valid:
  forall al s1 s2 map mut rl,
  map_wf map s1 ->
  alloc_regs map mut al s1 = OK rl s2 ->
  forall r, In r rl -> reg_valid r s2.
Proof.
  induction al; simpl; intros.
   monadInv H0. subst rl. elim H1.
   monadInv H0. subst rl; subst s0.
   elim H1; intro.
     subst r0. eauto with rtlg.
     eauto with rtlg.
Qed.
Hint Resolve alloc_regs_valid: rtlg.

Lemma alloc_regs_fresh_or_in_map:
  forall map mut al s rl s',
  map_wf map s ->
  alloc_regs map mut al s = OK rl s' ->
  forall r, In r rl -> reg_in_map map r \/ reg_fresh r s.
Proof.
  induction al; simpl; intros.
  monadInv H0. subst rl. elim H1.
  monadInv H0. subst rl. elim (in_inv H1); intro.
  subst r. 
  assert (MWF: map_wf map s0). eauto with rtlg.
  elim (alloc_reg_fresh_or_in_map map mut e s0 r0 s1 MWF EQ0); intro.
  left; assumption. right; eauto with rtlg.
  eauto with rtlg.
Qed.

Inductive target_regs_ok: state -> mapping -> list ident -> exprlist -> list reg -> Prop :=
  | target_regs_nil:
      forall s map mut,
      target_regs_ok s map mut Enil nil
  | target_regs_cons:
      forall s map mut a r al rl,
      reg_in_map map r \/ ~(In r rl) ->
      target_reg_ok s map mut a r ->
      target_regs_ok s map mut al rl ->
      target_regs_ok s map mut (Econs a al) (r :: rl).

Lemma target_regs_ok_incr:
  forall s1 map mut al rl,
  target_regs_ok s1 map mut al rl ->
  forall s2,
  state_incr s1 s2 ->
  target_regs_ok s2 map mut al rl.
Proof.
  induction 1; intros.
  apply target_regs_nil. 
  apply target_regs_cons; eauto with rtlg. 
Qed.
Hint Resolve target_regs_ok_incr: rtlg.

Lemma target_regs_valid:
  forall s map mut al rl,
  target_regs_ok s map mut al rl ->
  map_wf map s ->
  forall r, In r rl -> reg_valid r s.
Proof.
  induction 1; simpl; intros.
  contradiction.
  elim H3; intro.
  subst r0. eauto with rtlg.
  auto.
Qed.
Hint Resolve target_regs_valid: rtlg.

Lemma target_regs_not_mutated:
  forall s map mut el rl,
  target_regs_ok s map mut el rl ->
  map_wf map s ->
  forall r, In r rl -> ~(mutated_reg map mut r).
Proof.
  induction 1; simpl; intros.
  contradiction.
  elim H3; intro. subst r0. eauto with rtlg.
  auto. 
Qed. 
Hint Resolve target_regs_not_mutated: rtlg.

Lemma alloc_regs_target_ok:
  forall al s1 s2 map mut rl,
  map_wf map s1 ->
  alloc_regs map mut al s1 = OK rl s2 ->
  target_regs_ok s2 map mut al rl.
Proof.
  induction al; simpl; intros.
  monadInv H0. subst rl; apply target_regs_nil.
  monadInv H0. subst s0; subst rl. 
  apply target_regs_cons; eauto 6 with rtlg.
  assert (MWF: map_wf map s). eauto with rtlg.
  elim (alloc_reg_fresh_or_in_map map mut e s r s2 MWF EQ0); intro.
  left; assumption. right; red; intro; eauto with rtlg.
Qed.
Hint Resolve alloc_regs_target_ok: rtlg.

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
  forall s1 s2 map or,
  state_incr s1 s2 ->
  return_reg_ok s1 map or ->
  return_reg_ok s2 map or.
Proof.
  intros. inversion H0; constructor. 
  assumption. eauto with rtlg.
Qed.
Hint Resolve return_reg_ok_incr: rtlg.

Lemma new_reg_return_ok:
  forall s1 r s2 map sig,
  new_reg s1 = OK r s2 ->
  map_wf map s1 ->
  return_reg_ok s2 map (ret_reg sig r).
Proof.
  intros. unfold ret_reg. destruct (sig_res sig); constructor.
  eauto with rtlg. eauto with rtlg.
Qed.

(** * Correspondence between Cminor environments and RTL register sets *)

(** An RTL register environment matches a Cminor local environment and
  let-environment if the value of every local or let-bound variable in
  the Cminor environments is identical to the value of the
  corresponding pseudo-register in the RTL register environment. *)

Record match_env
      (map: mapping) (e: Cminor.env) (le: Cminor.letenv) (rs: regset) : Prop :=
  mk_match_env {
    me_vars:
      (forall id v,
         e!id = Some v -> exists r, map.(map_vars)!id = Some r /\ rs#r = v);
    me_letvars:
      rs##(map.(map_letvars)) = le
  }.

Lemma match_env_find_reg:
  forall map id s1 s2 r e le rs v,
  find_var map id s1 = OK r s2 ->
  match_env map e le rs ->
  e!id = Some v ->
  rs#r = v.
Proof.
  intros until v.
  unfold find_var. caseEq (map.(map_vars)!id).
  intros r' EQ. monadSimpl. subst r'. intros.
  generalize (me_vars _ _ _ _ H _ _ H1). intros [r' [EQ' RS]].
  rewrite EQ' in EQ; injection EQ; intro; subst r'.
  assumption.
  intro; monadSimpl.
Qed.
Hint Resolve match_env_find_reg: rtlg.

Lemma match_env_invariant:
  forall map e le rs rs',
  match_env map e le rs ->
  (forall r, (reg_in_map map r) -> rs'#r = rs#r) ->
  match_env map e le rs'.
Proof.
  intros. apply mk_match_env.
  intros id v' E.
  generalize (me_vars _ _ _ _ H _ _ E). intros (r', (M, R)).
  exists r'. split. auto. rewrite <- R. apply H0. 
  left. exists id. auto. 
  transitivity rs ## (map_letvars map).
  apply list_map_exten. intros. 
  symmetry. apply H0. right. auto.
  exact (me_letvars _ _ _ _ H).
Qed.

(** Matching between environments is preserved when an unmapped register
  (not corresponding to any Cminor variable) is assigned in the RTL
  execution. *)

Lemma match_env_update_temp:
  forall map e le rs r v,
  match_env map e le rs ->
  ~(reg_in_map map r) ->
  match_env map e le (rs#r <- v).
Proof.
  intros. apply match_env_invariant with rs; auto.
  intros. case (Reg.eq r r0); intro. 
  subst r0; contradiction.
  apply Regmap.gso; auto.
Qed.
Hint Resolve match_env_update_temp: rtlg.

(** Matching between environments is preserved by simultaneous
  assignment to a Cminor local variable (in the Cminor environments)
  and to the corresponding RTL pseudo-register (in the RTL register
  environment). *)

Lemma match_env_update_var:
  forall map e le rs rs' id r v s s',
  map_wf map s ->
  find_var map id s = OK r s' ->
  match_env map e le rs ->
  rs'#r = v ->
  (forall x, x <> r -> rs'#x = rs#x) ->
  match_env map (PTree.set id v e) le rs'.
Proof.
  intros until s'; intro MWF.
  unfold find_var in |- *. caseEq (map_vars map)!id.
  intros. monadInv H0. subst r0. apply mk_match_env.
  intros id' v' E. case (peq id' id); intros.
  subst id'. rewrite PTree.gss in E. injection E; intro; subst v'.
  exists r. split. auto. auto.
  rewrite PTree.gso in E; auto.
  elim (me_vars _ _ _ _ H1 _ _ E). intros r' (M, R).
  exists r'. split. assumption. rewrite <- R; apply H3; auto.
  red in |- *; intro. subst r'. apply n. eauto with rtlg.
  transitivity rs ## (map_letvars map).
  apply list_map_exten. intros. symmetry. apply H3.
  red in |- *; intro. subst x. eauto with rtlg.
  exact (me_letvars _ _ _ _ H1).
  intro; monadSimpl.
Qed.

Lemma match_env_letvar:
  forall map e le rs r v,
  match_env map e le rs ->
  rs#r = v ->
  match_env (add_letvar map r) e (v :: le) rs.
Proof.
  intros.  unfold add_letvar in |- *; apply mk_match_env; simpl in |- *.
  exact (me_vars _ _ _ _ H).
  rewrite H0. rewrite (me_letvars _ _ _ _ H). auto.
Qed.

Lemma match_env_exten:
  forall map e le rs1 rs2,
    (forall r, rs2#r = rs1#r) ->
    match_env map e le rs1 ->
    match_env map e le rs2.
Proof.
  intros. apply mk_match_env.
  intros. generalize (me_vars _ _ _ _ H0 _ _ H1). intros (r, (M1, M2)).
  exists r. split. assumption. subst v. apply H. 
  transitivity rs1 ## (map_letvars map).
  apply list_map_exten. intros. symmetry  in |- *. apply H. 
  exact (me_letvars _ _ _ _ H0).
Qed.

Lemma match_env_empty:
  forall map,
  map.(map_letvars) = nil ->
  match_env map (PTree.empty val) nil (Regmap.init Vundef).
Proof.
  intros. apply mk_match_env.
  intros. rewrite PTree.gempty in H0. discriminate.
  rewrite H. reflexivity.
Qed.

(** The assignment of function arguments to local variables (on the Cminor
  side) and pseudo-registers (on the RTL side) preserves matching
  between environments. *)

Lemma match_set_params_init_regs:
  forall il rl s1 map2 s2 vl,
  add_vars init_mapping il s1 = OK (rl, map2) s2 ->
  match_env map2 (set_params vl il) nil (init_regs vl rl)
  /\ (forall r, reg_fresh r s2 -> (init_regs vl rl)#r = Vundef).
Proof.
  induction il; simpl in |- *; intros.

  monadInv H. intro; subst rl; simpl in |- *.
  split. apply match_env_empty. subst map2; auto.
  intros. apply Regmap.gi. 

  monadInv H. intro EQ1; subst s0; subst y0; subst rl. clear H.
  monadInv EQ0. intro EQ2. subst x0; subst s0. simpl.

  assert (LV : map_letvars map2 = nil).
  transitivity (map_letvars y).
  eapply add_var_letenv; eauto. 
  transitivity (map_letvars init_mapping).
  eapply add_vars_letenv; eauto.
  reflexivity.

  destruct vl.
  (* vl = nil *)
  generalize (IHil _ _ _ _ nil EQ). intros [ME UNDEF]. split.
  constructor. intros id v. subst map2. simpl. 
  repeat rewrite PTree.gsspec; case (peq id a); intros.
  exists r; split. auto. rewrite Regmap.gi. congruence.
  destruct (me_vars _ _ _ _ ME id v H) as (r', (MV, IR)).
  exists r'. split. auto. 
  replace (init_regs nil x) with (Regmap.init Vundef) in IR. auto.
  destruct x; reflexivity.
  rewrite LV; reflexivity.
  intros. apply Regmap.gi.
  (* vl = v :: vl *)
  generalize (IHil _ _ _ _ vl EQ). intros [ME UNDEF]. split.
  constructor. intros id v1. subst map2. simpl. 
  repeat rewrite PTree.gsspec; case (peq id a); intros.
  exists r; split. auto. rewrite Regmap.gss. congruence.
  destruct (me_vars _ _ _ _ ME id v1 H) as (r', (MV, IR)).
  exists r'. split. auto. rewrite Regmap.gso. auto.
  apply valid_fresh_different with s.
  assert (MWF : map_wf y s).
  eapply add_vars_wf; eauto. apply init_mapping_wf.
  eauto with rtlg. eauto with rtlg.
  rewrite LV; reflexivity.
  intros. rewrite Regmap.gso. apply UNDEF. eauto with rtlg. 
  apply sym_not_equal. eauto with rtlg.
Qed.

Lemma match_set_locals:
  forall map1 s1,
  map_wf map1 s1 ->
  forall il rl map2 s2 e le rs,
  match_env map1 e le rs ->
  (forall r, reg_fresh r s1 -> rs#r = Vundef) ->
  add_vars map1 il s1 = OK (rl, map2) s2 ->
  match_env map2 (set_locals il e) le rs.
Proof.
  induction il; simpl in *; intros.

  monadInv H2. intros; subst map2; auto.

  monadInv H2. intros. subst s0; subst y0.
  assert (match_env y (set_locals il e) le rs).
    eapply IHil; eauto. 
  monadInv EQ0. intro. subst s0; subst x0.  rewrite <- H7.
  constructor.
  intros id v. simpl. repeat rewrite PTree.gsspec. 
  case (peq id a); intros.
  exists r. split. auto. injection H5; intro; subst v.
  apply H1. apply reg_fresh_decr with s. 
  eapply add_vars_incr; eauto.
  eauto with rtlg.
  eapply me_vars; eauto. 
  simpl. eapply me_letvars; eauto.
Qed.

Lemma match_init_env_init_reg:
  forall params s0 rparams map1 s1 vars rvars map2 s2 vparams,
  add_vars init_mapping params s0 = OK (rparams, map1) s1 ->
  add_vars map1 vars s1 = OK (rvars, map2) s2 ->
  match_env map2 (set_locals vars (set_params vparams params))
            nil (init_regs vparams rparams).
Proof.
  intros. 
  generalize (match_set_params_init_regs _ _ _ _ _ vparams H).
  intros [A B].
  eapply match_set_locals; eauto.
  eapply add_vars_wf; eauto. apply init_mapping_wf.
Qed.

(** * Monotonicity properties of the state for the translation functions *)

(** We show that the translation functions modify the state monotonically
  (in the sense of the [state_incr] relation). *)

Lemma add_move_incr:
  forall r1 r2 nd s ns s',
  add_move r1 r2 nd s = OK ns s' ->
  state_incr s s'.
Proof.
  intros until s'. unfold add_move. 
  case (Reg.eq r1 r2); intro.
  monadSimpl. subst s'; auto with rtlg.
  intro; eauto with rtlg.
Qed.
Hint Resolve add_move_incr: rtlg.

Scheme expr_ind3 := Induction for expr Sort Prop
  with condexpr_ind3 := Induction for condexpr Sort Prop
  with exprlist_ind3 := Induction for exprlist Sort Prop.

Lemma expr_condexpr_exprlist_ind:
forall (P : expr -> Prop) (P0 : condexpr -> Prop)
         (P1 : exprlist -> Prop),
       (forall i : ident, P (Evar i)) ->
       (forall (i : ident) (e : expr), P e -> P (Eassign i e)) ->
       (forall (o : operation) (e : exprlist), P1 e -> P (Eop o e)) ->
       (forall (m : memory_chunk) (a : addressing) (e : exprlist),
        P1 e -> P (Eload m a e)) ->
       (forall (m : memory_chunk) (a : addressing) (e : exprlist),
        P1 e -> forall e0 : expr, P e0 -> P (Estore m a e e0)) ->
       (forall (s : signature) (e : expr),
        P e -> forall e0 : exprlist, P1 e0 -> P (Ecall s e e0)) ->
       (forall c : condexpr,
        P0 c ->
        forall e : expr,
        P e -> forall e0 : expr, P e0 -> P (Econdition c e e0)) ->
       (forall e : expr, P e -> forall e0 : expr, P e0 -> P (Elet e e0)) ->
       (forall n : nat, P (Eletvar n)) ->
       (forall e : expr, P e -> P (Ealloc e)) ->
       P0 CEtrue ->
       P0 CEfalse ->
       (forall (c : condition) (e : exprlist), P1 e -> P0 (CEcond c e)) ->
       (forall c : condexpr,
        P0 c ->
        forall c0 : condexpr,
        P0 c0 -> forall c1 : condexpr, P0 c1 -> P0 (CEcondition c c0 c1)) ->
       P1 Enil ->
       (forall e : expr,
        P e -> forall e0 : exprlist, P1 e0 -> P1 (Econs e e0)) ->
       (forall e : expr, P e) /\
       (forall ce : condexpr, P0 ce) /\
       (forall el : exprlist, P1 el).
Proof.
  intros. split. apply (expr_ind3 P P0 P1); assumption.
  split. apply (condexpr_ind3 P P0 P1); assumption.
  apply (exprlist_ind3 P P0 P1); assumption.
Qed.

Definition transl_expr_incr_pred (a: expr) : Prop :=
  forall map mut rd nd s ns s',
  transl_expr map mut a rd nd s = OK ns s' -> state_incr s s'.
Definition transl_condition_incr_pred (c: condexpr) : Prop :=
  forall map mut ntrue nfalse s ns s',
  transl_condition map mut c ntrue nfalse s = OK ns s' -> state_incr s s'.
Definition transl_exprlist_incr_pred (al: exprlist) : Prop :=
  forall map mut rl nd s ns s',
  transl_exprlist map mut al rl nd s = OK ns s' -> state_incr s s'.

Lemma transl_expr_condition_exprlist_incr:
  (forall a, transl_expr_incr_pred a) /\
  (forall c, transl_condition_incr_pred c) /\
  (forall al, transl_exprlist_incr_pred al).
Proof.
  apply expr_condexpr_exprlist_ind;
  unfold transl_expr_incr_pred,
         transl_condition_incr_pred,
         transl_exprlist_incr_pred;
  simpl; intros; 
  try (monadInv H); try (monadInv H0); 
  try (monadInv H1); try (monadInv H2);
  eauto 6 with rtlg.

  intro EQ2. 
  apply state_incr_trans3 with s0 s1 s2; eauto with rtlg. 

  intro EQ4.
  apply state_incr_trans4 with s1 s2 s3 s4; eauto with rtlg.

  subst s'; auto with rtlg.
  subst s'; auto with rtlg.
  destruct rl; monadInv H. subst s'; auto with rtlg.
  destruct rl; monadInv H1. eauto with rtlg.  
Qed.

Lemma transl_expr_incr:
  forall a map mut rd nd s ns s',
  transl_expr map mut a rd nd s = OK ns s' -> state_incr s s'.
Proof (proj1 transl_expr_condition_exprlist_incr).

Lemma transl_condition_incr:
  forall a map mut ntrue nfalse s ns s',
  transl_condition map mut a ntrue nfalse s = OK ns s' -> state_incr s s'.
Proof (proj1 (proj2 transl_expr_condition_exprlist_incr)).

Lemma transl_exprlist_incr:
  forall al map mut rl nd s ns s',
  transl_exprlist map mut al rl nd s = OK ns s' -> state_incr s s'.
Proof (proj2 (proj2 transl_expr_condition_exprlist_incr)).

Hint Resolve transl_expr_incr transl_condition_incr transl_exprlist_incr: rtlg.

Lemma transl_exit_incr:
  forall nexits n s ns s',
  transl_exit nexits n s = OK ns s' ->
  state_incr s s'.
Proof.
  intros until s'. unfold transl_exit. 
  destruct (nth_error nexits n); intros; simplify_eq H; intros; subst s'.
  auto with rtlg.
Qed.

Hint Resolve transl_exit_incr: rtlg.

Lemma transl_switch_incr:
  forall r nexits default cases s n s',
  transl_switch r nexits cases default s = OK n s' ->
  state_incr s s'.
Proof.
  induction cases; simpl; intros.
  eauto with rtlg.
  destruct a as [key1 exit1].
  monadInv H. intros EQ2.
  apply state_incr_trans with s0. eauto.
  eauto with rtlg. 
Qed. 

Hint Resolve transl_switch_incr: rtlg.

Lemma transl_stmt_incr:
  forall a map nd nexits nret rret s ns s',
  transl_stmt map a nd nexits nret rret s = OK ns s' ->
  state_incr s s'.
Proof.
  induction a; simpl; intros.

  monadInv H. subst s'. auto with rtlg.

  monadInv H. eauto with rtlg.

  monadInv H. eauto with rtlg.

  generalize H. case (more_likely c a1 a2); monadSimpl; eauto 6 with rtlg.

  monadInv H. subst s'. 
  apply update_instr_incr with s0 s1 (Inop n0) n u; eauto with rtlg.

  eauto.

  eauto with rtlg.

  monadInv H. eauto 6 with rtlg.

  generalize H. destruct o; destruct rret; try monadSimpl.
  eauto with rtlg.
  subst s'; auto with rtlg.
Qed.

Hint Resolve transl_stmt_incr: rtlg.

