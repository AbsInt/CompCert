(** Correctness proof for the [Allocation] pass (translation from
  RTL to LTL). *)

Require Import Relations.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import RTLtyping.
Require Import Locations.
Require Import Conventions.
Require Import Coloring.
Require Import Coloringproof.
Require Import Parallelmove.
Require Import Allocation.

(** * Semantic properties of calling conventions *)

(** The value of a parameter in the called function is the same
  as the value of the corresponding argument in the caller function. *)

Lemma call_regs_param_of_arg:
  forall sig ls l,
  In l (loc_arguments sig) ->
  LTL.call_regs ls (parameter_of_argument l) = ls l.
Proof.
  intros. 
  generalize (loc_arguments_acceptable sig l H).
  unfold LTL.call_regs; unfold parameter_of_argument.
  unfold loc_argument_acceptable.
  destruct l. auto. destruct s; tauto.
Qed.

(** The return value, stored in the conventional return register,
  is correctly passed from the callee back to the caller. *)

Lemma return_regs_result:
  forall sig caller callee,
  LTL.return_regs caller callee (R (loc_result sig)) =
    callee (R (loc_result sig)).
Proof.
  intros. unfold LTL.return_regs.
  case (In_dec Loc.eq (R (loc_result sig)) temporaries); intro.
  auto.
  case (In_dec Loc.eq (R (loc_result sig)) destroyed_at_call); intro.
  auto.
  elim n0. apply loc_result_acceptable.
Qed.

(** Acceptable locations that are not destroyed at call keep
  their values across a call. *)

Lemma return_regs_not_destroyed:
  forall caller callee l,
  Loc.notin l destroyed_at_call -> loc_acceptable l ->
  LTL.return_regs caller callee l = caller l.
Proof.
  unfold loc_acceptable, LTL.return_regs.
  destruct l; auto.
  intros. case (In_dec Loc.eq (R m) temporaries); intro.
  contradiction.
  case (In_dec Loc.eq (R m) destroyed_at_call); intro.
  elim (Loc.notin_not_in _ _ H i). 
  auto.
Qed.

(** * Correctness condition for the liveness analysis *)

(** The liveness information computed by the dataflow analysis is
  correct in the following sense: all registers live ``before''
  an instruction are live ``after'' all of its predecessors. *)

Lemma analyze_correct:
  forall (f: function) (live: PMap.t Regset.t) (n s: node),
  analyze f = Some live ->
  f.(fn_code)!n <> None ->
  f.(fn_code)!s <> None ->
  In s (successors f n) ->
  Regset.ge live!!n (transfer f s live!!s).
Proof.
  intros.
  eapply DS.fixpoint_solution.
  unfold analyze in H. eexact H.
  elim (fn_code_wf f n); intro. auto. contradiction.
  elim (fn_code_wf f s); intro. auto. contradiction.
  auto.
Qed.

Definition live0 (f: RTL.function) (live: PMap.t Regset.t) :=
  transfer f f.(RTL.fn_entrypoint) live!!(f.(RTL.fn_entrypoint)).

(** * Properties of allocated locations *)

(** We list here various properties of the locations [alloc r],
  where [r] is an RTL pseudo-register and [alloc] is the register
  assignment returned by [regalloc]. *)

Section REGALLOC_PROPERTIES.

Variable f: function.
Variable env: regenv.
Variable live: PMap.t Regset.t.
Variable alloc: reg -> loc.
Hypothesis ALLOC: regalloc f live (live0 f live) env = Some alloc.

Lemma loc_acceptable_noteq_diff:
  forall l1 l2,
  loc_acceptable l1 -> l1 <> l2 -> Loc.diff l1 l2.
Proof.
  unfold loc_acceptable, Loc.diff; destruct l1; destruct l2;
  try (destruct s); try (destruct s0); intros; auto; try congruence.
  case (zeq z z0); intro. 
  compare t t0; intro.
  subst z0; subst t0; tauto.
  tauto. tauto.
  contradiction. contradiction.
Qed.

Lemma regalloc_noteq_diff:
  forall r1 l2,
  alloc r1 <> l2 -> Loc.diff (alloc r1) l2.
Proof.
  intros. apply loc_acceptable_noteq_diff. 
  eapply regalloc_acceptable; eauto.
  auto.
Qed.   

Lemma loc_acceptable_notin_notin:
  forall r ll,
  loc_acceptable r ->
  ~(In r ll) -> Loc.notin r ll.
Proof.
  induction ll; simpl; intros.
  auto.
  split. apply loc_acceptable_noteq_diff. assumption. 
  apply sym_not_equal. tauto. 
  apply IHll. assumption. tauto. 
Qed.

Lemma regalloc_notin_notin:
  forall r ll,
  ~(In (alloc r) ll) -> Loc.notin (alloc r) ll.
Proof.
  intros. apply loc_acceptable_notin_notin. 
  eapply regalloc_acceptable; eauto. auto.
Qed.
  
Lemma regalloc_norepet_norepet:
  forall rl,
  list_norepet (List.map alloc rl) ->
  Loc.norepet (List.map alloc rl).
Proof.
  induction rl; simpl; intros.
  apply Loc.norepet_nil.
  inversion H.
  apply Loc.norepet_cons.
  eapply regalloc_notin_notin; eauto.
  auto.
Qed.

Lemma regalloc_not_temporary:
  forall (r: reg), 
  Loc.notin (alloc r) temporaries.
Proof.
  intros. apply temporaries_not_acceptable. 
  eapply regalloc_acceptable; eauto.
Qed.

Lemma regalloc_disj_temporaries:
  forall (rl: list reg),
  Loc.disjoint (List.map alloc rl) temporaries.
Proof.
  intros. 
  apply Loc.notin_disjoint. intros.
  generalize (list_in_map_inv _ _ _ H). intros [r [EQ IN]].
  subst x. apply regalloc_not_temporary; auto.
Qed.

End REGALLOC_PROPERTIES. 

(** * Semantic agreement between RTL registers and LTL locations *)

Require Import LTL.

Section AGREE.

Variable f: RTL.function.
Variable env: regenv.
Variable flive: PMap.t Regset.t.
Variable assign: reg -> loc.
Hypothesis REGALLOC: regalloc f flive (live0 f flive) env = Some assign.

(** Remember the core of the code transformation performed in module
  [Allocation]: every reference to register [r] is replaced by
  a reference to location [assign r].  We will shortly prove
  the semantic equivalence between the original code and the transformed code.
  The key tool to do this is the following relation between
  a register set [rs] in the original RTL program and a location set
  [ls] in the transformed LTL program.  The two sets agree if
  they assign identical values to matching registers and locations,
  that is, the value of register [r] in [rs] is the same as
  the value of location [assign r] in [ls].  However, this equality
  needs to hold only for live registers [r].  If [r] is dead at
  the current point, its value is never used later, hence the value
  of [assign r] can be arbitrary. *)

Definition agree (live: Regset.t) (rs: regset) (ls: locset) : Prop :=
  forall (r: reg), Regset.mem r live = true -> ls (assign r) = rs#r.

(** What follows is a long list of lemmas expressing properties
  of the [agree_live_regs] predicate that are useful for the 
  semantic equivalence proof.  First: two register sets that agree
  on a given set of live registers also agree on a subset of
  those live registers. *)

Lemma agree_increasing:
  forall live1 live2 rs ls,
  Regset.ge live1 live2 -> agree live1 rs ls ->
  agree live2 rs ls.
Proof.
  unfold agree; intros. 
  apply H0. apply H. auto.
Qed.

(** Some useful special cases of [agree_increasing]. *)

Lemma agree_reg_live:
  forall r live rs ls,
  agree (reg_live r live) rs ls -> agree live rs ls.
Proof.
  intros. apply agree_increasing with (reg_live r live).
  red; intros. case (Reg.eq r r0); intro.
  subst r0. apply Regset.mem_add_same.
  rewrite Regset.mem_add_other; auto. auto.
Qed.

Lemma agree_reg_list_live:
  forall rl live rs ls,
  agree (reg_list_live rl live) rs ls -> agree live rs ls.
Proof.
  induction rl; simpl; intros.
  assumption. 
  apply agree_reg_live with a. apply IHrl. assumption.
Qed.

Lemma agree_reg_sum_live:
  forall ros live rs ls,
  agree (reg_sum_live ros live) rs ls -> agree live rs ls.
Proof.
  intros. destruct ros; simpl in H.
  apply agree_reg_live with r; auto.
  auto.  
Qed.

(** Agreement over a set of live registers just extended with [r]
  implies equality of the values of [r] and [assign r]. *)

Lemma agree_eval_reg:
  forall r live rs ls,
  agree (reg_live r live) rs ls -> ls (assign r) = rs#r.
Proof.
  intros. apply H. apply Regset.mem_add_same.
Qed.

(** Same, for a list of registers. *)

Lemma agree_eval_regs:
  forall rl live rs ls,
  agree (reg_list_live rl live) rs ls ->
  List.map ls (List.map assign rl) = rs##rl.
Proof.
  induction rl; simpl; intros.
  reflexivity.
  apply (f_equal2 (@cons val)). 
  apply agree_eval_reg with live. 
  apply agree_reg_list_live with rl. auto.
  eapply IHrl. eexact H.
Qed.

(** Agreement is insensitive to the current values of the temporary
  machine registers. *)

Lemma agree_exten:
  forall live rs ls ls',
  agree live rs ls ->
  (forall l, Loc.notin l temporaries -> ls' l = ls l) ->
  agree live rs ls'.
Proof.
  unfold agree; intros. 
  rewrite H0. apply H. auto. eapply regalloc_not_temporary; eauto.
Qed.

(** If a register is dead, assigning it an arbitrary value in [rs]
    and leaving [ls] unchanged preserves agreement.  (This corresponds
    to an operation over a dead register in the original program
    that is turned into a no-op in the transformed program.) *)

Lemma agree_assign_dead:
  forall live r rs ls v,
  Regset.mem r live = false ->
  agree live rs ls ->
  agree live (rs#r <- v) ls.
Proof.
  unfold agree; intros.
  case (Reg.eq r r0); intro.
  subst r0. congruence.
  rewrite Regmap.gso; auto. 
Qed.

(** Setting [r] to value [v] in [rs]
  and simultaneously setting [assign r] to value [v] in [ls]
  preserves agreement, provided that all live registers except [r]
  are mapped to locations other than that of [r]. *)

Lemma agree_assign_live:
  forall live r rs ls ls' v,
  (forall s,
     Regset.mem s live = true -> s <> r -> assign s <> assign r) ->
  ls' (assign r) = v ->
  (forall l, Loc.diff l (assign r) -> Loc.notin l temporaries -> ls' l = ls l) ->
  agree (reg_dead r live) rs ls ->
  agree live (rs#r <- v) ls'.
Proof.
  unfold agree; intros.
  case (Reg.eq r r0); intro.
  subst r0. rewrite Regmap.gss. assumption.
  rewrite Regmap.gso; auto.
  rewrite H1. apply H2. rewrite Regset.mem_remove_other. auto.
  auto.  eapply regalloc_noteq_diff. eauto. apply H. auto.  auto.
  eapply regalloc_not_temporary; eauto.
Qed.

(** This is a special case of the previous lemma where the value [v]
  being stored is not arbitrary, but is the value of
  another register [arg].  (This corresponds to a register-register move
  instruction.)  In this case, the condition can be weakened:
  it suffices that all live registers except [arg] and [res] 
  are mapped to locations other than that of [res]. *)

Lemma agree_move_live:
  forall live arg res rs (ls ls': locset),
  (forall r,
     Regset.mem r live = true -> r <> res -> r <> arg -> 
     assign r <> assign res) ->
  ls' (assign res) = ls (assign arg) ->
  (forall l, Loc.diff l (assign res) -> Loc.notin l temporaries -> ls' l = ls l) ->
  agree (reg_live arg (reg_dead res live)) rs ls ->
  agree live (rs#res <- (rs#arg)) ls'.
Proof.
  unfold agree; intros. 
  case (Reg.eq res r); intro.
  subst r. rewrite Regmap.gss. rewrite H0. apply H2.
  apply Regset.mem_add_same.
  rewrite Regmap.gso; auto.
  case (Loc.eq (assign r) (assign res)); intro.
  rewrite e. rewrite H0.
  case (Reg.eq arg r); intro.
  subst r. apply H2. apply Regset.mem_add_same.
  elim (H r); auto.
  rewrite H1. apply H2. 
  case (Reg.eq arg r); intro. subst r. apply Regset.mem_add_same.
  rewrite Regset.mem_add_other; auto.
  rewrite Regset.mem_remove_other; auto.
  eapply regalloc_noteq_diff; eauto.
  eapply regalloc_not_temporary; eauto.
Qed.

(** This complicated lemma states agreement between the states after
  a function call, provided that the states before the call agree
  and that calling conventions are respected. *)

Lemma agree_call:
  forall live args ros res rs v (ls ls': locset),
  (forall r,
    Regset.mem r live = true ->
    r <> res ->
    ~(In (assign r) Conventions.destroyed_at_call)) ->
  (forall r,
    Regset.mem r live = true -> r <> res -> assign r <> assign res) ->
  ls' (assign res) = v ->
  (forall l,
    Loc.notin l destroyed_at_call -> loc_acceptable l -> Loc.diff l (assign res) ->
    ls' l = ls l) ->
  agree (reg_list_live args (reg_sum_live ros (reg_dead res live))) rs ls ->
  agree live (rs#res <- v) ls'.
Proof.
  intros. 
  assert (agree (reg_dead res live) rs ls).
  apply agree_reg_sum_live with ros. 
  apply agree_reg_list_live with args. assumption.
  red; intros. 
  case (Reg.eq r res); intro.
  subst r. rewrite Regmap.gss. assumption.
  rewrite Regmap.gso; auto. rewrite H2. apply H4.
  rewrite Regset.mem_remove_other; auto.
  eapply regalloc_notin_notin; eauto. 
  eapply regalloc_acceptable; eauto.
  eapply regalloc_noteq_diff; eauto.
Qed.

(** Agreement between the initial register set at RTL function entry
  and the location set at LTL function entry. *)

Lemma agree_init_regs:
  forall rl vl ls live,
  (forall r1 r2,
    In r1 rl -> Regset.mem r2 live = true -> r1 <> r2 ->
    assign r1 <> assign r2) ->
  List.map ls (List.map assign rl) = vl ->
  agree (reg_list_dead rl live) (Regmap.init Vundef) ls ->
  agree live (init_regs vl rl) ls.
Proof.
  induction rl; simpl; intros.
  assumption.
  destruct vl. discriminate. 
  assert (agree (reg_dead a live) (init_regs vl rl) ls).
  apply IHrl. intros. apply H. tauto. 
  case (Reg.eq a r2); intro. subst r2. 
  rewrite Regset.mem_remove_same in H3. discriminate.
  rewrite Regset.mem_remove_other in H3; auto.
  auto. congruence. assumption.
  red; intros. case (Reg.eq a r); intro.
  subst r. rewrite Regmap.gss. congruence. 
  rewrite Regmap.gso; auto. apply H2. 
  rewrite Regset.mem_remove_other; auto.
Qed.

Lemma agree_parameters:
  forall vl ls,
  let params := f.(RTL.fn_params) in
  List.map ls (List.map assign params) = vl ->
  (forall r,
     Regset.mem r (reg_list_dead params (live0 f flive)) = true ->
     ls (assign r) = Vundef) ->
  agree (live0 f flive) (init_regs vl params) ls.
Proof.
  intros. apply agree_init_regs. 
  intros. eapply regalloc_correct_3; eauto.
  assumption. 
  red; intros. rewrite Regmap.gi. auto.
Qed.

End AGREE.

(** * Correctness of the LTL constructors *)

(** This section proves theorems that establish the correctness of the
  LTL constructor functions such as [add_op].  The theorems are of
  the general form ``the generated LTL instructions execute and
  modify the location set in the expected way: the result location(s)
  contain the expected values and other, non-temporary locations keep
  their values''. *)

Section LTL_CONSTRUCTORS.

Variable ge: LTL.genv.
Variable sp: val.

Lemma reg_for_spec:
  forall l,
  R(reg_for l) = l \/ In (R (reg_for l)) temporaries.
Proof.
  intros. unfold reg_for. destruct l. tauto.
  case (slot_type s); simpl; tauto.
Qed.

Lemma add_reload_correct:
  forall src dst k rs m,
  exists rs',
  exec_instrs ge sp (add_reload src dst k) rs m E0 k rs' m /\
  rs' (R dst) = rs src /\
  forall l, Loc.diff (R dst) l -> rs' l = rs l.
Proof.
  intros. unfold add_reload. destruct src.
  case (mreg_eq m0 dst); intro.
  subst dst. exists rs. split. apply exec_refl. tauto.
  exists (Locmap.set (R dst) (rs (R m0)) rs).
  split. apply exec_one; apply exec_Bop.  reflexivity. 
  split. apply Locmap.gss. 
  intros; apply Locmap.gso; auto.
  exists (Locmap.set (R dst) (rs (S s)) rs).
  split. apply exec_one; apply exec_Bgetstack. 
  split. apply Locmap.gss. 
  intros; apply Locmap.gso; auto.
Qed.

Lemma add_spill_correct:
  forall src dst k rs m,
  exists rs',
  exec_instrs ge sp (add_spill src dst k) rs m E0 k rs' m /\
  rs' dst = rs (R src) /\
  forall l, Loc.diff dst l -> rs' l = rs l.
Proof.
  intros. unfold add_spill. destruct dst.
  case (mreg_eq src m0); intro.
  subst src. exists rs. split. apply exec_refl. tauto.
  exists (Locmap.set (R m0) (rs (R src)) rs).
  split. apply exec_one. apply exec_Bop. reflexivity.
  split. apply Locmap.gss.
  intros; apply Locmap.gso; auto.
  exists (Locmap.set (S s) (rs (R src)) rs).
  split. apply exec_one. apply exec_Bsetstack. 
  split. apply Locmap.gss.
  intros; apply Locmap.gso; auto.
Qed.

Lemma add_reloads_correct_rec:
  forall srcs itmps ftmps k rs m,
  (List.length srcs <= List.length itmps)%nat ->
  (List.length srcs <= List.length ftmps)%nat ->
  (forall r, In (R r) srcs -> In r itmps -> False) ->
  (forall r, In (R r) srcs -> In r ftmps -> False) ->
  list_disjoint itmps ftmps ->
  list_norepet itmps ->
  list_norepet ftmps ->
  exists rs',
  exec_instrs ge sp (add_reloads srcs (regs_for_rec srcs itmps ftmps) k) rs m E0 k rs' m /\
  reglist (regs_for_rec srcs itmps ftmps) rs' = map rs srcs /\
  (forall r, ~(In r itmps) -> ~(In r ftmps) -> rs' (R r) = rs (R r)) /\
  (forall s, rs' (S s) = rs (S s)).
Proof.
  induction srcs; simpl; intros.
  (* base case *)
  exists rs. split. apply exec_refl. tauto.
  (* inductive case *)
  destruct itmps; simpl in H. omegaContradiction.
  destruct ftmps; simpl in H0. omegaContradiction.
  assert (R1: (length srcs <= length itmps)%nat). omega.
  assert (R2: (length srcs <= length ftmps)%nat). omega.
  assert (R3: forall r, In (R r) srcs -> In r itmps -> False).
    intros. apply H1 with r. tauto. auto with coqlib. 
  assert (R4: forall r, In (R r) srcs -> In r ftmps -> False).
    intros. apply H2 with r. tauto. auto with coqlib.
  assert (R5: list_disjoint itmps ftmps).
    eapply list_disjoint_cons_left.
    eapply list_disjoint_cons_right. eauto.
  assert (R6: list_norepet itmps).
    inversion H4; auto.
  assert (R7: list_norepet ftmps).
    inversion H5; auto.
  destruct a.
  (* a is a register *)
  generalize (IHsrcs itmps ftmps k rs m R1 R2 R3 R4 R5 R6 R7).
  intros [rs' [EX [RES [OTH1 OTH2]]]].
  exists rs'. split.
  unfold add_reload. case (mreg_eq m2 m2); intro; tauto.
  split. simpl. apply (f_equal2 (@cons val)). 
  apply OTH1. 
  red; intro; apply H1 with m2. tauto. auto with coqlib.
  red; intro; apply H2 with m2. tauto. auto with coqlib.
  assumption.
  split. intros. apply OTH1. simpl in H6; tauto. simpl in H7; tauto.
  auto.
  (* a is a stack location *)
  set (tmp := match slot_type s with Tint => m0 | Tfloat => m1 end).
  assert (NI: ~(In tmp itmps)).
    unfold tmp; case (slot_type s).
    inversion H4; auto. 
    apply list_disjoint_notin with (m1 :: ftmps). 
    apply list_disjoint_sym. apply list_disjoint_cons_left with m0.
    auto. auto with coqlib.
  assert (NF: ~(In tmp ftmps)).
    unfold tmp; case (slot_type s).
    apply list_disjoint_notin with (m0 :: itmps). 
    apply list_disjoint_cons_right with m1.
    auto. auto with coqlib.
    inversion H5; auto. 
  generalize
    (add_reload_correct (S s) tmp
       (add_reloads srcs (regs_for_rec srcs itmps ftmps) k) rs m).
  intros [rs1 [EX1 [RES1 OTH]]].     
  generalize (IHsrcs itmps ftmps k rs1 m R1 R2 R3 R4 R5 R6 R7).
  intros [rs' [EX [RES [OTH1 OTH2]]]].
  exists rs'.
  split. eapply exec_trans; eauto. traceEq.
  split. simpl. apply (f_equal2 (@cons val)). 
  rewrite OTH1; auto.
  rewrite RES. apply list_map_exten. intros.
  symmetry. apply OTH. 
  destruct x; try exact I. simpl. red; intro; subst m2.
  generalize H6; unfold tmp. case (slot_type s).
  intro. apply H1 with m0. tauto. auto with coqlib.
  intro. apply H2 with m1. tauto. auto with coqlib.
  split. intros. simpl in H6; simpl in H7.
  rewrite OTH1. apply OTH. 
  simpl. unfold tmp. case (slot_type s); tauto.
  tauto. tauto.
  intros. rewrite OTH2. apply OTH. exact I.
Qed.

Lemma add_reloads_correct:
  forall srcs k rs m,
  (List.length srcs <= 3)%nat ->
  Loc.disjoint srcs temporaries ->
  exists rs',
  exec_instrs ge sp (add_reloads srcs (regs_for srcs) k) rs m E0 k rs' m /\
  reglist (regs_for srcs) rs' = List.map rs srcs /\
  forall l, Loc.notin l temporaries -> rs' l = rs l.
Proof.
  intros.
  pose (itmps := IT1 :: IT2 :: IT3 :: nil).
  pose (ftmps := FT1 :: FT2 :: FT3 :: nil).
  assert (R1: (List.length srcs <= List.length itmps)%nat).
    unfold itmps; simpl; assumption.
  assert (R2: (List.length srcs <= List.length ftmps)%nat).
    unfold ftmps; simpl; assumption.
  assert (R3: forall r, In (R r) srcs -> In r itmps -> False).
    intros. assert (In (R r) temporaries). 
    simpl in H2; simpl; intuition congruence.
    generalize (H0 _ _ H1 H3). simpl. tauto.
  assert (R4: forall r, In (R r) srcs -> In r ftmps -> False).
    intros. assert (In (R r) temporaries). 
    simpl in H2; simpl; intuition congruence.
    generalize (H0 _ _ H1 H3). simpl. tauto.
  assert (R5: list_disjoint itmps ftmps).
    red; intros r1 r2; simpl; intuition congruence.
  assert (R6: list_norepet itmps).
    unfold itmps. NoRepet.
  assert (R7: list_norepet ftmps).
    unfold ftmps. NoRepet.
  generalize (add_reloads_correct_rec srcs itmps ftmps k rs m
                R1 R2 R3 R4 R5 R6 R7).
  intros [rs' [EX [RES [OTH1 OTH2]]]].
  exists rs'. split. exact EX. 
  split. exact RES.
  intros. destruct l. apply OTH1.
  generalize (Loc.notin_not_in _ _ H1). simpl. intuition congruence.
  generalize (Loc.notin_not_in _ _ H1). simpl. intuition congruence.
  apply OTH2.
Qed.

Lemma add_move_correct:
  forall src dst k rs m,
  exists rs',
  exec_instrs ge sp (add_move src dst k) rs m E0 k rs' m /\
  rs' dst = rs src /\
  forall l, Loc.diff l dst -> Loc.diff l (R IT1) -> Loc.diff l (R FT1) -> rs' l = rs l.
Proof.
  intros; unfold add_move.
  case (Loc.eq src dst); intro.
  subst dst. exists rs. split. apply exec_refl. tauto.
  destruct src.
  (* src is a register *)
  generalize (add_spill_correct m0 dst k rs m); intros [rs' [EX [RES OTH]]].
  exists rs'; intuition. apply OTH; apply Loc.diff_sym; auto.
  destruct dst.
  (* src is a stack slot, dst a register *)
  generalize (add_reload_correct (S s) m0 k rs m); intros [rs' [EX [RES OTH]]].
  exists rs'; intuition. apply OTH; apply Loc.diff_sym; auto.
  (* src and dst are stack slots *)
  set (tmp := match slot_type s with Tint => IT1 | Tfloat => FT1 end).
  generalize (add_reload_correct (S s) tmp (add_spill tmp (S s0) k) rs m);
  intros [rs1 [EX1 [RES1 OTH1]]].
  generalize (add_spill_correct tmp (S s0) k rs1 m);
  intros [rs2 [EX2 [RES2 OTH2]]].
  exists rs2. split.
  eapply exec_trans; eauto. traceEq.
  split. congruence.
  intros. rewrite OTH2. apply OTH1. 
  apply Loc.diff_sym. unfold tmp; case (slot_type s); auto.
  apply Loc.diff_sym; auto.
Qed.

Lemma effect_move_sequence:
  forall k moves rs m,
  let k' := List.fold_right (fun p k => add_move (fst p) (snd p) k) k moves in
  exists rs',
  exec_instrs ge sp k' rs m E0 k rs' m /\
  effect_seqmove moves rs rs'.
Proof.
  induction moves; intros until m; simpl.
  exists rs; split. constructor. constructor.
  destruct a as [src dst]; simpl.
  set (k1 := fold_right
              (fun (p : loc * loc) (k : block) => add_move (fst p) (snd p) k)
              k moves) in *.
  destruct (add_move_correct src dst k1 rs m) as [rs1 [A [B C]]].
  destruct (IHmoves rs1 m) as [rs' [D E]].
  exists rs'; split. 
  eapply exec_trans; eauto. traceEq.
  econstructor; eauto. red. tauto. 
Qed.

Theorem parallel_move_correct:
  forall srcs dsts k rs m,
  List.length srcs = List.length dsts ->
  Loc.no_overlap srcs dsts ->
  Loc.norepet dsts ->
  Loc.disjoint srcs temporaries ->
  Loc.disjoint dsts temporaries ->
  exists rs',
  exec_instrs ge sp (parallel_move srcs dsts k) rs m E0 k rs' m /\
  List.map rs' dsts = List.map rs srcs /\
  rs' (R IT3) = rs (R IT3) /\
  forall l, Loc.notin l dsts -> Loc.notin l temporaries -> rs' l = rs l.
Proof.
  intros. 
  generalize (effect_move_sequence k (parmove srcs dsts) rs m).
  intros [rs' [EXEC EFFECT]].
  exists rs'. split. exact EXEC. 
  apply effect_parmove; auto.
Qed.
 
Lemma add_op_correct:
  forall op args res s rs m v,
  (List.length args <= 3)%nat ->
  Loc.disjoint args temporaries ->
  eval_operation ge sp op (List.map rs args) = Some v ->
  exists rs',
  exec_block ge sp (add_op op args res s) rs m E0 (Cont s) rs' m /\
  rs' res =  v /\
  forall l, Loc.diff l res -> Loc.notin l temporaries -> rs' l = rs l.
Proof.
  intros. unfold add_op. 
  caseEq (is_move_operation op args).
  (* move *)
  intros arg IMO. 
  generalize (is_move_operation_correct op args IMO). 
  intros [EQ1 EQ2]. subst op; subst args.   
  generalize (add_move_correct arg res (Bgoto s) rs m).
  intros [rs' [EX [RES OTHER]]].
  exists rs'. split. 
  apply exec_Bgoto. exact EX. 
  split. simpl in H1. congruence.
  intros. unfold temporaries in H3; simpl in H3. 
  apply OTHER. assumption. tauto. tauto. 
  (* other ops *)
  intros.
  set (rargs := regs_for args). set (rres := reg_for res).
  generalize (add_reloads_correct args
                (Bop op rargs rres (add_spill rres res (Bgoto s)))
                rs m H H0).
  intros [rs1 [EX1 [RES1 OTHER1]]].
  pose (rs2 := Locmap.set (R rres) v rs1).
  generalize (add_spill_correct rres res (Bgoto s) rs2 m).
  intros [rs3 [EX3 [RES3 OTHER3]]].
  exists rs3.
  split. apply exec_Bgoto. eapply exec_trans. eexact EX1. 
  eapply exec_trans; eauto. 
  apply exec_one. unfold rs2. apply exec_Bop. 
  unfold rargs. rewrite RES1. auto. traceEq.
  split. rewrite RES3. unfold rs2; apply Locmap.gss. 
  intros. rewrite OTHER3. unfold rs2. rewrite Locmap.gso.
  apply OTHER1. assumption. 
  apply Loc.diff_sym. unfold rres. elim (reg_for_spec res); intro.
  rewrite H5; auto. 
  eapply Loc.in_notin_diff; eauto. apply Loc.diff_sym; auto.
Qed.

Lemma add_load_correct:
  forall chunk addr args res s rs m a v,
  (List.length args <= 2)%nat ->
  Loc.disjoint args temporaries ->
  eval_addressing ge sp addr (List.map rs args) = Some a ->
  loadv chunk m a = Some v ->
  exists rs',
  exec_block ge sp (add_load chunk addr args res s) rs m E0 (Cont s) rs' m /\
  rs' res = v /\
  forall l, Loc.diff l res -> Loc.notin l temporaries -> rs' l = rs l.
Proof.
  intros. unfold add_load. 
  set (rargs := regs_for args). set (rres := reg_for res).
  assert (LL: (List.length args <= 3)%nat). omega.
  generalize (add_reloads_correct args
                (Bload chunk addr rargs rres (add_spill rres res (Bgoto s)))
                rs m LL H0).
  intros [rs1 [EX1 [RES1 OTHER1]]].
  pose (rs2 := Locmap.set (R rres) v rs1).
  generalize (add_spill_correct rres res (Bgoto s) rs2 m).
  intros [rs3 [EX3 [RES3 OTHER3]]].
  exists rs3.
  split. apply exec_Bgoto. eapply exec_trans; eauto.
  eapply exec_trans; eauto. 
  apply exec_one.  unfold rs2. apply exec_Bload with a.
  unfold rargs; rewrite RES1. assumption. assumption. traceEq.
  split. rewrite RES3. unfold rs2; apply Locmap.gss.
  intros. rewrite OTHER3. unfold rs2. rewrite Locmap.gso. 
  apply OTHER1. assumption. 
  apply Loc.diff_sym. unfold rres. elim (reg_for_spec res); intro.
  rewrite H5; auto.
  eapply Loc.in_notin_diff; eauto. apply Loc.diff_sym; auto.
Qed.

Lemma add_store_correct:
  forall chunk addr args src s rs m m' a,
  (List.length args <= 2)%nat ->
  Loc.disjoint args temporaries ->
  Loc.notin src temporaries ->
  eval_addressing ge sp addr (List.map rs args) = Some a ->
  storev chunk m a (rs src) = Some m' ->
  exists rs',
  exec_block ge sp (add_store chunk addr args src s) rs m E0 (Cont s) rs' m' /\
  forall l, Loc.notin l temporaries -> rs' l = rs l.
Proof.
  intros. 
  assert (LL: (List.length (src :: args) <= 3)%nat).
    simpl. omega.
  assert (DISJ: Loc.disjoint (src :: args) temporaries).
    red; intros. elim H4; intro. subst x1. 
    eapply Loc.in_notin_diff; eauto.
    auto with coqlib.
  unfold add_store. caseEq (regs_for (src :: args)).
  unfold regs_for; simpl; intro; discriminate.
  intros rsrc rargs EQ. 
  generalize (add_reloads_correct (src :: args)
               (Bstore chunk addr rargs rsrc (Bgoto s))
               rs m LL DISJ).
  intros [rs1 [EX1 [RES1 OTHER1]]].
  rewrite EQ in RES1. simpl in RES1. injection RES1. 
  intros RES2 RES3. 
  exists rs1.
  split. apply exec_Bgoto. 
  eapply exec_trans. rewrite <- EQ. eexact EX1. 
  apply exec_one. apply exec_Bstore with a. 
  rewrite RES2. assumption. rewrite RES3. assumption. traceEq.
  exact OTHER1.
Qed.

Lemma add_alloc_correct:
  forall arg res s rs m m' sz b,
  rs arg = Vint sz ->
  Mem.alloc m 0 (Int.signed sz) = (m', b) ->
  exists rs',
  exec_block ge sp (add_alloc arg res s) rs m E0 (Cont s) rs' m' /\
  rs' res = Vptr b Int.zero /\
  forall l,
    Loc.diff l (R Conventions.loc_alloc_argument) ->
    Loc.diff l (R Conventions.loc_alloc_result) ->
    Loc.diff l res -> 
    rs' l = rs l.
Proof.
  intros; unfold add_alloc.
  generalize (add_reload_correct arg loc_alloc_argument
                (Balloc (add_spill loc_alloc_result res (Bgoto s)))
                rs m).
  intros [rs1 [EX1 [RES1 OTHER1]]].
  pose (rs2 := Locmap.set (R loc_alloc_result) (Vptr b Int.zero) rs1).
  generalize (add_spill_correct loc_alloc_result res (Bgoto s) rs2 m').
  intros [rs3 [EX3 [RES3 OTHER3]]].
  exists rs3.
  split. apply exec_Bgoto. eapply exec_trans. eexact EX1.
  eapply exec_trans. apply exec_one. eapply exec_Balloc; eauto. congruence. 
  fold rs2. eexact EX3. reflexivity. traceEq. 
  split. rewrite RES3; unfold rs2. apply Locmap.gss.
  intros. rewrite OTHER3. unfold rs2. rewrite Locmap.gso.
  apply OTHER1. apply Loc.diff_sym; auto.
  apply Loc.diff_sym; auto.
  apply Loc.diff_sym; auto.
Qed.

Lemma add_cond_correct:
  forall cond args ifso ifnot rs m b s,
  (List.length args <= 3)%nat ->
  Loc.disjoint args temporaries ->
  eval_condition cond (List.map rs args) = Some b ->
  s = (if b then ifso else ifnot) ->
  exists rs',
  exec_block ge sp (add_cond cond args ifso ifnot) rs m E0 (Cont s) rs' m /\
  forall l, Loc.notin l temporaries -> rs' l = rs l.
Proof.
  intros. unfold add_cond.
  set (rargs := regs_for args).
  generalize (add_reloads_correct args
               (Bcond cond rargs ifso ifnot)
               rs m H H0).
  intros [rs1 [EX1 [RES1 OTHER1]]].
  fold rargs in EX1.
  exists rs1.
  split. destruct b; subst s.
  eapply exec_Bcond_true. eexact EX1. 
  unfold rargs; rewrite RES1. assumption. 
  eapply exec_Bcond_false. eexact EX1.
  unfold rargs; rewrite RES1. assumption. 
  exact OTHER1.
Qed.

Definition find_function2 (los: loc + ident) (ls: locset) : option fundef :=
  match los with
  | inl l => Genv.find_funct ge (ls l)
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

Lemma add_call_correct:
  forall f vargs m t vres m' sig los args res s ls
    (EXECF:
      forall lsi,
        List.map lsi (loc_arguments (funsig f)) = vargs ->
        exists lso,
            exec_function ge f lsi m t lso m'
         /\ lso (R (loc_result (funsig f))) = vres)
    (FIND: find_function2 los ls = Some f)
    (SIG: sig = funsig f)
    (VARGS: List.map ls args = vargs)
    (LARGS: List.length args = List.length sig.(sig_args))
    (AARGS: locs_acceptable args)
    (RES: loc_acceptable res),
  exists ls',
  exec_block ge sp (add_call sig los args res s) ls m t (Cont s) ls' m' /\
  ls' res = vres /\
  forall l,
    Loc.notin l destroyed_at_call -> loc_acceptable l -> Loc.diff l res ->
    ls' l = ls l.
Proof.
  intros until los. 
  case los; intro fn; intros; simpl in FIND; rewrite <- SIG in EXECF; unfold add_call.
  (* indirect call *)
  assert (LEN: List.length args = List.length (loc_arguments sig)).
    rewrite LARGS. symmetry. apply loc_arguments_length.
  pose (DISJ := locs_acceptable_disj_temporaries args AARGS).
  generalize (add_reload_correct fn IT3
       (parallel_move args (loc_arguments sig)
          (Bcall sig (inl ident IT3)
             (add_spill (loc_result sig) res (Bgoto s))))
       ls m).
  intros [ls1 [EX1 [RES1 OTHER1]]].
  generalize
    (parallel_move_correct args (loc_arguments sig)
        (Bcall sig (inl ident IT3)
             (add_spill (loc_result sig) res (Bgoto s)))
        ls1 m LEN 
        (no_overlap_arguments args sig AARGS)
        (loc_arguments_norepet sig)
        DISJ 
        (loc_arguments_not_temporaries sig)).
  intros [ls2 [EX2 [RES2 [TMP2 OTHER2]]]].
  assert (PARAMS: List.map ls2 (loc_arguments sig) = vargs).
    rewrite <- VARGS. rewrite RES2. 
    apply list_map_exten. intros. symmetry. apply OTHER1.
    apply Loc.diff_sym. apply DISJ. auto. simpl; tauto.
  generalize (EXECF ls2 PARAMS).
  intros [ls3 [EX3 RES3]].
  pose (ls4 := return_regs ls2 ls3).
  generalize (add_spill_correct (loc_result sig) res
                (Bgoto s) ls4 m').
  intros [ls5 [EX5 [RES5 OTHER5]]].
  exists ls5.
  (* Execution *)
  split. apply exec_Bgoto. 
  eapply exec_trans. eexact EX1.
  eapply exec_trans. eexact EX2.
  eapply exec_trans. apply exec_one. apply exec_Bcall with f.
  unfold find_function. rewrite TMP2. rewrite RES1. 
  assumption. assumption. eexact EX3.
  eexact EX5. reflexivity. reflexivity. traceEq.
  (* Result *)
  split. rewrite RES5. unfold ls4. rewrite return_regs_result. 
  assumption.
  (* Other regs *)
  intros. rewrite OTHER5; auto.
  unfold ls4; rewrite return_regs_not_destroyed; auto. 
  rewrite OTHER2. apply OTHER1. 
  apply Loc.diff_sym. apply Loc.in_notin_diff with temporaries.  
  apply temporaries_not_acceptable; auto. simpl; tauto.
  apply arguments_not_preserved; auto.
  apply temporaries_not_acceptable; auto.
  apply Loc.diff_sym; auto.
  (* direct call *)
  assert (LEN: List.length args = List.length (loc_arguments sig)).
    rewrite LARGS. symmetry. apply loc_arguments_length.
  pose (DISJ := locs_acceptable_disj_temporaries args AARGS).
  generalize
    (parallel_move_correct args (loc_arguments sig)
        (Bcall sig (inr mreg fn)
             (add_spill (loc_result sig) res (Bgoto s)))
        ls m LEN 
        (no_overlap_arguments args sig AARGS)
        (loc_arguments_norepet sig)
        DISJ (loc_arguments_not_temporaries sig)).
  intros [ls2 [EX2 [RES2 [TMP2 OTHER2]]]].
  assert (PARAMS: List.map ls2 (loc_arguments sig) = vargs).
    rewrite <- VARGS. rewrite RES2. auto.
  generalize (EXECF ls2 PARAMS).
  intros [ls3 [EX3 RES3]].
  pose (ls4 := return_regs ls2 ls3).
  generalize (add_spill_correct (loc_result sig) res
                (Bgoto s) ls4 m').
  intros [ls5 [EX5 [RES5 OTHER5]]].
  exists ls5.
  (* Execution *)
  split. apply exec_Bgoto. 
  eapply exec_trans. eexact EX2.
  eapply exec_trans. apply exec_one. apply exec_Bcall with f.
  unfold find_function. assumption. assumption. eexact EX3.
  eexact EX5. reflexivity. traceEq.
  (* Result *)
  split. rewrite RES5. 
  unfold ls4. rewrite return_regs_result. 
  assumption.
  (* Other regs *)
  intros. rewrite OTHER5; auto.
  unfold ls4; rewrite return_regs_not_destroyed; auto. 
  apply OTHER2.
  apply arguments_not_preserved; auto.
  apply temporaries_not_acceptable; auto.
  apply Loc.diff_sym; auto.
Qed.

Lemma add_undefs_correct:
  forall res b ls m,
  (forall l, In l res -> loc_acceptable l) ->
  (forall ofs ty, In (S (Local ofs ty)) res -> ls (S (Local ofs ty)) = Vundef) ->
  exists ls',
  exec_instrs ge sp (add_undefs res b) ls m E0 b ls' m /\
  (forall l, In l res -> ls' l = Vundef) /\
  (forall l, Loc.notin l res -> ls' l = ls l).
Proof.
  induction res; simpl; intros.
  exists ls. split. apply exec_refl. tauto.
  assert (ACC: forall l, In l res -> loc_acceptable l).
    intros. apply H. tauto.
  destruct a.
  (* a is a register *)
  pose (ls1 := Locmap.set (R m0) Vundef ls).
  assert (UNDEFS: forall ofs ty, In (S (Local ofs ty)) res -> ls1 (S (Local ofs ty)) = Vundef).
    intros. unfold ls1; rewrite Locmap.gso. auto. red; auto.
  generalize (IHres b (Locmap.set (R m0) Vundef ls) m ACC UNDEFS).
  intros [ls2 [EX2 [RES2 OTHER2]]].
  exists ls2. split.
  eapply exec_trans. apply exec_one. apply exec_Bop. 
  simpl; reflexivity. eexact EX2. traceEq.
  split. intros. case (In_dec Loc.eq l res); intro.
  apply RES2; auto. 
  rewrite OTHER2. elim H1; intro.
  subst l. apply Locmap.gss.
  contradiction.
  apply loc_acceptable_notin_notin; auto.  
  intros. rewrite OTHER2. apply Locmap.gso. 
  apply Loc.diff_sym; tauto. tauto.
  (* a is a stack location *)
  assert (UNDEFS: forall ofs ty, In (S (Local ofs ty)) res -> ls (S (Local ofs ty)) = Vundef).
    intros. apply H0. tauto.
  generalize (IHres b ls m ACC UNDEFS).
  intros [ls2 [EX2 [RES2 OTHER2]]].
  exists ls2. split. assumption.
  split. intros. case (In_dec Loc.eq l res); intro.
  auto.
  rewrite OTHER2. elim H1; intro. 
  subst l. generalize (H (S s) (in_eq _ _)). 
  unfold loc_acceptable; destruct s; intuition auto.
  contradiction.
  apply loc_acceptable_notin_notin; auto. 
  intros. apply OTHER2. tauto.
Qed.

Lemma add_entry_correct:
  forall sig params undefs s ls m,
  List.length params = List.length sig.(sig_args) ->
  Loc.norepet params ->
  locs_acceptable params ->
  Loc.disjoint params undefs ->
  locs_acceptable undefs ->
  (forall ofs ty, ls (S (Local ofs ty)) = Vundef) ->
  exists ls',
  exec_block ge sp (add_entry sig params undefs s) ls m E0 (Cont s) ls' m /\
  List.map ls' params = List.map ls (loc_parameters sig) /\
  (forall l, In l undefs -> ls' l = Vundef).
Proof.
  intros. 
  assert (List.length (loc_parameters sig) = List.length params).
    unfold loc_parameters. rewrite list_length_map. 
    rewrite loc_arguments_length. auto.
  assert (DISJ: Loc.disjoint params temporaries).
    apply locs_acceptable_disj_temporaries; auto.
  generalize (parallel_move_correct _ _ (add_undefs undefs (Bgoto s))
                ls m H5
                (no_overlap_parameters _ _ H1)
                H0 (loc_parameters_not_temporaries sig) DISJ).
  intros [ls1 [EX1 [RES1 [TMP1 OTHER1]]]].
  assert (forall ofs ty, In (S (Local ofs ty)) undefs -> ls1 (S (Local ofs ty)) = Vundef).
    intros. rewrite OTHER1. auto. apply Loc.disjoint_notin with undefs.
    apply Loc.disjoint_sym. auto. auto.
    simpl; tauto.
  generalize (add_undefs_correct undefs (Bgoto s) ls1 m H3 H6).
  intros [ls2 [EX2 [RES2 OTHER2]]].
  exists ls2.
  split. apply exec_Bgoto. unfold add_entry. 
  eapply exec_trans. eexact EX1. eexact EX2. traceEq.
  split. rewrite <- RES1. apply list_map_exten. 
  intros. symmetry. apply OTHER2. eapply Loc.disjoint_notin; eauto.
  exact RES2.
Qed.

Lemma add_return_correct:
  forall sig optarg ls m,
  exists ls',
  exec_block ge sp (add_return sig optarg) ls m E0 Return ls' m /\
  match optarg with
  | Some arg => ls' (R (loc_result sig)) = ls arg
  | None => ls' (R (loc_result sig)) = Vundef
  end.
Proof.
  intros. unfold add_return.
  destruct optarg.
  generalize (add_reload_correct l (loc_result sig) Breturn ls m).
  intros [ls1 [EX1 [RES1 OTH1]]].
  exists ls1.
    split. apply exec_Breturn. assumption. assumption.
  exists (Locmap.set (R (loc_result sig)) Vundef ls).
    split. apply exec_Breturn. apply exec_one. 
    apply exec_Bop. reflexivity. apply Locmap.gss. 
Qed.

End LTL_CONSTRUCTORS.

(** * Exploitation of the typing hypothesis *)

(** Register allocation is applied to RTL code that passed type inference
  (see file [RTLtyping]), and therefore is well-typed in the type system
  of [RTLtyping].  We exploit this hypothesis to obtain information on
  the number of arguments to operations, addressing modes and conditions. *)

Remark length_type_of_condition:
  forall (c: condition), (List.length (type_of_condition c) <= 3)%nat.
Proof.
  destruct c; unfold type_of_condition; simpl; omega.
Qed.

Remark length_type_of_operation:
  forall (op: operation), (List.length (fst (type_of_operation op)) <= 3)%nat.
Proof.
  destruct op; unfold type_of_operation; simpl; try omega.
  apply length_type_of_condition.
Qed.

Remark length_type_of_addressing:
  forall (addr: addressing), (List.length (type_of_addressing addr) <= 2)%nat.
Proof.
  destruct addr; unfold type_of_addressing; simpl; omega.
Qed.

Lemma length_op_args:
  forall (env: regenv) (op: operation) (args: list reg) (res: reg),
  (List.map env args, env res) = type_of_operation op ->
  (List.length args <= 3)%nat.
Proof.
  intros. rewrite <- (list_length_map env). 
  generalize (length_type_of_operation op).
  rewrite <- H. simpl. auto.
Qed.

Lemma length_addr_args:
  forall (env: regenv) (addr: addressing) (args: list reg),
  List.map env args = type_of_addressing addr ->
  (List.length args <= 2)%nat.
Proof.
  intros. rewrite <- (list_length_map env). 
  rewrite H. apply length_type_of_addressing.
Qed.

Lemma length_cond_args:
  forall (env: regenv) (cond: condition) (args: list reg),
  List.map env args = type_of_condition cond ->
  (List.length args <= 3)%nat.
Proof.
  intros. rewrite <- (list_length_map env). 
  rewrite H. apply length_type_of_condition.
Qed.

(** * Preservation of semantics *)

(** We now show that the LTL code reflecting register allocation has
  the same semantics as the original RTL code.  We start with
  standard properties of translated functions and 
  global environments in the original and translated code. *)

Section PRESERVATION.

Variable prog: RTL.program.
Variable tprog: LTL.program.
Hypothesis TRANSF: transf_program prog = Some tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intro. unfold ge, tge.
  apply Genv.find_symbol_transf_partial with transf_fundef.
  exact TRANSF.
Qed.

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = Some tf.
Proof.  
  intros. 
  generalize 
   (Genv.find_funct_transf_partial transf_fundef TRANSF H).
  case (transf_fundef f).
  intros tf [A B]. exists tf. tauto.
  intros [A B]. elim B. reflexivity.
Qed.

Lemma function_ptr_translated:
  forall (b: Values.block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = Some tf.
Proof.  
  intros. 
  generalize 
   (Genv.find_funct_ptr_transf_partial transf_fundef TRANSF H).
  case (transf_fundef f).
  intros tf [A B]. exists tf. tauto.
  intros [A B]. elim B. reflexivity.
Qed.

Lemma sig_function_translated:
  forall f tf,
  transf_fundef f = Some tf ->
  LTL.funsig tf = RTL.funsig f.
Proof.
  intros f tf. destruct f; simpl. 
  unfold transf_function.
  destruct (type_function f).
  destruct (analyze f).
  destruct (regalloc f t). 
  intro EQ; injection EQ; intro EQ1; rewrite <- EQ1; simpl; auto.
  congruence. congruence. congruence.
  intro EQ; inversion EQ; subst tf. reflexivity.
Qed.

Lemma entrypoint_function_translated:
  forall f tf,
  transf_function f = Some tf ->
  tf.(LTL.fn_entrypoint) = f.(RTL.fn_nextpc).
Proof.
  intros f tf. unfold transf_function.
  destruct (type_function f).
  destruct (analyze f).
  destruct (regalloc f t). 
  intro EQ; injection EQ; intro EQ1; rewrite <- EQ1; simpl; auto.
  intros; discriminate.
  intros; discriminate.
  intros; discriminate.
Qed.

(** The proof of semantic preservation is a simulation argument
  based on diagrams of the following form:
<<
        pc, rs, m ------------------- pc, ls, m
            |                             |
            |                             |
            v                             v
        pc', rs', m' ---------------- Cont pc', ls', m'
>>
  Hypotheses: the left vertical arrow represents a transition in the
  original RTL code.  The top horizontal bar expresses agreement between
  [rs] and [ls] over the pseudo-registers live before the RTL instruction
  at [pc].  

  Conclusions: the right vertical arrow is an [exec_blocks] transition
  in the LTL code generated by translation of the current function.
  The bottom horizontal bar expresses agreement between [rs'] and [ls']
  over the pseudo-registers live after the RTL instruction at [pc]
  (which implies agreement over the pseudo-registers live before
  the instruction at [pc']).

  We capture these diagrams in the following propositions parameterized
  by the transition in the original RTL code (the left arrow).
*)

Definition exec_instr_prop
        (c: RTL.code) (sp: val)
        (pc: node) (rs: regset) (m: mem) (t: trace)
        (pc': node) (rs': regset) (m': mem) : Prop :=
  forall f env live assign ls
         (CF: c = f.(RTL.fn_code))
         (WT: wt_function f env)
         (ASG: regalloc f live (live0 f live) env = Some assign)
         (AG: agree assign (transfer f pc live!!pc) rs ls),
  let tc := PTree.map (transf_instr f live assign) c in
  exists ls',
    exec_blocks tge tc sp pc ls m t (Cont pc') ls' m' /\
    agree assign live!!pc rs' ls'.

Definition exec_instrs_prop
        (c: RTL.code) (sp: val)
        (pc: node) (rs: regset) (m: mem) (t: trace)
        (pc': node) (rs': regset) (m': mem) : Prop :=
  forall f env live assign ls,
  forall (CF: c = f.(RTL.fn_code))
         (WT: wt_function f env)
         (ANL: analyze f = Some live)
         (ASG: regalloc f live (live0 f live) env = Some assign)
         (AG: agree assign (transfer f pc live!!pc) rs ls)
         (VALIDPC': c!pc' <> None),
  let tc := PTree.map (transf_instr f live assign) c in
  exists ls',
    exec_blocks tge tc sp pc ls m t (Cont pc') ls' m' /\
    agree assign (transfer f pc' live!!pc') rs' ls'.

Definition exec_function_prop
        (f: RTL.fundef) (args: list val) (m: mem)
        (t: trace) (res: val) (m': mem) : Prop :=
  forall ls tf,
  transf_fundef f = Some tf ->
  List.map ls (Conventions.loc_arguments (funsig tf)) = args ->
  exists ls',
    LTL.exec_function tge tf ls m t ls' m' /\
    ls' (R (Conventions.loc_result (funsig tf))) = res.

(** The simulation proof is by structural induction over the RTL evaluation
  derivation.  We prove each case of the proof as a separate lemma.
  There is one lemma for each RTL evaluation rule.  Each lemma concludes
  one of the [exec_*_prop] predicates, and takes the induction hypotheses
  (if any) as hypotheses also expressed with the [exec_*_prop] predicates.
*)

Ltac CleanupHyps :=
  match goal with
  | H1: (PTree.get _ _ = Some _),
    H2: (_ = RTL.fn_code _),
    H3: (agree _ (transfer _ _ _) _ _) |- _ =>
      unfold transfer in H3; rewrite <- H2 in H3; rewrite H1 in H3;
      simpl in H3;
      CleanupHyps
  | H1: (PTree.get _ _ = Some _),
    H2: (_ = RTL.fn_code _),
    H3: (wt_function _ _) |- _ =>
      let H := fresh in
      let R := fresh "WTI" in (
      generalize (wt_instrs _ _ H3); intro H;
      rewrite <- H2 in H; generalize (H _ _ H1);
      intro R; clear H; clear H3);
      CleanupHyps
  | _ => idtac
  end.

Ltac CleanupGoal :=
  match goal with
  | H1: (PTree.get _ _ = Some _) |- _ =>
      eapply exec_blocks_one;
      [rewrite PTree.gmap; rewrite H1;
       unfold option_map; unfold transf_instr; reflexivity
      |idtac]
  end.

Lemma transl_Inop_correct:
 forall (c : PTree.t instruction) (sp: val) (pc : positive)
    (rs : regset) (m : mem) (pc' : RTL.node),
  c ! pc = Some (Inop pc') ->
  exec_instr_prop c sp pc rs m E0 pc' rs m.
Proof.
  intros; red; intros; CleanupHyps.
  exists ls. split.
  CleanupGoal. apply exec_Bgoto. apply exec_refl.
  assumption.
Qed.

Lemma transl_Iop_correct:
  forall (c : PTree.t instruction) (sp: val) (pc : positive)
    (rs : Regmap.t val) (m : mem) (op : operation) (args : list reg)
    (res : reg) (pc' : RTL.node) (v: val),
  c ! pc = Some (Iop op args res pc') ->
  eval_operation ge sp op (rs ## args) = Some v ->
  exec_instr_prop c sp pc rs m E0 pc' (rs # res <- v) m.
Proof.
  intros; red; intros; CleanupHyps.
  caseEq (Regset.mem res live!!pc); intro LV;
  rewrite LV in AG.
  assert (LL: (List.length (List.map assign args) <= 3)%nat).
    rewrite list_length_map. 
    inversion WTI. simpl; omega. simpl; omega.
    eapply length_op_args. eauto.
  assert (DISJ: Loc.disjoint (List.map assign args) temporaries).
    eapply regalloc_disj_temporaries; eauto.
  assert (eval_operation tge sp op (map ls (map assign args)) = Some v).
    replace (map ls (map assign args)) with rs##args. 
    rewrite (eval_operation_preserved symbols_preserved). assumption.
    symmetry. eapply agree_eval_regs; eauto.
  generalize (add_op_correct tge sp op 
               (List.map assign args) (assign res)
               pc' ls m v LL DISJ H1).
  intros [ls' [EX [RES OTHER]]].
  exists ls'. split. 
  CleanupGoal. rewrite LV. exact EX. 
  rewrite CF in H. 
  generalize (regalloc_correct_1 f env live _ _ _ _ ASG H).
  unfold correct_alloc_instr. 
  caseEq (is_move_operation op args).
  (* Special case for moves *)
  intros arg IMO CORR.
  generalize (is_move_operation_correct _ _ IMO).
  intros [EQ1 EQ2]. subst op; subst args. 
  injection H0; intro. rewrite <- H2. 
  apply agree_move_live with f env live ls; auto. 
  rewrite RES. rewrite <- H2. symmetry. eapply agree_eval_reg.
  simpl in AG. eexact AG.
  (* Not a move *)
  intros INMO CORR.
  apply agree_assign_live with f env live ls; auto.
  eapply agree_reg_list_live; eauto.
  (* Result is not live, instruction turned into a nop *)
  exists ls. split.
  CleanupGoal. rewrite LV. 
  apply exec_Bgoto; apply exec_refl.
  apply agree_assign_dead; assumption.
Qed.

Lemma transl_Iload_correct:
 forall (c : PTree.t instruction) (sp: val) (pc : positive)
    (rs : Regmap.t val) (m : mem) (chunk : memory_chunk)
    (addr : addressing) (args : list reg) (dst : reg) (pc' : RTL.node)
    (a v : val),
  c ! pc = Some (Iload chunk addr args dst pc') ->
  eval_addressing ge sp addr rs ## args = Some a ->
  loadv chunk m a = Some v ->
  exec_instr_prop c sp pc rs m E0 pc' rs # dst <- v m.
Proof.
  intros; red; intros; CleanupHyps.
  caseEq (Regset.mem dst live!!pc); intro LV;
  rewrite LV in AG.
  (* dst is live *)
  assert (LL: (List.length (List.map assign args) <= 2)%nat).
    rewrite list_length_map. 
    inversion WTI. 
    eapply length_addr_args. eauto.
  assert (DISJ: Loc.disjoint (List.map assign args) temporaries).
    eapply regalloc_disj_temporaries; eauto.
  assert (EADDR:
      eval_addressing tge sp addr (map ls (map assign args)) = Some a).
    rewrite <- H0. 
    replace (rs##args) with (map ls (map assign args)).
    apply eval_addressing_preserved. exact symbols_preserved.
    eapply agree_eval_regs; eauto.
  generalize (add_load_correct tge sp chunk addr
               (List.map assign args) (assign dst)
               pc' ls m _ _ LL DISJ EADDR H1).
  intros [ls' [EX [RES OTHER]]].
  exists ls'. split. CleanupGoal. rewrite LV. exact EX. 
  rewrite CF in H. 
  generalize (regalloc_correct_1 f env live _ _ _ _ ASG H).
  unfold correct_alloc_instr. intro CORR.
  eapply agree_assign_live; eauto.
  eapply agree_reg_list_live; eauto.
  (* dst is dead *)
  exists ls. split.
  CleanupGoal. rewrite LV. 
  apply exec_Bgoto; apply exec_refl.
  apply agree_assign_dead; auto.
Qed.

Lemma transl_Istore_correct:
 forall (c : PTree.t instruction) (sp: val) (pc : positive)
    (rs : Regmap.t val) (m : mem) (chunk : memory_chunk)
    (addr : addressing) (args : list reg) (src : reg) (pc' : RTL.node)
    (a : val) (m' : mem),
  c ! pc = Some (Istore chunk addr args src pc') ->
  eval_addressing ge sp addr rs ## args = Some a ->
  storev chunk m a rs # src = Some m' ->
  exec_instr_prop c sp pc rs m E0 pc' rs m'.
Proof.
  intros; red; intros; CleanupHyps.
  assert (LL: (List.length (List.map assign args) <= 2)%nat).
    rewrite list_length_map. 
    inversion WTI. 
    eapply length_addr_args. eauto.
  assert (DISJ: Loc.disjoint (List.map assign args) temporaries).
    eapply regalloc_disj_temporaries; eauto.
  assert (SRC: Loc.notin (assign src) temporaries).
    eapply regalloc_not_temporary; eauto.
  assert (EADDR:
      eval_addressing tge sp addr (map ls (map assign args)) = Some a).
    rewrite <- H0.
    replace (rs##args) with (map ls (map assign args)).
    apply eval_addressing_preserved. exact symbols_preserved.
    eapply agree_eval_regs; eauto.
  assert (ESRC: ls (assign src) = rs#src).
    eapply agree_eval_reg. eapply agree_reg_list_live. eauto.
  rewrite <- ESRC in H1.
  generalize (add_store_correct tge sp chunk addr
               (List.map assign args) (assign src)
               pc' ls m m' a LL DISJ SRC EADDR H1).
  intros [ls' [EX RES]].
  exists ls'. split. CleanupGoal. exact EX. 
  rewrite CF in H. 
  generalize (regalloc_correct_1 f env live _ _ _ _ ASG H).
  unfold correct_alloc_instr. intro CORR.
  eapply agree_exten. eauto. 
  eapply agree_reg_live. eapply agree_reg_list_live. eauto.
  assumption.
Qed.  

Lemma transl_Icall_correct:
 forall (c : PTree.t instruction) (sp: val) (pc : positive)
    (rs : regset) (m : mem) (sig : signature) (ros : reg + ident)
    (args : list reg) (res : reg) (pc' : RTL.node)
    (f : RTL.fundef) (vres : val) (m' : mem) (t: trace),
  c ! pc = Some (Icall sig ros args res pc') ->
  RTL.find_function ge ros rs = Some f ->
  RTL.funsig f = sig ->
  RTL.exec_function ge f (rs##args) m t vres m' ->
  exec_function_prop f (rs##args) m t vres m' ->
  exec_instr_prop c sp pc rs m t pc' (rs#res <- vres) m'.
Proof.
  intros; red; intros; CleanupHyps.
  set (los := sum_left_map assign ros).
  assert (FIND: exists tf,
            find_function2 tge los ls = Some tf /\
            transf_fundef f = Some tf).
    unfold los. destruct ros; simpl; simpl in H0.
    apply functions_translated. 
    replace (ls (assign r)) with rs#r. assumption.
    simpl in AG. symmetry; eapply agree_eval_reg.
    eapply agree_reg_list_live; eauto.
    rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
    apply function_ptr_translated. auto.
    discriminate.
  elim FIND; intros tf [AFIND TRF]; clear FIND.
  assert (ASIG: sig = funsig tf).
    rewrite (sig_function_translated _ _ TRF). auto.
  generalize (fun ls => H3 ls tf TRF); intro AEXECF.
  assert (AVARGS: List.map ls (List.map assign args) = rs##args).
    eapply agree_eval_regs; eauto.
  assert (ALARGS: List.length (List.map assign args) = 
                                   List.length sig.(sig_args)).
    inversion WTI. rewrite <- H10. 
    repeat rewrite list_length_map. auto.
  assert (AACCEPT: locs_acceptable (List.map assign args)).
    eapply regsalloc_acceptable; eauto.
  rewrite CF in H. 
  generalize (regalloc_correct_1 f0 env live _ _ _ _ ASG H).
  unfold correct_alloc_instr. intros [CORR1 CORR2].
  assert (ARES: loc_acceptable (assign res)).
    eapply regalloc_acceptable; eauto.
  generalize (add_call_correct tge sp tf _ _ _ _ _ _ _ _ _ pc' _
                AEXECF AFIND ASIG AVARGS ALARGS
                AACCEPT ARES).
  intros [ls' [EX [RES OTHER]]].
  exists ls'.
  split. rewrite CF. CleanupGoal. exact EX.
  simpl. eapply agree_call; eauto.
Qed.

Lemma transl_Ialloc_correct:
  forall (c : PTree.t instruction) (sp: val) (pc : positive)
    (rs : Regmap.t val) (m : mem) (pc': RTL.node) (arg res: reg)
    (sz: int) (m': mem) (b: Values.block),
  c ! pc = Some (Ialloc arg res pc') ->
  rs#arg = Vint sz ->
  Mem.alloc m 0 (Int.signed sz) = (m', b) ->
  exec_instr_prop c sp pc rs m E0 pc' (rs # res <- (Vptr b Int.zero)) m'.
Proof.
  intros; red; intros; CleanupHyps.
  assert (SZ: ls (assign arg) = Vint sz).
    rewrite <- H0. eapply agree_eval_reg. eauto.
  generalize (add_alloc_correct tge sp (assign arg) (assign res)
                                pc' ls m m' sz b SZ H1).
  intros [ls' [EX [RES OTHER]]].
  exists ls'. 
  split. CleanupGoal. exact EX. 
  rewrite CF in H.
  generalize (regalloc_correct_1 f env live _ _ _ _ ASG H). 
  unfold correct_alloc_instr.  intros [CORR1 CORR2].
  eapply agree_call with (args := arg :: nil) (ros := inr reg 1%positive) (ls := ls) (ls' := ls'); eauto.
  intros. apply OTHER. 
  eapply Loc.in_notin_diff; eauto. 
  unfold loc_alloc_argument, destroyed_at_call; simpl; tauto.
  eapply Loc.in_notin_diff; eauto. 
  unfold loc_alloc_argument, destroyed_at_call; simpl; tauto.
  auto.
Qed.

Lemma transl_Icond_true_correct:
 forall (c : PTree.t instruction) (sp: val) (pc : positive)
    (rs : Regmap.t val) (m : mem) (cond : condition) (args : list reg)
    (ifso ifnot : RTL.node),
  c ! pc = Some (Icond cond args ifso ifnot) ->
  eval_condition cond rs ## args = Some true ->
  exec_instr_prop c sp pc rs m E0 ifso rs m.
Proof.
  intros; red; intros; CleanupHyps.
  assert (LL: (List.length (map assign args) <= 3)%nat).
    rewrite list_length_map. inversion WTI. 
    eapply length_cond_args. eauto.
  assert (DISJ: Loc.disjoint (map assign args) temporaries).
    eapply regalloc_disj_temporaries; eauto.
  assert (COND: eval_condition cond (map ls (map assign args)) = Some true).
    replace (map ls (map assign args)) with rs##args. assumption.
    symmetry. eapply agree_eval_regs; eauto.
  generalize (add_cond_correct tge sp _ _ _ ifnot _ m _ _
               LL DISJ COND (refl_equal ifso)).
  intros [ls' [EX OTHER]].
  exists ls'. split.
  CleanupGoal. assumption.
  eapply agree_exten. eauto. eapply agree_reg_list_live. eauto. 
  assumption.
Qed.

Lemma transl_Icond_false_correct:
 forall (c : PTree.t instruction) (sp: val) (pc : positive)
    (rs : Regmap.t val) (m : mem) (cond : condition) (args : list reg)
    (ifso ifnot : RTL.node),
  c ! pc = Some (Icond cond args ifso ifnot) ->
  eval_condition cond rs ## args = Some false ->
  exec_instr_prop c sp pc rs m E0 ifnot rs m.
Proof.
  intros; red; intros; CleanupHyps.
  assert (LL: (List.length (map assign args) <= 3)%nat).
    rewrite list_length_map. inversion WTI. 
    eapply length_cond_args. eauto.
  assert (DISJ: Loc.disjoint (map assign args) temporaries).
    eapply regalloc_disj_temporaries; eauto.
  assert (COND: eval_condition cond (map ls (map assign args)) = Some false).
    replace (map ls (map assign args)) with rs##args. assumption.
    symmetry. eapply agree_eval_regs; eauto.
  generalize (add_cond_correct tge sp _ _ ifso _ _ m _ _
               LL DISJ COND (refl_equal ifnot)).
  intros [ls' [EX OTHER]].
  exists ls'. split.
  CleanupGoal. assumption.
  eapply agree_exten. eauto. eapply agree_reg_list_live. eauto. 
  assumption.
Qed.

Lemma transl_refl_correct:
 forall (c : RTL.code) (sp: val) (pc : RTL.node) (rs : regset)
    (m : mem), exec_instrs_prop c sp pc rs m E0 pc rs m.
Proof.
  intros; red; intros. 
  exists ls. split. apply exec_blocks_refl. assumption.
Qed.

Lemma transl_one_correct:
 forall (c : RTL.code) (sp: val) (pc : RTL.node) (rs : regset)
    (m : mem) (t: trace) (pc' : RTL.node) (rs' : regset) (m' : mem),
  RTL.exec_instr ge c sp pc rs m t pc' rs' m' ->
  exec_instr_prop c sp pc rs m t pc' rs' m' ->
  exec_instrs_prop c sp pc rs m t pc' rs' m'.
Proof.
  intros; red; intros.
  generalize (H0 f env live assign ls CF WT ASG AG).
  intros [ls' [EX AG']].
  exists ls'. split.
  exact EX.
  apply agree_increasing with live!!pc.
  apply analyze_correct. auto. 
  rewrite <- CF. eapply exec_instr_present; eauto.
  rewrite <- CF. auto.
  eapply RTL.successors_correct.
  rewrite <- CF. eexact H. exact AG'.
Qed.

Lemma transl_trans_correct:
 forall (c : RTL.code) (sp: val) (pc1 : RTL.node) (rs1 : regset)
    (m1 : mem) (t1: trace) (pc2 : RTL.node) (rs2 : regset) (m2 : mem)
    (t2: trace) (pc3 : RTL.node) (rs3 : regset) (m3 : mem) (t3: trace),
  RTL.exec_instrs ge c sp pc1 rs1 m1 t1 pc2 rs2 m2 ->
  exec_instrs_prop c sp pc1 rs1 m1 t1 pc2 rs2 m2 ->
  RTL.exec_instrs ge c sp pc2 rs2 m2 t2 pc3 rs3 m3 ->
  exec_instrs_prop c sp pc2 rs2 m2 t2 pc3 rs3 m3 ->
  t3 = t1 ** t2 ->
  exec_instrs_prop c sp pc1 rs1 m1 t3 pc3 rs3 m3.
Proof.
  intros; red; intros.
  assert (VALIDPC2: c!pc2 <> None).
    eapply exec_instrs_present; eauto.
  generalize (H0 f env live assign ls CF WT ANL ASG AG VALIDPC2).
  intros [ls1 [EX1 AG1]]. 
  generalize (H2 f env live assign ls1 CF WT ANL ASG AG1 VALIDPC'). 
  intros [ls2 [EX2 AG2]].
  exists ls2. split.
  eapply exec_blocks_trans. eexact EX1. eexact EX2. auto.
  exact AG2.
Qed.

Remark regset_mem_reg_list_dead:
  forall rl r live,
  Regset.mem r (reg_list_dead rl live) = true ->
  ~(In r rl) /\ Regset.mem r live = true.
Proof.
  induction rl; simpl; intros.
  tauto.
  elim (IHrl r (reg_dead a live) H). intros.
  assert (a <> r). red; intro; subst r. 
  rewrite Regset.mem_remove_same in H1. discriminate.
  rewrite Regset.mem_remove_other in H1; auto.
  tauto. 
Qed. 

Lemma transf_entrypoint_correct:
  forall f env live assign c ls args sp m,
  wt_function f env ->
  regalloc f live (live0 f live) env = Some assign ->
  c!(RTL.fn_nextpc f) = None ->
  List.map ls (loc_parameters (RTL.fn_sig f)) = args ->
  (forall ofs ty, ls (S (Local ofs ty)) = Vundef) ->
  let tc := transf_entrypoint f live assign c in
  exists ls',
  exec_blocks tge tc sp (RTL.fn_nextpc f) ls m E0
                        (Cont (RTL.fn_entrypoint f)) ls' m /\
  agree assign (transfer f (RTL.fn_entrypoint f) live!!(RTL.fn_entrypoint f))
        (init_regs args (RTL.fn_params f)) ls'.
Proof.
  intros until m.
  unfold transf_entrypoint. 
  set (oldentry := RTL.fn_entrypoint f).
  set (newentry := RTL.fn_nextpc f).
  set (params := RTL.fn_params f).
  set (undefs := Regset.elements (reg_list_dead params (transfer f oldentry live!!oldentry))).
  intros.

  assert (A1: List.length (List.map assign params) =
              List.length (RTL.fn_sig f).(sig_args)).
    rewrite <- (wt_params _ _ H).  
    repeat (rewrite list_length_map). auto.
  assert (A2: Loc.norepet (List.map assign (RTL.fn_params f))).
    eapply regalloc_norepet_norepet; eauto.
    eapply regalloc_correct_2; eauto.
    eapply wt_norepet; eauto.
  assert (A3: locs_acceptable (List.map assign (RTL.fn_params f))).
    eapply regsalloc_acceptable; eauto.
  assert (A4: Loc.disjoint 
                (List.map assign (RTL.fn_params f))
                (List.map assign undefs)).
    red. intros ap au INAP INAU.
    generalize (list_in_map_inv _ _ _ INAP).
    intros [p [AP INP]]. clear INAP; subst ap.
    generalize (list_in_map_inv _ _ _ INAU).
    intros [u [AU INU]]. clear INAU; subst au.
    generalize (Regset.elements_complete _ _ INU). intro.
    generalize (regset_mem_reg_list_dead _ _ _ H4).
    intros [A B]. 
    eapply regalloc_noteq_diff; eauto.
    eapply regalloc_correct_3; eauto.
    red; intro; subst u. elim (A INP).
  assert (A5: forall l, In l (List.map assign undefs) -> loc_acceptable l).
    intros. 
    generalize (list_in_map_inv _ _ _ H4).
    intros [r [AR INR]]. clear H4; subst l.
    eapply regalloc_acceptable; eauto.
  generalize (add_entry_correct
    tge sp (RTL.fn_sig f)
    (List.map assign (RTL.fn_params f))
    (List.map assign undefs)
    oldentry ls m A1 A2 A3 A4 A5 H3).
  intros [ls1 [EX1 [PARAMS1 UNDEFS1]]].
  exists ls1. 
  split. eapply exec_blocks_one.
  rewrite PTree.gss. reflexivity.
  assumption.
  change (transfer f oldentry live!!oldentry)
    with (live0 f live).
  unfold params; eapply agree_parameters; eauto.
  change Regset.elt with reg in PARAMS1. 
  rewrite PARAMS1. assumption.
  fold oldentry; fold params. intros.
  apply UNDEFS1. apply in_map. 
  unfold undefs; apply Regset.elements_correct; auto.
Qed.

Lemma transl_function_correct:
 forall (f : RTL.function) (m m1 : mem) (stk : Values.block)
    (args : list val) (t: trace) (pc : RTL.node) (rs : regset) (m2 : mem)
    (or : option reg) (vres : val),
  alloc m 0 (RTL.fn_stacksize f) = (m1, stk) ->
  RTL.exec_instrs ge (RTL.fn_code f) (Vptr stk Int.zero)
    (RTL.fn_entrypoint f) (init_regs args (fn_params f)) m1 t pc rs m2 ->
  exec_instrs_prop (RTL.fn_code f) (Vptr stk Int.zero)
    (RTL.fn_entrypoint f) (init_regs args (fn_params f)) m1 t pc rs m2 ->
  (RTL.fn_code f) ! pc = Some (Ireturn or) ->
  vres = regmap_optget or Vundef rs ->
  exec_function_prop (Internal f) args m t vres (free m2 stk).
Proof.
  intros; red; intros until tf.
  unfold transf_fundef, transf_partial_fundef, transf_function.
  caseEq (type_function f).
  intros env TRF. 
  caseEq (analyze f).
  intros live ANL.
  change (transfer f (RTL.fn_entrypoint f) live!!(RTL.fn_entrypoint f))
    with (live0 f live).
  caseEq (regalloc f live (live0 f live) env).
  intros alloc ASG.
  set (tc1 := PTree.map (transf_instr f live alloc) (RTL.fn_code f)).
  set (tc2 := transf_entrypoint f live alloc tc1).
  intro EQ; injection EQ; intro TF; clear EQ. intro VARGS. 
  generalize (type_function_correct _ _ TRF); intro WTF.
  assert (NEWINSTR: tc1!(RTL.fn_nextpc f) = None).
    unfold tc1; rewrite PTree.gmap. unfold option_map.
    elim (RTL.fn_code_wf f (fn_nextpc f)); intro.
    elim (Plt_ne _ _ H4). auto.
    rewrite H4. auto.
  pose (ls1 := call_regs ls).
  assert (VARGS1: List.map ls1 (loc_parameters (RTL.fn_sig f)) = args).
    replace (RTL.fn_sig f) with (funsig tf).
    rewrite <- VARGS. unfold loc_parameters.
    rewrite list_map_compose. apply list_map_exten.
    intros. symmetry. unfold ls1. eapply call_regs_param_of_arg; eauto.
    rewrite <- TF; reflexivity.
  assert (VUNDEFS: forall (ofs : Z) (ty : typ), ls1 (S (Local ofs ty)) = Vundef).
    intros. reflexivity.    
  generalize (transf_entrypoint_correct f env live alloc
                tc1 ls1 args (Vptr stk Int.zero) m1
                WTF ASG NEWINSTR VARGS1 VUNDEFS).
  fold tc2. intros [ls2 [EX2 AGREE2]].
  assert (VALIDPC: f.(RTL.fn_code)!pc <> None). congruence.
  generalize (H1 f env live alloc ls2
               (refl_equal _) WTF ANL ASG AGREE2 VALIDPC).
  fold tc1. intros [ls3 [EX3 AGREE3]].
  generalize (add_return_correct tge (Vptr stk Int.zero) (RTL.fn_sig f) 
                            (option_map alloc or) ls3 m2).
  intros [ls4 [EX4 RES4]].
  exists ls4. 
  (* Execution *)
  split. rewrite <- TF; apply exec_funct_internal with m1; simpl.
  assumption.
  fold ls1. 
  eapply exec_blocks_trans. eexact EX2. 
  apply exec_blocks_extends with tc1.
  intro p. unfold tc2. unfold transf_entrypoint.
  case (peq p (fn_nextpc f)); intro.
  subst p. right. unfold tc1; rewrite PTree.gmap. 
  elim (RTL.fn_code_wf f (fn_nextpc f)); intro.
  elim (Plt_ne _ _ H4); auto. rewrite H4; reflexivity.
  left; apply PTree.gso; auto.
  eapply exec_blocks_trans. eexact EX3.
  eapply exec_blocks_one. 
  unfold tc1. rewrite PTree.gmap. rewrite H2. simpl. reflexivity.
  eexact EX4. reflexivity. traceEq.
  destruct or.
  simpl in RES4. simpl in H3.
  rewrite H3. rewrite <- TF; simpl. rewrite RES4.
  eapply agree_eval_reg; eauto.
  unfold transfer in AGREE3; rewrite H2 in AGREE3. 
  unfold reg_option_live in AGREE3. eexact AGREE3.
  simpl in RES4. simpl in H3.
  rewrite <- TF; simpl. congruence.
  intros; discriminate.
  intros; discriminate.
  intros; discriminate.
Qed.

Lemma transl_external_function_correct:
  forall (ef : external_function) (args : list val) (m : mem)
         (t: trace) (res: val),
  event_match ef args t res ->
  exec_function_prop (External ef) args m t res m.
Proof.
  intros; red; intros.
  simpl in H0. 
  simplify_eq H0; intro.
  exists (Locmap.set (R (loc_result (funsig tf))) res ls); split.
  subst tf. eapply exec_funct_external; eauto. 
  apply Locmap.gss.
Qed.

(** The correctness of the code transformation is obtained by
  structural induction (and case analysis on the last rule used)
  on the RTL evaluation derivation.
  This is a 3-way mutual induction, using [exec_instr_prop],
  [exec_instrs_prop] and [exec_function_prop] as the induction
  hypotheses, and the lemmas above as cases for the induction. *)

Theorem transl_function_correctness:
  forall f args m t res m',
  RTL.exec_function ge f args m t res m' ->
  exec_function_prop f args m t res m'.
Proof
  (exec_function_ind_3 ge 
          exec_instr_prop 
          exec_instrs_prop
          exec_function_prop
         
          transl_Inop_correct
          transl_Iop_correct
          transl_Iload_correct
          transl_Istore_correct
          transl_Icall_correct
          transl_Ialloc_correct
          transl_Icond_true_correct
          transl_Icond_false_correct

          transl_refl_correct
          transl_one_correct
          transl_trans_correct

          transl_function_correct
          transl_external_function_correct).

(** The semantic equivalence between the original and transformed programs
  follows easily. *)

Theorem transl_program_correct:
  forall (t: trace) (r: val),
  RTL.exec_program prog t r -> LTL.exec_program tprog t r.
Proof.
  intros t r [b [f [m [FIND1 [FIND2 [SIG EXEC]]]]]].
  generalize (function_ptr_translated _ _ FIND2).
  intros [tf [TFIND TRF]].
  assert (SIG2: funsig tf = mksignature nil (Some Tint)).
    rewrite <- SIG. apply sig_function_translated; auto.
  assert (VPARAMS: map (Locmap.init Vundef) (loc_arguments (funsig tf)) = nil).
    rewrite SIG2. reflexivity.
  generalize (transl_function_correctness _ _ _ _ _ _ EXEC
                (Locmap.init Vundef) tf TRF VPARAMS).
  intros [ls' [TEXEC RES]].
  red. exists b; exists tf; exists ls'; exists m.
  split. rewrite symbols_preserved. 
  rewrite (transform_partial_program_main _ _ TRANSF).
  assumption. 
  split. assumption.
  split. assumption.
  split. replace (Genv.init_mem tprog) with (Genv.init_mem prog).
  assumption. symmetry. 
  exact (Genv.init_mem_transf_partial _ _ TRANSF).
  assumption.
Qed.

End PRESERVATION.
