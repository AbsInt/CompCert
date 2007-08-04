(** Correctness proof for the [Allocation] pass (translation from
  RTL to LTL). *)

Require Import FSets.
Require Import SetoidList.
Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Smallstep.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import RTLtyping.
Require Import Locations.
Require Import Conventions.
Require Import Coloring.
Require Import Coloringproof.
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
  elim n0. apply loc_result_caller_save.
Qed.

(** Function arguments for a tail call are preserved by a
    [return_regs] operation. *)

Lemma return_regs_arguments:
  forall sig caller callee,
  tailcall_possible sig ->
  map (LTL.return_regs caller callee) (loc_arguments sig) =
  map callee (loc_arguments sig).
Proof.
  intros. apply list_map_exten; intros.
  generalize (H x H0). destruct x; intro.
  unfold LTL.return_regs.
  destruct (In_dec Loc.eq (R m) temporaries). auto.
  destruct (In_dec Loc.eq (R m) destroyed_at_call). auto.
  elim n0. eapply arguments_caller_save; eauto.
  contradiction.
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

(** Characterization of parallel assignments. *)

Lemma parmov_spec:
  forall ls srcs dsts,
  Loc.norepet dsts -> List.length srcs = List.length dsts ->
  List.map (LTL.parmov srcs dsts ls) dsts = List.map ls srcs /\
  (forall l, Loc.notin l dsts -> LTL.parmov srcs dsts ls l = ls l).
Proof.
  induction srcs; destruct dsts; simpl; intros; try discriminate.
  auto.
  inv H. inv H0. destruct (IHsrcs _ H4 H1). split.
  f_equal. apply Locmap.gss. rewrite <- H. apply list_map_exten; intros.
  symmetry. apply Locmap.gso. eapply Loc.in_notin_diff; eauto. 
  intros x [A B]. rewrite Locmap.gso; auto. apply Loc.diff_sym; auto.
Qed.

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

Lemma regalloc_noteq_diff:
  forall r1 l2,
  alloc r1 <> l2 -> Loc.diff (alloc r1) l2.
Proof.
  intros. apply loc_acceptable_noteq_diff. 
  eapply regalloc_acceptable; eauto.
  auto.
Qed.   

Lemma regalloc_notin_notin:
  forall r ll,
  ~(In (alloc r) ll) -> Loc.notin (alloc r) ll.
Proof.
  intros. apply loc_acceptable_notin_notin. 
  eapply regalloc_acceptable; eauto. auto.
Qed.

Lemma regalloc_notin_notin_2:
  forall l rl,
  ~(In l (map alloc rl)) -> Loc.notin l (map alloc rl).
Proof.
  induction rl; simpl; intros. auto. 
  split. apply Loc.diff_sym. apply regalloc_noteq_diff. tauto.
  apply IHrl. tauto.
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
Module RegsetP := Properties(Regset).

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
  forall (r: reg), Regset.In r live -> Val.lessdef (rs#r) (ls (assign r)).

(** What follows is a long list of lemmas expressing properties
  of the [agree_live_regs] predicate that are useful for the 
  semantic equivalence proof.  First: two register sets that agree
  on a given set of live registers also agree on a subset of
  those live registers. *)

Lemma agree_increasing:
  forall live1 live2 rs ls,
  RegsetLat.ge live1 live2 -> agree live1 rs ls ->
  agree live2 rs ls.
Proof.
  unfold agree; intros. 
  apply H0. apply H. auto.
Qed.

Lemma agree_succ:
  forall n s rs ls live,
  analyze f = Some live ->
  In s (RTL.successors f n) ->
  agree live!!n rs ls ->
  agree (transfer f s live!!s) rs ls.
Proof.
  intros.
  elim (RTL.fn_code_wf f n); intro.
  elim (RTL.fn_code_wf f s); intro.
  apply agree_increasing with (live!!n).
  eapply DS.fixpoint_solution. unfold analyze in H; eauto.
  auto. auto. auto. auto.
  unfold transfer. rewrite H3.
  red; intros. elim (Regset.empty_1 _ H4).
  unfold RTL.successors in H0; rewrite H2 in H0; elim H0.
Qed.

(** Some useful special cases of [agree_increasing]. *)


Lemma agree_reg_live:
  forall r live rs ls,
  agree (reg_live r live) rs ls -> agree live rs ls.
Proof.
  intros. apply agree_increasing with (reg_live r live); auto.
  red. apply RegsetP.subset_add_2. apply RegsetP.subset_refl.
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
  agree (reg_live r live) rs ls -> Val.lessdef (rs#r) (ls (assign r)).
Proof.
  intros. apply H. apply Regset.add_1. auto. 
Qed.

(** Same, for a list of registers. *)

Lemma agree_eval_regs:
  forall rl live rs ls,
  agree (reg_list_live rl live) rs ls ->
  Val.lessdef_list (rs##rl) (List.map ls (List.map assign rl)).
Proof.
  induction rl; simpl; intros.
  constructor.
  constructor.
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
  ~Regset.In r live ->
  agree live rs ls ->
  agree live (rs#r <- v) ls.
Proof.
  unfold agree; intros.
  case (Reg.eq r r0); intro.
  subst r0. contradiction.
  rewrite Regmap.gso; auto. 
Qed.

(** Setting [r] to value [v] in [rs]
  and simultaneously setting [assign r] to value [v] in [ls]
  preserves agreement, provided that all live registers except [r]
  are mapped to locations other than that of [r]. *)

Lemma agree_assign_live:
  forall live r rs ls v v',
  (forall s,
     Regset.In s live -> s <> r -> assign s <> assign r) ->
  Val.lessdef v v' ->
  agree (reg_dead r live) rs ls ->
  agree live (rs#r <- v) (Locmap.set (assign r) v' ls).
Proof.
  unfold agree; intros. rewrite Regmap.gsspec.
  destruct (peq r0 r).
  subst r0. rewrite Locmap.gss. auto.
  rewrite Locmap.gso. apply H1. apply Regset.remove_2; auto.
  eapply regalloc_noteq_diff. eauto. apply sym_not_equal. apply H. auto.  auto.
Qed.

(** This is a special case of the previous lemma where the value [v]
  being stored is not arbitrary, but is the value of
  another register [arg].  (This corresponds to a register-register move
  instruction.)  In this case, the condition can be weakened:
  it suffices that all live registers except [arg] and [res] 
  are mapped to locations other than that of [res]. *)

Lemma agree_move_live:
  forall live arg res rs (ls: locset),
  (forall r,
     Regset.In r live -> r <> res -> r <> arg -> 
     assign r <> assign res) ->
  agree (reg_live arg (reg_dead res live)) rs ls ->
  agree live (rs#res <- (rs#arg)) (Locmap.set (assign res) (ls (assign arg)) ls).
Proof.
  unfold agree; intros. rewrite Regmap.gsspec. destruct (peq r res). 
  subst r. rewrite Locmap.gss. apply H0.
  apply Regset.add_1; auto.
  destruct (Reg.eq r arg).
  subst r.
  replace (Locmap.set (assign res) (ls (assign arg)) ls (assign arg))
     with (ls (assign arg)).
  apply H0. apply Regset.add_1. auto.
  symmetry. destruct (Loc.eq (assign arg) (assign res)).
  rewrite <- e. apply Locmap.gss.
  apply Locmap.gso. eapply regalloc_noteq_diff; eauto.

  rewrite Locmap.gso. apply H0. apply Regset.add_2. apply Regset.remove_2. auto. auto.
  eapply regalloc_noteq_diff; eauto. apply sym_not_equal. apply H; auto.
Qed.

(** Yet another special case corresponding to the case of 
  a redundant move. *)

Lemma agree_redundant_move_live:
  forall live arg res rs (ls: locset),
  (forall r,
     Regset.In r live -> r <> res -> r <> arg -> 
     assign r <> assign res) ->
  agree (reg_live arg (reg_dead res live)) rs ls ->
  assign res = assign arg ->
  agree live (rs#res <- (rs#arg)) ls.
Proof.
  intros. 
  apply agree_exten with (Locmap.set (assign res) (ls (assign arg)) ls).
  eapply agree_move_live; eauto. 
  intros. symmetry. rewrite H1. destruct (Loc.eq l (assign arg)).
  subst l. apply Locmap.gss.
  apply Locmap.gso. eapply regalloc_noteq_diff; eauto. 
Qed.

(** This complicated lemma states agreement between the states after
  a function call, provided that the states before the call agree
  and that calling conventions are respected. *)

Lemma agree_call:
  forall live args ros res rs v (ls ls': locset),
  (forall r,
    Regset.In r live -> r <> res ->
    ~(In (assign r) Conventions.destroyed_at_call)) ->
  (forall r,
    Regset.In r live -> r <> res -> assign r <> assign res) ->
  Val.lessdef v (ls' (assign res)) ->
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
  apply Regset.remove_2; auto. 
  eapply regalloc_notin_notin; eauto. 
  eapply regalloc_acceptable; eauto.
  eapply regalloc_noteq_diff; eauto.
Qed.

(** Agreement between the initial register set at RTL function entry
  and the location set at LTL function entry. *)

Lemma agree_init_regs:
  forall rl vl ls live,
  (forall r1 r2,
    In r1 rl -> Regset.In r2 live -> r1 <> r2 ->
    assign r1 <> assign r2) ->
  Val.lessdef_list vl (List.map ls (List.map assign rl)) ->
  agree live (init_regs vl rl) ls.
Proof.
  induction rl; simpl; intros.
  red; intros. rewrite Regmap.gi. auto.
  inv H0. 
  assert (agree live (init_regs vl1 rl) ls).
  apply IHrl. intros. apply H. tauto. auto. auto. auto.
  red; intros. case (Reg.eq a r); intro.
  subst r. rewrite Regmap.gss. auto.
  rewrite Regmap.gso; auto.
Qed.

Lemma agree_parameters:
  forall vl ls,
  let params := f.(RTL.fn_params) in
  Val.lessdef_list vl (List.map ls (List.map assign params)) ->
  agree (live0 f flive)
        (init_regs vl params) 
        ls.
Proof.
  intros. apply agree_init_regs. 
  intros. eapply regalloc_correct_3; eauto.
  auto.
Qed.

End AGREE.

(** * Preservation of semantics *)

(** We now show that the LTL code reflecting register allocation has
  the same semantics as the original RTL code.  We start with
  standard properties of translated functions and 
  global environments in the original and translated code. *)

Section PRESERVATION.

Variable prog: RTL.program.
Variable tprog: LTL.program.
Hypothesis TRANSF: transf_program prog = OK tprog.

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
  Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_transf_partial transf_fundef TRANSF).

Lemma function_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial transf_fundef TRANSF).

Lemma sig_function_translated:
  forall f tf,
  transf_fundef f = OK tf ->
  LTL.funsig tf = RTL.funsig f.
Proof.
  intros f tf. destruct f; simpl.
  unfold transf_function.
  destruct (type_function f).
  destruct (analyze f).
  destruct (regalloc f t).
  intro. monadInv H. inv EQ. auto.  
  simpl; congruence. simpl; congruence. simpl; congruence.
  intro EQ; inv EQ. auto.
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
  Hypotheses: the left vertical arrow represents a transition in the
  original RTL code.  The top horizontal bar is the [match_states]
  relation defined below.  It implies agreement between
  the RTL register map [rs] and the LTL location map [ls]
  over the pseudo-registers live before the RTL instruction at [pc].  

  Conclusions: the right vertical arrow is an [exec_instrs] transition
  in the LTL code generated by translation of the current function.
  The bottom horizontal bar is the [match_states] relation.
*)

Inductive match_stackframes: list RTL.stackframe -> list LTL.stackframe -> signature -> Prop :=
  | match_stackframes_nil: forall ty_args,
      match_stackframes nil nil (mksignature ty_args (Some Tint))
  | match_stackframes_cons:
      forall s ts sig res f sp pc rs ls env live assign,
      match_stackframes s ts (RTL.fn_sig f) ->
      wt_function f env ->
      analyze f = Some live ->
      regalloc f live (live0 f live) env = Some assign ->
      (forall rv ls1,
        (forall l, Loc.notin l destroyed_at_call -> loc_acceptable l -> ls1 l = ls l) ->
        Val.lessdef rv (ls1 (R (loc_result sig))) ->
        agree assign (transfer f pc live!!pc)
              (rs#res <- rv)
              (Locmap.set (assign res) (ls1 (R (loc_result sig))) ls1)) ->
      match_stackframes
        (RTL.Stackframe res (RTL.fn_code f) sp pc rs :: s)
        (LTL.Stackframe (assign res) (transf_fun f live assign) sp ls pc :: ts)
        sig.

Inductive match_states: RTL.state -> LTL.state -> Prop :=
  | match_states_intro:
      forall s f sp pc rs m ts ls tm live assign env
      (STACKS: match_stackframes s ts (RTL.fn_sig f))
      (WT: wt_function f env)
      (ANL: analyze f = Some live)
      (ASG: regalloc f live (live0 f live) env = Some assign)
      (AG: agree assign (transfer f pc live!!pc) rs ls)
      (MMD: Mem.lessdef m tm),
      match_states (RTL.State s (RTL.fn_code f) sp pc rs m)
                   (LTL.State ts (transf_fun f live assign) sp pc ls tm)
  | match_states_call:
      forall s f args m ts tf ls tm,
      match_stackframes s ts (RTL.funsig f) ->
      transf_fundef f = OK tf ->
      Val.lessdef_list args (List.map ls (loc_arguments (funsig tf))) ->
      Mem.lessdef m tm ->
      (forall l, Loc.notin l destroyed_at_call -> loc_acceptable l -> ls l = parent_locset ts l) ->
      match_states (RTL.Callstate s f args m)
                   (LTL.Callstate ts tf ls tm)
  | match_states_return:
      forall s v m ts sig ls tm,
      match_stackframes s ts sig ->
      Val.lessdef v (ls (R (loc_result sig))) ->
      Mem.lessdef m tm ->
      (forall l, Loc.notin l destroyed_at_call -> loc_acceptable l -> ls l = parent_locset ts l) ->
      match_states (RTL.Returnstate s v m)
                   (LTL.Returnstate ts sig ls tm).

Remark match_stackframes_change:
  forall s ts sig,
  match_stackframes s ts sig ->
  forall sig',
  sig_res sig' = sig_res sig ->
  match_stackframes s ts sig'.
Proof.
  induction 1; intros.
  destruct sig'. simpl in H; inv H. constructor.
  assert (loc_result sig' = loc_result sig).
  unfold loc_result. rewrite H4; auto.
  econstructor; eauto.
  rewrite H5. auto. 
Qed.

(** The simulation proof is by case analysis over the RTL transition
  taken in the source program. *)

Ltac CleanupHyps :=
  match goal with
  | H: (match_states _ _) |- _ =>
      inv H; CleanupHyps
  | H1: (PTree.get _ _ = Some _),
    H2: (agree _ (transfer _ _ _) _ _) |- _ =>
      unfold transfer in H2; rewrite H1 in H2; simpl in H2; CleanupHyps
  | _ => idtac
  end.

Ltac WellTypedHyp :=
  match goal with
  | H1: (PTree.get _ _ = Some _),
    H2: (wt_function _ _) |- _ =>
      let R := fresh "WTI" in (
      generalize (wt_instrs _ _ H2 _ _ H1); intro R)
  | _ => idtac
  end.

Ltac TranslInstr :=
  match goal with
  | H: (PTree.get _ _ = Some _) |- _ =>
      simpl; rewrite PTree.gmap; rewrite H; simpl; auto
  end.

Ltac MatchStates :=
  match goal with
  | |- match_states (RTL.State _ _ _ _ _ _) (LTL.State _ _ _ _ _ _) =>
      eapply match_states_intro; eauto; MatchStates
  | H: (PTree.get ?pc _ = Some _) |- agree _ _ _ _ =>
      eapply agree_succ with (n := pc); eauto; MatchStates
  | H: (PTree.get _ _ = Some _) |- In _ (RTL.successors _ _) =>
      unfold RTL.successors; rewrite H; auto with coqlib
  | _ => idtac
  end.


Lemma transl_find_function:
  forall ros f args lv rs ls alloc,
  RTL.find_function ge ros rs = Some f ->
  agree alloc (reg_list_live args (reg_sum_live ros lv)) rs ls ->
  exists tf,
    LTL.find_function tge (sum_left_map alloc ros) ls = Some tf /\
    transf_fundef f = OK tf.
Proof.
  intros; destruct ros; simpl in *.
  assert (Val.lessdef (rs#r) (ls (alloc r))).
    eapply agree_eval_reg. eapply agree_reg_list_live; eauto.
  inv H1. apply functions_translated. auto.
  exploit Genv.find_funct_inv; eauto. intros [b EQ]. congruence.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply function_ptr_translated. auto. discriminate.
Qed.

Theorem transl_step_correct:
  forall s1 t s2, RTL.step ge s1 t s2 ->
  forall s1', match_states s1 s1' ->
  exists s2', LTL.step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros; CleanupHyps; WellTypedHyp.

  (* Inop *)
  econstructor; split.
  eapply exec_Lnop. TranslInstr. MatchStates.

  (* Iop *)
  generalize (PTree.gmap (transf_instr f live assign) pc (RTL.fn_code f)).
  rewrite H. simpl. 
  caseEq (Regset.mem res live!!pc); intro LV;
  rewrite LV in AG.
  generalize (Regset.mem_2 _ _ LV). intro LV'.
  generalize (regalloc_correct_1 f env live _ _ _ _ ASG H).
  unfold correct_alloc_instr, is_redundant_move.
  caseEq (is_move_operation op args).
  (* Special case for moves *)
  intros arg IMO CORR.
  generalize (is_move_operation_correct _ _ IMO).
  intros [EQ1 EQ2]. subst op; subst args. 
  injection H0; intro.
  destruct (Loc.eq (assign arg) (assign res)); intro CODE.
  (* sub-case: redundant move *)
  econstructor; split. eapply exec_Lnop; eauto.
  MatchStates. 
  rewrite <- H1. eapply agree_redundant_move_live; eauto.
  (* sub-case: non-redundant move *)
  econstructor; split. eapply exec_Lop; eauto. simpl. eauto.
  MatchStates.
  rewrite <- H1. eapply agree_move_live; eauto.
  (* Not a move *)
  intros INMO CORR CODE.
  assert (exists v1,
          eval_operation tge sp op (map ls (map assign args)) tm = Some v1
          /\ Val.lessdef v v1).
    apply eval_operation_lessdef with m (rs##args); auto.
    eapply agree_eval_regs; eauto.
    rewrite (eval_operation_preserved symbols_preserved). assumption.
  destruct H1 as [v1 [EV VMD]].
  econstructor; split. eapply exec_Lop; eauto. 
  MatchStates. 
  apply agree_assign_live with f env live; auto.
  eapply agree_reg_list_live; eauto.
  (* Result is not live, instruction turned into a nop *)
  intro CODE. econstructor; split. eapply exec_Lnop; eauto.
  MatchStates. apply agree_assign_dead; auto. 
  red; intro. exploit Regset.mem_1; eauto. congruence.

  (* Iload *)
  caseEq (Regset.mem dst live!!pc); intro LV;
  rewrite LV in AG.
  (* dst is live *)
  exploit Regset.mem_2; eauto. intro LV'.
  assert (exists a',
      eval_addressing tge sp addr (map ls (map assign args)) = Some a'
      /\ Val.lessdef a a').
    apply eval_addressing_lessdef with (rs##args). 
    eapply agree_eval_regs; eauto.
    rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  destruct H2 as [a' [EVAL VMD]].
  exploit Mem.loadv_lessdef; eauto. 
  intros [v' [LOADV VMD2]].
  econstructor; split.
  eapply exec_Lload; eauto. TranslInstr. rewrite LV; auto.
  generalize (regalloc_correct_1 f env live _ _ _ _ ASG H).
  unfold correct_alloc_instr. intro CORR.
  MatchStates. 
  eapply agree_assign_live; eauto.
  eapply agree_reg_list_live; eauto.
  (* dst is dead *)
  econstructor; split.
  eapply exec_Lnop. TranslInstr. rewrite LV; auto.
  MatchStates. apply agree_assign_dead; auto.
  red; intro; exploit Regset.mem_1; eauto. congruence.

  (* Istore *)
  assert (exists a',
      eval_addressing tge sp addr (map ls (map assign args)) = Some a'
      /\ Val.lessdef a a').
    apply eval_addressing_lessdef with (rs##args). 
    eapply agree_eval_regs; eauto.
    rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  destruct H2 as [a' [EVAL VMD]].
  assert (ESRC: Val.lessdef rs#src (ls (assign src))).
    eapply agree_eval_reg. eapply agree_reg_list_live. eauto.
  assert (exists tm', storev chunk tm a' (ls (assign src)) = Some tm'
                     /\ Mem.lessdef m' tm').
    eapply Mem.storev_lessdef; eauto. 
  destruct H2 as [m1' [STORE MMD']].
  econstructor; split.
  eapply exec_Lstore; eauto. TranslInstr.
  MatchStates. eapply agree_reg_live. eapply agree_reg_list_live. eauto.

  (* Icall *)
  exploit transl_find_function; eauto.  intros [tf [TFIND TF]].
  generalize (regalloc_correct_1 f0 env live _ _ _ _ ASG H).  unfold correct_alloc_instr. intros [CORR1 CORR2].
  exploit (parmov_spec ls (map assign args) 
                            (loc_arguments (RTL.funsig f))).
  apply loc_arguments_norepet.
  rewrite loc_arguments_length. inv WTI.
  rewrite <- H7. repeat rewrite list_length_map. auto.
  intros [PM1 PM2].  
  econstructor; split. 
  eapply exec_Lcall; eauto. TranslInstr.
  rewrite (sig_function_translated _ _ TF). eauto.
  rewrite (sig_function_translated _ _ TF).
  econstructor; eauto.
  econstructor; eauto.
  intros. eapply agree_succ with (n := pc); eauto.
  unfold RTL.successors; rewrite H; auto with coqlib.
  eapply agree_call with (ls := ls); eauto.
  rewrite Locmap.gss. auto.
  intros. rewrite Locmap.gso. rewrite H1; auto. apply PM2; auto.
  eapply arguments_not_preserved; eauto. apply Loc.diff_sym; auto.
  rewrite (sig_function_translated _ _ TF).
  change Regset.elt with reg in PM1. 
  rewrite PM1. eapply agree_eval_regs; eauto. 

  (* Itailcall *)
  exploit transl_find_function; eauto.  intros [tf [TFIND TF]].
  exploit (parmov_spec ls (map assign args) 
                            (loc_arguments (RTL.funsig f))).
  apply loc_arguments_norepet.
  rewrite loc_arguments_length. inv WTI.
  rewrite <- H6. repeat rewrite list_length_map. auto.
  intros [PM1 PM2].  
  econstructor; split. 
  eapply exec_Ltailcall; eauto. TranslInstr.
  rewrite (sig_function_translated _ _ TF). eauto.
  rewrite (sig_function_translated _ _ TF).
  econstructor; eauto.
  apply match_stackframes_change with (RTL.fn_sig f0); auto.
  inv WTI. auto.
  rewrite (sig_function_translated _ _ TF).
  rewrite return_regs_arguments. 
  change Regset.elt with reg in PM1. 
  rewrite PM1. eapply agree_eval_regs; eauto.
  inv WTI; auto.
  apply free_lessdef; auto.
  intros. rewrite return_regs_not_destroyed; auto. 

  (* Ialloc *)
  assert (Val.lessdef (Vint sz) (ls (assign arg))).
    rewrite <- H0. eapply agree_eval_reg. eauto.
  inversion H2. subst v. 
  pose (ls1 := Locmap.set (R loc_alloc_argument) (ls (assign arg)) ls).
  pose (ls2 := Locmap.set (R loc_alloc_result) (Vptr b Int.zero) ls1).
  pose (ls3 := Locmap.set (assign res) (ls2 (R loc_alloc_result)) ls2).
  caseEq (alloc tm 0 (Int.signed sz)). intros tm' b1 ALLOC1.
  exploit Mem.alloc_lessdef; eauto. intros [EQ MMD1]. subst b1.
  exists (State ts (transf_fun f live assign) sp pc' ls3 tm'); split.
  unfold ls3, ls2, ls1. eapply exec_Lalloc; eauto. TranslInstr.
  generalize (regalloc_correct_1 f env live _ _ _ _ ASG H). 
  unfold correct_alloc_instr.  intros [CORR1 CORR2].
  MatchStates.
  eapply agree_call with (args := arg :: nil) (ros := inr reg 1%positive) (ls := ls); eauto.
  unfold ls3; rewrite Locmap.gss. 
  unfold ls2; rewrite Locmap.gss. auto.
  intros. unfold ls3; rewrite Locmap.gso.
  unfold ls2; rewrite Locmap.gso. 
  unfold ls1; apply Locmap.gso.
  apply Loc.diff_sym. eapply Loc.in_notin_diff; eauto. 
  unfold loc_alloc_argument, destroyed_at_call; simpl; tauto.
  apply Loc.diff_sym. eapply Loc.in_notin_diff; eauto. 
  unfold loc_alloc_result, destroyed_at_call; simpl; tauto.
  apply Loc.diff_sym; auto.

  (* Icond, true *)
  assert (COND: eval_condition cond (map ls (map assign args)) tm = Some true).
    eapply eval_condition_lessdef; eauto. 
    eapply agree_eval_regs; eauto.
  econstructor; split.
  eapply exec_Lcond_true; eauto. TranslInstr.
  MatchStates. eapply agree_reg_list_live. eauto.
  (* Icond, false *)
  assert (COND: eval_condition cond (map ls (map assign args)) tm = Some false).
    eapply eval_condition_lessdef; eauto. 
    eapply agree_eval_regs; eauto.
  econstructor; split.
  eapply exec_Lcond_false; eauto. TranslInstr.
  MatchStates. eapply agree_reg_list_live. eauto.

  (* Ireturn *)
  econstructor; split.
  eapply exec_Lreturn; eauto. TranslInstr; eauto.
  econstructor; eauto.
  rewrite return_regs_result.  
  inv WTI. destruct or; simpl in *. 
  rewrite Locmap.gss. eapply agree_eval_reg; eauto.
  constructor. 
  apply free_lessdef; auto.
  intros. apply return_regs_not_destroyed; auto.

  (* internal function *)
  generalize H6. simpl.  unfold transf_function.
  caseEq (type_function f); simpl; try congruence. intros env TYP.
  assert (WTF: wt_function f env). apply type_function_correct; auto.
  caseEq (analyze f); simpl; try congruence. intros live ANL.
  caseEq (regalloc f live (live0 f live) env); simpl; try congruence.
  intros alloc ALLOC EQ. inv EQ. simpl in *.
  caseEq (Mem.alloc tm 0 (RTL.fn_stacksize f)). intros tm' stk' MEMALLOC.
  exploit alloc_lessdef; eauto. intros [EQ LDM]. subst stk'.
  econstructor; split.
  eapply exec_function_internal; simpl; eauto.
  simpl. econstructor; eauto.
  apply agree_init_regs. intros; eapply regalloc_correct_3; eauto.
  inv WTF.
  exploit (parmov_spec (call_regs ls) 
                       (loc_parameters (RTL.fn_sig f))
                       (map alloc (RTL.fn_params f))).
  eapply regalloc_norepet_norepet; eauto.
  eapply regalloc_correct_2; eauto.
  rewrite loc_parameters_length. symmetry. 
  transitivity (length (map env (RTL.fn_params f))).
  repeat rewrite list_length_map. auto.
  rewrite wt_params; auto.
  intros [PM1 PM2].
  change Regset.elt with reg in PM1. rewrite PM1.
  replace (map (call_regs ls) (loc_parameters (RTL.fn_sig f)))
     with (map ls (loc_arguments (RTL.fn_sig f))).
  auto.
  symmetry. unfold loc_parameters. rewrite list_map_compose.
  apply list_map_exten. intros. symmetry. eapply call_regs_param_of_arg; eauto.

  (* external function *)
  injection H6; intro EQ; inv EQ.
  exploit event_match_lessdef; eauto. intros [tres [A B]].
  econstructor; split.
  eapply exec_function_external; eauto.
  eapply match_states_return; eauto.
  rewrite Locmap.gss. auto.
  intros. rewrite <- H10; auto. apply Locmap.gso.
  apply Loc.diff_sym. eapply Loc.in_notin_diff; eauto.
  apply loc_result_caller_save. 

  (* return *)
  inv H3. 
  econstructor; split.
  eapply exec_return; eauto.
  econstructor; eauto.
Qed.

(** The semantic equivalence between the original and transformed programs
  follows easily. *)

Lemma transf_initial_states:
  forall st1, RTL.initial_state prog st1 ->
  exists st2, LTL.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  assert (SIG2: funsig tf = mksignature nil (Some Tint)).
    rewrite <- H2. apply sig_function_translated; auto.
  assert (VPARAMS: Val.lessdef_list nil (map (Locmap.init Vundef) (loc_arguments (funsig tf)))).
    rewrite SIG2. simpl. constructor.
  assert (GENV: (Genv.init_mem tprog) = (Genv.init_mem prog)).
    exact (Genv.init_mem_transf_partial _ _ TRANSF).
  assert (MMD: Mem.lessdef (Genv.init_mem prog) (Genv.init_mem tprog)).
    rewrite GENV. apply Mem.lessdef_refl.
  exists (LTL.Callstate nil tf (Locmap.init Vundef) (Genv.init_mem tprog)); split.
  econstructor; eauto.
  rewrite symbols_preserved. 
  rewrite (transform_partial_program_main _ _ TRANSF).  auto.
  constructor; auto. rewrite H2; constructor. 
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> RTL.final_state st1 r -> LTL.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H3. econstructor.
  inv H4. auto. 
Qed.

Theorem transf_program_correct:
  forall (beh: program_behavior),
  RTL.exec_program prog beh -> LTL.exec_program tprog beh.
Proof.
  unfold RTL.exec_program, LTL.exec_program; intros.
  eapply simulation_step_preservation; eauto.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transl_step_correct. 
Qed.

End PRESERVATION.
