(** Preservation of typing during register allocation. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Locations.
Require Import LTL.
Require Import Coloring.
Require Import Coloringproof.
Require Import Allocation.
Require Import Allocproof.
Require Import RTLtyping.
Require Import LTLtyping.
Require Import Conventions.
Require Import Alloctyping_aux.

(** This file proves that register allocation (the translation from
  RTL to LTL defined in file [Allocation]) preserves typing:
  given a well-typed RTL input, it produces LTL code that is
  well-typed. *)

Section TYPING_FUNCTION.

Variable f: RTL.function.
Variable env: regenv.
Variable live: PMap.t Regset.t.
Variable alloc: reg -> loc.
Variable tf: LTL.function.

Hypothesis TYPE_RTL: type_rtl_function f = Some env.
Hypothesis ALLOC: regalloc f live (live0 f live) env = Some alloc.
Hypothesis TRANSL: transf_function f = Some tf.

Lemma wt_rtl_function: RTLtyping.wt_function env f.
Proof.
  apply type_rtl_function_correct; auto.
Qed.

Lemma alloc_type: forall r, Loc.type (alloc r) = env r.
Proof.
  intro. eapply regalloc_preserves_types; eauto.
Qed.

Lemma alloc_types:
  forall rl, List.map Loc.type (List.map alloc rl) = List.map env rl.
Proof.
  intros. rewrite list_map_compose. apply list_map_exten.
  intros. symmetry. apply alloc_type. 
Qed.

(** [loc_read_ok l] states whether location [l] is well-formed in an
  argument context (for reading). *)

Definition loc_read_ok (l: loc) : Prop :=
  match l with R r => True | S s => slot_bounded tf s end.

(** [loc_write_ok l] states whether location [l] is well-formed in a
  result context (for writing). *)

Definition loc_write_ok (l: loc) : Prop :=
  match l with 
  | R r => True
  | S (Incoming _ _) => False
  | S s => slot_bounded tf s end.

Definition locs_read_ok (ll: list loc) : Prop :=
  forall l, In l ll -> loc_read_ok l.

Definition locs_write_ok (ll: list loc) : Prop :=
  forall l, In l ll -> loc_write_ok l.

Remark loc_write_ok_read_ok:
  forall l, loc_write_ok l -> loc_read_ok l.
Proof.
  destruct l; simpl. auto.
  destruct s; tauto.
Qed.
Hint Resolve loc_write_ok_read_ok: allocty.

Remark locs_write_ok_read_ok:
  forall ll, locs_write_ok ll -> locs_read_ok ll.
Proof.
  unfold locs_write_ok, locs_read_ok. auto with allocty.
Qed.
Hint Resolve locs_write_ok_read_ok: allocty.

Lemma alloc_write_ok:
  forall r, loc_write_ok (alloc r).
Proof.
  intros. generalize (regalloc_acceptable _ _ _ _ _ r ALLOC).
  destruct (alloc r); simpl. auto. 
  destruct s; try contradiction. simpl. omega.
Qed.
Hint Resolve alloc_write_ok: allocty.

Lemma allocs_write_ok:
  forall rl, locs_write_ok (List.map alloc rl).
Proof.
  intros; red; intros.
  generalize (list_in_map_inv _ _ _ H). intros [r [EQ IN]].
  subst l. auto with allocty.
Qed.
Hint Resolve allocs_write_ok: allocty.

(** * Typing LTL constructors *)

(** We show that the LTL constructor functions defined in [Allocation]
  generate well-typed LTL basic blocks, given sufficient typing
  and well-formedness hypotheses over the locations involved. *)

Lemma wt_add_reload:
  forall src dst k,
  loc_read_ok src ->
  Loc.type src = mreg_type dst ->
  wt_block tf k ->
  wt_block tf (add_reload src dst k).
Proof.
  intros. unfold add_reload. destruct src. 
  case (mreg_eq m dst); intro. auto. apply wt_Bopmove. exact H0. auto.
  apply wt_Bgetstack. exact H0. exact H. auto.
Qed.

Lemma wt_add_spill:
  forall src dst k,
  loc_write_ok dst ->
  mreg_type src = Loc.type dst ->
  wt_block tf k ->
  wt_block tf (add_spill src dst k).
Proof.
  intros. unfold add_spill. destruct dst. 
  case (mreg_eq src m); intro. auto. 
  apply wt_Bopmove. exact H0. auto.
  apply wt_Bsetstack. generalize H. simpl. destruct s; auto.
  symmetry. exact H0. generalize H. simpl. destruct s; auto. contradiction.
  auto.
Qed.

Lemma wt_add_reloads:
  forall srcs dsts k,
  locs_read_ok srcs ->
  List.map Loc.type srcs = List.map mreg_type dsts ->
  wt_block tf k ->
  wt_block tf (add_reloads srcs dsts k).
Proof.
  induction srcs; intros.
  destruct dsts. simpl; auto. simpl in H0; discriminate. 
  destruct dsts; simpl in H0. discriminate. simpl. 
  apply wt_add_reload. apply H; apply in_eq. congruence. 
  apply IHsrcs. red; intros; apply H; apply in_cons; auto.
  congruence. auto.
Qed.

Lemma wt_reg_for:
  forall l, mreg_type (reg_for l) = Loc.type l.
Proof.
  intros. destruct l; simpl. auto.
  case (slot_type s); reflexivity.
Qed.
Hint Resolve wt_reg_for: allocty.

Lemma wt_regs_for_rec:
  forall locs itmps ftmps,
  (List.length locs <= List.length itmps)%nat ->
  (List.length locs <= List.length ftmps)%nat ->
  (forall r, In r itmps -> mreg_type r = Tint) ->
  (forall r, In r ftmps -> mreg_type r = Tfloat) ->
  List.map mreg_type (regs_for_rec locs itmps ftmps) = List.map Loc.type locs.
Proof.
  induction locs; intros.
  simpl. auto.
  destruct itmps; simpl in H. omegaContradiction.
  destruct ftmps; simpl in H0. omegaContradiction.
  simpl. apply (f_equal2 (@cons typ)). 
  destruct a. reflexivity. simpl. case (slot_type s).
  apply H1; apply in_eq. apply H2; apply in_eq.
  apply IHlocs. omega. omega. 
  intros; apply H1; apply in_cons; auto.
  intros; apply H2; apply in_cons; auto.
Qed.

Lemma wt_regs_for:
  forall locs,
  (List.length locs <= 3)%nat ->
  List.map mreg_type (regs_for locs) = List.map Loc.type locs.
Proof.
  intros. unfold regs_for. apply wt_regs_for_rec.
  simpl. auto. simpl. auto. 
  simpl; intros; intuition; subst r; reflexivity.
  simpl; intros; intuition; subst r; reflexivity.
Qed.
Hint Resolve wt_regs_for: allocty.

Lemma wt_add_move:
  forall src dst b,
  loc_read_ok src -> loc_write_ok dst ->
  Loc.type src = Loc.type dst ->
  wt_block tf b ->
  wt_block tf (add_move src dst b).
Proof.
  intros. unfold add_move. 
  case (Loc.eq src dst); intro.
  auto.
  destruct src. apply wt_add_spill; auto. 
  destruct dst. apply wt_add_reload; auto.
  set (tmp := match slot_type s with Tint => IT1 | Tfloat => FT1 end).
  apply wt_add_reload. auto. 
  simpl. unfold tmp. case (slot_type s); reflexivity.
  apply wt_add_spill. auto.
  simpl. simpl in H1. rewrite <- H1. unfold tmp. case (slot_type s); reflexivity.
  auto.
Qed.

Theorem wt_parallel_move:
 forall srcs dsts b,
 List.map Loc.type srcs = List.map Loc.type dsts ->
 locs_read_ok srcs ->
 locs_write_ok dsts -> wt_block tf b ->  wt_block tf (parallel_move srcs dsts b).
Proof.
  unfold locs_read_ok, locs_write_ok.
  apply wt_parallel_moveX; simpl; auto.
  exact wt_add_move.
Qed.
 
Lemma wt_add_op_move:
  forall src res s,
  Loc.type src = Loc.type res ->
  loc_read_ok src -> loc_write_ok res ->
  wt_block tf (add_op Omove (src :: nil) res s).
Proof.
  intros. unfold add_op. simpl. 
  apply wt_add_move. auto. auto. auto. constructor. 
Qed.

Lemma wt_add_op_undef:
  forall res s,
  loc_write_ok res ->
  wt_block tf (add_op Oundef nil res s).
Proof.
  intros. unfold add_op. simpl. 
  apply wt_Bopundef. apply wt_add_spill. auto. auto with allocty. 
  constructor.
Qed.

Lemma wt_add_op_others:
  forall op args res s,
  op <> Omove -> op <> Oundef ->
  (List.map Loc.type args, Loc.type res) = type_of_operation op ->
  locs_read_ok args ->
  loc_write_ok res ->
  wt_block tf (add_op op args res s).
Proof.
  intros. unfold add_op. 
  caseEq (is_move_operation op args). intros.
  generalize (is_move_operation_correct op args H4). tauto.
  intro. assert ((List.length args <= 3)%nat).
    replace (length args) with (length (fst (type_of_operation op))).
    apply Allocproof.length_type_of_operation. 
    rewrite <- H1. simpl. apply list_length_map. 
  generalize (wt_regs_for args H5); intro.
  generalize (wt_reg_for res); intro.
  apply wt_add_reloads. auto. auto. 
  apply wt_Bop. auto. auto. congruence. 
  apply wt_add_spill. auto. auto. constructor.
Qed.

Lemma wt_add_load:
  forall chunk addr args dst s,
  List.map Loc.type args = type_of_addressing addr ->
  Loc.type dst = type_of_chunk chunk ->
  locs_read_ok args ->
  loc_write_ok dst ->
  wt_block tf (add_load chunk addr args dst s).
Proof.
  intros. unfold add_load.
  assert ((List.length args <= 2)%nat).
    replace (length args) with (length (type_of_addressing addr)).
    apply Allocproof.length_type_of_addressing.
    rewrite <- H. apply list_length_map.
  assert ((List.length args <= 3)%nat). omega.
  generalize (wt_regs_for args H4); intro.
  generalize (wt_reg_for dst); intro.
  apply wt_add_reloads. auto. auto. 
  apply wt_Bload. congruence. congruence. 
  apply wt_add_spill. auto. auto. constructor.
Qed.

Lemma wt_add_store:
  forall chunk addr args src s,
  List.map Loc.type args = type_of_addressing addr ->
  Loc.type src = type_of_chunk chunk ->
  locs_read_ok args ->
  loc_read_ok src ->
  wt_block tf (add_store chunk addr args src s).
Proof.
  intros. unfold add_store.
  assert ((List.length args <= 2)%nat).
    replace (length args) with (length (type_of_addressing addr)).
    apply Allocproof.length_type_of_addressing.
    rewrite <- H. apply list_length_map.
  assert ((List.length (src :: args) <= 3)%nat). simpl. omega.
  generalize (wt_regs_for (src :: args) H4); intro.
  caseEq (regs_for (src :: args)).
  intro. constructor.
  intros rsrc rargs EQ. rewrite EQ in H5. simpl in H5.
  apply wt_add_reloads. 
  red; intros. elim H6; intro. subst l; auto. auto. 
  simpl. congruence. 
  apply wt_Bstore. congruence. congruence. constructor.
Qed.

Lemma wt_add_call:
  forall sig los args res s,
  match los with inl l => Loc.type l = Tint | inr s => True end ->
  List.map Loc.type args = sig.(sig_args) ->
  Loc.type res = match sig.(sig_res) with None => Tint | Some ty => ty end ->
  locs_read_ok args ->
  match los with inl l => loc_read_ok l | inr s => True end ->
  loc_write_ok res ->
  wt_block tf (add_call sig los args res s).
Proof.
  intros. 
  assert (locs_write_ok (loc_arguments sig)).
    red; intros. generalize (loc_arguments_acceptable sig l H5).
    destruct l; simpl. auto. 
    destruct s0; try contradiction. simpl. omega.
  unfold add_call. destruct los.
  apply wt_add_reload. auto. simpl; congruence. 
  apply wt_parallel_move. rewrite loc_arguments_type. auto.
  auto. auto. 
  apply wt_Bcall. reflexivity. 
  apply wt_add_spill. auto. 
  rewrite loc_result_type. auto. constructor.
  apply wt_parallel_move. rewrite loc_arguments_type. auto.
  auto. auto. 
  apply wt_Bcall. auto.
  apply wt_add_spill. auto. 
  rewrite loc_result_type. auto. constructor.
Qed.

Lemma wt_add_cond:
  forall cond args ifso ifnot,
  List.map Loc.type args = type_of_condition cond ->
  locs_read_ok args ->
  wt_block tf (add_cond cond args ifso ifnot).
Proof.
  intros. 
  assert ((List.length args) <= 3)%nat.
    replace (length args) with (length (type_of_condition cond)).
    apply Allocproof.length_type_of_condition. 
    rewrite <- H. apply list_length_map. 
  generalize (wt_regs_for args H1). intro.  
  unfold add_cond. apply wt_add_reloads.
  auto. auto. 
  apply wt_Bcond. congruence. 
Qed.

Lemma wt_add_return:
  forall sig optarg,
  option_map Loc.type optarg = sig.(sig_res) ->
  match optarg with None => True | Some arg => loc_read_ok arg end ->
  wt_block tf (add_return sig optarg).
Proof.
  intros. unfold add_return. destruct optarg.
  apply wt_add_reload. auto. rewrite loc_result_type. 
  simpl in H. destruct (sig_res sig). congruence. discriminate.
  constructor.
  apply wt_Bopundef. constructor.
Qed.

Lemma wt_add_undefs:
  forall ll b,
  wt_block tf b -> wt_block tf (add_undefs ll b).
Proof.
  induction ll; intros.
  simpl. auto. 
  simpl. destruct a. apply wt_Bopundef. auto. auto.
Qed.

Lemma wt_add_entry:
  forall params undefs s,
  List.map Loc.type params = sig_args (RTL.fn_sig f) ->
  locs_write_ok params ->
  wt_block tf (add_entry (RTL.fn_sig f) params undefs s).
Proof.
  set (sig := RTL.fn_sig f).
  assert (sig = tf.(fn_sig)).
    unfold sig. symmetry. apply Allocproof.sig_function_translated. auto.
  assert (locs_read_ok (loc_parameters sig)).
    red; unfold loc_parameters. intros. 
    generalize (list_in_map_inv _ _ _ H0). intros [l1 [EQ IN]].
    subst l. generalize (loc_arguments_acceptable _ _ IN).
    destruct l1. simpl. auto. 
    destruct s; try contradiction. 
    simpl; intros. split. omega. rewrite <- H. 
    apply loc_arguments_bounded. auto.
  intros. unfold add_entry.
  apply wt_parallel_move. rewrite loc_parameters_type. auto.
  auto. auto. 
  apply wt_add_undefs. constructor.
Qed.

(** * Type preservation during translation from RTL to LTL *)

Lemma wt_transf_instr:
  forall pc instr,
  RTLtyping.wt_instr env f instr ->
  wt_block tf (transf_instr f live alloc pc instr).
Proof.
  intros. inversion H; simpl.
  (* nop *)
  constructor.
  (* move *)
  case (Regset.mem r live!!pc). 
  apply wt_add_op_move; auto with allocty.
  repeat rewrite alloc_type. auto. constructor.
  (* undef *)
  case (Regset.mem r live!!pc). 
  apply wt_add_op_undef; auto with allocty.
  constructor.
  (* other ops *)
  case (Regset.mem res live!!pc). 
  apply wt_add_op_others; auto with allocty. 
  rewrite alloc_types. rewrite alloc_type. auto. 
  constructor.
  (* load *)
  case (Regset.mem dst live!!pc). 
  apply wt_add_load; auto with allocty. 
  rewrite alloc_types. auto. rewrite alloc_type. auto. 
  constructor.
  (* store *)
  apply wt_add_store; auto with allocty.
  rewrite alloc_types. auto. rewrite alloc_type. auto. 
  (* call *)
  apply wt_add_call. 
  destruct ros; simpl. rewrite alloc_type; auto. auto. 
  rewrite alloc_types; auto.
  rewrite alloc_type. auto. 
  auto with allocty.
  destruct ros; simpl; auto with allocty.
  auto with allocty.
  (* cond *)
  apply wt_add_cond. rewrite alloc_types; auto. auto with allocty.
  (* return *)
  apply wt_add_return. 
  destruct optres; simpl. rewrite alloc_type. exact H0. exact H0.
  destruct optres; simpl; auto with allocty.
Qed.

Lemma wt_transf_instrs:
  let c := PTree.map (transf_instr f live alloc) (RTL.fn_code f) in
  forall pc b, c!pc = Some b -> wt_block tf b.
Proof.
  intros until b.
  unfold c. rewrite PTree.gmap. caseEq (RTL.fn_code f)!pc. 
  intros instr EQ. simpl. intros. injection H; intro; subst b.
  apply wt_transf_instr. eapply RTLtyping.wt_instrs; eauto.
  apply wt_rtl_function. 
  simpl; intros; discriminate.
Qed.

Lemma wt_transf_entrypoint:
  let c := transf_entrypoint f live alloc
            (PTree.map (transf_instr f live alloc) (RTL.fn_code f)) in
  (forall pc b, c!pc = Some b -> wt_block tf b).
Proof.
  simpl. unfold transf_entrypoint. 
  intros pc b. rewrite PTree.gsspec. 
  case (peq pc (fn_nextpc f)); intros.
  injection H; intro; subst b. 
  apply wt_add_entry.
  rewrite alloc_types. eapply RTLtyping.wt_params. apply wt_rtl_function.
  auto with allocty. 
  apply wt_transf_instrs with pc; auto.
Qed.

End TYPING_FUNCTION.

Lemma wt_transf_function:
  forall f tf,
  transf_function f = Some tf -> wt_function tf.
Proof.
  intros. generalize H; unfold transf_function.
  caseEq (type_rtl_function f). intros env TYP. 
  caseEq (analyze f). intros live ANL.
  change (transfer f (RTL.fn_entrypoint f)
                     live!!(RTL.fn_entrypoint f))
    with (live0 f live).
  caseEq (regalloc f live (live0 f live) env).
  intros alloc ALLOC.
  intro EQ; injection EQ; intro; subst tf.
  red. simpl. intros. eapply wt_transf_entrypoint; eauto.
  intros; discriminate.
  intros; discriminate.
  intros; discriminate.
Qed. 

Lemma program_typing_preserved:
  forall (p: RTL.program) (tp: LTL.program),
  transf_program p = Some tp ->
  LTLtyping.wt_program tp.
Proof.
  intros; red; intros.
  generalize (transform_partial_program_function transf_function p i f H H0).
  intros [f0 [IN TRANSF]].
  apply wt_transf_function with f0; auto.
Qed.
