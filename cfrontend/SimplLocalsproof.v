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

(** Semantic preservation for the SimplLocals pass. *)

Require Import FSets.
Require FSetAVL.
Require Import Coqlib.
Require Import Errors.
Require Import Ordered.
Require Import AST.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.
Require Import Clight.
Require Import SimplLocals.

Module VSF := FSetFacts.Facts(VSet).
Module VSP := FSetProperties.Properties(VSet).

Section PRESERVATION.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF: transf_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  exact (Genv.find_symbol_transf_partial _ _ TRANSF).
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  exact (Genv.find_var_info_transf_partial _ _ TRANSF).
Qed.

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof.
  exact (Genv.find_funct_transf_partial _ _ TRANSF).
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof.  
  exact (Genv.find_funct_ptr_transf_partial _ _ TRANSF).
Qed.

Lemma type_of_fundef_preserved:
  forall fd tfd,
  transf_fundef fd = OK tfd -> type_of_fundef tfd = type_of_fundef fd.
Proof.
  intros. destruct fd; monadInv H; auto.
  monadInv EQ. simpl; unfold type_of_function; simpl. auto.  
Qed.

Lemma type_of_global_preserved:
  forall id ty, type_of_global ge id = Some ty -> type_of_global tge id = Some ty.
Proof.
  unfold type_of_global; intros.
  rewrite varinfo_preserved. destruct (Genv.find_var_info ge id). auto. 
  destruct (Genv.find_funct_ptr ge id) as [fd|] eqn:?; inv H.
  exploit function_ptr_translated; eauto. intros [tf [A B]]. rewrite A. 
  decEq. apply type_of_fundef_preserved; auto.
Qed.

(** Matching between environments before and after *)

Inductive match_var (f: meminj) (cenv: compilenv) (e: env) (m: mem) (te: env) (tle: temp_env) (id: ident) : Prop :=
  | match_var_lifted: forall b ty chunk v tv
      (ENV: e!id = Some(b, ty))
      (TENV: te!id = None)
      (LIFTED: VSet.mem id cenv = true)
      (MAPPED: f b = None)
      (MODE: access_mode ty = By_value chunk)
      (LOAD: Mem.load chunk m b 0 = Some v)
      (TLENV: tle!(id) = Some tv)
      (VINJ: val_inject f v tv),
      match_var f cenv e m te tle id
  | match_var_not_lifted: forall b ty b'
      (ENV: e!id = Some(b, ty))
      (TENV: te!id = Some(b', ty))
      (LIFTED: VSet.mem id cenv = false)
      (MAPPED: f b = Some(b', 0)),
      match_var f cenv e m te tle id
  | match_var_not_local: forall
      (ENV: e!id = None)
      (TENV: te!id = None)
      (LIFTED: VSet.mem id cenv = false),
      match_var f cenv e m te tle id.

Record match_envs (f: meminj) (cenv: compilenv)
                  (e: env) (le: temp_env) (m: mem) (lo hi: Z)
                  (te: env) (tle: temp_env) (tlo thi: Z) : Prop :=
  mk_match_envs {
    me_vars:
      forall id, match_var f cenv e m te tle id;
    me_temps:
      forall id v,
      le!id = Some v ->
      (exists tv, tle!id = Some tv /\ val_inject f v tv)
      /\ (VSet.mem id cenv = true -> v = Vundef);
    me_inj:
      forall id1 b1 ty1 id2 b2 ty2, e!id1 = Some(b1, ty1) -> e!id2 = Some(b2, ty2) -> id1 <> id2 -> b1 <> b2;
    me_range:
      forall id b ty, e!id = Some(b, ty) -> lo <= b < hi;
    me_trange:
      forall id b ty, te!id = Some(b, ty) -> tlo <= b < thi;
    me_mapped:
      forall id b' ty,
      te!id = Some(b', ty) -> exists b, f b = Some(b', 0) /\ e!id = Some(b, ty);
    me_flat:
      forall id b' ty b delta,
      te!id = Some(b', ty) -> f b = Some(b', delta) -> e!id = Some(b, ty) /\ delta = 0;
    me_incr:
      lo <= hi;
    me_tincr:
      tlo <= thi
  }.

(** Invariance by change of memory and injection *)

Lemma match_envs_invariant:
  forall f cenv e le m lo hi te tle tlo thi f' m',
  match_envs f cenv e le m lo hi te tle tlo thi ->
  (forall b chunk v,
    f b = None -> lo <= b < hi -> Mem.load chunk m b 0 = Some v -> Mem.load chunk m' b 0 = Some v) ->
  inject_incr f f' ->
  (forall b, lo <= b < hi -> f' b = f b) ->
  (forall b b' delta, f' b = Some(b', delta) -> tlo <= b' < thi -> f' b = f b) ->
  match_envs f' cenv e le m' lo hi te tle tlo thi.
Proof.
  intros until m'; intros ME LD INCR INV1 INV2. 
  destruct ME; constructor; eauto. 
(* vars *)
  intros. generalize (me_vars0 id); intros MV; inv MV.
  eapply match_var_lifted; eauto.
  rewrite <- MAPPED; eauto. 
  eapply match_var_not_lifted; eauto.
  eapply match_var_not_local; eauto.
(* temps *)
  intros. exploit me_temps0; eauto. intros [[v' [A B]] C]. split; auto. exists v'; eauto. 
(* mapped *)
  intros. exploit me_mapped0; eauto. intros [b [A B]]. exists b; split; auto.  
(* flat *)
  intros. eapply me_flat0; eauto. rewrite <- H0. symmetry. eapply INV2; eauto.
Qed.

(** Invariance by external call *)

Lemma match_envs_extcall:
  forall f cenv e le m lo hi te tle tlo thi tm f' m',
  match_envs f cenv e le m lo hi te tle tlo thi ->
  mem_unchanged_on (loc_unmapped f) m m' ->
  inject_incr f f' ->
  inject_separated f f' m tm ->
  hi <= Mem.nextblock m -> thi <= Mem.nextblock tm ->
  match_envs f' cenv e le m' lo hi te tle tlo thi.
Proof.
  intros. eapply match_envs_invariant; eauto. 
  intros. destruct H0.  eapply H8. intros; red. auto. auto. 
  red in H2. intros. destruct (f b) as [[b' delta]|] eqn:?. 
  eapply H1; eauto.
  destruct (f' b) as [[b' delta]|] eqn:?; auto. 
  exploit H2; eauto. unfold Mem.valid_block. intros [A B].
  omegaContradiction.
  intros. destruct (f b) as [[b'' delta']|] eqn:?. eauto. 
  exploit H2; eauto. unfold Mem.valid_block. intros [A B].
  omegaContradiction.
Qed.

(** Properties of values obtained by casting to a given type. *)

Inductive val_casted: val -> type -> Prop :=
  | val_casted_int: forall sz si attr n,
      cast_int_int sz si n = n ->
      val_casted (Vint n) (Tint sz si attr)
  | val_casted_float: forall sz attr n,
      cast_float_float sz n = n ->
      val_casted (Vfloat n) (Tfloat sz attr)
  | val_casted_ptr_ptr: forall b ofs ty attr,
      val_casted (Vptr b ofs) (Tpointer ty attr)
  | val_casted_int_ptr: forall n ty attr,
      val_casted (Vint n) (Tpointer ty attr)
  | val_casted_ptr_int: forall b ofs si attr,
      val_casted (Vptr b ofs) (Tint I32 si attr)
  | val_casted_struct: forall id fld attr v,
      val_casted v (Tstruct id fld attr)
  | val_casted_union: forall id fld attr v,
      val_casted v (Tunion id fld attr)
  | val_casted_void: forall v,
      val_casted v Tvoid.

Remark cast_int_int_idem:
  forall sz sg i, cast_int_int sz sg (cast_int_int sz sg i) = cast_int_int sz sg i.
Proof.
  intros. destruct sz; simpl; auto. 
  destruct sg; [apply Int.sign_ext_idem|apply Int.zero_ext_idem]; compute; intuition congruence.
  destruct sg; [apply Int.sign_ext_idem|apply Int.zero_ext_idem]; compute; intuition congruence.
  destruct (Int.eq i Int.zero); auto.
Qed.

Remark cast_float_float_idem:
  forall sz f, cast_float_float sz (cast_float_float sz f) = cast_float_float sz f.
Proof.
  intros; destruct sz; simpl.
  apply Float.singleoffloat_idem; auto.
  auto.
Qed.

Lemma cast_val_is_casted:
  forall v ty ty' v', sem_cast v ty ty' = Some v' -> val_casted v' ty'.
Proof.
  unfold sem_cast; intros. destruct ty'; simpl in *.
(* void *)
  constructor.
(* int *)
  destruct i; destruct ty; simpl in H; try discriminate; destruct v; inv H.
  constructor. apply (cast_int_int_idem I8 s). 
  destruct (cast_float_int s f0); inv H1.   constructor. apply (cast_int_int_idem I8 s). 
  constructor. apply (cast_int_int_idem I16 s). 
  destruct (cast_float_int s f0); inv H1.   constructor. apply (cast_int_int_idem I16 s). 
  constructor. auto.
  constructor. 
  destruct (cast_float_int s f0); inv H1. constructor. auto.
  constructor. auto.
  constructor.
  constructor; auto.
  constructor.
  constructor; auto.
  constructor; auto.
  constructor. simpl. destruct (Int.eq i0 Int.zero); auto.
  constructor. simpl. destruct (Float.cmp Ceq f0 Float.zero); auto.
  constructor. simpl. destruct (Int.eq i Int.zero); auto.
  constructor; auto.
  constructor. simpl. destruct (Int.eq i Int.zero); auto.
  constructor; auto.
  constructor. simpl. destruct (Int.eq i Int.zero); auto.
  constructor; auto.
(* float *)
  destruct ty; simpl in H; try discriminate; destruct v; inv H.
  constructor. apply cast_float_float_idem.
  constructor. apply cast_float_float_idem.
(* pointer *)
  destruct ty; simpl in H; try discriminate; destruct v; inv H; try constructor.
(* impossible cases *)
  discriminate.
  discriminate.
(* structs,unions *)
  constructor.
  constructor.
(* impossible cases *)
  discriminate.
Qed.

Lemma val_casted_load_result:
  forall v ty chunk,
  val_casted v ty -> access_mode ty = By_value chunk ->
  Val.load_result chunk v = v.
Proof.
  intros. inversion H; clear H; subst v ty; simpl in H0.
  destruct sz.
  destruct si; inversion H0; clear H0; subst chunk; simpl in *; congruence.
  destruct si; inversion H0; clear H0; subst chunk; simpl in *; congruence.
  clear H1. inv H0. auto.
  inversion H0; clear H0; subst chunk. simpl in *. 
  destruct (Int.eq n Int.zero); subst n; reflexivity.
  destruct sz; inversion H0; clear H0; subst chunk; simpl in *; congruence.
  inv H0; auto.
  inv H0; auto.
  inv H0; auto.
  discriminate.
  discriminate.
  discriminate.
Qed.

Lemma cast_val_casted:
  forall v ty, val_casted v ty -> sem_cast v ty ty = Some v.
Proof.
  intros. inversion H; clear H; subst v ty; unfold sem_cast; simpl.
  destruct sz; congruence.
  congruence.
  auto.
  auto.
  auto.
  unfold proj_sumbool; repeat rewrite dec_eq_true; auto.
  unfold proj_sumbool; repeat rewrite dec_eq_true; auto.
  auto.
Qed.

Lemma val_casted_inject:
  forall f v v' ty,
  val_inject f v v' -> val_casted v ty -> val_casted v' ty.
Proof.
  intros. inv H.
  auto.
  auto.
  inv H0; constructor.
  inv H0; constructor.
Qed.

Inductive val_casted_list: list val -> typelist -> Prop :=
  | vcl_nil:
      val_casted_list nil Tnil
  | vcl_cons: forall v1 vl ty1 tyl,
      val_casted v1 ty1 -> val_casted_list vl tyl ->
      val_casted_list (v1 :: vl) (Tcons  ty1 tyl).

Lemma val_casted_list_params:
  forall params vl,
  val_casted_list vl (type_of_params params) ->
  list_forall2 val_casted vl (map snd params).
Proof.
  induction params; simpl; intros. 
  inv H. constructor.
  destruct a as [id ty]. inv H. constructor; auto. 
Qed.

(** Correctness of [make_cast] *)

Lemma make_cast_correct:
  forall e le m a v1 tto v2,
  eval_expr tge e le m a v1 ->
  sem_cast v1 (typeof a) tto = Some v2 ->
  eval_expr tge e le m (make_cast a tto) v2.
Proof.
  intros.
  assert (DFL: eval_expr tge e le m (Ecast a tto) v2).
    econstructor; eauto.
  unfold sem_cast, make_cast in *. 
  destruct (classify_cast (typeof a) tto); auto.
  destruct v1; inv H0; auto.
  destruct sz2; auto. destruct v1; inv H0; auto.
  destruct sz2; auto. destruct v1; inv H0; auto.
  destruct (ident_eq id1 id2 && fieldlist_eq fld1 fld2); inv H0; auto.
  destruct (ident_eq id1 id2 && fieldlist_eq fld1 fld2); inv H0; auto.
  inv H0; auto.
Qed.

(** Preservation by assignment to lifted variable. *)

Lemma match_envs_assign_lifted:
  forall f cenv e le m lo hi te tle tlo thi b ty v m' id tv,
  match_envs f cenv e le m lo hi te tle tlo thi ->
  e!id = Some(b, ty) ->
  val_casted v ty ->
  val_inject f v tv ->
  assign_loc ty m b Int.zero v m' ->
  VSet.mem id cenv = true ->
  match_envs f cenv e le m' lo hi te (PTree.set id tv tle) tlo thi.
Proof.
  intros. destruct H. generalize (me_vars0 id); intros MV; inv MV; try congruence.
  rewrite ENV in H0; inv H0. inv H3; try congruence.
  unfold Mem.storev in H0. rewrite Int.unsigned_zero in H0.
  constructor; eauto; intros.
(* vars *)
  destruct (peq id0 id). subst id0.
  eapply match_var_lifted with (v := v); eauto. 
  exploit Mem.load_store_same; eauto. erewrite val_casted_load_result; eauto.
  apply PTree.gss. 
  generalize (me_vars0 id0); intros MV; inv MV.
  eapply match_var_lifted; eauto.
  rewrite <- LOAD0. eapply Mem.load_store_other; eauto. 
  rewrite PTree.gso; auto.
  eapply match_var_not_lifted; eauto. 
  eapply match_var_not_local; eauto.
(* temps *)
  exploit me_temps0; eauto. intros [[tv1 [A B]] C]. split; auto.
  rewrite PTree.gsspec. destruct (peq id0 id). 
  subst id0. exists tv; split; auto. rewrite C; auto.
  exists tv1; auto.
Qed.

(** Preservation by assignment to a temporary *)

Lemma match_envs_set_temp:
  forall f cenv e le m lo hi te tle tlo thi id v tv x,
  match_envs f cenv e le m lo hi te tle tlo thi ->
  val_inject f v tv ->
  check_temp cenv id = OK x ->
  match_envs f cenv e (PTree.set id v le) m lo hi te (PTree.set id tv tle) tlo thi.
Proof.
  intros. unfold check_temp in H1. 
  destruct (VSet.mem id cenv) eqn:?; monadInv H1.
  destruct H. constructor; eauto; intros.
(* vars *)
  generalize (me_vars0 id0); intros MV; inv MV.
  eapply match_var_lifted; eauto. rewrite PTree.gso. eauto. congruence.
  eapply match_var_not_lifted; eauto. 
  eapply match_var_not_local; eauto. 
(* temps *)
  rewrite PTree.gsspec in *. destruct (peq id0 id). 
  inv H. split. exists tv; auto. intros; congruence.
  eapply me_temps0; eauto. 
Qed.

Lemma match_envs_set_opttemp:
  forall f cenv e le m lo hi te tle tlo thi optid v tv x,
  match_envs f cenv e le m lo hi te tle tlo thi ->
  val_inject f v tv ->
  check_opttemp cenv optid = OK x ->
  match_envs f cenv e (set_opttemp optid v le) m lo hi te (set_opttemp optid tv tle) tlo thi.
Proof.
  intros. unfold set_opttemp. destruct optid; simpl in H1.
  eapply match_envs_set_temp; eauto.
  auto.
Qed.

(** Extensionality with respect to temporaries *)

Lemma match_envs_temps_exten:
  forall f cenv e le m lo hi te tle tlo thi tle',
  match_envs f cenv e le m lo hi te tle tlo thi ->
  (forall id, tle'!id = tle!id) ->
  match_envs f cenv e le m lo hi te tle' tlo thi.
Proof.
  intros. destruct H. constructor; auto; intros.
  (* vars *)
  generalize (me_vars0 id); intros MV; inv MV.
  eapply match_var_lifted; eauto. rewrite H0; auto.
  eapply match_var_not_lifted; eauto.
  eapply match_var_not_local; eauto.
  (* temps *)
  rewrite H0. eauto.
Qed.

(** Invariance by assignment to an irrelevant temporary *)

Lemma match_envs_change_temp:
  forall f cenv e le m lo hi te tle tlo thi id v,
  match_envs f cenv e le m lo hi te tle tlo thi ->
  le!id = None -> VSet.mem id cenv = false ->
  match_envs f cenv e le m lo hi te (PTree.set id v tle) tlo thi.
Proof.
  intros. destruct H. constructor; auto; intros.
  (* vars *)
  generalize (me_vars0 id0); intros MV; inv MV.
  eapply match_var_lifted; eauto. rewrite PTree.gso; auto. congruence. 
  eapply match_var_not_lifted; eauto.
  eapply match_var_not_local; eauto.
  (* temps *)
  rewrite PTree.gso. eauto. congruence.
Qed.

(** Properties of [cenv_for]. *)

Definition cenv_for_gen (atk: VSet.t) (vars: list (ident * type)) : compilenv :=
  List.fold_right (add_local_variable atk) VSet.empty vars.

Remark add_local_variable_charact:
  forall id ty atk cenv id1,
  VSet.In id1 (add_local_variable atk (id, ty) cenv) <->
  VSet.In id1 cenv \/ exists chunk, access_mode ty = By_value chunk /\ id = id1 /\ VSet.mem id atk = false.
Proof.
  intros. unfold add_local_variable. split; intros. 
  destruct (access_mode ty) eqn:?; auto.
  destruct (VSet.mem id atk) eqn:?; auto.
  rewrite VSF.add_iff in H. destruct H; auto. right; exists m; auto.
  destruct H as [A | [chunk [A [B C]]]].
  destruct (access_mode ty); auto. destruct (VSet.mem id atk); auto. rewrite VSF.add_iff; auto.
  rewrite A. rewrite <- B. rewrite C. apply VSet.add_1; auto.
Qed.

Lemma cenv_for_gen_domain:
 forall atk id vars, VSet.In id (cenv_for_gen atk vars) -> In id (var_names vars).
Proof.
  induction vars; simpl; intros.
  rewrite VSF.empty_iff in H. auto.
  destruct a as [id1 ty1]. rewrite add_local_variable_charact in H. 
  destruct H as [A | [chunk [A [B C]]]]; auto.
Qed.

Lemma cenv_for_gen_by_value:
  forall atk id ty vars,
  In (id, ty) vars ->
  list_norepet (var_names vars) ->
  VSet.In id (cenv_for_gen atk vars) ->
  exists chunk, access_mode ty = By_value chunk.
Proof.
  induction vars; simpl; intros.
  contradiction.
  destruct a as [id1 ty1]. simpl in H0. inv H0. 
  rewrite add_local_variable_charact in H1.
  destruct H; destruct H1 as [A | [chunk [A [B C]]]].
  inv H. elim H4. eapply cenv_for_gen_domain; eauto. 
  inv H. exists chunk; auto.
  eauto.
  subst id1. elim H4. change id with (fst (id, ty)). apply in_map; auto. 
Qed.

Lemma cenv_for_gen_compat:
  forall atk id vars,
  VSet.In id (cenv_for_gen atk vars) -> VSet.mem id atk = false.
Proof.
  induction vars; simpl; intros.
  rewrite VSF.empty_iff in H. contradiction.
  destruct a as [id1 ty1]. rewrite add_local_variable_charact in H.
  destruct H as [A | [chunk [A [B C]]]].
  auto.
  congruence.
Qed.

(** Compatibility between a compilation environment and an address-taken set. *)

Definition compat_cenv (atk: VSet.t) (cenv: compilenv) : Prop :=
  forall id, VSet.In id atk -> VSet.In id cenv -> False.

Lemma compat_cenv_for:
  forall f, compat_cenv (addr_taken_stmt f.(fn_body)) (cenv_for f).
Proof.
  intros; red; intros. 
  assert (VSet.mem id (addr_taken_stmt (fn_body f)) = false).
    eapply cenv_for_gen_compat. eexact H0. 
  rewrite VSF.mem_iff in H. congruence.
Qed.

Lemma compat_cenv_union_l:
  forall atk1 atk2 cenv,
  compat_cenv (VSet.union atk1 atk2) cenv -> compat_cenv atk1 cenv.
Proof.
  intros; red; intros. eapply H; eauto. apply VSet.union_2; auto. 
Qed.

Lemma compat_cenv_union_r:
  forall atk1 atk2 cenv,
  compat_cenv (VSet.union atk1 atk2) cenv -> compat_cenv atk2 cenv.
Proof.
  intros; red; intros. eapply H; eauto. apply VSet.union_3; auto. 
Qed.

Lemma compat_cenv_empty:
  forall cenv, compat_cenv VSet.empty cenv.
Proof.
  intros; red; intros. eapply VSet.empty_1; eauto. 
Qed.

Hint Resolve compat_cenv_union_l compat_cenv_union_r compat_cenv_empty: compat.

(** Allocation and initialization of parameters *)

Lemma alloc_variables_nextblock:
  forall e m vars e' m',
  alloc_variables e m vars e' m' -> Mem.nextblock m <= Mem.nextblock m'.
Proof.
  induction 1.
  omega.
  exploit Mem.nextblock_alloc; eauto. unfold block. omega.
Qed.

Lemma alloc_variables_range:
  forall id b ty e m vars e' m',
  alloc_variables e m vars e' m' ->
  e'!id = Some(b, ty) -> e!id = Some(b, ty) \/ Mem.nextblock m <= b < Mem.nextblock m'.
Proof.
  induction 1; intros.
  auto.
  exploit IHalloc_variables; eauto. rewrite PTree.gsspec. intros [A|A].
  destruct (peq id id0). inv A. 
  right. exploit Mem.alloc_result; eauto. exploit Mem.nextblock_alloc; eauto. unfold block.
  generalize (alloc_variables_nextblock _ _ _ _ _ H0). omega.
  auto.
  right. exploit Mem.nextblock_alloc; eauto. unfold block. omega.
Qed.

Lemma alloc_variables_injective:
  forall id1 b1 ty1 id2 b2 ty2 e m vars e' m',
  alloc_variables e m vars e' m' ->
  (e!id1 = Some(b1, ty1) -> e!id2 = Some(b2, ty2) -> id1 <> id2 -> b1 <> b2) ->
  (forall id b ty, e!id = Some(b, ty) -> b < Mem.nextblock m) ->
  (e'!id1 = Some(b1, ty1) -> e'!id2 = Some(b2, ty2) -> id1 <> id2 -> b1 <> b2).
Proof.
  induction 1; intros. 
  eauto.
  eapply IHalloc_variables; eauto. 
  repeat rewrite PTree.gsspec; intros.
  destruct (peq id1 id); destruct (peq id2 id).
  congruence.
  inv H6. exploit Mem.alloc_result; eauto. exploit H2; eauto. unfold block; omega.
  inv H7. exploit Mem.alloc_result; eauto. exploit H2; eauto. unfold block; omega.
  eauto.
  intros. rewrite PTree.gsspec in H6. destruct (peq id0 id). inv H6.
  exploit Mem.alloc_result; eauto. exploit Mem.nextblock_alloc; eauto. unfold block; omega.
  exploit H2; eauto. exploit Mem.nextblock_alloc; eauto. unfold block; omega.
Qed.

Lemma match_alloc_variables:
  forall cenv e m vars e' m',
  alloc_variables e m vars e' m' ->
  forall j tm te,
  list_norepet (var_names vars) ->
  Mem.inject j m tm ->
  exists j', exists te', exists tm',
      alloc_variables te tm (remove_lifted cenv vars) te' tm'
  /\ Mem.inject j' m' tm'
  /\ inject_incr j j'
  /\ (forall b, Mem.valid_block m b -> j' b = j b)
  /\ (forall b b' delta, j' b = Some(b', delta) -> Mem.valid_block tm b' -> j' b = j b)
  /\ (forall b b' delta, j' b = Some(b', delta) -> ~Mem.valid_block tm b' -> 
         exists id, exists ty, e'!id = Some(b, ty) /\ te'!id = Some(b', ty) /\ delta = 0)
  /\ (forall id ty, In (id, ty) vars ->
      exists b, 
          e'!id = Some(b, ty)
       /\ if VSet.mem id cenv
          then te'!id = te!id /\ j' b = None
          else exists tb, te'!id = Some(tb, ty) /\ j' b = Some(tb, 0))
  /\ (forall id, ~In id (var_names vars) -> e'!id = e!id /\ te'!id = te!id).
Proof.
  induction 1; intros.
  (* base case *)
  exists j; exists te; exists tm. simpl.
  split. constructor.
  split. auto. split. auto. split. auto.  split. auto. 
  split. intros. elim H2. eapply Mem.mi_mappedblocks; eauto.
  split. tauto. auto. 
  
  (* inductive case *)
  simpl in H1. inv H1. simpl.
  destruct (VSet.mem id cenv) eqn:?. simpl.
  (* variable is lifted out of memory *)
  exploit Mem.alloc_left_unmapped_inject; eauto. 
  intros [j1 [A [B [C D]]]].
  exploit IHalloc_variables; eauto. instantiate (1 := te).
  intros [j' [te' [tm' [J [K [L [M [N [Q [O P]]]]]]]]]].
  exists j'; exists te'; exists tm'.
  split. auto.
  split. auto.
  split. eapply inject_incr_trans; eauto. 
  split. intros. transitivity (j1 b). apply M. eapply Mem.valid_block_alloc; eauto. 
    apply D. apply Mem.valid_not_valid_diff with m; auto. eapply Mem.fresh_block_alloc; eauto. 
  split. intros. transitivity (j1 b). eapply N; eauto.
    destruct (eq_block b b1); auto. subst. 
    assert (j' b1 = j1 b1). apply M. eapply Mem.valid_new_block; eauto. 
    congruence.
  split. exact Q.  
  split. intros. destruct (ident_eq id0 id).
    (* same var *)
    subst id0.
    assert (ty0 = ty).
      destruct H1. congruence. elim H5. unfold var_names. change id with (fst (id, ty0)). apply in_map; auto.
    subst ty0. 
    exploit P; eauto. intros [X Y]. rewrite Heqb. rewrite X. rewrite Y. 
    exists b1. split. apply PTree.gss.
    split. auto.
    rewrite M. auto. eapply Mem.valid_new_block; eauto. 
    (* other vars *)
    eapply O; eauto. destruct H1. congruence. auto. 
  intros. exploit (P id0). tauto. intros [X Y]. rewrite X; rewrite Y. 
    split; auto. apply PTree.gso. intuition. 

  (* variable is not lifted out of memory *)
  exploit Mem.alloc_parallel_inject.
    eauto. eauto. apply Zle_refl. apply Zle_refl. 
  intros [j1 [tm1 [tb1 [A [B [C [D E]]]]]]].
  exploit IHalloc_variables; eauto. instantiate (1 := PTree.set id (tb1, ty) te). 
  intros [j' [te' [tm' [J [K [L [M [N [Q [O P]]]]]]]]]].
  exists j'; exists te'; exists tm'.
  split. simpl. econstructor; eauto.
  split. auto.
  split. eapply inject_incr_trans; eauto. 
  split. intros. transitivity (j1 b). apply M. eapply Mem.valid_block_alloc; eauto. 
    apply E. apply Mem.valid_not_valid_diff with m; auto. eapply Mem.fresh_block_alloc; eauto. 
  split. intros. transitivity (j1 b). eapply N; eauto. eapply Mem.valid_block_alloc; eauto. 
    destruct (eq_block b b1); auto. subst. 
    assert (j' b1 = j1 b1). apply M. eapply Mem.valid_new_block; eauto.
    rewrite H4 in H1. rewrite D in H1. inv H1. eelim Mem.fresh_block_alloc; eauto.
  split. intros. destruct (zeq b' tb1). 
    subst b'. rewrite (N _ _ _ H1) in H1.
    destruct (zeq b b1). subst b. rewrite D in H1; inv H1. 
    exploit (P id); auto. intros [X Y]. exists id; exists ty.
    rewrite X; rewrite Y. repeat rewrite PTree.gss. auto.
    rewrite E in H1; auto. elim H3. eapply Mem.mi_mappedblocks; eauto. 
    eapply Mem.valid_new_block; eauto.
    eapply Q; eauto. unfold Mem.valid_block in *.
    exploit Mem.nextblock_alloc. eexact A. exploit Mem.alloc_result. eexact A. 
    unfold block; omega.
  split. intros. destruct (ident_eq id0 id).
    (* same var *)
    subst id0.
    assert (ty0 = ty).
      destruct H1. congruence. elim H5. unfold var_names. change id with (fst (id, ty0)). apply in_map; auto.
    subst ty0. 
    exploit P; eauto. intros [X Y]. rewrite Heqb. rewrite X. rewrite Y. 
    exists b1. split. apply PTree.gss.
    exists tb1; split. 
    apply PTree.gss.
    rewrite M. auto. eapply Mem.valid_new_block; eauto. 
    (* other vars *)
    exploit (O id0 ty0). destruct H1. congruence. auto. 
    rewrite PTree.gso; auto.
  intros. exploit (P id0). tauto. intros [X Y]. rewrite X; rewrite Y.
    split; apply PTree.gso; intuition.
Qed.

Lemma alloc_variables_load:
  forall e m vars e' m',
  alloc_variables e m vars e' m' ->
  forall chunk b ofs v,
  Mem.load chunk m b ofs = Some v ->
  Mem.load chunk m' b ofs = Some v.
Proof.
  induction 1; intros.
  auto.
  apply IHalloc_variables. eapply Mem.load_alloc_other; eauto.
Qed.

Lemma sizeof_by_value:
  forall ty chunk,
  access_mode ty = By_value chunk -> sizeof ty = size_chunk chunk.
Proof.
  unfold access_mode; intros. 
  destruct ty; try destruct i; try destruct s; try destruct f; inv H; auto.
Qed.

Definition env_initial_value (e: env) (m: mem) :=
  forall id b ty chunk,
  e!id = Some(b, ty) -> access_mode ty = By_value chunk -> Mem.load chunk m b 0 = Some Vundef.
 
Lemma alloc_variables_initial_value:
  forall e m vars e' m',
  alloc_variables e m vars e' m' ->
  env_initial_value e m ->
  env_initial_value e' m'.
Proof.
  induction 1; intros.
  auto.
  apply IHalloc_variables. red; intros. rewrite PTree.gsspec in H2. 
  destruct (peq id0 id). inv H2. 
  eapply Mem.load_alloc_same'; eauto. 
  omega. erewrite sizeof_by_value; eauto. omega. 
  apply Zdivide_0. 
  eapply Mem.load_alloc_other; eauto. 
Qed.

Lemma create_undef_temps_charact:
  forall id ty vars, In (id, ty) vars -> (create_undef_temps vars)!id = Some Vundef.
Proof.
  induction vars; simpl; intros.
  contradiction.
  destruct H. subst a. apply PTree.gss. 
  destruct a as [id1 ty1]. rewrite PTree.gsspec. destruct (peq id id1); auto. 
Qed.

Lemma create_undef_temps_inv:
  forall vars id v, (create_undef_temps vars)!id = Some v -> v = Vundef /\ In id (var_names vars).
Proof.
  induction vars; simpl; intros. 
  rewrite PTree.gempty in H; congruence.
  destruct a as [id1 ty1]. rewrite PTree.gsspec in H. destruct (peq id id1).
  inv H. auto.
  exploit IHvars; eauto. tauto.
Qed.

Lemma create_undef_temps_exten:
  forall id l1 l2,
  (In id (var_names l1) <-> In id (var_names l2)) ->
  (create_undef_temps l1)!id = (create_undef_temps l2)!id.
Proof.
  assert (forall id l1 l2,
          (In id (var_names l1) -> In id (var_names l2)) ->
          (create_undef_temps l1)!id = None \/ (create_undef_temps l1)!id = (create_undef_temps l2)!id).
    intros. destruct ((create_undef_temps l1)!id) as [v1|] eqn:?; auto.
    exploit create_undef_temps_inv; eauto. intros [A B]. subst v1.
    exploit list_in_map_inv. unfold var_names in H. apply H. eexact B.
    intros [[id1 ty1] [P Q]]. simpl in P; subst id1.
    right; symmetry; eapply create_undef_temps_charact; eauto.
  intros. 
  exploit (H id l1 l2). tauto. 
  exploit (H id l2 l1). tauto. 
  intuition congruence.
Qed.

Remark var_names_app:
  forall vars1 vars2, var_names (vars1 ++ vars2) = var_names vars1 ++ var_names vars2.
Proof.
  intros. apply map_app. 
Qed.

Remark filter_app:
  forall (A: Type) (f: A -> bool) l1 l2,
  List.filter f (l1 ++ l2) = List.filter f l1 ++ List.filter f l2.
Proof.
  induction l1; simpl; intros.
  auto.
  destruct (f a). simpl. decEq; auto. auto.
Qed.

Remark filter_charact:
  forall (A: Type) (f: A -> bool) x l,
  In x (List.filter f l) <-> In x l /\ f x = true.
Proof.
  induction l; simpl. tauto. 
  destruct (f a) eqn:?. 
  simpl. rewrite IHl. intuition congruence.
  intuition congruence.
Qed.

Remark filter_norepet:
  forall (A: Type) (f: A -> bool) l,
  list_norepet l -> list_norepet (List.filter f l).
Proof.
  induction 1; simpl. constructor. 
  destruct (f hd); auto. constructor; auto. rewrite filter_charact. tauto. 
Qed.

Remark filter_map:
  forall (A B: Type) (f: A -> B) (pa: A -> bool) (pb: B -> bool),
  (forall a, pb (f a) = pa a) ->
  forall l, List.map f (List.filter pa l) = List.filter pb (List.map f l).
Proof.
  induction l; simpl.
  auto.
  rewrite H. destruct (pa a); simpl; congruence.
Qed.

Lemma create_undef_temps_lifted:
  forall id f,
  ~ In id (var_names (fn_params f)) ->
  (create_undef_temps (add_lifted (cenv_for f) (fn_vars f) (fn_temps f))) ! id =
  (create_undef_temps (add_lifted (cenv_for f) (fn_params f ++ fn_vars f) (fn_temps f))) ! id.
Proof.
  intros. apply create_undef_temps_exten. 
  unfold add_lifted. rewrite filter_app. 
  unfold var_names in *. 
  repeat rewrite map_app. repeat rewrite in_app. intuition. 
  exploit list_in_map_inv; eauto. intros [[id1 ty1] [P Q]]. simpl in P. subst id. 
  rewrite filter_charact in Q. destruct Q. 
  elim H. change id1 with (fst (id1, ty1)). apply List.in_map. auto.
Qed.

Lemma vars_and_temps_properties:
  forall cenv params vars temps,
  list_norepet (var_names params ++ var_names vars) ->
  list_disjoint (var_names params) (var_names temps) ->
  list_norepet (var_names params)
  /\ list_norepet (var_names (remove_lifted cenv (params ++ vars)))
  /\ list_disjoint (var_names params) (var_names (add_lifted cenv vars temps)).
Proof.
  intros. rewrite list_norepet_app in H. destruct H as [A [B C]].
  split. auto.
  split. unfold remove_lifted. unfold var_names. erewrite filter_map. 
  instantiate (1 := fun a => negb (VSet.mem a cenv)). 2: auto.
  apply filter_norepet. rewrite map_app. apply list_norepet_append; assumption.
  unfold add_lifted. rewrite var_names_app. 
  unfold var_names at 2. erewrite filter_map. 
  instantiate (1 := fun a => VSet.mem a cenv). 2: auto.
  change (map fst vars) with (var_names vars).
  red; intros.
  rewrite in_app in H1. destruct H1.
  rewrite filter_charact in H1. destruct H1. apply C; auto.
  apply H0; auto.
Qed.

Theorem match_envs_alloc_variables:
  forall cenv m vars e m' temps j tm,
  alloc_variables empty_env m vars e m' ->
  list_norepet (var_names vars) ->
  Mem.inject j m tm ->
  (forall id ty, In (id, ty) vars -> VSet.mem id cenv = true ->
                     exists chunk, access_mode ty = By_value chunk) ->
  (forall id, VSet.mem id cenv = true -> In id (var_names vars)) ->
  exists j', exists te, exists tm',
     alloc_variables empty_env tm (remove_lifted cenv vars) te tm'
  /\ match_envs j' cenv e (create_undef_temps temps) m' (Mem.nextblock m) (Mem.nextblock m')
                        te (create_undef_temps (add_lifted cenv vars temps)) (Mem.nextblock tm) (Mem.nextblock tm')
  /\ Mem.inject j' m' tm'
  /\ inject_incr j j'
  /\ (forall b, Mem.valid_block m b -> j' b = j b)
  /\ (forall b b' delta, j' b = Some(b', delta) -> Mem.valid_block tm b' -> j' b = j b).
Proof.
  intros. 
  exploit (match_alloc_variables cenv); eauto. instantiate (1 := empty_env). 
  intros [j' [te [tm' [A [B [C [D [E [K [F G]]]]]]]]]]. 
  exists j'; exists te; exists tm'.
  split. auto. split; auto.
  constructor; intros.
  (* vars *)
  destruct (In_dec ident_eq id (var_names vars)).
  unfold var_names in i. exploit list_in_map_inv; eauto.
  intros [[id' ty] [EQ IN]]; simpl in EQ; subst id'.
  exploit F; eauto. intros [b [P R]]. 
  destruct (VSet.mem id cenv) eqn:?.
  (* local var, lifted *)
  destruct R as [U V]. exploit H2; eauto. intros [chunk X]. 
  eapply match_var_lifted with (v := Vundef) (tv := Vundef); eauto.
  rewrite U; apply PTree.gempty.
  eapply alloc_variables_initial_value; eauto. 
  red. unfold empty_env; intros. rewrite PTree.gempty in H4; congruence.
  apply create_undef_temps_charact with ty. 
  unfold add_lifted. apply in_or_app. left.
  rewrite filter_In. auto.
  (* local var, not lifted *)
  destruct R as [tb [U V]].
  eapply match_var_not_lifted; eauto. 
  (* non-local var *)
  exploit G; eauto. unfold empty_env. rewrite PTree.gempty. intros [U V].
  eapply match_var_not_local; eauto. 
  destruct (VSet.mem id cenv) eqn:?; auto.
  elim n; eauto.

  (* temps *)
  exploit create_undef_temps_inv; eauto. intros [P Q]. subst v.
  unfold var_names in Q. exploit list_in_map_inv; eauto. 
  intros [[id1 ty] [EQ IN]]; simpl in EQ; subst id1. 
  split; auto. exists Vundef; split; auto. 
  apply create_undef_temps_charact with ty. unfold add_lifted. 
  apply in_or_app; auto.

  (* injective *)
  eapply alloc_variables_injective. eexact H. 
  rewrite PTree.gempty. congruence.
  intros. rewrite PTree.gempty in H7. congruence.
  eauto. eauto. auto. 

  (* range *)
  exploit alloc_variables_range. eexact H. eauto. 
  rewrite PTree.gempty. intuition congruence.

  (* trange *)
  exploit alloc_variables_range. eexact A. eauto. 
  rewrite PTree.gempty. intuition congruence.

  (* mapped *)
  destruct (In_dec ident_eq id (var_names vars)).
  unfold var_names in i. exploit list_in_map_inv; eauto. 
  intros [[id' ty'] [EQ IN]]; simpl in EQ; subst id'.
  exploit F; eauto. intros [b [P Q]].
  destruct (VSet.mem id cenv). 
  rewrite PTree.gempty in Q. destruct Q; congruence.
  destruct Q as [tb [U V]]. exists b; split; congruence.
  exploit G; eauto. rewrite PTree.gempty. intuition congruence.

  (* flat *)
  exploit alloc_variables_range. eexact A. eauto. 
  rewrite PTree.gempty. intros [P|P]. congruence. 
  exploit K; eauto. unfold Mem.valid_block. omega. 
  intros [id0 [ty0 [U [V W]]]]. split; auto. 
  destruct (ident_eq id id0). congruence.
  assert (b' <> b').
  eapply alloc_variables_injective with (e' := te) (id1 := id) (id2 := id0); eauto.
  rewrite PTree.gempty; congruence. 
  intros until ty1; rewrite PTree.gempty; congruence.
  congruence.

  (* incr *)
  eapply alloc_variables_nextblock; eauto.
  eapply alloc_variables_nextblock; eauto.
Qed.

Lemma assign_loc_inject:
  forall f ty m loc ofs v m' tm loc' ofs' v',
  assign_loc ty m loc ofs v m' ->
  val_inject f (Vptr loc ofs) (Vptr loc' ofs') ->
  val_inject f v v' ->
  Mem.inject f m tm ->
  exists tm',
     assign_loc ty tm loc' ofs' v' tm'
  /\ Mem.inject f m' tm'
  /\ (forall b chunk v,
      f b = None -> Mem.load chunk m b 0 = Some v -> Mem.load chunk m' b 0 = Some v).
Proof.
  intros. inv H.
  (* by value *)
  exploit Mem.storev_mapped_inject; eauto. intros [tm' [A B]].
  exists tm'; split. eapply assign_loc_value; eauto. 
  split. auto.
  intros. rewrite <- H5. eapply Mem.load_store_other; eauto.
  left. inv H0. congruence.
  (* by copy *)
  inv H0. inv H1.
  rename b' into bsrc. rename ofs'0 into osrc. 
  rename loc into bdst. rename ofs into odst.
  rename loc' into bdst'. rename b2 into bsrc'.
  exploit Mem.loadbytes_length; eauto. intros LEN.
  assert (SZPOS: sizeof ty > 0) by apply sizeof_pos.
  assert (RPSRC: Mem.range_perm m bsrc (Int.unsigned osrc) (Int.unsigned osrc + sizeof ty) Cur Nonempty).
    eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm; eauto. auto with mem.
  assert (RPDST: Mem.range_perm m bdst (Int.unsigned odst) (Int.unsigned odst + sizeof ty) Cur Nonempty).
    replace (sizeof ty) with (Z_of_nat (length bytes)).
    eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. auto with mem.
    rewrite LEN. apply nat_of_Z_eq. omega.
  assert (PSRC: Mem.perm m bsrc (Int.unsigned osrc) Cur Nonempty).
    apply RPSRC. omega.
  assert (PDST: Mem.perm m bdst (Int.unsigned odst) Cur Nonempty).
    apply RPDST. omega.
  exploit Mem.address_inject.  eauto. eexact PSRC. eauto. intros EQ1.
  exploit Mem.address_inject.  eauto. eexact PDST. eauto. intros EQ2.
  exploit Mem.loadbytes_inject; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_mapped_inject; eauto. intros [tm' [C D]].
  exists tm'. 
  split. eapply assign_loc_copy; try rewrite EQ1; try rewrite EQ2; eauto. 
  eapply Mem.aligned_area_inject with (m := m); eauto. apply alignof_1248.
  apply sizeof_alignof_compat.
  eapply Mem.aligned_area_inject with (m := m); eauto. apply alignof_1248.
  apply sizeof_alignof_compat.
  eapply Mem.disjoint_or_equal_inject with (m := m); eauto.
  apply Mem.range_perm_max with Cur; auto.
  apply Mem.range_perm_max with Cur; auto.
  split. auto.
  intros. rewrite <- H0. eapply Mem.load_storebytes_other; eauto. 
  left. congruence.
Qed.

Remark bind_parameter_temps_inv:
  forall id params args le le',
  bind_parameter_temps params args le = Some le' ->
  ~In id (var_names params) ->
  le'!id = le!id.
Proof.
  induction params; simpl; intros. 
  destruct args; inv H. auto.
  destruct a as [id1 ty1]. destruct args; try discriminate. 
  transitivity ((PTree.set id1 v le)!id). 
  eapply IHparams; eauto. apply PTree.gso. intuition. 
Qed.

Lemma assign_loc_nextblock:
  forall ty m b ofs v m',
  assign_loc ty m b ofs v m' -> Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction 1. 
  simpl in H0. eapply Mem.nextblock_store; eauto.
  eapply Mem.nextblock_storebytes; eauto.
Qed.

Theorem store_params_correct:
  forall j f k cenv le lo hi te tlo thi e m params args m',
  bind_parameters e m params args m' ->
  forall s tm tle1 tle2 targs,
  list_norepet (var_names params) ->
  list_forall2 val_casted args (map snd params) ->
  val_list_inject j args targs ->
  match_envs j cenv e le m lo hi te tle1 tlo thi ->
  Mem.inject j m tm ->
  (forall id, ~In id (var_names params) -> tle2!id = tle1!id) ->
  (forall id, In id (var_names params) -> le!id = None) ->
  exists tle, exists tm',
  star step2 tge (State f (store_params cenv params s) k te tle tm)
             E0 (State f s k te tle tm')
  /\ bind_parameter_temps params targs tle2 = Some tle
  /\ Mem.inject j m' tm'
  /\ match_envs j cenv e le m' lo hi te tle tlo thi
  /\ Mem.nextblock tm' = Mem.nextblock tm.
Proof.
  induction 1; simpl; intros until targs; intros NOREPET CASTED VINJ MENV MINJ TLE LE.
  (* base case *)
  inv VINJ. exists tle2; exists tm; split. apply star_refl. split. auto. split. auto.
  split. apply match_envs_temps_exten with tle1; auto. auto.
  (* inductive case *)
  inv NOREPET. inv CASTED. inv VINJ.
  exploit me_vars; eauto. instantiate (1 := id); intros MV.
  destruct (VSet.mem id cenv) eqn:?.
  (* lifted to temp *)
  eapply IHbind_parameters with (tle1 := PTree.set id v' tle1); eauto.
  eapply match_envs_assign_lifted; eauto. 
  inv MV; try congruence. rewrite ENV in H; inv H.
  inv H0; try congruence.
  unfold Mem.storev in H2. eapply Mem.store_unmapped_inject; eauto.
  intros. repeat rewrite PTree.gsspec. destruct (peq id0 id). auto.
  apply TLE. intuition. 
  (* still in memory *)
  inv MV; try congruence. rewrite ENV in H; inv H.
  exploit assign_loc_inject; eauto. 
  intros [tm1 [A [B C]]].
  exploit IHbind_parameters. eauto. eauto. eauto.
  instantiate (1 := PTree.set id v' tle1).
  apply match_envs_change_temp.  
  eapply match_envs_invariant; eauto.
  apply LE; auto. auto.
  eauto.
  instantiate (1 := PTree.set id v' tle2). 
  intros. repeat rewrite PTree.gsspec. destruct (peq id0 id). auto.
  apply TLE. intuition.
  intros. apply LE. auto.
  instantiate (1 := s). 
  intros [tle [tm' [U [V [X [Y Z]]]]]].
  exists tle; exists tm'; split.
  eapply star_trans.
  eapply star_left. econstructor.
  eapply star_left. econstructor. 
    eapply eval_Evar_local. eauto. 
    eapply eval_Etempvar. erewrite bind_parameter_temps_inv; eauto.
    apply PTree.gss. 
    simpl. instantiate (1 := v'). apply cast_val_casted.
    eapply val_casted_inject with (v := v1); eauto.
    simpl. eexact A. 
  apply star_one. constructor.
  reflexivity. reflexivity. 
  eexact U. 
  traceEq.
  rewrite (assign_loc_nextblock _ _ _ _ _ _ A) in Z. auto. 
Qed.

Lemma bind_parameters_nextblock:
  forall e m params args m',
  bind_parameters e m params args m' -> Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction 1.
  auto.
  rewrite IHbind_parameters. eapply assign_loc_nextblock; eauto. 
Qed.

Lemma bind_parameters_load:
  forall e chunk b ofs,
  (forall id b' ty, e!id = Some(b', ty) -> b <> b') ->
  forall m params args m',
  bind_parameters e m params args m' ->
  Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  induction 2.
  auto.
  rewrite IHbind_parameters.
  assert (b <> b0) by eauto.
  inv H1. 
  simpl in H5. eapply Mem.load_store_other; eauto.
  eapply Mem.load_storebytes_other; eauto.
Qed.

(** Freeing of local variables *)

Lemma free_blocks_of_env_perm_1:
  forall m e m' id b ty ofs k p,
  Mem.free_list m (blocks_of_env e) = Some m' ->
  e!id = Some(b, ty) ->
  Mem.perm m' b ofs k p ->
  0 <= ofs < sizeof ty ->
  False.
Proof.
  intros. exploit Mem.perm_free_list; eauto. intros [A B].
  apply B with 0 (sizeof ty); auto.
  unfold blocks_of_env. change (b, 0, sizeof ty) with (block_of_binding (id, (b, ty))).
  apply in_map. apply PTree.elements_correct. auto.
Qed.

Lemma free_list_perm':
  forall b lo hi l m m',
  Mem.free_list m l = Some m' ->
  In (b, lo, hi) l ->
  Mem.range_perm m b lo hi Cur Freeable.
Proof.
  induction l; simpl; intros.
  contradiction.
  destruct a as [[b1 lo1] hi1]. 
  destruct (Mem.free m b1 lo1 hi1) as [m1|] eqn:?; try discriminate.
  destruct H0. inv H0. eapply Mem.free_range_perm; eauto. 
  red; intros. eapply Mem.perm_free_3; eauto. eapply IHl; eauto. 
Qed.

Lemma free_blocks_of_env_perm_2:
  forall m e m' id b ty,
  Mem.free_list m (blocks_of_env e) = Some m' ->
  e!id = Some(b, ty) ->
  Mem.range_perm m b 0 (sizeof ty) Cur Freeable.
Proof.
  intros. eapply free_list_perm'; eauto. 
  unfold blocks_of_env. change (b, 0, sizeof ty) with (block_of_binding (id, (b, ty))).
  apply in_map. apply PTree.elements_correct. auto.
Qed.

Lemma can_free_list:
  forall l m,
  (forall b lo hi, In (b, lo, hi) l -> Mem.range_perm m b lo hi Cur Freeable) ->
  list_norepet (map (fun b_lo_hi => fst(fst b_lo_hi)) l) ->
  exists m', Mem.free_list m l = Some m'.
Proof.
  induction l; simpl; intros.
  exists m; auto.
  destruct a as [[b lo] hi]. simpl in H0. inv H0. 
  destruct (Mem.range_perm_free m b lo hi) as [m1 A]; auto. 
  rewrite A. apply IHl; auto. intros. 
  red; intros. eapply Mem.perm_free_1; eauto. 
  left; red; intros. subst b0. elim H3.
  set (F := fun b_lo_hi : block * Z * Z => fst (fst b_lo_hi)).
  change b with (F (b,lo0,hi0)). eapply in_map; auto.
  eapply H; eauto. 
Qed.

Lemma free_list_right_inject:
  forall j m1 l m2 m2',
  Mem.inject j m1 m2 ->
  Mem.free_list m2 l = Some m2' ->
  (forall b1 b2 delta lo hi ofs k p,
     j b1 = Some(b2, delta) -> In (b2, lo, hi) l ->
     Mem.perm m1 b1 ofs k p -> lo <= ofs + delta < hi -> False) ->
  Mem.inject j m1 m2'.
Proof.
  induction l; simpl; intros.
  congruence.
  destruct a as [[b lo] hi]. destruct (Mem.free m2 b lo hi) as [m21|] eqn:?; try discriminate.
  eapply IHl with (m2 := m21); eauto.
  eapply Mem.free_right_inject; eauto. 
Qed.

Theorem match_envs_free_blocks:
  forall j cenv e le m lo hi te tle tlo thi m' tm,
  match_envs j cenv e le m lo hi te tle tlo thi ->
  Mem.inject j m tm ->
  Mem.free_list m (blocks_of_env e) = Some m' ->
  exists tm',
     Mem.free_list tm (blocks_of_env te) = Some tm'
  /\ Mem.inject j m' tm'.
Proof.
  intros. 
  assert (exists tm', Mem.free_list tm (blocks_of_env te) = Some tm').
    apply can_free_list.
    intros. unfold blocks_of_env in H2.
    exploit list_in_map_inv; eauto. intros [[id [b' ty]] [EQ IN]].
    simpl in EQ; inv EQ. 
    exploit me_mapped; eauto. eapply PTree.elements_complete; eauto. 
    intros [b [A B]]. 
    change 0 with (0 + 0). replace (sizeof ty) with (sizeof ty + 0) by omega.
    eapply Mem.range_perm_inject; eauto. 
    eapply free_blocks_of_env_perm_2; eauto.
    (* no repetitions *)
    set (F := fun id => match te!id with Some(b, ty) => b | None => 0 end).
    replace (map (fun b_lo_hi : block * Z * Z => fst (fst b_lo_hi)) (blocks_of_env te))
       with (map F (map (fun x => fst x) (PTree.elements te))).
    apply list_map_norepet. apply PTree.elements_keys_norepet. 
    intros. 
    exploit list_in_map_inv. eexact H2. intros [[id1 [b1' ty1]] [EQ1 IN1]].
    exploit list_in_map_inv. eexact H3. intros [[id2 [b2' ty2]] [EQ2 IN2]].
    simpl in *. subst x y.
    assert (te!id1 = Some(b1', ty1)) by (apply PTree.elements_complete; auto).
    assert (te!id2 = Some(b2', ty2)) by (apply PTree.elements_complete; auto).
    exploit me_mapped. eauto. eexact H5. intros [b1 [P1 Q1]].
    exploit me_mapped. eauto. eexact H6. intros [b2 [P2 Q2]].
    assert (b1 <> b2) by (eapply me_inj; eauto). 
    exploit Mem.mi_no_overlap; eauto. 
    instantiate (1 := 0). apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
    eapply free_blocks_of_env_perm_2; eauto. generalize (sizeof_pos ty1); omega.
    instantiate (1 := 0). apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
    eapply free_blocks_of_env_perm_2; eauto. generalize (sizeof_pos ty2); omega.
    intros [A | A]; try omegaContradiction. 
    unfold F. rewrite H5; rewrite H6. auto.
    unfold blocks_of_env. repeat rewrite list_map_compose. apply list_map_exten; intros. 
    unfold F. destruct x as [id [b ty]]. simpl. erewrite PTree.elements_complete; eauto. auto.
  destruct H2 as [tm' FREE].
  exists tm'; split; auto.
  eapply free_list_right_inject; eauto. 
  eapply Mem.free_list_left_inject; eauto. 
  intros. unfold blocks_of_env in H3. exploit list_in_map_inv; eauto. 
  intros [[id [b' ty]] [EQ IN]]. simpl in EQ. inv EQ.
  exploit me_flat; eauto. apply PTree.elements_complete; eauto. 
  intros [P Q]. subst delta. eapply free_blocks_of_env_perm_1 with (m := m); eauto.
  omega. 
Qed.

(** Matching global environments *)

Inductive match_globalenvs (f: meminj) (bound: Z): Prop :=
  | mk_match_globalenvs
      (POS: bound > 0)
      (DOMAIN: forall b, b < bound -> f b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, f b1 = Some(b2, delta) -> b2 < bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> b < bound)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> b < bound)
      (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> b < bound).

Lemma match_globalenvs_preserves_globals:
  forall f,
  (exists bound, match_globalenvs f bound) ->
  meminj_preserves_globals ge f.
Proof.
  intros. destruct H as [bound MG]. inv MG.
  split; intros. eauto. split; intros. eauto. symmetry. eapply IMAGE; eauto.
Qed. 

(** Evaluation of expressions *)

Section EVAL_EXPR.

Variables e te: env.
Variables le tle: temp_env.
Variables m tm: mem.
Variable f: meminj.
Variable cenv: compilenv.
Variables lo hi tlo thi: Z.
Hypothesis MATCH: match_envs f cenv e le m lo hi te tle tlo thi.
Hypothesis MEMINJ: Mem.inject f m tm.
Hypothesis GLOB: exists bound, match_globalenvs f bound.

Lemma typeof_simpl_expr:
  forall a, typeof (simpl_expr cenv a) = typeof a.
Proof.
  destruct a; simpl; auto. destruct (VSet.mem i cenv); auto.
Qed.

Lemma deref_loc_inject:
  forall ty loc ofs v loc' ofs',
  deref_loc ty m loc ofs v ->
  val_inject f (Vptr loc ofs) (Vptr loc' ofs') ->
  exists tv, deref_loc ty tm loc' ofs' tv /\ val_inject f v tv.
Proof.
  intros. inv H. 
  (* by value *)
  exploit Mem.loadv_inject; eauto. intros [tv [A B]]. 
  exists tv; split; auto. eapply deref_loc_value; eauto.
  (* by reference *)
  exists (Vptr loc' ofs'); split; auto. eapply deref_loc_reference; eauto.
  (* by copy *)
  exists (Vptr loc' ofs'); split; auto. eapply deref_loc_copy; eauto.
Qed.

Remark val_inject_vtrue: forall f, val_inject f Vtrue Vtrue.
Proof. unfold Vtrue; auto. Qed.

Remark val_inject_vfalse: forall f, val_inject f Vfalse Vfalse.
Proof. unfold Vfalse; auto. Qed.

Remark val_inject_of_bool: forall f b, val_inject f (Val.of_bool b) (Val.of_bool b).
Proof. intros. unfold Val.of_bool. destruct b; [apply val_inject_vtrue|apply val_inject_vfalse]. 
Qed.

Hint Resolve val_inject_vtrue val_inject_vfalse val_inject_of_bool.

Ltac TrivialInject :=
  match goal with
  | |- exists v', Some ?v = Some v' /\ _ => exists v; split; auto
(*
  | |- exists v', _ /\ val_inject _ (Vint ?n) _ => exists (Vint n); split; auto
  | |- exists v', _ /\ val_inject _ (Vfloat ?n) _ => exists (Vfloat n); split; auto
  | |- exists v', _ /\ val_inject _ Vtrue _ => exists Vtrue; split; auto
  | |- exists v', _ /\ val_inject _ Vfalse _ => exists Vfalse; split; auto
  | |- exists v', _ /\ val_inject _ (Val.of_bool ?b) _ => exists (Val.of_bool b); split; auto
*)
  | _ => idtac
  end.

Lemma sem_unary_operation_inject:
  forall op v1 ty v tv1,
  sem_unary_operation op v1 ty = Some v ->
  val_inject f v1 tv1 ->
  exists tv, sem_unary_operation op tv1 ty = Some tv /\ val_inject f v tv.
Proof.
  unfold sem_unary_operation; intros. destruct op.
  (* notbool *)
  unfold sem_notbool in *; destruct (classify_bool ty); inv H0; inv H; TrivialInject.
  (* notint *)
  unfold sem_notint in *; destruct (classify_notint ty); inv H0; inv H; TrivialInject.
  (* neg *)
  unfold sem_neg in *; destruct (classify_neg ty); inv H0; inv H; TrivialInject.
Qed.

Lemma sem_cmp_inject:
  forall cmp v1 tv1 ty1 v2 tv2 ty2 v,
  sem_cmp cmp v1 ty1 v2 ty2 m = Some v ->
  val_inject f v1 tv1 ->
  val_inject f v2 tv2 ->
  exists tv, sem_cmp cmp tv1 ty1 tv2 ty2 tm = Some tv /\ val_inject f v tv.
Proof.
  unfold sem_cmp; intros. 
  assert (MM: option_map Val.of_bool (Val.cmp_different_blocks cmp) = Some v ->
      exists tv, option_map Val.of_bool (Val.cmp_different_blocks cmp) = Some tv /\ val_inject f v tv).
    intros. exists v; split; auto. 
    destruct cmp; simpl in H2; inv H2; auto.

  destruct (classify_cmp ty1 ty2); try destruct s; inv H0; try discriminate; inv H1; inv H; TrivialInject.
  destruct (Int.eq i Int.zero); try discriminate; auto.
  destruct (Int.eq i Int.zero); try discriminate; auto.

  destruct (zeq b1 b0); subst.
  rewrite H0 in H2. inv H2. rewrite zeq_true.
  destruct (Mem.weak_valid_pointer m b0 (Int.unsigned ofs1)) eqn:?; try discriminate.
  destruct (Mem.weak_valid_pointer m b0 (Int.unsigned ofs0)) eqn:?; try discriminate.
  simpl H3.
  rewrite (Mem.weak_valid_pointer_inject_val _ _ _ _ _ _ _ MEMINJ Heqb) by eauto.
  rewrite (Mem.weak_valid_pointer_inject_val _ _ _ _ _ _ _ MEMINJ Heqb0) by eauto.
  simpl. replace  (Int.cmpu cmp (Int.add ofs1 (Int.repr delta))
                         (Int.add ofs0 (Int.repr delta)))
     with  (Int.cmpu cmp ofs1 ofs0).
  inv H3; TrivialInject.
  symmetry. apply Int.translate_cmpu. 
  eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  destruct (Mem.valid_pointer m b1 (Int.unsigned ofs1)) eqn:?; try discriminate.
  destruct (Mem.valid_pointer m b0 (Int.unsigned ofs0)) eqn:?; try discriminate.
  destruct (zeq b2 b3); subst.
  rewrite Mem.valid_pointer_implies
    by (eapply (Mem.valid_pointer_inject_val _ _ _ _ _ _ _ MEMINJ Heqb); eauto).
  rewrite Mem.valid_pointer_implies
    by (eapply (Mem.valid_pointer_inject_val _ _ _ _ _ _ _ MEMINJ Heqb0); eauto).
  simpl.
  exploit Mem.different_pointers_inject; eauto. intros [[]|A]. easy.
  destruct cmp; simpl in H3; inv H3.
  simpl. unfold Int.eq. rewrite zeq_false; auto.
  simpl. unfold Int.eq. rewrite zeq_false; auto.
  rewrite (Mem.valid_pointer_inject_val _ _ _ _ _ _ _ MEMINJ Heqb) by eauto.
  rewrite (Mem.valid_pointer_inject_val _ _ _ _ _ _ _ MEMINJ Heqb0) by eauto.
  simpl in H3 |- *. auto.
Qed.

Lemma sem_binary_operation_inject:
  forall op v1 ty1 v2 ty2 v tv1 tv2,
  sem_binary_operation op v1 ty1 v2 ty2 m = Some v ->
  val_inject f v1 tv1 -> val_inject f v2 tv2 ->
  exists tv, sem_binary_operation op tv1 ty1 tv2 ty2 tm = Some tv /\ val_inject f v tv.
Proof.
  unfold sem_binary_operation; intros. destruct op.
(* add *)
  unfold sem_add in *; destruct (classify_add ty1 ty2); inv H0; try discriminate; inv H1; inv H; TrivialInject.
  econstructor. eauto. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  econstructor. eauto. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
(* sub *)
  unfold sem_sub in *; destruct (classify_sub ty1 ty2); inv H0; try discriminate; inv H1; inv H; TrivialInject.
  econstructor. eauto. rewrite Int.sub_add_l. auto. 
  destruct (zeq b1 b0); try discriminate. subst b1. rewrite H0 in H2; inv H2.
  rewrite zeq_true. destruct (Int.eq (Int.repr (sizeof ty)) Int.zero); inv H3.
  rewrite Int.sub_shifted. TrivialInject. 
(* mul *)
  unfold sem_mul in *; destruct (classify_mul ty1 ty2); inv H0; try discriminate; inv H1; inv H; TrivialInject.
(* div *)
  unfold sem_div in *; destruct (classify_div ty1 ty2); try destruct s; inv H0; try discriminate; inv H1; inv H; TrivialInject.
  destruct ( Int.eq i0 Int.zero
           || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H1; TrivialInject.
  destruct (Int.eq i0 Int.zero); inv H1; TrivialInject.
(* mod *)
  unfold sem_mod in *; destruct (classify_binint ty1 ty2); try destruct s; inv H0; try discriminate; inv H1; inv H; TrivialInject.
  destruct ( Int.eq i0 Int.zero
           || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H1; TrivialInject.
  destruct (Int.eq i0 Int.zero); inv H1; TrivialInject.
(* and *)
  unfold sem_and in *; destruct (classify_binint ty1 ty2); inv H0; try discriminate; inv H1; inv H; TrivialInject.
(* or *)
  unfold sem_or in *; destruct (classify_binint ty1 ty2); inv H0; try discriminate; inv H1; inv H; TrivialInject.
(* xor *)
  unfold sem_xor in *; destruct (classify_binint ty1 ty2); inv H0; try discriminate; inv H1; inv H; TrivialInject.
(* shl *)
  unfold sem_shl in *; destruct (classify_shift ty1 ty2); inv H0; try discriminate; inv H1; inv H; TrivialInject.
  destruct (Int.ltu i0 Int.iwordsize); inv H1; TrivialInject.
(* shr *)
  unfold sem_shr in *; destruct (classify_shift ty1 ty2); try destruct s; inv H0; try discriminate; inv H1; inv H; TrivialInject.
  destruct (Int.ltu i0 Int.iwordsize); inv H1; TrivialInject.
  destruct (Int.ltu i0 Int.iwordsize); inv H1; TrivialInject.
(* comparisons *)
  eapply sem_cmp_inject; eauto.
  eapply sem_cmp_inject; eauto.
  eapply sem_cmp_inject; eauto.
  eapply sem_cmp_inject; eauto.
  eapply sem_cmp_inject; eauto.
  eapply sem_cmp_inject; eauto.
Qed.

Lemma sem_cast_inject:
  forall v1 ty1 ty v tv1,
  sem_cast v1 ty1 ty = Some v ->
  val_inject f v1 tv1 ->
  exists tv, sem_cast tv1 ty1 ty = Some tv /\ val_inject f v tv.
Proof.
  unfold sem_cast; intros.
  destruct (classify_cast ty1 ty); try discriminate.
  inv H0; inv H; TrivialInject. econstructor; eauto.
  inv H0; inv H; TrivialInject. 
  inv H0; inv H; TrivialInject. 
  inv H0; inv H; TrivialInject. 
  inv H0; try discriminate. destruct (cast_float_int si2 f0); inv H. TrivialInject.
  inv H0; inv H. TrivialInject.
  inv H0; inv H. TrivialInject.
  TrivialInject.
  destruct (ident_eq id1 id2 && fieldlist_eq fld1 fld2); inv H. TrivialInject.
  destruct (ident_eq id1 id2 && fieldlist_eq fld1 fld2); inv H. TrivialInject.
  inv H; TrivialInject.
Qed.

Lemma bool_val_inject:
  forall v ty b tv,
  bool_val v ty = Some b ->
  val_inject f v tv ->
  bool_val tv ty = Some b.
Proof.
  unfold bool_val; intros. 
  destruct (classify_bool ty); inv H0; congruence.
Qed.

Lemma eval_simpl_expr:
  forall a v,
  eval_expr ge e le m a v ->
  compat_cenv (addr_taken_expr a) cenv ->
  exists tv, eval_expr tge te tle tm (simpl_expr cenv a) tv /\ val_inject f v tv

with eval_simpl_lvalue:
  forall a b ofs,
  eval_lvalue ge e le m a b ofs ->
  compat_cenv (addr_taken_expr a) cenv ->
  match a with Evar id ty => VSet.mem id cenv = false | _ => True end ->
  exists b', exists ofs', eval_lvalue tge te tle tm (simpl_expr cenv a) b' ofs' /\ val_inject f (Vptr b ofs) (Vptr b' ofs').

Proof.
  destruct 1; simpl; intros.
(* const *)
  exists (Vint i); split; auto. constructor.
  exists (Vfloat f0); split; auto. constructor.
(* tempvar *)
  exploit me_temps; eauto. intros [[tv [A B]] C]. 
  exists tv; split; auto. constructor; auto.
(* addrof *)
  exploit eval_simpl_lvalue; eauto. 
  destruct a; auto with compat.
  destruct a; auto. destruct (VSet.mem i cenv) eqn:?; auto. 
  elim (H0 i). apply VSet.singleton_2. auto. apply VSet.mem_2. auto.
  intros [b' [ofs' [A B]]]. 
  exists (Vptr b' ofs'); split; auto. constructor; auto. 
(* unop *)
  exploit eval_simpl_expr; eauto. intros [tv1 [A B]].
  exploit sem_unary_operation_inject; eauto. intros [tv [C D]].
  exists tv; split; auto. econstructor; eauto. rewrite typeof_simpl_expr; auto.
(* binop *)
  exploit eval_simpl_expr. eexact H. eauto with compat. intros [tv1 [A B]].
  exploit eval_simpl_expr. eexact H0. eauto with compat. intros [tv2 [C D]].
  exploit sem_binary_operation_inject; eauto. intros [tv [E F]].
  exists tv; split; auto. econstructor; eauto. repeat rewrite typeof_simpl_expr; auto.
(* cast *)
  exploit eval_simpl_expr; eauto. intros [tv1 [A B]].
  exploit sem_cast_inject; eauto. intros [tv2 [C D]].
  exists tv2; split; auto. econstructor. eauto. rewrite typeof_simpl_expr; auto. 
(* rval *)
  assert (EITHER: (exists id, exists ty, a = Evar id ty /\ VSet.mem id cenv = true)
               \/ (match a with Evar id _ => VSet.mem id cenv = false | _ => True end)).
    destruct a; auto. destruct (VSet.mem i cenv) eqn:?; auto. left; exists i; exists t; auto.  
  destruct EITHER as [ [id [ty [EQ OPT]]] | NONOPT ].
  (* a variable pulled out of memory *)
  subst a. simpl. rewrite OPT.
  exploit me_vars; eauto. instantiate (1 := id). intros MV. 
  inv H; inv MV; try congruence.
  rewrite ENV in H6; inv H6.
  inv H0; try congruence.
  assert (chunk0 = chunk). simpl in H. congruence. subst chunk0. 
  assert (v0 = v). unfold Mem.loadv in H2. rewrite Int.unsigned_zero in H2. congruence. subst v0.
  exists tv; split; auto. constructor; auto.
  simpl in H; congruence.
  simpl in H; congruence.
  (* any other l-value *)
  exploit eval_simpl_lvalue; eauto. intros [loc' [ofs' [A B]]].
  exploit deref_loc_inject; eauto. intros [tv [C D]].
  exists tv; split; auto. econstructor. eexact A. rewrite typeof_simpl_expr; auto. 

(* lvalues *)
  destruct 1; simpl; intros.
(* local var *)
  rewrite H1.    
  exploit me_vars; eauto. instantiate (1 := id). intros MV. inv MV; try congruence.
  rewrite ENV in H; inv H.
  exists b'; exists Int.zero; split.
  apply eval_Evar_local; auto.
  econstructor; eauto.
(* global var *)
  rewrite H3.
  exploit me_vars; eauto. instantiate (1 := id). intros MV. inv MV; try congruence.
  exists l; exists Int.zero; split.
  apply eval_Evar_global. auto. rewrite <- H0. apply symbols_preserved. 
  eapply type_of_global_preserved; eauto. 
  destruct GLOB as [bound GLOB1]. inv GLOB1.
  econstructor; eauto. 
(* deref *)
  exploit eval_simpl_expr; eauto. intros [tv [A B]]. 
  inversion B. subst. 
  econstructor; econstructor; split; eauto. econstructor; eauto. 
(* field struct *)
  exploit eval_simpl_expr; eauto. intros [tv [A B]]. 
  inversion B. subst. 
  econstructor; econstructor; split. 
  eapply eval_Efield_struct; eauto. rewrite typeof_simpl_expr; eauto. 
  econstructor; eauto. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
(* field union *)
  exploit eval_simpl_expr; eauto. intros [tv [A B]]. 
  inversion B. subst. 
  econstructor; econstructor; split. 
  eapply eval_Efield_union; eauto. rewrite typeof_simpl_expr; eauto. auto.
Qed.

Lemma eval_simpl_exprlist:
  forall al tyl vl,
  eval_exprlist ge e le m al tyl vl ->
  compat_cenv (addr_taken_exprlist al) cenv ->
  val_casted_list vl tyl /\
  exists tvl,
     eval_exprlist tge te tle tm (simpl_exprlist cenv al) tyl tvl
  /\ val_list_inject f vl tvl.
Proof.
  induction 1; simpl; intros.
  split. constructor. econstructor; split. constructor. auto.
  exploit eval_simpl_expr; eauto with compat. intros [tv1 [A B]].
  exploit sem_cast_inject; eauto. intros [tv2 [C D]].
  exploit IHeval_exprlist; eauto with compat. intros [E [tvl [F G]]].
  split. constructor; auto. eapply cast_val_is_casted; eauto.  
  exists (tv2 :: tvl); split. econstructor; eauto.
  rewrite typeof_simpl_expr; auto.
  econstructor; eauto.
Qed.

End EVAL_EXPR.

(** Matching continuations *)

Inductive match_cont (f: meminj): compilenv -> cont -> cont -> mem -> Z -> Z -> Prop :=
  | match_Kstop: forall cenv m bound tbound hi,
      match_globalenvs f hi -> hi <= bound -> hi <= tbound ->
      match_cont f cenv Kstop Kstop m bound tbound
  | match_Kseq: forall cenv s k ts tk m bound tbound,
      simpl_stmt cenv s = OK ts ->
      match_cont f cenv k tk m bound tbound ->
      compat_cenv (addr_taken_stmt s) cenv ->
      match_cont f cenv (Kseq s k) (Kseq ts tk) m bound tbound
  | match_Kloop1: forall cenv s1 s2 k ts1 ts2 tk m bound tbound,
      simpl_stmt cenv s1 = OK ts1 ->
      simpl_stmt cenv s2 = OK ts2 ->
      match_cont f cenv k tk m bound tbound ->
      compat_cenv (VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2)) cenv ->
      match_cont f cenv (Kloop1 s1 s2 k) (Kloop1 ts1 ts2 tk) m bound tbound
  | match_Kloop2: forall cenv s1 s2 k ts1 ts2 tk m bound tbound,
      simpl_stmt cenv s1 = OK ts1 ->
      simpl_stmt cenv s2 = OK ts2 ->
      match_cont f cenv k tk m bound tbound ->
      compat_cenv (VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2)) cenv ->
      match_cont f cenv (Kloop2 s1 s2 k) (Kloop2 ts1 ts2 tk) m bound tbound
  | match_Kswitch: forall cenv k tk m bound tbound,
      match_cont f cenv k tk m bound tbound ->
      match_cont f cenv (Kswitch k) (Kswitch tk) m bound tbound
  | match_Kcall: forall cenv optid fn e le k tfn te tle tk m hi thi lo tlo bound tbound x,
      transf_function fn = OK tfn ->
      match_envs f (cenv_for fn) e le m lo hi te tle tlo thi ->
      match_cont f (cenv_for fn) k tk m lo tlo ->
      check_opttemp (cenv_for fn) optid = OK x ->
      hi <= bound -> thi <= tbound ->
      match_cont f cenv (Kcall optid fn e le k)
                        (Kcall optid tfn te tle tk) m bound tbound.

(** Invariance property by change of memory and injection *)

Lemma match_cont_invariant:
  forall f' m' f cenv k tk m bound tbound,
  match_cont f cenv k tk m bound tbound ->
  (forall b chunk v,
    f b = None -> b < bound -> Mem.load chunk m b 0 = Some v -> Mem.load chunk m' b 0 = Some v) ->
  inject_incr f f' ->
  (forall b, b < bound -> f' b = f b) ->
  (forall b b' delta, f' b = Some(b', delta) -> b' < tbound -> f' b = f b) ->
  match_cont f' cenv k tk m' bound tbound.
Proof.
  induction 1; intros LOAD INCR INJ1 INJ2; econstructor; eauto.
(* globalenvs *)
  inv H. constructor; intros; eauto.
  assert (f b1 = Some (b2, delta)). rewrite <- H; symmetry; eapply INJ2; eauto. omega.
  eapply IMAGE; eauto.
(* call *)
  eapply match_envs_invariant; eauto. 
  intros. apply LOAD; auto. omega.
  intros. apply INJ1; auto; omega.
  intros. eapply INJ2; eauto; omega.
  eapply IHmatch_cont; eauto. 
  intros; apply LOAD; auto. inv H0; omega.
  intros; apply INJ1. inv H0; omega.
  intros; eapply INJ2; eauto. inv H0; omega.
Qed.

(** Invariance by assignment to location "above" *)

Lemma match_cont_assign_loc:
  forall f cenv k tk m bound tbound ty loc ofs v m',
  match_cont f cenv k tk m bound tbound ->
  assign_loc ty m loc ofs v m' ->
  bound <= loc ->
  match_cont f cenv k tk m' bound tbound.
Proof.
  intros. eapply match_cont_invariant; eauto.
  intros. rewrite <- H4. inv H0.
  (* scalar *)
  simpl in H6. eapply Mem.load_store_other; eauto. left. unfold block; omega. 
  (* block copy *)
  eapply Mem.load_storebytes_other; eauto. left. unfold block; omega.
Qed.

(** Invariance by external calls *)

Lemma match_cont_extcall:
  forall f cenv k tk m bound tbound tm f' m',
  match_cont f cenv k tk m bound tbound ->
  mem_unchanged_on (loc_unmapped f) m m' ->
  inject_incr f f' ->
  inject_separated f f' m tm ->
  bound <= Mem.nextblock m -> tbound <= Mem.nextblock tm ->
  match_cont f' cenv k tk m' bound tbound.
Proof.
  intros. eapply match_cont_invariant; eauto. 
  destruct H0. intros. eapply H5; eauto. 
  red in H2. intros. destruct (f b) as [[b' delta] | ] eqn:?. auto. 
  destruct (f' b) as [[b' delta] | ] eqn:?; auto. 
  exploit H2; eauto. unfold Mem.valid_block. intros [A B]. omegaContradiction.
  red in H2. intros. destruct (f b) as [[b'' delta''] | ] eqn:?. auto. 
  exploit H2; eauto. unfold Mem.valid_block. intros [A B]. omegaContradiction.
Qed.

(** Invariance by change of bounds *)

Lemma match_cont_incr_bounds:
  forall f cenv k tk m bound tbound,
  match_cont f cenv k tk m bound tbound ->
  forall bound' tbound',
  bound <= bound' -> tbound <= tbound' ->
  match_cont f cenv k tk m bound' tbound'.
Proof.
  induction 1; intros; econstructor; eauto; omega.
Qed.

(** [match_cont] and call continuations. *)

Lemma match_cont_change_cenv:
  forall f cenv k tk m bound tbound cenv',
  match_cont f cenv k tk m bound tbound ->
  is_call_cont k ->
  match_cont f cenv' k tk m bound tbound.
Proof.
  intros. inv H; simpl in H0; try contradiction; econstructor; eauto.
Qed.

Lemma match_cont_is_call_cont:
  forall f cenv k tk m bound tbound,
  match_cont f cenv k tk m bound tbound ->
  is_call_cont k ->
  is_call_cont tk.
Proof.
  intros. inv H; auto. 
Qed.

Lemma match_cont_call_cont:
  forall f cenv k tk m bound tbound,
  match_cont f cenv k tk m bound tbound ->
  forall cenv',
  match_cont f cenv' (call_cont k) (call_cont tk) m bound tbound.
Proof.
  induction 1; simpl; auto; intros; econstructor; eauto.
Qed.

(** [match_cont] and freeing of environment blocks *)

Remark free_list_nextblock:
  forall l m m',
  Mem.free_list m l = Some m' -> Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction l; simpl; intros.
  congruence.
  destruct a. destruct p. destruct (Mem.free m b z0 z) as [m1|] eqn:?; try discriminate.
  transitivity (Mem.nextblock m1). eauto. eapply Mem.nextblock_free; eauto. 
Qed.

Remark free_list_load:
  forall chunk b' l m m',
  Mem.free_list m l = Some m' ->
  (forall b lo hi, In (b, lo, hi) l -> b' < b) ->
  Mem.load chunk m' b' 0 = Mem.load chunk m b' 0.
Proof.
  induction l; simpl; intros.
  inv H; auto.
  destruct a. destruct p. destruct (Mem.free m b z0 z) as [m1|] eqn:?; try discriminate.
  transitivity (Mem.load chunk m1 b' 0). eauto. 
  eapply Mem.load_free. eauto. left. assert (b' < b) by eauto. unfold block; omega.
Qed.

Lemma match_cont_free_env:
  forall f cenv e le m lo hi te tle tm tlo thi k tk m' tm',
  match_envs f cenv e le m lo hi te tle tlo thi ->
  match_cont f cenv k tk m lo tlo ->
  hi <= Mem.nextblock m ->
  thi <= Mem.nextblock tm ->
  Mem.free_list m (blocks_of_env e) = Some m' ->
  Mem.free_list tm (blocks_of_env te) = Some tm' ->
  match_cont f cenv k tk m' (Mem.nextblock m') (Mem.nextblock tm').
Proof.
  intros. apply match_cont_incr_bounds with lo tlo.
  eapply match_cont_invariant; eauto. 
  intros. rewrite <- H7. eapply free_list_load; eauto. 
  unfold blocks_of_env; intros. exploit list_in_map_inv; eauto. 
  intros [[id [b1 ty]] [P Q]]. simpl in P. inv P. 
  exploit me_range; eauto. eapply PTree.elements_complete; eauto. omega.
  rewrite (free_list_nextblock _ _ _ H3). inv H; omega.
  rewrite (free_list_nextblock _ _ _ H4). inv H; omega.
Qed.

(** Matching of global environments *)

Lemma match_cont_globalenv:
  forall f cenv k tk m bound tbound,
  match_cont f cenv k tk m bound tbound ->
  exists bound, match_globalenvs f bound.
Proof.
  induction 1; auto. exists hi; auto. 
Qed.

Hint Resolve match_cont_globalenv: compat.

Lemma match_cont_find_funct:
  forall f cenv k tk m bound tbound vf fd tvf,
  match_cont f cenv k tk m bound tbound ->
  Genv.find_funct ge vf = Some fd ->
  val_inject f vf tvf ->
  exists tfd, Genv.find_funct tge tvf = Some tfd /\ transf_fundef fd = OK tfd.
Proof.
  intros. exploit match_cont_globalenv; eauto. intros [bound1 MG]. destruct MG.
  inv H1; simpl in H0; try discriminate. destruct (Int.eq_dec ofs1 Int.zero); try discriminate.
  subst ofs1.
  assert (f b1 = Some(b1, 0)). 
    apply DOMAIN. eapply FUNCTIONS; eauto. 
  rewrite H1 in H2; inv H2.
  rewrite Int.add_zero. simpl. rewrite dec_eq_true. apply function_ptr_translated; auto.
Qed.

(** Relating execution states *)

Inductive match_states: state -> state -> Prop :=
  | match_regular_states:
      forall f s k e le m tf ts tk te tle tm j lo hi tlo thi
        (TRF: transf_function f = OK tf)
        (TRS: simpl_stmt (cenv_for f) s = OK ts)
        (MENV: match_envs j (cenv_for f) e le m lo hi te tle tlo thi)
        (MCONT: match_cont j (cenv_for f) k tk m lo tlo)
        (MINJ: Mem.inject j m tm)
        (COMPAT: compat_cenv (addr_taken_stmt s) (cenv_for f))
        (BOUND: hi <= Mem.nextblock m)
        (TBOUND: thi <= Mem.nextblock tm),
      match_states (State f s k e le m)
                   (State tf ts tk te tle tm)
  | match_call_state:
      forall fd vargs k m tfd tvargs tk tm j targs tres
        (TRFD: transf_fundef fd = OK tfd)
        (MCONT: forall cenv, match_cont j cenv k tk m (Mem.nextblock m) (Mem.nextblock tm))
        (MINJ: Mem.inject j m tm)
        (AINJ: val_list_inject j vargs tvargs)
        (FUNTY: type_of_fundef fd = Tfunction targs tres)
        (ANORM: val_casted_list vargs targs),
      match_states (Callstate fd vargs k m)
                   (Callstate tfd tvargs tk tm)
  | match_return_state:
      forall v k m tv tk tm j
        (MCONT: forall cenv, match_cont j cenv k tk m (Mem.nextblock m) (Mem.nextblock tm))
        (MINJ: Mem.inject j m tm)
        (RINJ: val_inject j v tv),
      match_states (Returnstate v k m)
                   (Returnstate tv tk tm).

(** The simulation diagrams *)

Remark is_liftable_var_charact:
  forall cenv a,
  match is_liftable_var cenv a with
  | Some id => exists ty, a = Evar id ty /\ VSet.mem id cenv = true
  | None => match a with Evar id ty => VSet.mem id cenv = false | _ => True end
  end.
Proof.
  intros. destruct a; simpl; auto.
  destruct (VSet.mem i cenv) eqn:?. 
  exists t; auto. 
  auto.
Qed.

Remark simpl_select_switch:
  forall cenv n ls tls,
  simpl_lblstmt cenv ls = OK tls ->
  simpl_lblstmt cenv (select_switch n ls) = OK (select_switch n tls).
Proof.
  induction ls; simpl; intros.
  monadInv H. rewrite EQ; auto.
  monadInv H. simpl. destruct (Int.eq i n). 
  simpl. rewrite EQ; rewrite EQ1. auto. 
  eauto.
Qed.

Remark simpl_seq_of_labeled_statement:
  forall cenv ls tls,
  simpl_lblstmt cenv ls = OK tls ->
  simpl_stmt cenv (seq_of_labeled_statement ls) = OK (seq_of_labeled_statement tls).
Proof.
  induction ls; simpl; intros.
  monadInv H. auto. 
  monadInv H. rewrite EQ; simpl. erewrite IHls; eauto. simpl. auto.
Qed.

Remark compat_cenv_select_switch:
  forall cenv n ls,
  compat_cenv (addr_taken_lblstmt ls) cenv ->
  compat_cenv (addr_taken_lblstmt (select_switch n ls)) cenv.
Proof.
  induction ls; simpl; intros. auto. destruct (Int.eq i n); simpl; eauto with compat.
Qed.

Remark addr_taken_seq_of_labeled_statement:
  forall ls, addr_taken_stmt (seq_of_labeled_statement ls) = addr_taken_lblstmt ls.
Proof.
  induction ls; simpl; congruence.
Qed.

Section FIND_LABEL.

Variable f: meminj.
Variable cenv: compilenv.
Variable m: mem.
Variables bound tbound: block.
Variable lbl: ident.

Lemma simpl_find_label:
  forall s k ts tk,
  simpl_stmt cenv s = OK ts ->
  match_cont f cenv k tk m bound tbound ->
  compat_cenv (addr_taken_stmt s) cenv ->
  match find_label lbl s k with
  | None =>
      find_label lbl ts tk = None
  | Some(s', k') =>
      exists ts', exists tk', 
         find_label lbl ts tk = Some(ts', tk')
      /\ compat_cenv (addr_taken_stmt s') cenv
      /\ simpl_stmt cenv s' = OK ts'
      /\ match_cont f cenv k' tk' m bound tbound
  end

with simpl_find_label_ls:
  forall ls k tls tk,
  simpl_lblstmt cenv ls = OK tls ->
  match_cont f cenv k tk m bound tbound ->
  compat_cenv (addr_taken_lblstmt ls) cenv ->
  match find_label_ls lbl ls k with
  | None =>
      find_label_ls lbl tls tk = None
  | Some(s', k') =>
      exists ts', exists tk', 
         find_label_ls lbl tls tk = Some(ts', tk')
      /\ compat_cenv (addr_taken_stmt s') cenv
      /\ simpl_stmt cenv s' = OK ts'
      /\ match_cont f cenv k' tk' m bound tbound
  end.

Proof.
  induction s; simpl; intros until tk; intros TS MC COMPAT; auto.
  (* skip *)
  monadInv TS; auto.
  (* var *)
  destruct (is_liftable_var cenv e); monadInv TS; auto. 
  (* set *)
  monadInv TS; auto.
  (* call *)
  monadInv TS; auto.
  (* builtin *)
  monadInv TS; auto.
  (* seq *)
  monadInv TS.
  exploit (IHs1 (Kseq s2 k) x (Kseq x0 tk)); eauto with compat. 
    constructor; eauto with compat.
  destruct (find_label lbl s1 (Kseq s2 k)) as [[s' k']|]. 
  intros [ts' [tk' [P [Q [R S]]]]]. exists ts'; exists tk'. simpl. rewrite P. auto.
  intros E. simpl. rewrite E. eapply IHs2; eauto with compat.
  (* ifthenelse *)
  monadInv TS.
  exploit (IHs1 k x tk); eauto with compat. 
  destruct (find_label lbl s1 k) as [[s' k']|]. 
  intros [ts' [tk' [P [Q [R S]]]]]. exists ts'; exists tk'. simpl. rewrite P. auto. 
  intros E. simpl. rewrite E. eapply IHs2; eauto with compat.
  (* loop *)
  monadInv TS.
  exploit (IHs1 (Kloop1 s1 s2 k) x (Kloop1 x x0 tk)); eauto with compat.
    constructor; eauto with compat.
  destruct (find_label lbl s1 (Kloop1 s1 s2 k)) as [[s' k']|]. 
  intros [ts' [tk' [P [Q [R S]]]]]. exists ts'; exists tk'. simpl; rewrite P. auto. 
  intros E. simpl; rewrite E. eapply IHs2; eauto with compat. econstructor; eauto with compat.
  (* break *)
  monadInv TS; auto.
  (* continue *)
  monadInv TS; auto.
  (* return *)
  monadInv TS; auto.
  (* switch *)
  monadInv TS. simpl.
  eapply simpl_find_label_ls; eauto with compat. constructor; auto.
  (* label *)
  monadInv TS. simpl.
  destruct (ident_eq lbl l).
  exists x; exists tk; auto.
  eapply IHs; eauto.
  (* goto *)
  monadInv TS; auto.

  induction ls; simpl; intros.
  (* default *)
  monadInv H. apply simpl_find_label; auto. 
  (* case *)
  monadInv H.
  exploit (simpl_find_label s (Kseq (seq_of_labeled_statement ls) k)).
    eauto. constructor. eapply simpl_seq_of_labeled_statement; eauto. eauto.
    rewrite addr_taken_seq_of_labeled_statement. eauto with compat.
    eauto with compat. 
  destruct (find_label lbl s (Kseq (seq_of_labeled_statement ls) k)) as [[s' k']|].
  intros [ts' [tk' [P [Q [R S]]]]]. exists ts'; exists tk'; split. simpl; rewrite P. auto. auto.
  intros E. simpl; rewrite E. eapply IHls; eauto with compat.
Qed.

Lemma find_label_store_params:
  forall lbl s k params, find_label lbl (store_params cenv params s) k = find_label lbl s k.
Proof.
  induction params; simpl. auto. 
  destruct a as [id ty]. destruct (VSet.mem id cenv); auto. 
Qed.

End FIND_LABEL.  


Lemma step_simulation:
  forall S1 t S2, step1 ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus step2 tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; simpl; intros; inv MS; simpl in *; try (monadInv TRS).

(* assign *)
  generalize (is_liftable_var_charact (cenv_for f) a1); destruct (is_liftable_var (cenv_for f) a1) as [id|]; monadInv TRS.
  (* liftable *)
  intros [ty [P Q]]; subst a1; simpl in *.
  exploit eval_simpl_expr; eauto with compat. intros [tv2 [A B]].
  exploit sem_cast_inject; eauto. intros [tv [C D]].
  exploit me_vars; eauto. instantiate (1 := id). intros MV. 
  inv H.
  (* local variable *)
  econstructor; split. 
  apply plus_one. econstructor. eapply make_cast_correct. eexact A. rewrite typeof_simpl_expr. eexact C.
  econstructor; eauto with compat. 
  eapply match_envs_assign_lifted; eauto. eapply cast_val_is_casted; eauto.
  eapply match_cont_assign_loc; eauto. exploit me_range; eauto. omega.
  inv MV; try congruence. inv H2; try congruence. unfold Mem.storev in H3.
  eapply Mem.store_unmapped_inject; eauto. congruence. 
  erewrite assign_loc_nextblock; eauto.
  (* global variable *)
  inv MV; congruence.
  (* not liftable *)
  intros P. 
  exploit eval_simpl_lvalue; eauto with compat. intros [tb [tofs [E F]]]. 
  exploit eval_simpl_expr; eauto with compat. intros [tv2 [A B]].
  exploit sem_cast_inject; eauto. intros [tv [C D]].
  exploit assign_loc_inject; eauto. intros [tm' [X [Y Z]]]. 
  econstructor; split.
  apply plus_one. econstructor. eexact E. eexact A. repeat rewrite typeof_simpl_expr. eexact C. 
  rewrite typeof_simpl_expr; auto. eexact X.
  econstructor; eauto with compat. 
  eapply match_envs_invariant; eauto. 
  eapply match_cont_invariant; eauto. 
  erewrite assign_loc_nextblock; eauto.
  erewrite assign_loc_nextblock; eauto.

(* set temporary *)
  exploit eval_simpl_expr; eauto with compat. intros [tv [A B]].
  econstructor; split.
  apply plus_one. econstructor. eauto. 
  econstructor; eauto with compat. 
  eapply match_envs_set_temp; eauto. 

(* call *)
  exploit eval_simpl_expr; eauto with compat. intros [tvf [A B]].
  exploit eval_simpl_exprlist; eauto with compat. intros [CASTED [tvargs [C D]]].
  exploit match_cont_find_funct; eauto. intros [tfd [P Q]].
  econstructor; split.
  apply plus_one. eapply step_call with (fd := tfd).
  rewrite typeof_simpl_expr. eauto.
  eauto. eauto. eauto.  
  erewrite type_of_fundef_preserved; eauto.
  econstructor; eauto. 
  intros. econstructor; eauto.

(* builtin *)
  exploit eval_simpl_exprlist; eauto with compat. intros [CASTED [tvargs [C D]]].
  exploit external_call_mem_inject; eauto. apply match_globalenvs_preserves_globals; eauto with compat.
  intros [j' [tvres [tm' [P [Q [R [S [T [U V]]]]]]]]].
  econstructor; split.
  apply plus_one. econstructor; eauto. eapply external_call_symbols_preserved; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto with compat.
  eapply match_envs_set_opttemp; eauto. 
  eapply match_envs_extcall; eauto. 
  eapply match_cont_extcall; eauto.
  inv MENV; omega. inv MENV; omega. 
  eapply Zle_trans; eauto. eapply external_call_nextblock; eauto.
  eapply Zle_trans; eauto. eapply external_call_nextblock; eauto.

(* sequence *)
  econstructor; split. apply plus_one. econstructor.
  econstructor; eauto with compat. econstructor; eauto with compat.

(* skip sequence *)
  inv MCONT. econstructor; split. apply plus_one. econstructor. econstructor; eauto. 

(* continue sequence *)
  inv MCONT. econstructor; split. apply plus_one. econstructor. econstructor; eauto.
 
(* break sequence *)
  inv MCONT. econstructor; split. apply plus_one. econstructor. econstructor; eauto.

(* ifthenelse *)
  exploit eval_simpl_expr; eauto with compat. intros [tv [A B]].
  econstructor; split.
  apply plus_one. apply step_ifthenelse with (v1 := tv) (b := b). auto.
  rewrite typeof_simpl_expr. eapply bool_val_inject; eauto.
  destruct b; econstructor; eauto with compat.

(* loop *)
  econstructor; split. apply plus_one. econstructor. econstructor; eauto with compat. econstructor; eauto with compat.

(* skip-or-continue loop *)
  inv MCONT. econstructor; split.
  apply plus_one. econstructor. destruct H; subst x; simpl in *; intuition congruence. 
  econstructor; eauto with compat. econstructor; eauto with compat.

(* break loop1 *)
  inv MCONT. econstructor; split. apply plus_one. eapply step_break_loop1. 
  econstructor; eauto.

(* skip loop2 *)
  inv MCONT. econstructor; split. apply plus_one. eapply step_skip_loop2. 
  econstructor; eauto with compat. simpl; rewrite H2; rewrite H4; auto. 

(* break loop2 *)
  inv MCONT. econstructor; split. apply plus_one. eapply step_break_loop2. 
  econstructor; eauto.

(* return none *)
  exploit match_envs_free_blocks; eauto. intros [tm' [P Q]].
  econstructor; split. apply plus_one. econstructor; eauto. 
  econstructor; eauto. 
  intros. eapply match_cont_call_cont. eapply match_cont_free_env; eauto.

(* return some *)
  exploit eval_simpl_expr; eauto with compat. intros [tv [A B]].
  exploit sem_cast_inject; eauto. intros [tv' [C D]].
  exploit match_envs_free_blocks; eauto. intros [tm' [P Q]].
  econstructor; split. apply plus_one. econstructor; eauto.
  rewrite typeof_simpl_expr. monadInv TRF; simpl. eauto.
  econstructor; eauto. 
  intros. eapply match_cont_call_cont. eapply match_cont_free_env; eauto.

(* skip call *)
  exploit match_envs_free_blocks; eauto. intros [tm' [P Q]].
  econstructor; split. apply plus_one. econstructor; eauto.
  eapply match_cont_is_call_cont; eauto.
  monadInv TRF; auto.
  econstructor; eauto. 
  intros. apply match_cont_change_cenv with (cenv_for f); auto. eapply match_cont_free_env; eauto.

(* switch *)
  exploit eval_simpl_expr; eauto with compat. intros [tv [A B]]. inv B.
  econstructor; split. apply plus_one. econstructor; eauto.
  econstructor; eauto. 
  erewrite simpl_seq_of_labeled_statement. reflexivity.
  eapply simpl_select_switch; eauto. 
  econstructor; eauto. rewrite addr_taken_seq_of_labeled_statement. 
  apply compat_cenv_select_switch. eauto with compat.

(* skip-break switch *)
  inv MCONT. econstructor; split. 
  apply plus_one. eapply step_skip_break_switch. destruct H; subst x; simpl in *; intuition congruence. 
  econstructor; eauto with compat.

(* continue switch *)
  inv MCONT. econstructor; split. 
  apply plus_one. eapply step_continue_switch.
  econstructor; eauto with compat.

(* label *)
  econstructor; split. apply plus_one. econstructor. econstructor; eauto.

(* goto *)
  generalize TRF; intros TRF'. monadInv TRF'. 
  exploit (simpl_find_label j (cenv_for f) m lo tlo lbl (fn_body f) (call_cont k) x0 (call_cont tk)).
    eauto. eapply match_cont_call_cont. eauto.  
    apply compat_cenv_for.
  rewrite H. intros [ts' [tk' [A [B [C D]]]]]. 
  econstructor; split.
  apply plus_one. econstructor; eauto. simpl. rewrite find_label_store_params. eexact A.
  econstructor; eauto.

(* internal function *)
  monadInv TRFD. inv H. 
  generalize EQ; intro EQ'; monadInv EQ'.
  assert (list_norepet (var_names (fn_params f ++ fn_vars f))).
    unfold var_names. rewrite map_app. auto.
  assert (list_disjoint (var_names (fn_params f)) (var_names (fn_temps f))).
    monadInv EQ0. auto. 
  exploit match_envs_alloc_variables; eauto.
    instantiate (1 := cenv_for_gen (addr_taken_stmt f.(fn_body)) (fn_params f ++ fn_vars f)).
    intros. eapply cenv_for_gen_by_value; eauto. rewrite VSF.mem_iff. eexact H5.
    intros. eapply cenv_for_gen_domain. rewrite VSF.mem_iff. eexact H4.
  intros [j' [te [tm0 [A [B [C [D [E F]]]]]]]].
  exploit store_params_correct.
    eauto. 
    eapply list_norepet_append_left; eauto.
    apply val_casted_list_params. unfold type_of_function in FUNTY. congruence.
    apply val_list_inject_incr with j'; eauto. 
    eexact B. eexact C.
    intros. apply (create_undef_temps_lifted id f). auto.
    intros. destruct (create_undef_temps (fn_temps f))!id as [v|] eqn:?; auto.
    exploit create_undef_temps_inv; eauto. intros [P Q]. elim (H3 id id); auto.
  intros [tel [tm1 [P [Q [R [S T]]]]]].
  change (cenv_for_gen (addr_taken_stmt (fn_body f)) (fn_params f ++ fn_vars f))
    with (cenv_for f) in *.
  generalize (vars_and_temps_properties (cenv_for f) (fn_params f) (fn_vars f) (fn_temps f)).
  intros [X [Y Z]]. auto. auto. 
  econstructor; split. 
  eapply plus_left. econstructor. 
  econstructor. exact Y. exact X. exact Z. simpl. eexact A. simpl. eexact Q.
  simpl. eexact P.
  traceEq.
  econstructor; eauto. 
  eapply match_cont_invariant; eauto. 
  intros. transitivity (Mem.load chunk m0 b 0). 
  eapply bind_parameters_load; eauto. intros. 
  exploit alloc_variables_range. eexact H1. eauto. 
  unfold empty_env. rewrite PTree.gempty. intros [?|?]. congruence. 
  red; intros; subst b'. omega. 
  eapply alloc_variables_load; eauto.
  apply compat_cenv_for. 
  rewrite (bind_parameters_nextblock _ _ _ _ _ H2). omega.
  rewrite T; omega.

(* external function *)
  monadInv TRFD. inv FUNTY. 
  exploit external_call_mem_inject; eauto. apply match_globalenvs_preserves_globals. 
  eapply match_cont_globalenv. eexact (MCONT VSet.empty). 
  intros [j' [tvres [tm' [P [Q [R [S [T [U V]]]]]]]]].
  econstructor; split.
  apply plus_one. econstructor; eauto. eapply external_call_symbols_preserved; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.
  intros. apply match_cont_incr_bounds with (Mem.nextblock m) (Mem.nextblock tm).
  eapply match_cont_extcall; eauto. omega. omega.
  eapply external_call_nextblock; eauto.
  eapply external_call_nextblock; eauto.

(* return *)
  specialize (MCONT (cenv_for f)). inv MCONT. 
  econstructor; split.
  apply plus_one. econstructor. 
  econstructor; eauto with compat.
  eapply match_envs_set_opttemp; eauto.
Qed.

Lemma initial_states_simulation:
  forall S, initial_state prog S ->
  exists R, initial_state tprog R /\ match_states S R.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros [tf [A B]]. 
  econstructor; split.
  econstructor.
  eapply Genv.init_mem_transf_partial; eauto.
  rewrite (transform_partial_program_main _ _ TRANSF).
  instantiate (1 := b). rewrite <- H1. apply symbols_preserved.
  eauto.
  rewrite <- H3; apply type_of_fundef_preserved; auto.
  econstructor; eauto. 
  intros. instantiate (1 := Mem.flat_inj (Mem.nextblock m0)). 
  econstructor. instantiate (1 := Mem.nextblock m0). 
  constructor; intros. 
  apply Mem.nextblock_pos.
  unfold Mem.flat_inj. apply zlt_true; auto. 
  unfold Mem.flat_inj in H. destruct (zlt b1 (Mem.nextblock m0)); inv H. auto.
  eapply Genv.find_symbol_not_fresh; eauto.
  eapply Genv.find_funct_ptr_not_fresh; eauto.
  eapply Genv.find_var_info_not_fresh; eauto.
  omega. omega.
  eapply Genv.initmem_inject; eauto.
  constructor.
Qed.

Lemma final_states_simulation:
  forall S R r,
  match_states S R -> final_state S r -> final_state R r.
Proof.
  intros. inv H0. inv H.
  specialize (MCONT VSet.empty). inv MCONT. 
  inv RINJ. constructor.
Qed.

Theorem transf_program_correct:
  forward_simulation (semantics1 prog) (semantics2 tprog).
Proof.
  eapply forward_simulation_plus.
  eexact symbols_preserved.
  eexact initial_states_simulation.
  eexact final_states_simulation.
  eexact step_simulation.
Qed.

End PRESERVATION.
