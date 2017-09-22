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

(** Compile-time evaluation of initializers for global C variables. *)

Require Import Coqlib Maps.
Require Import Errors Integers Floats Values AST Memory Globalenvs Events Smallstep.
Require Import Ctypes Cop Csyntax Csem.
Require Import Initializers.

Open Scope error_monad_scope.

Section SOUNDNESS.

Variable ge: genv.

(** * Simple expressions and their big-step semantics *)

(** An expression is simple if it contains no assignments and no
  function calls. *)

Fixpoint simple (a: expr) : Prop :=
  match a with
  | Eloc _ _ _ => True
  | Evar _ _ => True
  | Ederef r _ => simple r
  | Efield l1 _ _ => simple l1
  | Eval _ _ => True
  | Evalof l _ => simple l
  | Eaddrof l _ => simple l
  | Eunop _ r1 _ => simple r1
  | Ebinop _ r1 r2 _ => simple r1 /\ simple r2
  | Ecast r1 _ => simple r1
  | Eseqand r1 r2 _ => simple r1 /\ simple r2
  | Eseqor r1 r2 _ => simple r1 /\ simple r2
  | Econdition r1 r2 r3 _ => simple r1 /\ simple r2 /\ simple r3
  | Esizeof _ _ => True
  | Ealignof _ _ => True
  | Eassign _ _ _ => False
  | Eassignop _ _ _ _ _ => False
  | Epostincr _ _ _ => False
  | Ecomma r1 r2 _ => simple r1 /\ simple r2
  | Ecall _ _ _ => False
  | Ebuiltin _ _ _ _ => False
  | Eparen r1 _ _ => simple r1
  end.

(** A big-step semantics for simple expressions.  Similar to the
  big-step semantics from [Cstrategy], with the addition of
  conditionals, comma and paren operators.  It is a pity we do not
  share definitions with [Cstrategy], but such sharing raises
  technical difficulties. *)

Section SIMPLE_EXPRS.

Variable e: env.
Variable m: mem.

Inductive eval_simple_lvalue: expr -> block -> ptrofs -> Prop :=
  | esl_loc: forall b ofs ty,
      eval_simple_lvalue (Eloc b ofs ty) b ofs
  | esl_var_local: forall x ty b,
      e!x = Some(b, ty) ->
      eval_simple_lvalue (Evar x ty) b Ptrofs.zero
  | esl_var_global: forall x ty b,
      e!x = None ->
      Genv.find_symbol ge x = Some b ->
      eval_simple_lvalue (Evar x ty) b Ptrofs.zero
  | esl_deref: forall r ty b ofs,
      eval_simple_rvalue r (Vptr b ofs) ->
      eval_simple_lvalue (Ederef r ty) b ofs
  | esl_field_struct: forall r f ty b ofs id co a delta,
      eval_simple_rvalue r (Vptr b ofs) ->
      typeof r = Tstruct id a -> ge.(genv_cenv)!id = Some co -> field_offset ge f (co_members co) = OK delta ->
      eval_simple_lvalue (Efield r f ty) b (Ptrofs.add ofs (Ptrofs.repr delta))
  | esl_field_union: forall r f ty b ofs id a,
      eval_simple_rvalue r (Vptr b ofs) ->
      typeof r = Tunion id a ->
      eval_simple_lvalue (Efield r f ty) b ofs

with eval_simple_rvalue: expr -> val -> Prop :=
  | esr_val: forall v ty,
      eval_simple_rvalue (Eval v ty) v
  | esr_rvalof: forall b ofs l ty v,
      eval_simple_lvalue l b ofs ->
      ty = typeof l ->
      deref_loc ge ty m b ofs E0 v ->
      eval_simple_rvalue (Evalof l ty) v
  | esr_addrof: forall b ofs l ty,
      eval_simple_lvalue l b ofs ->
      eval_simple_rvalue (Eaddrof l ty) (Vptr b ofs)
  | esr_unop: forall op r1 ty v1 v,
      eval_simple_rvalue r1 v1 ->
      sem_unary_operation op v1 (typeof r1) m = Some v ->
      eval_simple_rvalue (Eunop op r1 ty) v
  | esr_binop: forall op r1 r2 ty v1 v2 v,
      eval_simple_rvalue r1 v1 -> eval_simple_rvalue r2 v2 ->
      sem_binary_operation ge op v1 (typeof r1) v2 (typeof r2) m = Some v ->
      eval_simple_rvalue (Ebinop op r1 r2 ty) v
  | esr_cast: forall ty r1 v1 v,
      eval_simple_rvalue r1 v1 ->
      sem_cast v1 (typeof r1) ty m = Some v ->
      eval_simple_rvalue (Ecast r1 ty) v
  | esr_sizeof: forall ty1 ty,
      eval_simple_rvalue (Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (sizeof ge ty1)))
  | esr_alignof: forall ty1 ty,
      eval_simple_rvalue (Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (alignof ge ty1)))
  | esr_seqand_true: forall r1 r2 ty v1 v2 v3,
      eval_simple_rvalue r1 v1 -> bool_val v1 (typeof r1) m = Some true ->
      eval_simple_rvalue r2 v2 ->
      sem_cast v2 (typeof r2) type_bool m = Some v3 ->
      eval_simple_rvalue (Eseqand r1 r2 ty) v3
  | esr_seqand_false: forall r1 r2 ty v1,
      eval_simple_rvalue r1 v1 -> bool_val v1 (typeof r1) m = Some false ->
      eval_simple_rvalue (Eseqand r1 r2 ty) (Vint Int.zero)
  | esr_seqor_false: forall r1 r2 ty v1 v2 v3,
      eval_simple_rvalue r1 v1 -> bool_val v1 (typeof r1) m = Some false ->
      eval_simple_rvalue r2 v2 ->
      sem_cast v2 (typeof r2) type_bool m = Some v3 ->
      eval_simple_rvalue (Eseqor r1 r2 ty) v3
  | esr_seqor_true: forall r1 r2 ty v1,
      eval_simple_rvalue r1 v1 -> bool_val v1 (typeof r1) m = Some true ->
      eval_simple_rvalue (Eseqor r1 r2 ty) (Vint Int.one)
  | esr_condition: forall r1 r2 r3 ty v v1 b v',
      eval_simple_rvalue r1 v1 -> bool_val v1 (typeof r1) m = Some b ->
      eval_simple_rvalue (if b then r2 else r3) v' ->
      sem_cast v' (typeof (if b then r2 else r3)) ty m = Some v ->
      eval_simple_rvalue (Econdition r1 r2 r3 ty) v
  | esr_comma: forall r1 r2 ty v1 v,
      eval_simple_rvalue r1 v1 -> eval_simple_rvalue r2 v ->
      eval_simple_rvalue (Ecomma r1 r2 ty) v
  | esr_paren: forall r tycast ty v v',
      eval_simple_rvalue r v -> sem_cast v (typeof r) tycast m = Some v' ->
      eval_simple_rvalue (Eparen r tycast ty) v'.

End SIMPLE_EXPRS.

(** * Correctness of the big-step semantics with respect to reduction sequences *)

(** In this section, we show that if a simple expression [a] reduces to
  some value (with the transition semantics from module [Csem]),
  then it evaluates to this value (with the big-step semantics above). *)

Definition compat_eval (k: kind) (e: env) (a a': expr) (m: mem) : Prop :=
  typeof a = typeof a' /\
  match k with
  | LV => forall b ofs, eval_simple_lvalue e m a' b ofs -> eval_simple_lvalue e m a b ofs
  | RV => forall v, eval_simple_rvalue e m a' v -> eval_simple_rvalue e m a v
  end.

Lemma lred_simple:
  forall e l m l' m', lred ge e l m l' m' -> simple l -> simple l'.
Proof.
  induction 1; simpl; tauto.
Qed.

Lemma lred_compat:
  forall e l m l' m', lred ge e l m l' m' ->
  m = m' /\ compat_eval LV e l l' m.
Proof.
  induction 1; simpl; split; auto; split; auto; intros bx ofsx EV; inv EV.
  apply esl_var_local; auto.
  apply esl_var_global; auto.
  constructor. constructor.
  eapply esl_field_struct; eauto. constructor. simpl; eauto.
  eapply esl_field_union; eauto. constructor. simpl; eauto.
Qed.

Lemma rred_simple:
  forall r m t r' m', rred ge r m t r' m' -> simple r -> simple r'.
Proof.
  induction 1; simpl; intuition. destruct b; auto.
Qed.

Lemma rred_compat:
  forall e r m r' m', rred ge r m E0 r' m' ->
  simple r ->
  m = m' /\ compat_eval RV e r r' m.
Proof.
  intros until m'; intros RED SIMP. inv RED; simpl in SIMP; try contradiction; split; auto; split; auto; intros vx EV.
  inv EV. econstructor. constructor. auto. auto.
  inv EV. econstructor. constructor.
  inv EV. econstructor; eauto. constructor.
  inv EV. econstructor; eauto. constructor. constructor.
  inv EV. econstructor; eauto. constructor.
  inv EV. eapply esr_seqand_true; eauto. constructor.
  inv EV. eapply esr_seqand_false; eauto. constructor.
  inv EV. eapply esr_seqor_true; eauto. constructor.
  inv EV. eapply esr_seqor_false; eauto. constructor.
  inv EV. eapply esr_condition; eauto. constructor.
  inv EV. constructor.
  inv EV. constructor.
  econstructor; eauto. constructor.
  inv EV. econstructor. constructor. auto.
Qed.

Lemma compat_eval_context:
  forall e a a' m from to C,
  context from to C ->
  compat_eval from e a a' m ->
  compat_eval to e (C a) (C a') m.
Proof.
  induction 1; intros CE; auto;
  try (generalize (IHcontext CE); intros [TY EV]; red; split; simpl; auto; intros).
  inv H0. constructor; auto.
  inv H0.
    eapply esl_field_struct; eauto. rewrite TY; eauto.
    eapply esl_field_union; eauto. rewrite TY; eauto.
  inv H0. econstructor. eauto. auto. auto.
  inv H0. econstructor; eauto.
  inv H0. econstructor; eauto. congruence.
  inv H0. econstructor; eauto. congruence.
  inv H0. econstructor; eauto. congruence.
  inv H0. econstructor; eauto. congruence.
  inv H0.
    eapply esr_seqand_true; eauto. rewrite TY; auto.
    eapply esr_seqand_false; eauto. rewrite TY; auto.
  inv H0.
    eapply esr_seqor_false; eauto. rewrite TY; auto.
    eapply esr_seqor_true; eauto. rewrite TY; auto.
  inv H0. eapply esr_condition; eauto. congruence.
  inv H0.
  inv H0.
  inv H0.
  inv H0.
  inv H0.
  inv H0.
  red; split; intros. auto. inv H0.
  red; split; intros. auto. inv H0.
  inv H0. econstructor; eauto.
  inv H0. econstructor; eauto. congruence.
Qed.

Lemma simple_context_1:
  forall a from to C, context from to C -> simple (C a) -> simple a.
Proof.
  induction 1; simpl; tauto.
Qed.

Lemma simple_context_2:
  forall a a', simple a' -> forall from to C, context from to C -> simple (C a) -> simple (C a').
Proof.
  induction 2; simpl; try tauto.
Qed.

Lemma compat_eval_steps_aux f r e m r' m' s2 :
  simple r ->
  star step ge s2 nil (ExprState f r' Kstop e m') ->
  estep ge (ExprState f r Kstop e m) nil s2 ->
  exists r1,
    s2 = ExprState f r1 Kstop e m /\
    compat_eval RV e r r1 m /\ simple r1.
Proof.
  intros.
  inv H1.
  (* lred *)
  assert (S: simple a) by (eapply simple_context_1; eauto).
  exploit lred_compat; eauto. intros [A B]. subst m'0.
  econstructor; split. eauto. split.
  eapply compat_eval_context; eauto.
  eapply simple_context_2; eauto. eapply lred_simple; eauto.
  (* rred *)
  assert (S: simple a) by (eapply simple_context_1; eauto).
  exploit rred_compat; eauto. intros [A B]. subst m'0.
  econstructor; split. eauto. split.
  eapply compat_eval_context; eauto.
  eapply simple_context_2; eauto. eapply rred_simple; eauto.
  (* callred *)
  assert (S: simple a) by (eapply simple_context_1; eauto).
  inv H8; simpl in S; contradiction.
  (* stuckred *)
  inv H0. destruct H1; inv H0.
Qed.

Lemma compat_eval_steps:
  forall f r e m  r' m',
  star step ge (ExprState f r Kstop e m) E0 (ExprState f r' Kstop e m') ->
  simple r ->
  m' = m /\ compat_eval RV e r r' m.
Proof.
  intros.
  remember (ExprState f r Kstop e m) as S1.
  remember E0 as t.
  remember (ExprState f r' Kstop e m') as S2.
  revert S1 t S2 H r m r' m' HeqS1 Heqt HeqS2 H0.
  induction 1; intros; subst.
  (* base case *)
  inv HeqS2. split. auto. red; auto.
  (* inductive case *)
  destruct (app_eq_nil t1 t2); auto. subst. inv H.
  (* expression step *)
  exploit compat_eval_steps_aux; eauto.
  intros [r1 [A [B C]]]. subst s2.
  exploit IHstar; eauto. intros [D E].
  split. auto. destruct B; destruct E. split. congruence. auto.
  (* statement steps *)
  inv H1.
Qed.

Theorem eval_simple_steps:
  forall f r e m v ty m',
  star step ge (ExprState f r Kstop e m) E0 (ExprState f (Eval v ty) Kstop e m') ->
  simple r ->
  m' = m /\ ty = typeof r /\ eval_simple_rvalue e m r v.
Proof.
  intros. exploit compat_eval_steps; eauto. intros [A [B C]].
  intuition. apply C. constructor.
Qed.

(** * Soundness of the compile-time evaluator *)

(** A global environment [ge] induces a memory injection mapping
  our symbolic pointers [Vptr id ofs] to run-time pointers
  [Vptr b ofs] where [Genv.find_symbol ge id = Some b]. *)

Definition inj (b: block) :=
  match Genv.find_symbol ge b with
  | Some b' => Some (b', 0)
  | None => None
  end.

Lemma mem_empty_not_valid_pointer:
  forall b ofs, Mem.valid_pointer Mem.empty b ofs = false.
Proof.
  intros. unfold Mem.valid_pointer. destruct (Mem.perm_dec Mem.empty b ofs Cur Nonempty); auto.
  eelim Mem.perm_empty; eauto.
Qed.

Lemma mem_empty_not_weak_valid_pointer:
  forall b ofs, Mem.weak_valid_pointer Mem.empty b ofs = false.
Proof.
  intros. unfold Mem.weak_valid_pointer.
  now rewrite !mem_empty_not_valid_pointer.
Qed.

Lemma sem_cast_match:
  forall v1 ty1 ty2 m v2 v1' v2',
  sem_cast v1 ty1 ty2 m = Some v2 ->
  do_cast v1' ty1 ty2 = OK v2' ->
  Val.inject inj v1' v1 ->
  Val.inject inj v2' v2.
Proof.
  intros. unfold do_cast in H0. destruct (sem_cast v1' ty1 ty2 Mem.empty) as [v2''|] eqn:E; inv H0.
  exploit (sem_cast_inj inj Mem.empty m).
  intros. rewrite mem_empty_not_weak_valid_pointer in H2. discriminate.
  eexact E. eauto.
  intros [v' [A B]]. congruence.
Qed.

Lemma bool_val_match:
  forall v ty b v' m,
  bool_val v ty Mem.empty = Some b ->
  Val.inject inj v v' ->
  bool_val v' ty m = Some b.
Proof.
  intros. eapply bool_val_inj; eauto. intros. rewrite mem_empty_not_weak_valid_pointer in H2; discriminate.
Qed.

(** Soundness of [constval] with respect to the big-step semantics *)

Lemma constval_rvalue:
  forall m a v,
  eval_simple_rvalue empty_env m a v ->
  forall v',
  constval ge a = OK v' ->
  Val.inject inj v' v
with constval_lvalue:
  forall m a b ofs,
  eval_simple_lvalue empty_env m a b ofs ->
  forall v',
  constval ge a = OK v' ->
  Val.inject inj v' (Vptr b ofs).
Proof.
  (* rvalue *)
  induction 1; intros vres CV; simpl in CV; try (monadInv CV).
  (* val *)
  destruct v; monadInv CV; constructor.
  (* rval *)
  inv H1; rewrite H2 in CV; try congruence. eauto. eauto.
  (* addrof *)
  eauto.
  (* unop *)
  destruct (sem_unary_operation op x (typeof r1) Mem.empty) as [v1'|] eqn:E; inv EQ0.
  exploit (sem_unary_operation_inj inj Mem.empty m).
  intros. rewrite mem_empty_not_weak_valid_pointer in H2; discriminate.
  eexact E. eauto.
  intros [v' [A B]]. congruence.
  (* binop *)
  destruct (sem_binary_operation ge op x (typeof r1) x0 (typeof r2) Mem.empty) as [v1'|] eqn:E; inv EQ2.
  exploit (sem_binary_operation_inj inj Mem.empty m).
  intros. rewrite mem_empty_not_valid_pointer in H3; discriminate.
  intros. rewrite mem_empty_not_weak_valid_pointer in H3; discriminate.
  intros. rewrite mem_empty_not_weak_valid_pointer in H3; discriminate.
  intros. rewrite mem_empty_not_valid_pointer in H3; discriminate.
  eauto. eauto. eauto.
  intros [v' [A B]]. congruence.
  (* cast *)
  eapply sem_cast_match; eauto.
  (* sizeof *)
  auto.
  (* alignof *)
  auto.
  (* seqand *)
  destruct (bool_val x (typeof r1) Mem.empty) as [b|] eqn:E; inv EQ2.
  exploit bool_val_match. eexact E. eauto. instantiate (1 := m). intros E'.
  assert (b = true) by congruence. subst b.
  eapply sem_cast_match; eauto.
  destruct (bool_val x (typeof r1) Mem.empty) as [b|] eqn:E; inv EQ2.
  exploit bool_val_match. eexact E. eauto. instantiate (1 := m). intros E'.
  assert (b = false) by congruence. subst b. inv H2. auto.
  (* seqor *)
  destruct (bool_val x (typeof r1) Mem.empty) as [b|] eqn:E; inv EQ2.
  exploit bool_val_match. eexact E. eauto. instantiate (1 := m). intros E'.
  assert (b = false) by congruence. subst b.
  eapply sem_cast_match; eauto.
  destruct (bool_val x (typeof r1) Mem.empty) as [b|] eqn:E; inv EQ2.
  exploit bool_val_match. eexact E. eauto. instantiate (1 := m). intros E'.
  assert (b = true) by congruence. subst b. inv H2. auto.
  (* conditional *)
  destruct (bool_val x (typeof r1) Mem.empty) as [b'|] eqn:E; inv EQ3.
  exploit bool_val_match. eexact E. eauto. instantiate (1 := m). intros E'.
  assert (b' = b) by congruence. subst b'.
  destruct b; eapply sem_cast_match; eauto.
  (* comma *)
  auto.
  (* paren *)
  eapply sem_cast_match; eauto.

  (* lvalue *)
  induction 1; intros v' CV; simpl in CV; try (monadInv CV).
  (* var local *)
  unfold empty_env in H. rewrite PTree.gempty in H. congruence.
  (* var_global *)
  econstructor. unfold inj. rewrite H0. eauto. auto.
  (* deref *)
  eauto.
  (* field struct *)
  rewrite H0 in CV. monadInv CV. unfold lookup_composite in EQ; rewrite H1 in EQ; monadInv EQ.
  exploit constval_rvalue; eauto. intro MV. inv MV.
  replace x0 with delta by congruence. rewrite Ptrofs.add_assoc. rewrite (Ptrofs.add_commut (Ptrofs.repr delta0)).
  simpl; destruct Archi.ptr64 eqn:SF;
  econstructor; eauto; rewrite ! Ptrofs.add_assoc; f_equal; f_equal; symmetry; auto with ptrofs.
  destruct Archi.ptr64; auto.
  (* field union *)
  rewrite H0 in CV. eauto.
Qed.

Lemma constval_simple:
  forall a v, constval ge a = OK v -> simple a.
Proof.
  induction a; simpl; intros vx CV; try (monadInv CV); eauto.
  destruct (typeof a); discriminate || eauto.
  monadInv CV. eauto.
  destruct (access_mode ty); discriminate || eauto.
  intuition eauto.
Qed.

(** Soundness of [constval] with respect to the reduction semantics. *)

Theorem constval_steps:
  forall f r m v v' ty m',
  star step ge (ExprState f r Kstop empty_env m) E0 (ExprState f (Eval v' ty) Kstop empty_env m') ->
  constval ge r = OK v ->
  m' = m /\ ty = typeof r /\ Val.inject inj v v'.
Proof.
  intros. exploit eval_simple_steps; eauto. eapply constval_simple; eauto.
  intros [A [B C]]. intuition. eapply constval_rvalue; eauto.
Qed.

(** * Relational specification of the translation of initializers *)

Definition tr_padding (frm to: Z) : list init_data :=
  if zlt frm to then Init_space (to - frm) :: nil else nil.

Inductive tr_init: type -> initializer -> list init_data -> Prop :=
  | tr_init_sgl: forall ty a d,
      transl_init_single ge ty a = OK d ->
      tr_init ty (Init_single a) (d :: nil)
  | tr_init_arr: forall tyelt nelt attr il d,
      tr_init_array tyelt il (Z.max 0 nelt) d ->
      tr_init (Tarray tyelt nelt attr) (Init_array il) d
  | tr_init_str: forall id attr il co d,
      lookup_composite ge id = OK co -> co_su co = Struct ->
      tr_init_struct (Tstruct id attr) (co_members co) il 0 d ->
      tr_init (Tstruct id attr) (Init_struct il) d
  | tr_init_uni: forall id attr f i1 co ty1 d,
      lookup_composite ge id = OK co -> co_su co = Union -> field_type f (co_members co) = OK ty1 ->
      tr_init ty1 i1 d ->
      tr_init (Tunion id attr) (Init_union f i1)
              (d ++ tr_padding (sizeof ge ty1) (sizeof ge (Tunion id attr)))

with tr_init_array: type -> initializer_list -> Z -> list init_data -> Prop :=
  | tr_init_array_nil_0: forall ty,
      tr_init_array ty Init_nil 0 nil
  | tr_init_array_nil_pos: forall ty sz,
      0 < sz ->
      tr_init_array ty Init_nil sz (Init_space (sz * sizeof ge ty) :: nil)
  | tr_init_array_cons: forall ty i il sz d1 d2,
      tr_init ty i d1 -> tr_init_array ty il (sz - 1) d2 ->
      tr_init_array ty (Init_cons i il) sz (d1 ++ d2)

with tr_init_struct: type -> members -> initializer_list -> Z -> list init_data -> Prop :=
  | tr_init_struct_nil: forall ty pos,
      tr_init_struct ty nil Init_nil pos (tr_padding pos (sizeof ge ty))
  | tr_init_struct_cons: forall ty f1 ty1 fl i1 il pos d1 d2,
      let pos1 := align pos (alignof ge ty1) in
      tr_init ty1 i1 d1 ->
      tr_init_struct ty fl il (pos1 + sizeof ge ty1) d2 ->
      tr_init_struct ty ((f1, ty1) :: fl) (Init_cons i1 il)
                     pos (tr_padding pos pos1 ++ d1 ++ d2).

Lemma transl_padding_spec:
  forall frm to k, padding frm to k = rev (tr_padding frm to) ++ k.
Proof.
  unfold padding, tr_padding; intros. 
  destruct (zlt frm to); auto.
Qed.

Lemma transl_init_rec_spec:
  forall i ty k res,
  transl_init_rec ge ty i k = OK res ->
  exists d, tr_init ty i d /\ res = rev d ++ k

with transl_init_array_spec:
  forall il ty sz k res,
  transl_init_array ge ty il sz k = OK res ->
  exists d, tr_init_array ty il sz d /\ res = rev d ++ k

with transl_init_struct_spec:
  forall il ty fl pos k res,
  transl_init_struct ge ty fl il pos k = OK res ->
  exists d, tr_init_struct ty fl il pos d /\ res = rev d ++ k.

Proof.
Local Opaque sizeof.
- destruct i; intros until res; intros TR; simpl in TR.
+ monadInv TR. exists (x :: nil); split; auto. constructor; auto.
+ destruct ty; try discriminate.
  destruct (transl_init_array_spec _ _ _ _ _ TR) as (d & A & B).
  exists d; split; auto. constructor; auto.
+ destruct ty; try discriminate. monadInv TR. destruct (co_su x) eqn:SU; try discriminate.
  destruct (transl_init_struct_spec _ _ _ _ _ _ EQ0) as (d & A & B).
  exists d; split; auto. econstructor; eauto.
+ destruct ty; try discriminate.
  monadInv TR. destruct (co_su x) eqn:SU; monadInv EQ0.
  destruct (transl_init_rec_spec _ _ _ _ EQ0) as (d & A & B).
  exists (d ++ tr_padding (sizeof ge x0) (sizeof ge (Tunion i0 a))); split.
  econstructor; eauto.
  rewrite rev_app_distr, app_ass, B. apply transl_padding_spec. 

- destruct il; intros until res; intros TR; simpl in TR.
+ destruct (zeq sz 0). 
  inv TR. exists (@nil init_data); split; auto. constructor.
  destruct (zle 0 sz).
  inv TR. econstructor; split. constructor. omega. auto.
  discriminate.
+ monadInv TR. 
  destruct (transl_init_rec_spec _ _ _ _ EQ) as (d1 & A1 & B1).
  destruct (transl_init_array_spec _ _ _ _ _ EQ0) as (d2 & A2 & B2).
  exists (d1 ++ d2); split. econstructor; eauto. 
  subst res x. rewrite rev_app_distr, app_ass. auto.

- destruct il; intros until res; intros TR; simpl in TR.
+ destruct fl; inv TR. econstructor; split. constructor. apply transl_padding_spec.
+ destruct fl as [ | [f1 ty1] fl ]; monadInv TR.
  destruct (transl_init_rec_spec _ _ _ _ EQ) as (d1 & A1 & B1).
  destruct (transl_init_struct_spec _ _ _ _ _ _ EQ0) as (d2 & A2 & B2).
  exists (tr_padding pos (align pos (alignof ge ty1)) ++ d1 ++ d2); split.
  econstructor; eauto.
  rewrite ! rev_app_distr. subst res x. rewrite ! app_ass. rewrite transl_padding_spec. auto.
Qed.

Theorem transl_init_spec:
  forall ty i d, transl_init ge ty i = OK d -> tr_init ty i d.
Proof.
  unfold transl_init; intros. monadInv H. 
  exploit transl_init_rec_spec; eauto. intros (d & A & B). 
  subst x. unfold rev'; rewrite <- rev_alt. 
  rewrite rev_app_distr; simpl. rewrite rev_involutive. auto.
Qed.

(** * Soundness of the translation of initializers *)

(** Soundness for single initializers. *)

Theorem transl_init_single_steps:
  forall ty a data f m v1 ty1 m' v chunk b ofs m'',
  transl_init_single ge ty a = OK data ->
  star step ge (ExprState f a Kstop empty_env m) E0 (ExprState f (Eval v1 ty1) Kstop empty_env m') ->
  sem_cast v1 ty1 ty m' = Some v ->
  access_mode ty = By_value chunk ->
  Mem.store chunk m' b ofs v = Some m'' ->
  Genv.store_init_data ge m b ofs data = Some m''.
Proof.
  intros. monadInv H. monadInv EQ. 
  exploit constval_steps; eauto. intros [A [B C]]. subst m' ty1.
  exploit sem_cast_match; eauto. intros D.
  unfold Genv.store_init_data.
  inv D.
- (* int *)
  remember Archi.ptr64 as ptr64.  destruct ty; try discriminate EQ0.
+ destruct i0; inv EQ0.
  destruct s; simpl in H2; inv H2. rewrite <- Mem.store_signed_unsigned_8; auto. auto.
  destruct s; simpl in H2; inv H2. rewrite <- Mem.store_signed_unsigned_16; auto. auto.
  simpl in H2; inv H2. assumption.
  simpl in H2; inv H2. assumption.
+ destruct ptr64; inv EQ0. simpl in H2; unfold Mptr in H2; rewrite <- Heqptr64 in H2; inv H2. assumption.
- (* Long *)
  remember Archi.ptr64 as ptr64. destruct ty; inv EQ0.
+ simpl in H2; inv H2. assumption.
+ simpl in H2; unfold Mptr in H2; destruct Archi.ptr64; inv H4. 
  inv H2; assumption.
- (* float *)
  destruct ty; try discriminate.
  destruct f1; inv EQ0; simpl in H2; inv H2; assumption.
- (* single *)
  destruct ty; try discriminate.
  destruct f1; inv EQ0; simpl in H2; inv H2; assumption.
- (* pointer *)
  unfold inj in H.
  assert (data = Init_addrof b1 ofs1 /\ chunk = Mptr).
  { remember Archi.ptr64 as ptr64.
    destruct ty; inversion EQ0.
    destruct i; inv H5. unfold Mptr. destruct Archi.ptr64; inv H6; inv H2; auto.
    subst ptr64. unfold Mptr. destruct Archi.ptr64; inv H5; inv H2; auto.
    inv H2. auto. }
  destruct H4; subst. destruct (Genv.find_symbol ge b1); inv H.
  rewrite Ptrofs.add_zero in H3. auto.
- (* undef *)
  discriminate.
Qed.

(** Size properties for initializers. *)

Lemma transl_init_single_size:
  forall ty a data,
  transl_init_single ge ty a = OK data ->
  init_data_size data = sizeof ge ty.
Proof.
  intros. monadInv H. monadInv EQ. remember Archi.ptr64 as ptr64. destruct x.
- monadInv EQ0.
- destruct ty; try discriminate.
  destruct i0; inv EQ0; auto.
  destruct ptr64; inv EQ0. 
Local Transparent sizeof.
  unfold sizeof. rewrite <- Heqptr64; auto.
- destruct ty; inv EQ0; auto. 
  unfold sizeof. destruct Archi.ptr64; inv H0; auto.
- destruct ty; try discriminate.
  destruct f0; inv EQ0; auto.
- destruct ty; try discriminate.
  destruct f0; inv EQ0; auto.
- destruct ty; try discriminate.
  destruct i0; inv EQ0; auto.
  destruct Archi.ptr64 eqn:SF; inv H0. simpl. rewrite SF; auto.
  destruct ptr64; inv EQ0. simpl. rewrite <- Heqptr64; auto.
  inv EQ0. unfold init_data_size, sizeof. auto.
Qed.

Notation idlsize := init_data_list_size.

Remark padding_size:
  forall frm to, frm <= to -> idlsize (tr_padding frm to) = to - frm.
Proof.
  unfold tr_padding; intros. destruct (zlt frm to).
  simpl. xomega.
  simpl. omega.
Qed.

Remark idlsize_app:
  forall d1 d2, idlsize (d1 ++ d2) = idlsize d1 + idlsize d2.
Proof.
  induction d1; simpl; intros.
  auto.
  rewrite IHd1. omega.
Qed.

Remark union_field_size:
  forall f ty fl, field_type f fl = OK ty -> sizeof ge ty <= sizeof_union ge fl.
Proof.
  induction fl as [|[i t]]; simpl; intros.
- inv H.
- destruct (ident_eq f i).
  + inv H. xomega.
  + specialize (IHfl H). xomega.
Qed.

Hypothesis ce_consistent: composite_env_consistent ge.

Lemma tr_init_size:
  forall i ty data,
  tr_init ty i data ->
  idlsize data = sizeof ge ty
with tr_init_array_size:
  forall ty il sz data,
  tr_init_array ty il sz data ->
  idlsize data = sizeof ge ty * sz
with tr_init_struct_size:
  forall ty fl il pos data,
  tr_init_struct ty fl il pos data ->
  sizeof_struct ge pos fl <= sizeof ge ty ->
  idlsize data + pos = sizeof ge ty.
Proof.
Local Opaque sizeof.
- destruct 1; simpl.
+ erewrite transl_init_single_size by eauto. omega.
+ Local Transparent sizeof. simpl. eapply tr_init_array_size; eauto. 
+ replace (idlsize d) with (idlsize d + 0) by omega.
  eapply tr_init_struct_size; eauto. simpl.
  unfold lookup_composite in H. destruct (ge.(genv_cenv)!id) as [co'|] eqn:?; inv H.
  erewrite co_consistent_sizeof by (eapply ce_consistent; eauto).
  unfold sizeof_composite. rewrite H0. apply align_le.
  destruct (co_alignof_two_p co) as [n EQ]. rewrite EQ. apply two_power_nat_pos.
+ rewrite idlsize_app, padding_size. 
  exploit tr_init_size; eauto. intros EQ; rewrite EQ. omega.
  simpl. unfold lookup_composite in H. destruct (ge.(genv_cenv)!id) as [co'|] eqn:?; inv H.
  apply Z.le_trans with (sizeof_union ge (co_members co)).
  eapply union_field_size; eauto.
  erewrite co_consistent_sizeof by (eapply ce_consistent; eauto).
  unfold sizeof_composite. rewrite H0. apply align_le.
  destruct (co_alignof_two_p co) as [n EQ]. rewrite EQ. apply two_power_nat_pos.

- destruct 1; simpl.
+ omega.
+ rewrite Z.mul_comm.
  assert (0 <= sizeof ge ty * sz).
  { apply Zmult_gt_0_le_0_compat. omega. generalize (sizeof_pos ge ty); omega. }
  xomega.
+ rewrite idlsize_app. 
  erewrite tr_init_size by eauto. 
  erewrite tr_init_array_size by eauto.
  ring.

- destruct 1; simpl; intros.
+ rewrite padding_size by auto. omega.
+ rewrite ! idlsize_app, padding_size. 
  erewrite tr_init_size by eauto. 
  rewrite <- (tr_init_struct_size _ _ _ _ _ H0 H1). omega.
  unfold pos1. apply align_le. apply alignof_pos. 
Qed.

(** A semantics for general initializers *)

Definition dummy_function := mkfunction Tvoid cc_default nil nil Sskip.

Fixpoint fields_of_struct (fl: members) (pos: Z) : list (Z * type) :=
  match fl with
  | nil => nil
  | (id1, ty1) :: fl' =>
      (align pos (alignof ge ty1), ty1) :: fields_of_struct fl' (align pos (alignof ge ty1) + sizeof ge ty1)
  end.

Inductive exec_init: mem -> block -> Z -> type -> initializer -> mem -> Prop :=
  | exec_init_single: forall m b ofs ty a v1 ty1 chunk m' v m'',
      star step ge (ExprState dummy_function a Kstop empty_env m)
                E0 (ExprState dummy_function (Eval v1 ty1) Kstop empty_env m') ->
      sem_cast v1 ty1 ty m' = Some v ->
      access_mode ty = By_value chunk ->
      Mem.store chunk m' b ofs v = Some m'' ->
      exec_init m b ofs ty (Init_single a) m''
  | exec_init_array_: forall m b ofs ty sz a il m',
      exec_init_array m b ofs ty sz il m' ->
      exec_init m b ofs (Tarray ty sz a) (Init_array il) m'
  | exec_init_struct: forall m b ofs id a il co m',
      ge.(genv_cenv)!id = Some co -> co_su co = Struct ->
      exec_init_list m b ofs (fields_of_struct (co_members co) 0) il m' ->
      exec_init m b ofs (Tstruct id a) (Init_struct il) m'
  | exec_init_union: forall m b ofs id a f i ty co m',
      ge.(genv_cenv)!id = Some co -> co_su co = Union ->
      field_type f (co_members co) = OK ty ->
      exec_init m b ofs ty i m' ->
      exec_init m b ofs (Tunion id a) (Init_union f i) m'

with exec_init_array: mem -> block -> Z -> type -> Z -> initializer_list -> mem -> Prop :=
  | exec_init_array_nil: forall m b ofs ty sz,
      sz >= 0 ->
      exec_init_array m b ofs ty sz Init_nil m
  | exec_init_array_cons: forall m b ofs ty sz i1 il m' m'',
      exec_init m b ofs ty i1 m' ->
      exec_init_array m' b (ofs + sizeof ge ty) ty (sz - 1) il m'' ->
      exec_init_array m b ofs ty sz (Init_cons i1 il) m''

with exec_init_list: mem -> block -> Z -> list (Z * type) -> initializer_list -> mem -> Prop :=
  | exec_init_list_nil: forall m b ofs,
      exec_init_list m b ofs nil Init_nil m
  | exec_init_list_cons: forall m b ofs pos ty l i1 il m' m'',
      exec_init m b (ofs + pos) ty i1 m' ->
      exec_init_list m' b ofs l il m'' ->
      exec_init_list m b ofs ((pos, ty) :: l) (Init_cons i1 il) m''.

Scheme exec_init_ind3 := Minimality for exec_init Sort Prop
  with exec_init_array_ind3 := Minimality for exec_init_array Sort Prop
  with exec_init_list_ind3 := Minimality for exec_init_list Sort Prop.
Combined Scheme exec_init_scheme from exec_init_ind3, exec_init_array_ind3, exec_init_list_ind3.

Remark exec_init_array_length:
  forall m b ofs ty sz il m',
  exec_init_array m b ofs ty sz il m' -> sz >= 0.
Proof.
  induction 1; omega.
Qed.

Lemma store_init_data_list_app:
  forall data1 m b ofs m' data2 m'',
  Genv.store_init_data_list ge m b ofs data1 = Some m' ->
  Genv.store_init_data_list ge m' b (ofs + idlsize data1) data2 = Some m'' ->
  Genv.store_init_data_list ge m b ofs (data1 ++ data2) = Some m''.
Proof.
  induction data1; simpl; intros.
  inv H. rewrite Z.add_0_r in H0. auto.
  destruct (Genv.store_init_data ge m b ofs a); try discriminate.
  rewrite Z.add_assoc in H0. eauto.
Qed.

Remark store_init_data_list_padding:
  forall frm to b ofs m,
  Genv.store_init_data_list ge m b ofs (tr_padding frm to) = Some m.
Proof.
  intros. unfold tr_padding. destruct (zlt frm to); auto.
Qed.

Lemma tr_init_sound:
  (forall m b ofs ty i m', exec_init m b ofs ty i m' ->
   forall data, tr_init ty i data ->
   Genv.store_init_data_list ge m b ofs data = Some m')
/\(forall m b ofs ty sz il m', exec_init_array m b ofs ty sz il m' ->
   forall data, tr_init_array ty il sz data ->
   Genv.store_init_data_list ge m b ofs data = Some m')
/\(forall m b ofs l il m', exec_init_list m b ofs l il m' ->
   forall ty fl data pos,
   l = fields_of_struct fl pos ->
   tr_init_struct ty fl il pos data ->
   Genv.store_init_data_list ge m b (ofs + pos) data = Some m').
Proof.
Local Opaque sizeof.
  apply exec_init_scheme; simpl; intros.
- (* single *)
  inv H3. simpl. erewrite transl_init_single_steps by eauto. auto.
- (* array *)
  inv H1. replace (Z.max 0 sz) with sz in H7. eauto.
  assert (sz >= 0) by (eapply exec_init_array_length; eauto). xomega.
- (* struct *)
  inv H3. unfold lookup_composite in H7. rewrite H in H7. inv H7. 
  replace ofs with (ofs + 0) by omega. eauto.
- (* union *)
  inv H4. unfold lookup_composite in H9. rewrite H in H9. inv H9. rewrite H1 in H12; inv H12. 
  eapply store_init_data_list_app. eauto.
  apply store_init_data_list_padding.

- (* array, empty *)
  inv H0; auto.
- (* array, nonempty *)
  inv H3.
  eapply store_init_data_list_app.
  eauto.
  rewrite (tr_init_size _ _ _ H7). eauto.

- (* struct, empty *)
  inv H0. apply store_init_data_list_padding.
- (* struct, nonempty *)
  inv H4. simpl in H3; inv H3. 
  eapply store_init_data_list_app. apply store_init_data_list_padding.
  rewrite padding_size.
  replace (ofs + pos0 + (pos2 - pos0)) with (ofs + pos2) by omega.
  eapply store_init_data_list_app.
  eauto.
  rewrite (tr_init_size _ _ _ H9).
  rewrite <- Z.add_assoc. eapply H2. eauto. eauto.
  apply align_le. apply alignof_pos.
Qed.

End SOUNDNESS.

Theorem transl_init_sound:
  forall p m b ty i m' data,
  exec_init (globalenv p) m b 0 ty i m' ->
  transl_init (prog_comp_env p) ty i = OK data ->
  Genv.store_init_data_list (globalenv p) m b 0 data = Some m'.
Proof.
  intros.
  set (ge := globalenv p) in *.
  change (prog_comp_env p) with (genv_cenv ge) in H0.
  destruct (tr_init_sound ge) as (A & B & C).
  eapply build_composite_env_consistent. apply prog_comp_env_eq.
  eapply A; eauto. apply transl_init_spec; auto.
Qed.
