(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Observable events, execution traces, and semantics of external calls. *)

Require Import Coqlib.
Require Intv.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.

(** * Events and traces *)

(** The observable behaviour of programs is stated in terms of
  input/output events, which represent the actions of the program
  that the external world can observe.  CompCert leaves much flexibility as to
  the exact content of events: the only requirement is that they
  do not expose pointer values nor memory states, because these
  are not preserved literally during compilation.  For concreteness,
  we use the following type for events.  Each event represents either:

- A system call (e.g. an input/output operation), recording the
  name of the system call, its int-or-float parameters,
  and its int-or-float result.

- A volatile load from a memory location, recording a label
  associated with the read (e.g. a global variable name or a source code position).

- A volatile store to a memory location, also recording a label.
*)

Inductive eventval: Type :=
  | EVint: int -> eventval
  | EVfloat: float -> eventval.

Inductive event: Type :=
  | Event_syscall: ident -> list eventval -> eventval -> event
  | Event_load: ident -> event
  | Event_store: ident -> event.

(** The dynamic semantics for programs collect traces of events.
  Traces are of two kinds: finite (type [trace]) or infinite (type [traceinf]). *)

Definition trace := list event.

Definition E0 : trace := nil.

Definition Eapp (t1 t2: trace) : trace := t1 ++ t2.

CoInductive traceinf : Type :=
  | Econsinf: event -> traceinf -> traceinf.

Fixpoint Eappinf (t: trace) (T: traceinf) {struct t} : traceinf :=
  match t with
  | nil => T
  | ev :: t' => Econsinf ev (Eappinf t' T)
  end.

(** Concatenation of traces is written [**] in the finite case
  or [***] in the infinite case. *)

Infix "**" := Eapp (at level 60, right associativity).
Infix "***" := Eappinf (at level 60, right associativity).

Lemma E0_left: forall t, E0 ** t = t.
Proof. auto. Qed.

Lemma E0_right: forall t, t ** E0 = t.
Proof. intros. unfold E0, Eapp. rewrite <- app_nil_end. auto. Qed.

Lemma Eapp_assoc: forall t1 t2 t3, (t1 ** t2) ** t3 = t1 ** (t2 ** t3).
Proof. intros. unfold Eapp, trace. apply app_ass. Qed.

Lemma Eapp_E0_inv: forall t1 t2, t1 ** t2 = E0 -> t1 = E0 /\ t2 = E0.
Proof (@app_eq_nil event).
  
Lemma E0_left_inf: forall T, E0 *** T = T.
Proof. auto. Qed.

Lemma Eappinf_assoc: forall t1 t2 T, (t1 ** t2) *** T = t1 *** (t2 *** T).
Proof.
  induction t1; intros; simpl. auto. decEq; auto.
Qed.

Hint Rewrite E0_left E0_right Eapp_assoc
             E0_left_inf Eappinf_assoc: trace_rewrite.

Opaque trace E0 Eapp Eappinf.

(** The following [traceEq] tactic proves equalities between traces
  or infinite traces. *)

Ltac substTraceHyp :=
  match goal with
  | [ H: (@eq trace ?x ?y) |- _ ] =>
       subst x || clear H
  end.

Ltac decomposeTraceEq :=
  match goal with
  | [ |- (_ ** _) = (_ ** _) ] =>
      apply (f_equal2 Eapp); auto; decomposeTraceEq
  | _ =>
      auto
  end.

Ltac traceEq := 
  repeat substTraceHyp; autorewrite with trace_rewrite; decomposeTraceEq.

(** Bisimilarity between infinite traces. *)

CoInductive traceinf_sim: traceinf -> traceinf -> Prop :=
  | traceinf_sim_cons: forall e T1 T2,
      traceinf_sim T1 T2 ->
      traceinf_sim (Econsinf e T1) (Econsinf e T2).

Lemma traceinf_sim_refl:
  forall T, traceinf_sim T T.
Proof.
  cofix COINDHYP; intros.
  destruct T. constructor. apply COINDHYP.
Qed.
 
Lemma traceinf_sim_sym:
  forall T1 T2, traceinf_sim T1 T2 -> traceinf_sim T2 T1.
Proof.
  cofix COINDHYP; intros. inv H; constructor; auto.
Qed.

Lemma traceinf_sim_trans:
  forall T1 T2 T3, 
  traceinf_sim T1 T2 -> traceinf_sim T2 T3 -> traceinf_sim T1 T3.
Proof.
  cofix COINDHYP;intros. inv H; inv H0; constructor; eauto.
Qed.

CoInductive traceinf_sim': traceinf -> traceinf -> Prop :=
  | traceinf_sim'_cons: forall t T1 T2,
      t <> E0 -> traceinf_sim' T1 T2 -> traceinf_sim' (t *** T1) (t *** T2).

Lemma traceinf_sim'_sim:
  forall T1 T2, traceinf_sim' T1 T2 -> traceinf_sim T1 T2.
Proof.
  cofix COINDHYP; intros. inv H. 
  destruct t. elim H0; auto.
Transparent Eappinf.
Transparent E0.
  simpl. 
  destruct t. simpl. constructor. apply COINDHYP; auto.
  constructor. apply COINDHYP.
  constructor. unfold E0; congruence. auto.
Qed.

(** The "is prefix of" relation between a finite and an infinite trace. *)

Inductive traceinf_prefix: trace -> traceinf -> Prop :=
  | traceinf_prefix_nil: forall T,
      traceinf_prefix nil T
  | traceinf_prefix_cons: forall e t1 T2,
      traceinf_prefix t1 T2 ->
      traceinf_prefix (e :: t1) (Econsinf e T2).

Lemma traceinf_prefix_app:
  forall t1 T2 t,
  traceinf_prefix t1 T2 ->
  traceinf_prefix (t ** t1) (t *** T2).
Proof.
  induction t; simpl; intros. auto.
  change ((a :: t) ** t1) with (a :: (t ** t1)).
  change ((a :: t) *** T2) with (Econsinf a (t *** T2)).
  constructor. auto.
Qed.

(** An alternate presentation of infinite traces as
  infinite concatenations of nonempty finite traces. *)

CoInductive traceinf': Type :=
  | Econsinf': forall (t: trace) (T: traceinf'), t <> E0 -> traceinf'.

Program Definition split_traceinf' (t: trace) (T: traceinf') (NE: t <> E0): event * traceinf' :=
  match t with
  | nil => _
  | e :: nil => (e, T)
  | e :: t' => (e, Econsinf' t' T _)
  end.
Next Obligation.
  elimtype False. elim NE. auto. 
Qed.
Next Obligation.
  red; intro. elim (H e). rewrite H0. auto. 
Qed.

CoFixpoint traceinf_of_traceinf' (T': traceinf') : traceinf :=
  match T' with
  | Econsinf' t T'' NOTEMPTY =>
      let (e, tl) := split_traceinf' t T'' NOTEMPTY in
      Econsinf e (traceinf_of_traceinf' tl)
  end.

Remark unroll_traceinf':
  forall T, T = match T with Econsinf' t T' NE => Econsinf' t T' NE end.
Proof.
  intros. destruct T; auto.
Qed.

Remark unroll_traceinf:
  forall T, T = match T with Econsinf t T' => Econsinf t T' end.
Proof.
  intros. destruct T; auto.
Qed.

Lemma traceinf_traceinf'_app:
  forall t T NE,
  traceinf_of_traceinf' (Econsinf' t T NE) = t *** traceinf_of_traceinf' T.
Proof.
  induction t.
  intros. elim NE. auto.
  intros. simpl.   
  rewrite (unroll_traceinf (traceinf_of_traceinf' (Econsinf' (a :: t) T NE))).
  simpl. destruct t. auto.
Transparent Eappinf.
  simpl. f_equal. apply IHt. 
Qed.

(** * Semantics of external functions *)

(** Each external function is of one of the following kinds: *)

Inductive extfun_kind: signature -> Type :=
  | EF_syscall (sg: signature) (name: ident): extfun_kind sg
     (** A system call.  Takes integer-or-float arguments, produces a
         result that is an integer or a float, does not modify
         the memory, and produces an [Event_syscall] event in the trace. *)
  | EF_load (label: ident) (chunk: memory_chunk): extfun_kind (mksignature (Tint :: nil) (Some (type_of_chunk chunk)))
     (** A volatile read operation.  Reads and returns the given memory
         chunk from the address given as first argument.
         Produces an [Event_load] event containing the given label. *)
  | EF_store (label: ident) (chunk: memory_chunk): extfun_kind (mksignature (Tint :: type_of_chunk chunk :: nil) None)
     (** A volatile store operation.  Store the value given as second
         argument at the address given as first argument, using the
         given memory chunk.  
         Produces an [Event_store] event containing the given label. *)
  | EF_malloc: extfun_kind (mksignature (Tint :: nil) (Some Tint))
     (** Dynamic memory allocation.  Takes the requested size in bytes
         as argument; returns a pointer to a fresh block of the given size.
         Produces no observable event. *)
  | EF_free: extfun_kind (mksignature (Tint :: nil) None).
     (** Dynamic memory deallocation.  Takes a pointer to a block
         allocated by an [EF_malloc] external call and frees the
         corresponding block.
         Produces no observable event. *)

Parameter classify_external_function: 
  forall (ef: external_function), extfun_kind (ef.(ef_sig)).

(** For each external function, its behavior is defined by a predicate relating:
- the values of the arguments passed to this function
- the memory state before the call
- the result value of the call
- the memory state after the call
- the trace generated by the call (can be empty).

We now specify the expected properties of this predicate.
*)

Definition mem_unchanged_on (P: block -> Z -> Prop) (m_before m_after: mem): Prop :=
  (forall b ofs p,
   P b ofs -> Mem.perm m_before b ofs p -> Mem.perm m_after b ofs p)
/\(forall chunk b ofs v,
   (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
   Mem.load chunk m_before b ofs = Some v ->
   Mem.load chunk m_after b ofs = Some v).

Definition loc_out_of_bounds (m: mem) (b: block) (ofs: Z) : Prop :=
  ofs < Mem.low_bound m b \/ ofs > Mem.high_bound m b.

Definition loc_unmapped (f: meminj) (b: block) (ofs: Z): Prop :=
  f b = None.

Definition loc_out_of_reach (f: meminj) (m: mem) (b: block) (ofs: Z): Prop :=
  forall b0 delta,
  f b0 = Some(b, delta) ->
  ofs < Mem.low_bound m b0 + delta \/ ofs >= Mem.high_bound m b0 + delta.

Definition inject_separated (f f': meminj) (m1 m2: mem): Prop :=
  forall b1 b2 delta,
  f b1 = None -> f' b1 = Some(b2, delta) ->
  ~Mem.valid_block m1 b1 /\ ~Mem.valid_block m2 b2.

Fixpoint matching_traces (t1 t2: trace) {struct t1} : Prop :=
  match t1, t2 with
  | Event_syscall name1 args1 res1 :: t1', Event_syscall name2 args2 res2 :: t2' =>
      name1 = name2 -> args1 = args2 -> res1 = res2 /\ matching_traces t1' t2'
  | Event_load name1 :: t1', Event_load name2 :: t2' =>
      name1 = name2 -> matching_traces t1' t2'
  | Event_store name1 :: t1', Event_store name2 :: t2' =>
      name1 = name2 -> matching_traces t1' t2'
  | _, _ =>
      True
  end.

Record extcall_properties (sem: list val -> mem -> trace -> val -> mem -> Prop)
                          (sg: signature) : Prop := mk_extcall_properties {

(** The return value of an external call must agree with its signature. *)
  ec_well_typed:
    forall vargs m1 t vres m2,
    sem vargs m1 t vres m2 ->
    Val.has_type vres (proj_sig_res sg);

(** The number of arguments of an external call must agree with its signature. *)
  ec_arity:
    forall vargs m1 t vres m2,
    sem vargs m1 t vres m2 ->
    List.length vargs = List.length sg.(sig_args);

(** External calls cannot invalidate memory blocks.  (Remember that
  freeing a block does not invalidate its block identifier.) *)
  ec_valid_block:
    forall vargs m1 t vres m2 b,
    sem vargs m1 t vres m2 ->
    Mem.valid_block m1 b -> Mem.valid_block m2 b;

(** External calls preserve the bounds of valid blocks. *)
  ec_bounds:
    forall vargs m1 t vres m2 b,
    sem vargs m1 t vres m2 ->
    Mem.valid_block m1 b -> Mem.bounds m2 b = Mem.bounds m1 b;

(** External calls must commute with memory extensions, in the
  following sense. *)
  ec_mem_extends:
    forall vargs m1 t vres m2 m1' vargs',
    sem vargs m1 t vres m2 ->
    Mem.extends m1 m1' ->
    Val.lessdef_list vargs vargs' ->
    exists vres', exists m2',
       sem vargs' m1' t vres' m2'
    /\ Val.lessdef vres vres'
    /\ Mem.extends m2 m2'
    /\ mem_unchanged_on (loc_out_of_bounds m1) m1' m2';

(** External calls must commute with memory injections,
  in the following sense. *)
  ec_mem_inject:
    forall vargs m1 t vres m2 f m1' vargs',
    sem vargs m1 t vres m2 ->
    Mem.inject f m1 m1' ->
    val_list_inject f vargs vargs' ->
    exists f', exists vres', exists m2',
       sem vargs' m1' t vres' m2'
    /\ val_inject f' vres vres'
    /\ Mem.inject f' m2 m2'
    /\ mem_unchanged_on (loc_unmapped f) m1 m2
    /\ mem_unchanged_on (loc_out_of_reach f m1) m1' m2'
    /\ inject_incr f f'
    /\ inject_separated f f' m1 m1';

(** External calls must be internally deterministic:
  if the observable traces match, the return states must be
  identical. *)
  ec_determ:
    forall vargs m t1 vres1 m1 t2 vres2 m2,
    sem vargs m t1 vres1 m1 -> sem vargs m t2 vres2 m2 ->
    matching_traces t1 t2 -> t1 = t2 /\ vres1 = vres2 /\ m1 = m2
}.

(** ** Semantics of volatile loads *)

Inductive extcall_load_sem (label: ident) (chunk: memory_chunk):
      list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_load_sem_intro: forall b ofs m vres,
      Mem.load chunk m b (Int.signed ofs) = Some vres ->
      extcall_load_sem label chunk (Vptr b ofs :: nil) m (Event_load label :: nil) vres m.

Lemma extcall_load_ok:
  forall label chunk,
  extcall_properties (extcall_load_sem label chunk) 
                     (mksignature (Tint :: nil) (Some (type_of_chunk chunk))).
Proof.
  intros; constructor; intros.

  inv H. unfold proj_sig_res. simpl. eapply Mem.load_type; eauto.

  inv H. simpl. auto.

  inv H. auto.

  inv H. auto.

  inv H. inv H1. inv H6. inv H4. 
  exploit Mem.load_extends; eauto. intros [v2 [A B]].
  exists v2; exists m1'; intuition. 
  constructor; auto. 
  red. auto. 

  inv H. inv H1. inv H6.
  assert (Mem.loadv chunk m2 (Vptr b ofs) = Some vres). auto. 
  exploit Mem.loadv_inject; eauto. intros [v2 [A B]].
  inv H4. 
  exists f; exists v2; exists m1'; intuition.
  constructor. auto. 
  red; auto.
  red; auto.
  red; intros. congruence.

  inv H; inv H0. intuition congruence.
Qed.

(** ** Semantics of volatile stores *)

Inductive extcall_store_sem (label: ident) (chunk: memory_chunk):
      list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_store_sem_intro: forall b ofs v m m',
      Mem.store chunk m b (Int.signed ofs) v = Some m' ->
      extcall_store_sem label chunk (Vptr b ofs :: v :: nil) m (Event_store label :: nil) Vundef m'.

Lemma extcall_store_ok:
  forall label chunk,
  extcall_properties (extcall_store_sem label chunk) 
                     (mksignature (Tint :: type_of_chunk chunk :: nil) None).
Proof.
  intros; constructor; intros.

  inv H. unfold proj_sig_res. simpl. auto.

  inv H. simpl. auto.

  inv H. eauto with mem. 

  inv H. eapply Mem.bounds_store; eauto. 

  inv H. inv H1. inv H6. inv H7. inv H4.
  exploit Mem.store_within_extends; eauto. intros [m' [A B]].
  exists Vundef; exists m'; intuition.
  constructor; auto.
  red; split; intros.
  eapply Mem.perm_store_1; eauto.
  rewrite <- H1. eapply Mem.load_store_other; eauto.
  destruct (eq_block b0 b); auto. subst b0; right. 
  exploit Mem.valid_access_in_bounds. 
  eapply Mem.store_valid_access_3. eexact H2.
  intros [C D].
  generalize (size_chunk_pos chunk0). intro E.
  generalize (size_chunk_pos chunk). intro F.
  apply (Intv.range_disjoint' (ofs0, ofs0 + size_chunk chunk0)
                              (Int.signed ofs, Int.signed ofs + size_chunk chunk)).
  red; intros. generalize (H x H4). unfold loc_out_of_bounds, Intv.In; simpl. omega.
  simpl; omega. simpl; omega.

  inv H. inv H1. inv H6. inv H7.
  assert (Mem.storev chunk m1 (Vptr b ofs) v = Some m2). simpl; auto.
  exploit Mem.storev_mapped_inject; eauto. intros [m2' [A B]].
  inv H4. 
  exists f; exists Vundef; exists m2'; intuition.
  constructor; auto. 
  split; intros. eapply Mem.perm_store_1; eauto.
  rewrite <- H4. eapply Mem.load_store_other; eauto. 
  left. exploit (H1 ofs0). generalize (size_chunk_pos chunk0). omega. 
  unfold loc_unmapped. congruence.
  split; intros. eapply Mem.perm_store_1; eauto.
  rewrite <- H4. eapply Mem.load_store_other; eauto.
  destruct (eq_block b0 b2); auto. subst b0; right.
  assert (EQ: Int.signed (Int.add ofs (Int.repr delta)) = Int.signed ofs + delta).
    eapply Mem.address_inject; eauto with mem.
  simpl in A. rewrite EQ in A. rewrite EQ.
  exploit Mem.valid_access_in_bounds. 
  eapply Mem.store_valid_access_3. eexact H2.
  intros [C D].
  generalize (size_chunk_pos chunk0). intro E.
  generalize (size_chunk_pos chunk). intro F.
  apply (Intv.range_disjoint' (ofs0, ofs0 + size_chunk chunk0)
                              (Int.signed ofs + delta, Int.signed ofs + delta + size_chunk chunk)).
  red; intros. exploit (H1 x H5). eauto. unfold Intv.In; simpl. omega.
  simpl; omega. simpl; omega.

  red; intros. congruence.

  inv H; inv H0. intuition congruence.
Qed.

(** ** Semantics of dynamic memory allocation (malloc) *)

Inductive extcall_malloc_sem:
      list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_malloc_sem_intro: forall n m m' b m'',
      Mem.alloc m (-4) (Int.signed n) = (m', b) ->
      Mem.store Mint32 m' b (-4) (Vint n) = Some m'' ->
      extcall_malloc_sem (Vint n :: nil) m E0 (Vptr b Int.zero) m''.

Lemma extcall_malloc_ok:
  extcall_properties extcall_malloc_sem 
                     (mksignature (Tint :: nil) (Some Tint)).
Proof.
  assert (UNCHANGED:
    forall (P: block -> Z -> Prop) m n m' b m'',
    Mem.alloc m (-4) (Int.signed n) = (m', b) ->
    Mem.store Mint32 m' b (-4) (Vint n) = Some m'' ->
    mem_unchanged_on P m m'').
  intros; split; intros.
  eauto with mem.
  transitivity (Mem.load chunk m' b0 ofs). 
  eapply Mem.load_store_other; eauto. left. 
  apply Mem.valid_not_valid_diff with m; eauto with mem.
  eapply Mem.load_alloc_other; eauto. 

  constructor; intros.

  inv H. unfold proj_sig_res; simpl. auto.

  inv H. auto.

  inv H. eauto with mem.

  inv H. transitivity (Mem.bounds m' b).
  eapply Mem.bounds_store; eauto.
  eapply Mem.bounds_alloc_other; eauto.
  apply Mem.valid_not_valid_diff with m1; eauto with mem.

  inv H. inv H1. inv H5. inv H7. 
  exploit Mem.alloc_extends; eauto. apply Zle_refl. apply Zle_refl.
  intros [m3' [A B]].
  exploit Mem.store_within_extends. eexact B. eauto. 
  instantiate (1 := Vint n). auto. 
  intros [m2' [C D]].
  exists (Vptr b Int.zero); exists m2'; intuition.
  econstructor; eauto.
  eapply UNCHANGED; eauto.

  inv H. inv H1. inv H5. inv H7.
  exploit Mem.alloc_parallel_inject; eauto. apply Zle_refl. apply Zle_refl. 
  intros [f' [m3' [b' [ALLOC [A [B [C D]]]]]]].
  exploit Mem.store_mapped_inject. eexact A. eauto. eauto. 
  instantiate (1 := Vint n). auto. 
  intros [m2' [E F]].
  exists f'; exists (Vptr b' Int.zero); exists m2'; intuition.
  econstructor; eauto.
  econstructor. eauto. auto.
  eapply UNCHANGED; eauto.
  eapply UNCHANGED; eauto.
  red; intros. destruct (eq_block b1 b). 
  subst b1. rewrite C in H1. inv H1. eauto with mem. 
  rewrite D in H1. congruence. auto. 

  inv H; inv H0. intuition congruence. 
Qed.

(** ** Semantics of dynamic memory deallocation (free) *)

Inductive extcall_free_sem:
      list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_free_sem_intro: forall b lo sz m m',
      Mem.load Mint32 m b (Int.signed lo - 4) = Some (Vint sz) ->
      Int.signed sz > 0 ->
      Mem.free m b (Int.signed lo - 4) (Int.signed lo + Int.signed sz) = Some m' ->
      extcall_free_sem (Vptr b lo :: nil) m E0 Vundef m'.

Lemma extcall_free_ok:
  extcall_properties extcall_free_sem 
                     (mksignature (Tint :: nil) None).
Proof.
  assert (UNCHANGED:
    forall (P: block -> Z -> Prop) m b lo hi m',
    Mem.free m b lo hi = Some m' ->
    lo < hi ->
    (forall b' ofs, P b' ofs -> b' <> b \/ ofs < lo \/ hi <= ofs) ->
    mem_unchanged_on P m m').
  intros; split; intros.
  eapply Mem.perm_free_1; eauto.
  rewrite <- H3. eapply Mem.load_free; eauto. 
  destruct (eq_block b0 b); auto. right. right. 
  apply (Intv.range_disjoint' (ofs, ofs + size_chunk chunk) (lo, hi)).
  red; intros. apply Intv.notin_range. simpl. exploit H1; eauto. intuition. 
  simpl; generalize (size_chunk_pos chunk); omega.
  simpl; omega.

  constructor; intros.

  inv H. unfold proj_sig_res. simpl. auto.

  inv H. auto. 

  inv H. eauto with mem.

  inv H. eapply Mem.bounds_free; eauto.

  inv H. inv H1. inv H8. inv H6. 
  exploit Mem.load_extends; eauto. intros [vsz [A B]]. inv B. 
  exploit Mem.free_parallel_extends; eauto. intros [m2' [C D]].
  exists Vundef; exists m2'; intuition.
  econstructor; eauto.
  eapply UNCHANGED; eauto. omega. 
  intros. destruct (eq_block b' b); auto. subst b; right.
  red in H.
  exploit Mem.range_perm_in_bounds. 
  eapply Mem.free_range_perm. eexact H4. omega. omega.

  inv H. inv H1. inv H8. inv H6.
  exploit Mem.load_inject; eauto. intros [vsz [A B]]. inv B. 
  assert (Mem.range_perm m1 b (Int.signed lo - 4) (Int.signed lo + Int.signed sz) Freeable).
    eapply Mem.free_range_perm; eauto.
  exploit Mem.address_inject; eauto. 
    apply Mem.perm_implies with Freeable; auto with mem.
    apply H. instantiate (1 := lo). omega. 
  intro EQ.
  assert (Mem.range_perm m1' b2 (Int.signed lo + delta - 4) (Int.signed lo + delta + Int.signed sz) Freeable).
    red; intros. 
    replace ofs with ((ofs - delta) + delta) by omega.
    eapply Mem.perm_inject; eauto. apply H. omega. 
  destruct (Mem.range_perm_free _ _ _ _ H1) as [m2' FREE].
  exists f; exists Vundef; exists m2'; intuition.

  econstructor.
  rewrite EQ. replace (Int.signed lo + delta - 4) with (Int.signed lo - 4 + delta) by omega.
  eauto. auto. 
  rewrite EQ. auto.
  
  assert (Mem.free_list m1 ((b, Int.signed lo - 4, Int.signed lo + Int.signed sz) :: nil) = Some m2).
    simpl. rewrite H4. auto.
  eapply Mem.free_inject; eauto. 
  intros. destruct (eq_block b b1).
  subst b. assert (delta0 = delta) by congruence. subst delta0. 
  exists (Int.signed lo - 4); exists (Int.signed lo + Int.signed sz); split.
  simpl; auto. omega.
  elimtype False.
  exploit Mem.inject_no_overlap. eauto. eauto. eauto. eauto. 
  instantiate (1 := ofs + delta0 - delta). 
  apply Mem.perm_implies with Freeable; auto with mem.
  apply H. omega. eauto with mem.
  unfold block; omega.

  eapply UNCHANGED; eauto. omega. intros.  
  red in H6. left. congruence. 

  eapply UNCHANGED; eauto. omega. intros.
  destruct (eq_block b' b2); auto. subst b'. right. 
  red in H6. generalize (H6 _ _ H5). intros. 
  exploit Mem.range_perm_in_bounds. eexact H. omega. intros. omega.

  red; intros. congruence.

  inv H; inv H0. intuition congruence.
Qed.

(** ** Semantics of system calls. *)

Inductive eventval_match: eventval -> typ -> val -> Prop :=
  | ev_match_int:
      forall i, eventval_match (EVint i) Tint (Vint i)
  | ev_match_float:
      forall f, eventval_match (EVfloat f) Tfloat (Vfloat f).

Inductive eventval_list_match: list eventval -> list typ -> list val -> Prop :=
  | evl_match_nil:
      eventval_list_match nil nil nil
  | evl_match_cons:
      forall ev1 evl ty1 tyl v1 vl,
      eventval_match ev1 ty1 v1 ->
      eventval_list_match evl tyl vl ->
      eventval_list_match (ev1::evl) (ty1::tyl) (v1::vl).

Inductive extcall_io_sem (name: ident) (sg: signature):
      list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_io_sem_intro: forall vargs m args res vres,
      eventval_list_match args (sig_args sg) vargs ->
      eventval_match res (proj_sig_res sg) vres ->
      extcall_io_sem name sg vargs m (Event_syscall name args res :: E0) vres m.

Remark eventval_match_lessdef:
  forall ev ty v1 v2,
  eventval_match ev ty v1 -> Val.lessdef v1 v2 -> eventval_match ev ty v2.
Proof.
  intros. inv H; inv H0; constructor.
Qed.

Remark eventval_list_match_lessdef:
  forall evl tyl vl1, eventval_list_match evl tyl vl1 ->
  forall vl2, Val.lessdef_list vl1 vl2 -> eventval_list_match evl tyl vl2.
Proof.
  induction 1; intros. inv H; constructor.
  inv H1. constructor. eapply eventval_match_lessdef; eauto. eauto.
Qed.

Remark eventval_match_inject:
  forall f ev ty v1 v2,
  eventval_match ev ty v1 -> val_inject f v1 v2 -> eventval_match ev ty v2.
Proof.
  intros. inv H; inv H0; constructor.
Qed.

Remark eventval_match_inject_2:
  forall f ev ty v,
  eventval_match ev ty v -> val_inject f v v.
Proof.
  induction 1; constructor.
Qed.

Remark eventval_list_match_inject:
  forall f evl tyl vl1, eventval_list_match evl tyl vl1 ->
  forall vl2, val_list_inject f vl1 vl2 -> eventval_list_match evl tyl vl2.
Proof.
  induction 1; intros. inv H; constructor.
  inv H1. constructor. eapply eventval_match_inject; eauto. eauto.
Qed.

Remark eventval_list_match_length:
  forall evl tyl vl, eventval_list_match evl tyl vl -> List.length vl = List.length tyl.
Proof.
  induction 1; simpl; eauto.
Qed.

Remark eventval_match_determ_1:
  forall ev ty v1 v2, eventval_match ev ty v1 -> eventval_match ev ty v2 -> v1 = v2.
Proof.
  intros. inv H; inv H0; auto.
Qed.

Remark eventval_match_determ_2:
  forall ev1 ev2 ty v, eventval_match ev1 ty v -> eventval_match ev2 ty v -> ev1 = ev2.
Proof.
  intros. inv H; inv H0; auto.
Qed.

Remark eventval_list_match_determ_2:
  forall evl1 tyl vl, eventval_list_match evl1 tyl vl ->
  forall evl2, eventval_list_match evl2 tyl vl -> evl1 = evl2.
Proof.
  induction 1; intros. inv H. auto. inv H1. f_equal; eauto.
  eapply eventval_match_determ_2; eauto.
Qed.

Lemma extcall_io_ok:
  forall name sg,
  extcall_properties (extcall_io_sem name sg) sg.
Proof.
  intros; constructor; intros.

  inv H. inv H1; constructor. 

  inv H. eapply eventval_list_match_length; eauto.

  inv H; auto.

  inv H; auto.

  inv H.
  exists vres; exists m1'; intuition.
  econstructor; eauto. eapply eventval_list_match_lessdef; eauto.
  red; auto.

  inv H.
  exists f; exists vres; exists m1'; intuition.
  econstructor; eauto. eapply eventval_list_match_inject; eauto. 
  eapply eventval_match_inject_2; eauto. 
  red; auto.
  red; auto.
  red; intros; congruence.

  inv H; inv H0. simpl in H1.
  assert (args = args0) by (eapply eventval_list_match_determ_2; eauto).
  destruct H1; auto. subst.
  intuition. eapply eventval_match_determ_1; eauto. 
Qed.

(** ** Combined semantics of external calls *)

(** Combining the semantics given above for the various kinds of external calls,
  we define the predicate [external_call] that relates:
- the external function being invoked
- the values of the arguments passed to this function
- the memory state before the call
- the result value of the call
- the memory state after the call
- the trace generated by the call (can be empty).

This predicate is used in the semantics of all CompCert languages. *)

Definition external_call (ef: external_function):
         list val -> mem -> trace -> val -> mem -> Prop :=
  match classify_external_function ef with
  | EF_syscall sg name   => extcall_io_sem name sg
  | EF_load label chunk  => extcall_load_sem label chunk
  | EF_store label chunk => extcall_store_sem label chunk
  | EF_malloc            => extcall_malloc_sem 
  | EF_free              => extcall_free_sem
  end.

Theorem external_call_spec:
  forall ef, 
  extcall_properties (external_call ef) (ef.(ef_sig)).
Proof.
  intros. unfold external_call. destruct (classify_external_function ef). 
  apply extcall_io_ok.
  apply extcall_load_ok.
  apply extcall_store_ok.
  apply extcall_malloc_ok.
  apply extcall_free_ok.
Qed.

Definition external_call_well_typed ef := ec_well_typed _ _ (external_call_spec ef).
Definition external_call_arity ef := ec_arity _ _ (external_call_spec ef).
Definition external_call_valid_block ef := ec_valid_block _ _ (external_call_spec ef).
Definition external_call_bounds ef := ec_bounds _ _ (external_call_spec ef).
Definition external_call_mem_extends ef := ec_mem_extends _ _ (external_call_spec ef).
Definition external_call_mem_inject ef := ec_mem_inject _ _ (external_call_spec ef).
Definition external_call_determ ef := ec_determ _ _ (external_call_spec ef).
