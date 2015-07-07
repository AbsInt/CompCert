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
Require Import Globalenvs.

(** * Events and traces *)

(** The observable behaviour of programs is stated in terms of
  input/output events, which represent the actions of the program
  that the external world can observe.  CompCert leaves much flexibility as to
  the exact content of events: the only requirement is that they
  do not expose memory states nor pointer values 
  (other than pointers to global variables), because these
  are not preserved literally during compilation.  For concreteness,
  we use the following type for events.  Each event represents either:

- A system call (e.g. an input/output operation), recording the
  name of the system call, its parameters, and its result.

- A volatile load from a global memory location, recording the chunk
  and address being read and the value just read. 

- A volatile store to a global memory location, recording the chunk
  and address being written and the value stored there. 

- An annotation, recording the text of the annotation and the values
  of the arguments.

  The values attached to these events are of the following form.
  As mentioned above, we do not expose pointer values directly.
  Pointers relative to a global variable are shown with the name
  of the variable instead of the block identifier.
*)

Inductive eventval: Type :=
  | EVint: int -> eventval
  | EVlong: int64 -> eventval
  | EVfloat: float -> eventval
  | EVsingle: float32 -> eventval
  | EVptr_global: ident -> int -> eventval.

Inductive event: Type :=
  | Event_syscall: ident -> list eventval -> eventval -> event
  | Event_vload: memory_chunk -> ident -> int -> eventval -> event
  | Event_vstore: memory_chunk -> ident -> int -> eventval -> event
  | Event_annot: ident -> list eventval -> event.

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

(** Prefixes of traces. *)

Definition trace_prefix (t1 t2: trace) :=
  exists t3, t2 = t1 ** t3.

Definition traceinf_prefix (t1: trace) (T2: traceinf) :=
  exists T3, T2 = t1 *** T3.

Lemma trace_prefix_app:
  forall t1 t2 t,
  trace_prefix t1 t2 ->
  trace_prefix (t ** t1) (t ** t2).
Proof.
  intros. destruct H as [t3 EQ]. exists t3. traceEq. 
Qed.

Lemma traceinf_prefix_app:
  forall t1 T2 t,
  traceinf_prefix t1 T2 ->
  traceinf_prefix (t ** t1) (t *** T2).
Proof.
  intros. destruct H as [T3 EQ]. exists T3. subst T2. traceEq.
Qed.

(** * Relating values and event values *)

Set Implicit Arguments.

Section EVENTVAL.

(** Symbol environment used to translate between global variable names and their block identifiers. *)
Variable ge: Senv.t.

(** Translation between values and event values. *)

Inductive eventval_match: eventval -> typ -> val -> Prop :=
  | ev_match_int: forall i,
      eventval_match (EVint i) Tint (Vint i)
  | ev_match_long: forall i,
      eventval_match (EVlong i) Tlong (Vlong i)
  | ev_match_float: forall f,
      eventval_match (EVfloat f) Tfloat (Vfloat f)
  | ev_match_single: forall f,
      eventval_match (EVsingle f) Tsingle (Vsingle f)
  | ev_match_ptr: forall id b ofs,
      Senv.public_symbol ge id = true ->
      Senv.find_symbol ge id = Some b ->
      eventval_match (EVptr_global id ofs) Tint (Vptr b ofs).

Inductive eventval_list_match: list eventval -> list typ -> list val -> Prop :=
  | evl_match_nil:
      eventval_list_match nil nil nil
  | evl_match_cons:
      forall ev1 evl ty1 tyl v1 vl,
      eventval_match ev1 ty1 v1 ->
      eventval_list_match evl tyl vl ->
      eventval_list_match (ev1::evl) (ty1::tyl) (v1::vl).

(** Some properties of these translation predicates. *)

Lemma eventval_match_type:
  forall ev ty v,
  eventval_match ev ty v -> Val.has_type v ty.
Proof.
  intros. inv H; simpl; auto. 
Qed.

Lemma eventval_list_match_length:
  forall evl tyl vl, eventval_list_match evl tyl vl -> List.length vl = List.length tyl.
Proof.
  induction 1; simpl; eauto.
Qed.

Lemma eventval_match_lessdef:
  forall ev ty v1 v2,
  eventval_match ev ty v1 -> Val.lessdef v1 v2 -> eventval_match ev ty v2.
Proof.
  intros. inv H; inv H0; constructor; auto.
Qed.

Lemma eventval_list_match_lessdef:
  forall evl tyl vl1, eventval_list_match evl tyl vl1 ->
  forall vl2, Val.lessdef_list vl1 vl2 -> eventval_list_match evl tyl vl2.
Proof.
  induction 1; intros. inv H; constructor.
  inv H1. constructor. eapply eventval_match_lessdef; eauto. eauto.
Qed.

(** Determinism *)

Lemma eventval_match_determ_1:
  forall ev ty v1 v2, eventval_match ev ty v1 -> eventval_match ev ty v2 -> v1 = v2.
Proof.
  intros. inv H; inv H0; auto. congruence.
Qed.

Lemma eventval_match_determ_2:
  forall ev1 ev2 ty v, eventval_match ev1 ty v -> eventval_match ev2 ty v -> ev1 = ev2.
Proof.
  intros. inv H; inv H0; auto.
  decEq. eapply Senv.find_symbol_injective; eauto. 
Qed.

Lemma eventval_list_match_determ_2:
  forall evl1 tyl vl, eventval_list_match evl1 tyl vl ->
  forall evl2, eventval_list_match evl2 tyl vl -> evl1 = evl2.
Proof.
  induction 1; intros. inv H. auto. inv H1. f_equal; eauto.
  eapply eventval_match_determ_2; eauto.
Qed.

(** Validity *)

Definition eventval_valid (ev: eventval) : Prop :=
  match ev with
  | EVint _ => True
  | EVlong _ => True
  | EVfloat _ => True
  | EVsingle _ => True
  | EVptr_global id ofs => Senv.public_symbol ge id = true
  end.

Definition eventval_type (ev: eventval) : typ :=
  match ev with
  | EVint _ => Tint
  | EVlong _ => Tlong
  | EVfloat _ => Tfloat
  | EVsingle _ => Tsingle
  | EVptr_global id ofs => Tint
  end.

Lemma eventval_match_receptive:
  forall ev1 ty v1 ev2,
  eventval_match ev1 ty v1 ->
  eventval_valid ev1 -> eventval_valid ev2 -> eventval_type ev1 = eventval_type ev2 ->
  exists v2, eventval_match ev2 ty v2.
Proof.
  intros. inv H; destruct ev2; simpl in H2; try discriminate.
- exists (Vint i0); constructor.
- simpl in H1; exploit Senv.public_symbol_exists; eauto. intros [b FS]. 
  exists (Vptr b i1); constructor; auto.
- exists (Vlong i0); constructor.
- exists (Vfloat f0); constructor.
- exists (Vsingle f0); constructor; auto.
- exists (Vint i); constructor.
- simpl in H1. exploit Senv.public_symbol_exists. eexact H1. intros [b' FS]. 
  exists (Vptr b' i0); constructor; auto.
Qed.

Lemma eventval_match_valid:
  forall ev ty v, eventval_match ev ty v -> eventval_valid ev.
Proof.
  destruct 1; simpl; auto.
Qed.

Lemma eventval_match_same_type:
  forall ev1 ty v1 ev2 v2,
  eventval_match ev1 ty v1 -> eventval_match ev2 ty v2 -> eventval_type ev1 = eventval_type ev2.
Proof.
  destruct 1; intros EV; inv EV; auto. 
Qed.

End EVENTVAL.

(** Invariance under changes to the global environment *)

Section EVENTVAL_INV.

Variables ge1 ge2: Senv.t.

Hypothesis public_preserved:
  forall id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id.

Lemma eventval_valid_preserved:
  forall ev, eventval_valid ge1 ev -> eventval_valid ge2 ev.
Proof.
  intros. destruct ev; simpl in *; auto. rewrite <- H; auto. 
Qed.

Hypothesis symbols_preserved:
  forall id, Senv.find_symbol ge2 id = Senv.find_symbol ge1 id.

Lemma eventval_match_preserved:
  forall ev ty v,
  eventval_match ge1 ev ty v -> eventval_match ge2 ev ty v.
Proof.
  induction 1; constructor; auto.
  rewrite public_preserved; auto. 
  rewrite symbols_preserved; auto. 
Qed.

Lemma eventval_list_match_preserved:
  forall evl tyl vl,
  eventval_list_match ge1 evl tyl vl -> eventval_list_match ge2 evl tyl vl.
Proof.
  induction 1; constructor; auto. eapply eventval_match_preserved; eauto.
Qed.

End EVENTVAL_INV.

(** Compatibility with memory injections *)

Section EVENTVAL_INJECT.

Variable f: block -> option (block * Z).
Variable ge1 ge2: Senv.t.

Definition symbols_inject : Prop :=
   (forall id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id)
/\ (forall id b1 b2 delta,
     f b1 = Some(b2, delta) -> Senv.find_symbol ge1 id = Some b1 ->
     delta = 0 /\ Senv.find_symbol ge2 id = Some b2)
/\ (forall id b1,
     Senv.public_symbol ge1 id = true -> Senv.find_symbol ge1 id = Some b1 ->
     exists b2, f b1 = Some(b2, 0) /\ Senv.find_symbol ge2 id = Some b2)
/\ (forall b1 b2 delta,
     f b1 = Some(b2, delta) ->
     Senv.block_is_volatile ge2 b2 = Senv.block_is_volatile ge1 b1).

Hypothesis symb_inj: symbols_inject.

Lemma eventval_match_inject:
  forall ev ty v1 v2,
  eventval_match ge1 ev ty v1 -> Val.inject f v1 v2 -> eventval_match ge2 ev ty v2.
Proof.
  intros. inv H; inv H0; try constructor; auto.
  destruct symb_inj as (A & B & C & D). exploit C; eauto. intros [b3 [EQ FS]]. rewrite H4 in EQ; inv EQ.
  rewrite Int.add_zero. constructor; auto. rewrite A; auto.
Qed.

Lemma eventval_match_inject_2:
  forall ev ty v1,
  eventval_match ge1 ev ty v1 -> 
  exists v2, eventval_match ge2 ev ty v2 /\ Val.inject f v1 v2.
Proof.
  intros. inv H; try (econstructor; split; eauto; constructor; fail).
  destruct symb_inj as (A & B & C & D). exploit C; eauto. intros [b2 [EQ FS]].
  exists (Vptr b2 ofs); split. econstructor; eauto. 
  econstructor; eauto. rewrite Int.add_zero; auto.
Qed.

Lemma eventval_list_match_inject:
  forall evl tyl vl1, eventval_list_match ge1 evl tyl vl1 ->
  forall vl2, Val.inject_list f vl1 vl2 -> eventval_list_match ge2 evl tyl vl2.
Proof.
  induction 1; intros. inv H; constructor.
  inv H1. constructor. eapply eventval_match_inject; eauto. eauto.
Qed.

End EVENTVAL_INJECT.

(** * Matching traces. *)

Section MATCH_TRACES.

Variable ge: Senv.t.

(** Matching between traces corresponding to single transitions.
  Arguments (provided by the program) must be equal.
  Results (provided by the outside world) can vary as long as they
  can be converted safely to values. *)

Inductive match_traces: trace -> trace -> Prop :=
  | match_traces_E0:
      match_traces nil nil
  | match_traces_syscall: forall id args res1 res2,
      eventval_valid ge res1 -> eventval_valid ge res2 -> eventval_type res1 = eventval_type res2 ->
      match_traces (Event_syscall id args res1 :: nil) (Event_syscall id args res2 :: nil)
  | match_traces_vload: forall chunk id ofs res1 res2,
      eventval_valid ge res1 -> eventval_valid ge res2 -> eventval_type res1 = eventval_type res2 ->
      match_traces (Event_vload chunk id ofs res1 :: nil) (Event_vload chunk id ofs res2 :: nil)
  | match_traces_vstore: forall chunk id ofs arg,
      match_traces (Event_vstore chunk id ofs arg :: nil) (Event_vstore chunk id ofs arg :: nil)
  | match_traces_annot: forall id args,
      match_traces (Event_annot id args :: nil) (Event_annot id args :: nil).

End MATCH_TRACES.

(** Invariance by change of global environment *)

Section MATCH_TRACES_INV.

Variables ge1 ge2: Senv.t.

Hypothesis public_preserved:
  forall id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id.

Lemma match_traces_preserved:
  forall t1 t2, match_traces ge1 t1 t2 -> match_traces ge2 t1 t2.
Proof.
  induction 1; constructor; auto; eapply eventval_valid_preserved; eauto.
Qed.

End MATCH_TRACES_INV.

(** An output trace is a trace composed only of output events,
  that is, events that do not take any result from the outside world. *)

Definition output_event (ev: event) : Prop :=
  match ev with
  | Event_syscall _ _ _ => False
  | Event_vload _ _ _ _ => False
  | Event_vstore _ _ _ _ => True
  | Event_annot _ _ => True
  end.
  
Fixpoint output_trace (t: trace) : Prop :=
  match t with
  | nil => True
  | ev :: t' => output_event ev /\ output_trace t'
  end.

(** * Semantics of volatile memory accesses *)

Inductive volatile_load (ge: Senv.t):
                   memory_chunk -> mem -> block -> int -> trace -> val -> Prop :=
  | volatile_load_vol: forall chunk m b ofs id ev v,
      Senv.block_is_volatile ge b = true ->
      Senv.find_symbol ge id = Some b ->
      eventval_match ge ev (type_of_chunk chunk) v ->
      volatile_load ge chunk m b ofs
                      (Event_vload chunk id ofs ev :: nil)
                      (Val.load_result chunk v)
  | volatile_load_nonvol: forall chunk m b ofs v,
      Senv.block_is_volatile ge b = false ->
      Mem.load chunk m b (Int.unsigned ofs) = Some v ->
      volatile_load ge chunk m b ofs E0 v.

Inductive volatile_store (ge: Senv.t):
                  memory_chunk -> mem -> block -> int -> val -> trace -> mem -> Prop :=
  | volatile_store_vol: forall chunk m b ofs id ev v,
      Senv.block_is_volatile ge b = true ->
      Senv.find_symbol ge id = Some b ->
      eventval_match ge ev (type_of_chunk chunk) (Val.load_result chunk v) ->
      volatile_store ge chunk m b ofs v
                      (Event_vstore chunk id ofs ev :: nil)
                      m
  | volatile_store_nonvol: forall chunk m b ofs v m',
      Senv.block_is_volatile ge b = false ->
      Mem.store chunk m b (Int.unsigned ofs) v = Some m' ->
      volatile_store ge chunk m b ofs v E0 m'.

(** * Semantics of external functions *)

(** For each external function, its behavior is defined by a predicate relating:
- the global symbol environment
- the values of the arguments passed to this function
- the memory state before the call
- the result value of the call
- the memory state after the call
- the trace generated by the call (can be empty).
*)

Definition extcall_sem : Type := 
  Senv.t -> list val -> mem -> trace -> val -> mem -> Prop.

(** We now specify the expected properties of this predicate. *)

Definition loc_out_of_bounds (m: mem) (b: block) (ofs: Z) : Prop :=
  ~Mem.perm m b ofs Max Nonempty.

Definition loc_not_writable (m: mem) (b: block) (ofs: Z) : Prop :=
  ~Mem.perm m b ofs Max Writable.

Definition loc_unmapped (f: meminj) (b: block) (ofs: Z): Prop :=
  f b = None.

Definition loc_out_of_reach (f: meminj) (m: mem) (b: block) (ofs: Z): Prop :=
  forall b0 delta,
  f b0 = Some(b, delta) -> ~Mem.perm m b0 (ofs - delta) Max Nonempty.

Definition inject_separated (f f': meminj) (m1 m2: mem): Prop :=
  forall b1 b2 delta,
  f b1 = None -> f' b1 = Some(b2, delta) ->
  ~Mem.valid_block m1 b1 /\ ~Mem.valid_block m2 b2.

Record extcall_properties (sem: extcall_sem)
                          (sg: signature) (free_globals: list ident) : Prop :=
  mk_extcall_properties {

(** The return value of an external call must agree with its signature. *)
  ec_well_typed:
    forall ge vargs m1 t vres m2,
    sem ge vargs m1 t vres m2 ->
    Val.has_type vres (proj_sig_res sg);

(** The semantics is invariant under change of global environment that preserves symbols. *)
  ec_symbols_preserved:
    forall ge1 ge2 vargs m1 t vres m2,
    (forall id, Senv.find_symbol ge2 id = Senv.find_symbol ge1 id) ->
    (forall id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id) ->
    (forall b, Senv.block_is_volatile ge2 b = Senv.block_is_volatile ge1 b) ->
    sem ge1 vargs m1 t vres m2 ->
    sem ge2 vargs m1 t vres m2;

(** External calls cannot invalidate memory blocks.  (Remember that
  freeing a block does not invalidate its block identifier.) *)
  ec_valid_block:
    forall ge vargs m1 t vres m2 b,
    sem ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b -> Mem.valid_block m2 b;

(** External calls cannot increase the max permissions of a valid block.
    They can decrease the max permissions, e.g. by freeing. *)
  ec_max_perm:
    forall ge vargs m1 t vres m2 b ofs p,
    sem ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p;

(** External call cannot modify memory unless they have [Max, Writable]
   permissions. *)
  ec_readonly:
    forall ge vargs m1 t vres m2,
    sem ge vargs m1 t vres m2 ->
    Mem.unchanged_on (loc_not_writable m1) m1 m2;

(** External calls must commute with memory extensions, in the
  following sense. *)
  ec_mem_extends:
    forall ge vargs m1 t vres m2 m1' vargs',
    sem ge vargs m1 t vres m2 ->
    Mem.extends m1 m1' ->
    Val.lessdef_list vargs vargs' ->
    exists vres', exists m2',
       sem ge vargs' m1' t vres' m2'
    /\ Val.lessdef vres vres'
    /\ Mem.extends m2 m2'
    /\ Mem.unchanged_on (loc_out_of_bounds m1) m1' m2';

(** External calls must commute with memory injections,
  in the following sense. *)
  ec_mem_inject:
    forall ge1 ge2 vargs m1 t vres m2 f m1' vargs',
    symbols_inject f ge1 ge2 ->
    (forall id b1,
       In id free_globals -> Senv.find_symbol ge1 id = Some b1 ->
       exists b2, f b1 = Some(b2, 0) /\ Senv.find_symbol ge2 id = Some b2) ->
    sem ge1 vargs m1 t vres m2 ->
    Mem.inject f m1 m1' ->
    Val.inject_list f vargs vargs' ->
    exists f', exists vres', exists m2',
       sem ge2 vargs' m1' t vres' m2'
    /\ Val.inject f' vres vres'
    /\ Mem.inject f' m2 m2'
    /\ Mem.unchanged_on (loc_unmapped f) m1 m2
    /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'
    /\ inject_incr f f'
    /\ inject_separated f f' m1 m1';

(** External calls produce at most one event. *)
  ec_trace_length:
    forall ge vargs m t vres m',
    sem ge vargs m t vres m' -> (length t <= 1)%nat;

(** External calls must be receptive to changes of traces by another, matching trace. *)
  ec_receptive:
    forall ge vargs m t1 vres1 m1 t2,
    sem ge vargs m t1 vres1 m1 -> match_traces ge t1 t2 ->
    exists vres2, exists m2, sem ge vargs m t2 vres2 m2;

(** External calls must be deterministic up to matching between traces. *)
  ec_determ:
    forall ge vargs m t1 vres1 m1 t2 vres2 m2,
    sem ge vargs m t1 vres1 m1 -> sem ge vargs m t2 vres2 m2 ->
    match_traces ge t1 t2 /\ (t1 = t2 -> vres1 = vres2 /\ m1 = m2)
}.

(** ** Semantics of volatile loads *)

Inductive volatile_load_sem (chunk: memory_chunk) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | volatile_load_sem_intro: forall b ofs m t v,
      volatile_load ge chunk m b ofs t v ->
      volatile_load_sem chunk ge (Vptr b ofs :: nil) m t v m.

Lemma volatile_load_preserved:
  forall ge1 ge2 chunk m b ofs t v,
  (forall id, Senv.find_symbol ge2 id = Senv.find_symbol ge1 id) ->
  (forall id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id) ->
  (forall b, Senv.block_is_volatile ge2 b = Senv.block_is_volatile ge1 b) ->
  volatile_load ge1 chunk m b ofs t v ->
  volatile_load ge2 chunk m b ofs t v.
Proof.
  intros. inv H2; constructor; auto.
  rewrite H1; auto.
  rewrite H; auto.
  eapply eventval_match_preserved; eauto.
  rewrite H1; auto.
Qed.

Lemma volatile_load_extends:
  forall ge chunk m b ofs t v m',
  volatile_load ge chunk m b ofs t v ->
  Mem.extends m m' ->
  exists v', volatile_load ge chunk m' b ofs t v' /\ Val.lessdef v v'.
Proof.
  intros. inv H.
  econstructor; split; eauto. econstructor; eauto.
  exploit Mem.load_extends; eauto. intros [v' [A B]]. exists v'; split; auto. constructor; auto.
Qed.

Lemma volatile_load_inject:
  forall ge1 ge2 f chunk m b ofs t v b' ofs' m',
  symbols_inject f ge1 ge2 ->
  volatile_load ge1 chunk m b ofs t v ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  Mem.inject f m m' ->
  exists v', volatile_load ge2 chunk m' b' ofs' t v' /\ Val.inject f v v'.
Proof.
  intros until m'; intros SI VL VI MI. generalize SI; intros (A & B & C & D). 
  inv VL.
- (* volatile load *)
  inv VI. exploit B; eauto. intros [U V]. subst delta. 
  exploit eventval_match_inject_2; eauto. intros (v2 & X & Y).
  rewrite Int.add_zero. exists (Val.load_result chunk v2); split.
  constructor; auto.
  erewrite D; eauto.
  apply Val.load_result_inject. auto.
- (* normal load *)
  exploit Mem.loadv_inject; eauto. simpl; eauto. simpl; intros (v2 & X & Y). 
  exists v2; split; auto. 
  constructor; auto.
  inv VI. erewrite D; eauto. 
Qed.

Lemma volatile_load_receptive:
  forall ge chunk m b ofs t1 t2 v1,
  volatile_load ge chunk m b ofs t1 v1 -> match_traces ge t1 t2 ->
  exists v2, volatile_load ge chunk m b ofs t2 v2.
Proof.
  intros. inv H; inv H0.
  exploit eventval_match_receptive; eauto. intros [v' EM].
  exists (Val.load_result chunk v'). constructor; auto.
  exists v1; constructor; auto.
Qed.

Lemma volatile_load_ok:
  forall chunk,
  extcall_properties (volatile_load_sem chunk) 
                     (mksignature (Tint :: nil) (Some (type_of_chunk chunk)) cc_default)
                     nil.
Proof.
  intros; constructor; intros.
(* well typed *)
  unfold proj_sig_res; simpl. inv H. inv H0. apply Val.load_result_type. 
  eapply Mem.load_type; eauto. 
(* symbols *)
  inv H2. constructor. eapply volatile_load_preserved; eauto. 
(* valid blocks *)
  inv H; auto.
(* max perms *)
  inv H; auto.
(* readonly *)
  inv H. apply Mem.unchanged_on_refl.
(* mem extends *)
  inv H. inv H1. inv H6. inv H4. 
  exploit volatile_load_extends; eauto. intros [v' [A B]].
  exists v'; exists m1'; intuition. constructor; auto.
(* mem injects *)
  inv H1. inv H3. inv H8. inversion H6; subst. 
  exploit volatile_load_inject; eauto. intros [v' [A B]]. 
  exists f; exists v'; exists m1'; intuition. constructor; auto.
  red; intros. congruence.
(* trace length *)
  inv H; inv H0; simpl; omega.
(* receptive *)
  inv H. exploit volatile_load_receptive; eauto. intros [v2 A].
  exists v2; exists m1; constructor; auto.
(* determ *)
  inv H; inv H0. inv H1; inv H7; try congruence.
  assert (id = id0) by (eapply Senv.find_symbol_injective; eauto). subst id0.
  split. constructor. 
  eapply eventval_match_valid; eauto.
  eapply eventval_match_valid; eauto.
  eapply eventval_match_same_type; eauto.
  intros EQ; inv EQ. 
  assert (v = v0) by (eapply eventval_match_determ_1; eauto). subst v0.
  auto.
  split. constructor. intuition congruence.
Qed.

Inductive volatile_load_global_sem (chunk: memory_chunk) (id: ident) (ofs: int) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | volatile_load_global_sem_intro: forall b t v m,
      Senv.find_symbol ge id = Some b ->
      volatile_load ge chunk m b ofs t v ->
      volatile_load_global_sem chunk id ofs ge nil m t v m.

Remark volatile_load_global_charact:
  forall chunk id ofs ge vargs m t vres m',
  volatile_load_global_sem chunk id ofs ge vargs m t vres m' <->
  exists b, Senv.find_symbol ge id = Some b /\ volatile_load_sem chunk ge (Vptr b ofs :: vargs) m t vres m'.
Proof.
  intros; split.
  intros. inv H. exists b; split; auto. constructor; auto. 
  intros [b [P Q]]. inv Q. econstructor; eauto.
Qed.

Lemma volatile_load_global_ok:
  forall chunk id ofs,
  extcall_properties (volatile_load_global_sem chunk id ofs) 
                     (mksignature nil (Some (type_of_chunk chunk)) cc_default)
                     (id :: nil).
Proof.
  intros; constructor; intros.
(* well typed *)
  unfold proj_sig_res; simpl. inv H. inv H1. apply Val.load_result_type.
  eapply Mem.load_type; eauto. 
(* symbols *)
  inv H2. econstructor. rewrite H; eauto. eapply volatile_load_preserved; eauto. 
(* valid blocks *)
  inv H; auto.
(* max perm *)
  inv H; auto.
(* readonly *)
  inv H. apply Mem.unchanged_on_refl.
(* extends *)
  inv H. inv H1. exploit volatile_load_extends; eauto. intros [v' [A B]].
  exists v'; exists m1'; intuition. econstructor; eauto.
(* inject *)
  inv H1. inv H3.
  exploit H0; eauto with coqlib. intros (b2 & INJ & FS2). 
  assert (Val.inject f (Vptr b ofs) (Vptr b2 ofs)).
    econstructor; eauto. rewrite Int.add_zero; auto. 
  exploit volatile_load_inject; eauto. intros [v' [A B]].
  exists f; exists v'; exists m1'; intuition. econstructor; eauto. 
  red; intros; congruence. 
(* trace length *)
  inv H; inv H1; simpl; omega.
(* receptive *)
  inv H. exploit volatile_load_receptive; eauto. intros [v2 A].
  exists v2; exists m1; econstructor; eauto.
(* determ *)
  rewrite volatile_load_global_charact in *. 
  destruct H as [b1 [A1 B1]]. destruct H0 as [b2 [A2 B2]].
  rewrite A1 in A2; inv A2.
  eapply ec_determ. eapply volatile_load_ok. eauto. eauto. 
Qed.

(** ** Semantics of volatile stores *)

Inductive volatile_store_sem (chunk: memory_chunk) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | volatile_store_sem_intro: forall b ofs m1 v t m2,
      volatile_store ge chunk m1 b ofs v t m2 ->
      volatile_store_sem chunk ge (Vptr b ofs :: v :: nil) m1 t Vundef m2.

Lemma volatile_store_preserved:
  forall ge1 ge2 chunk m1 b ofs v t m2,
  (forall id, Senv.find_symbol ge2 id = Senv.find_symbol ge1 id) ->
  (forall id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id) ->
  (forall b, Senv.block_is_volatile ge2 b = Senv.block_is_volatile ge1 b) ->
  volatile_store ge1 chunk m1 b ofs v t m2 ->
  volatile_store ge2 chunk m1 b ofs v t m2.
Proof.
  intros. inv H2; constructor; auto.
  rewrite H1; auto.
  rewrite H; auto.
  eapply eventval_match_preserved; eauto.
  rewrite H1; auto.
Qed.

Lemma volatile_store_readonly:
  forall ge chunk1 m1 b1 ofs1 v t m2,
  volatile_store ge chunk1 m1 b1 ofs1 v t m2 ->
  Mem.unchanged_on (loc_not_writable m1) m1 m2.
Proof.
  intros. inv H.
  apply Mem.unchanged_on_refl.
  eapply Mem.store_unchanged_on; eauto. 
  exploit Mem.store_valid_access_3; eauto. intros [P Q]. 
  intros. unfold loc_not_writable. red; intros. elim H2. 
  apply Mem.perm_cur_max. apply P. auto. 
Qed.

Lemma volatile_store_extends:
  forall ge chunk m1 b ofs v t m2 m1' v',
  volatile_store ge chunk m1 b ofs v t m2 ->
  Mem.extends m1 m1' ->
  Val.lessdef v v' ->
  exists m2', 
     volatile_store ge chunk m1' b ofs v' t m2'
  /\ Mem.extends m2 m2'
  /\ Mem.unchanged_on (loc_out_of_bounds m1) m1' m2'.
Proof.
  intros. inv H.
- econstructor; split. econstructor; eauto.
  eapply eventval_match_lessdef; eauto. apply Val.load_result_lessdef; auto. 
  auto with mem.
- exploit Mem.store_within_extends; eauto. intros [m2' [A B]].
  exists m2'; intuition.
+ econstructor; eauto.
+ eapply Mem.store_unchanged_on; eauto. 
  unfold loc_out_of_bounds; intros.
  assert (Mem.perm m1 b i Max Nonempty).
  { apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
    exploit Mem.store_valid_access_3. eexact H3. intros [P Q]. eauto. }
  tauto.
Qed.

Lemma volatile_store_inject:
  forall ge1 ge2 f chunk m1 b ofs v t m2 m1' b' ofs' v',
  symbols_inject f ge1 ge2 ->
  volatile_store ge1 chunk m1 b ofs v t m2 ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  Val.inject f v v' ->
  Mem.inject f m1 m1' ->
  exists m2',
       volatile_store ge2 chunk m1' b' ofs' v' t m2'
    /\ Mem.inject f m2 m2'
    /\ Mem.unchanged_on (loc_unmapped f) m1 m2
    /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'.
Proof.
  intros until v'; intros SI VS AI VI MI. 
  generalize SI; intros (P & Q & R & S). 
  inv VS.
- (* volatile store *)
  inv AI. exploit Q; eauto. intros [A B]. subst delta. 
  rewrite Int.add_zero. exists m1'; split.
  constructor; auto. erewrite S; eauto. 
  eapply eventval_match_inject; eauto. apply Val.load_result_inject. auto.
  intuition auto with mem.
- (* normal store *)
  inversion AI; subst.
  assert (Mem.storev chunk m1 (Vptr b ofs) v = Some m2). simpl; auto.
  exploit Mem.storev_mapped_inject; eauto. intros [m2' [A B]].
  exists m2'; intuition auto.
+ constructor; auto. erewrite S; eauto. 
+ eapply Mem.store_unchanged_on; eauto.
  unfold loc_unmapped; intros. inv AI; congruence.
+ eapply Mem.store_unchanged_on; eauto. 
  unfold loc_out_of_reach; intros. red; intros. simpl in A. 
  assert (EQ: Int.unsigned (Int.add ofs (Int.repr delta)) = Int.unsigned ofs + delta)
  by (eapply Mem.address_inject; eauto with mem).
  rewrite EQ in *.
  eelim H3; eauto. 
  exploit Mem.store_valid_access_3. eexact H0. intros [X Y]. 
  apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem. 
  apply X. omega.
Qed.

Lemma volatile_store_receptive:
  forall ge chunk m b ofs v t1 m1 t2,
  volatile_store ge chunk m b ofs v t1 m1 -> match_traces ge t1 t2 -> t1 = t2.
Proof.
  intros. inv H; inv H0; auto.  
Qed.

Lemma volatile_store_ok:
  forall chunk,
  extcall_properties (volatile_store_sem chunk) 
                     (mksignature (Tint :: type_of_chunk chunk :: nil) None cc_default)
                     nil.
Proof.
  intros; constructor; intros.
(* well typed *)
  unfold proj_sig_res; simpl. inv H; constructor.
(* symbols preserved *)
  inv H2. constructor. eapply volatile_store_preserved; eauto. 
(* valid block *)
  inv H. inv H1. auto. eauto with mem.
(* perms *)
  inv H. inv H2. auto. eauto with mem. 
(* readonly *)
  inv H. eapply volatile_store_readonly; eauto.
(* mem extends*)
  inv H. inv H1. inv H6. inv H7. inv H4.
  exploit volatile_store_extends; eauto. intros [m2' [A [B C]]]. 
  exists Vundef; exists m2'; intuition. constructor; auto. 
(* mem inject *)
  inv H1. inv H3. inv H8. inv H9. inversion H6; subst.
  exploit volatile_store_inject; eauto. intros [m2' [A [B [C D]]]].
  exists f; exists Vundef; exists m2'; intuition. constructor; auto. red; intros; congruence.
(* trace length *)
  inv H; inv H0; simpl; omega.
(* receptive *)
  assert (t1 = t2). inv H. eapply volatile_store_receptive; eauto.
  subst t2; exists vres1; exists m1; auto.
(* determ *)
  inv H; inv H0. inv H1; inv H8; try congruence.
  assert (id = id0) by (eapply Senv.find_symbol_injective; eauto). subst id0.
  assert (ev = ev0) by (eapply eventval_match_determ_2; eauto). subst ev0.
  split. constructor. auto.
  split. constructor. intuition congruence.
Qed.

Inductive volatile_store_global_sem (chunk: memory_chunk) (id: ident) (ofs: int) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | volatile_store_global_sem_intro: forall b m1 v t m2,
      Senv.find_symbol ge id = Some b ->
      volatile_store ge chunk m1 b ofs v t m2 ->
      volatile_store_global_sem chunk id ofs ge (v :: nil) m1 t Vundef m2.

Remark volatile_store_global_charact:
  forall chunk id ofs ge vargs m t vres m',
  volatile_store_global_sem chunk id ofs ge vargs m t vres m' <->
  exists b, Senv.find_symbol ge id = Some b /\ volatile_store_sem chunk ge (Vptr b ofs :: vargs) m t vres m'.
Proof.
  intros; split. 
  intros. inv H; exists b; split; auto; econstructor; eauto.
  intros [b [P Q]]. inv Q. econstructor; eauto. 
Qed.

Lemma volatile_store_global_ok:
  forall chunk id ofs,
  extcall_properties (volatile_store_global_sem chunk id ofs) 
                     (mksignature (type_of_chunk chunk :: nil) None cc_default)
                     (id :: nil).
Proof.
  intros; constructor; intros.
(* well typed *)
  unfold proj_sig_res; simpl. inv H; constructor.
(* symbols preserved *)
  inv H2. econstructor. rewrite H; eauto. eapply volatile_store_preserved; eauto. 
(* valid block *)
  inv H. inv H2. auto. eauto with mem.
(* perms *)
  inv H. inv H3. auto. eauto with mem. 
(* readonly *)
  inv H. eapply volatile_store_readonly; eauto.
(* mem extends*)
  rewrite volatile_store_global_charact in H. destruct H as [b [P Q]]. 
  exploit ec_mem_extends. eapply volatile_store_ok. eexact Q. eauto. eauto. 
  intros [vres' [m2' [A [B [C D]]]]]. 
  exists vres'; exists m2'; intuition. rewrite volatile_store_global_charact. exists b; auto. 
(* mem inject *)
  rewrite volatile_store_global_charact in H1. destruct H1 as [b [P Q]].
  exploit H0; eauto with coqlib. intros (b2 & INJ & FS2). 
  assert (Val.inject f (Vptr b ofs) (Vptr b2 ofs)). econstructor; eauto. rewrite Int.add_zero; auto.
  exploit ec_mem_inject. eapply volatile_store_ok. eauto. intuition. eexact Q. eauto. constructor. eauto. eauto. 
  intros [f' [vres' [m2' [A [B [C [D [E G]]]]]]]].
  exists f'; exists vres'; exists m2'; intuition.
  rewrite volatile_store_global_charact. exists b2; auto. 
(* trace length *)
  inv H. inv H1; simpl; omega.
(* receptive *)
  assert (t1 = t2). inv H. eapply volatile_store_receptive; eauto. subst t2. 
  exists vres1; exists m1; congruence.
(* determ *)
  rewrite volatile_store_global_charact in *. 
  destruct H as [b1 [A1 B1]]. destruct H0 as [b2 [A2 B2]]. rewrite A1 in A2; inv A2. 
  eapply ec_determ. eapply volatile_store_ok. eauto. eauto. 
Qed.

(** ** Semantics of dynamic memory allocation (malloc) *)

Inductive extcall_malloc_sem (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_malloc_sem_intro: forall n m m' b m'',
      Mem.alloc m (-4) (Int.unsigned n) = (m', b) ->
      Mem.store Mint32 m' b (-4) (Vint n) = Some m'' ->
      extcall_malloc_sem ge (Vint n :: nil) m E0 (Vptr b Int.zero) m''.

Lemma extcall_malloc_ok:
  extcall_properties extcall_malloc_sem 
                     (mksignature (Tint :: nil) (Some Tint) cc_default)
                     nil.
Proof.
  assert (UNCHANGED:
    forall (P: block -> Z -> Prop) m n m' b m'',
    Mem.alloc m (-4) (Int.unsigned n) = (m', b) ->
    Mem.store Mint32 m' b (-4) (Vint n) = Some m'' ->
    Mem.unchanged_on P m m'').
  {
    intros; constructor; intros.
  - split; intros; eauto with mem.
  - assert (b0 <> b) by (eapply Mem.valid_not_valid_diff; eauto with mem).
    erewrite Mem.store_mem_contents; eauto. rewrite Maps.PMap.gso by auto.
    Local Transparent Mem.alloc. unfold Mem.alloc in H. injection H; intros A B.
    rewrite <- B; simpl. rewrite A. rewrite Maps.PMap.gso by auto. auto.
  } 

  constructor; intros.
(* well typed *)
  inv H. unfold proj_sig_res; simpl. auto.
(* symbols preserved *)
  inv H2; econstructor; eauto.
(* valid block *)
  inv H. eauto with mem.
(* perms *)
  inv H. exploit Mem.perm_alloc_inv. eauto. eapply Mem.perm_store_2; eauto.
  rewrite dec_eq_false. auto. 
  apply Mem.valid_not_valid_diff with m1; eauto with mem.
(* readonly *)
  inv H. eapply UNCHANGED; eauto. 
(* mem extends *)
  inv H. inv H1. inv H5. inv H7. 
  exploit Mem.alloc_extends; eauto. apply Zle_refl. apply Zle_refl.
  intros [m3' [A B]].
  exploit Mem.store_within_extends. eexact B. eauto. 
  instantiate (1 := Vint n). auto. 
  intros [m2' [C D]].
  exists (Vptr b Int.zero); exists m2'; intuition.
  econstructor; eauto.
  eapply UNCHANGED; eauto.
(* mem injects *)
  inv H1. inv H3. inv H7. inv H9.
  exploit Mem.alloc_parallel_inject; eauto. apply Zle_refl. apply Zle_refl. 
  intros [f' [m3' [b' [ALLOC [A [B [C D]]]]]]].
  exploit Mem.store_mapped_inject. eexact A. eauto. eauto. 
  instantiate (1 := Vint n). auto. 
  intros [m2' [E G]].
  exists f'; exists (Vptr b' Int.zero); exists m2'; intuition.
  econstructor; eauto.
  econstructor. eauto. auto.
  eapply UNCHANGED; eauto.
  eapply UNCHANGED; eauto.
  red; intros. destruct (eq_block b1 b). 
  subst b1. rewrite C in H3. inv H3. eauto with mem. 
  rewrite D in H3 by auto. congruence.
(* trace length *)
  inv H; simpl; omega.
(* receptive *)
  assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
(* determ *)
  inv H; inv H0. split. constructor. intuition congruence. 
Qed.

(** ** Semantics of dynamic memory deallocation (free) *)

Inductive extcall_free_sem (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_free_sem_intro: forall b lo sz m m',
      Mem.load Mint32 m b (Int.unsigned lo - 4) = Some (Vint sz) ->
      Int.unsigned sz > 0 ->
      Mem.free m b (Int.unsigned lo - 4) (Int.unsigned lo + Int.unsigned sz) = Some m' ->
      extcall_free_sem ge (Vptr b lo :: nil) m E0 Vundef m'.

Lemma extcall_free_ok:
  extcall_properties extcall_free_sem 
                     (mksignature (Tint :: nil) None cc_default)
                     nil.
Proof.
  constructor; intros.
(* well typed *)
  inv H. unfold proj_sig_res. simpl. auto.
(* symbols preserved *)
  inv H2; econstructor; eauto.
(* valid block *)
  inv H. eauto with mem.
(* perms *)
  inv H. eapply Mem.perm_free_3; eauto. 
(* readonly *)
  inv H. eapply Mem.free_unchanged_on; eauto. 
  intros. red; intros. elim H3. 
  apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem. 
  eapply Mem.free_range_perm; eauto. 
(* mem extends *)
  inv H. inv H1. inv H8. inv H6. 
  exploit Mem.load_extends; eauto. intros [vsz [A B]]. inv B. 
  exploit Mem.free_parallel_extends; eauto. intros [m2' [C D]].
  exists Vundef; exists m2'; intuition.
  econstructor; eauto.
  eapply Mem.free_unchanged_on; eauto. 
  unfold loc_out_of_bounds; intros. 
  assert (Mem.perm m1 b i Max Nonempty).
  { apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem. 
    eapply Mem.free_range_perm. eexact H4. eauto. }
  tauto.
(* mem inject *)
  inv H1. inv H3. inv H8. inv H10.
  exploit Mem.load_inject; eauto. intros [vsz [A B]]. inv B.
  assert (Mem.range_perm m1 b (Int.unsigned lo - 4) (Int.unsigned lo + Int.unsigned sz) Cur Freeable).
    eapply Mem.free_range_perm; eauto.
  exploit Mem.address_inject; eauto. 
    apply Mem.perm_implies with Freeable; auto with mem.
    apply H1. instantiate (1 := lo). omega. 
  intro EQ.
  exploit Mem.free_parallel_inject; eauto. intros (m2' & C & D).
  exists f, Vundef, m2'; split.
  apply extcall_free_sem_intro with (sz := sz) (m' := m2'). 
    rewrite EQ. rewrite <- A. f_equal. omega. 
    auto.
    rewrite ! EQ. rewrite <- C. f_equal; omega.
  split. auto. 
  split. auto.
  split. eapply Mem.free_unchanged_on; eauto. unfold loc_unmapped. intros; congruence.
  split. eapply Mem.free_unchanged_on; eauto. unfold loc_out_of_reach. 
    intros. red; intros. eelim H8; eauto.
    apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem. 
    apply H1. omega.
  split. auto. 
  red; intros. congruence.
(* trace length *)
  inv H; simpl; omega.
(* receptive *)
  assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
(* determ *)
  inv H; inv H0. split. constructor. intuition congruence.
Qed.

(** ** Semantics of [memcpy] operations. *)

Inductive extcall_memcpy_sem (sz al: Z) (ge: Senv.t):
                        list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_memcpy_sem_intro: forall bdst odst bsrc osrc m bytes m',
      al = 1 \/ al = 2 \/ al = 4 \/ al = 8 -> sz >= 0 -> (al | sz) ->
      (sz > 0 -> (al | Int.unsigned osrc)) ->
      (sz > 0 -> (al | Int.unsigned odst)) ->
      bsrc <> bdst \/ Int.unsigned osrc = Int.unsigned odst
                   \/ Int.unsigned osrc + sz <= Int.unsigned odst
                   \/ Int.unsigned odst + sz <= Int.unsigned osrc ->
      Mem.loadbytes m bsrc (Int.unsigned osrc) sz = Some bytes ->
      Mem.storebytes m bdst (Int.unsigned odst) bytes = Some m' ->
      extcall_memcpy_sem sz al ge (Vptr bdst odst :: Vptr bsrc osrc :: nil) m E0 Vundef m'.

Lemma extcall_memcpy_ok:
  forall sz al,
  extcall_properties (extcall_memcpy_sem sz al)
                     (mksignature (Tint :: Tint :: nil) None cc_default)
                     nil.
Proof.
  intros. constructor.
- (* return type *)
  intros. inv H. constructor. 
- (* change of globalenv *)
  intros. inv H2. econstructor; eauto.
- (* valid blocks *)
  intros. inv H. eauto with mem. 
- (* perms *)
  intros. inv H. eapply Mem.perm_storebytes_2; eauto. 
- (* readonly *)
  intros. inv H. eapply Mem.storebytes_unchanged_on; eauto. 
  intros; red; intros. elim H8. 
  apply Mem.perm_cur_max. eapply Mem.storebytes_range_perm; eauto. 
- (* extensions *)
  intros. inv H. 
  inv H1. inv H13. inv H14. inv H10. inv H11.
  exploit Mem.loadbytes_length; eauto. intros LEN.
  exploit Mem.loadbytes_extends; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_within_extends; eauto. intros [m2' [C D]].
  exists Vundef; exists m2'.
  split. econstructor; eauto.
  split. constructor.
  split. auto.
  eapply Mem.storebytes_unchanged_on; eauto. unfold loc_out_of_bounds; intros. 
  assert (Mem.perm m1 bdst i Max Nonempty).
  apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
  eapply Mem.storebytes_range_perm; eauto. 
  erewrite list_forall2_length; eauto. 
  tauto.
- (* injections *)
  intros. inv H1. inv H3. inv H15. inv H16. inv H12. inv H13.
  destruct (zeq sz 0).
+ (* special case sz = 0 *)
  assert (bytes = nil). 
  { exploit (Mem.loadbytes_empty m1 bsrc (Int.unsigned osrc) sz). omega. congruence. }
  subst.
  destruct (Mem.range_perm_storebytes m1' b0 (Int.unsigned (Int.add odst (Int.repr delta0))) nil)
  as [m2' SB].
  simpl. red; intros; omegaContradiction.
  exists f, Vundef, m2'. 
  split. econstructor; eauto. 
  intros; omegaContradiction.
  intros; omegaContradiction.
  right; omega. 
  apply Mem.loadbytes_empty. omega. 
  split. auto.
  split. eapply Mem.storebytes_empty_inject; eauto.
  split. eapply Mem.storebytes_unchanged_on; eauto. unfold loc_unmapped; intros.
  congruence.
  split. eapply Mem.storebytes_unchanged_on; eauto.
  simpl; intros; omegaContradiction.
  split. apply inject_incr_refl.
  red; intros; congruence.
+ (* general case sz > 0 *)
  exploit Mem.loadbytes_length; eauto. intros LEN.
  assert (RPSRC: Mem.range_perm m1 bsrc (Int.unsigned osrc) (Int.unsigned osrc + sz) Cur Nonempty).
    eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm; eauto. auto with mem.
  assert (RPDST: Mem.range_perm m1 bdst (Int.unsigned odst) (Int.unsigned odst + sz) Cur Nonempty).
    replace sz with (Z_of_nat (length bytes)).
    eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. auto with mem.
    rewrite LEN. apply nat_of_Z_eq. omega.
  assert (PSRC: Mem.perm m1 bsrc (Int.unsigned osrc) Cur Nonempty).
    apply RPSRC. omega.
  assert (PDST: Mem.perm m1 bdst (Int.unsigned odst) Cur Nonempty).
    apply RPDST. omega.
  exploit Mem.address_inject.  eauto. eexact PSRC. eauto. intros EQ1.
  exploit Mem.address_inject.  eauto. eexact PDST. eauto. intros EQ2.
  exploit Mem.loadbytes_inject; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_mapped_inject; eauto. intros [m2' [C D]].
  exists f; exists Vundef; exists m2'.
  split. econstructor; try rewrite EQ1; try rewrite EQ2; eauto. 
  intros; eapply Mem.aligned_area_inject with (m := m1); eauto.
  intros; eapply Mem.aligned_area_inject with (m := m1); eauto.
  eapply Mem.disjoint_or_equal_inject with (m := m1); eauto.
  apply Mem.range_perm_max with Cur; auto.
  apply Mem.range_perm_max with Cur; auto. omega.
  split. constructor.
  split. auto.
  split. eapply Mem.storebytes_unchanged_on; eauto. unfold loc_unmapped; intros.
  congruence.
  split. eapply Mem.storebytes_unchanged_on; eauto. unfold loc_out_of_reach; intros. red; intros.
  eelim H3; eauto. 
  apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
  eapply Mem.storebytes_range_perm; eauto. 
  erewrite list_forall2_length; eauto. 
  omega.
  split. apply inject_incr_refl.
  red; intros; congruence.
- (* trace length *)
  intros; inv H. simpl; omega.
- (* receptive *)
  intros. 
  assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
- (* determ *)
  intros; inv H; inv H0. split. constructor. intros; split; congruence.
Qed.

(** ** Semantics of annotations. *)

Inductive extcall_annot_sem (text: ident) (targs: list typ) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_annot_sem_intro: forall vargs m args,
      eventval_list_match ge args targs vargs ->
      extcall_annot_sem text targs ge vargs m (Event_annot text args :: E0) Vundef m.

Lemma extcall_annot_ok:
  forall text targs,
  extcall_properties (extcall_annot_sem text targs)
                     (mksignature targs None cc_default)
                     nil.
Proof.
  intros; constructor; intros.
(* well typed *)
  inv H. simpl. auto.
(* symbols *)
  inv H2. econstructor; eauto. 
  eapply eventval_list_match_preserved; eauto.
(* valid blocks *)
  inv H; auto.
(* perms *)
  inv H; auto.
(* readonly *)
  inv H. apply Mem.unchanged_on_refl.
(* mem extends *)
  inv H.
  exists Vundef; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_list_match_lessdef; eauto.
(* mem injects *)
  inv H1.
  exists f; exists Vundef; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_list_match_inject; eauto.
  red; intros; congruence.
(* trace length *)
  inv H; simpl; omega.
(* receptive *)
  assert (t1 = t2). inv H; inv H0; auto. 
  exists vres1; exists m1; congruence.
(* determ *)
  inv H; inv H0.
  assert (args = args0). eapply eventval_list_match_determ_2; eauto. subst args0.
  split. constructor. auto.
Qed.

Inductive extcall_annot_val_sem (text: ident) (targ: typ) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_annot_val_sem_intro: forall varg m arg,
      eventval_match ge arg targ varg ->
      extcall_annot_val_sem text targ ge (varg :: nil) m (Event_annot text (arg :: nil) :: E0) varg m.

Lemma extcall_annot_val_ok:
  forall text targ,
  extcall_properties (extcall_annot_val_sem text targ)
                     (mksignature (targ :: nil) (Some targ) cc_default)
                     nil.
Proof.
  intros; constructor; intros.
(* well typed *)
  inv H. unfold proj_sig_res; simpl. eapply eventval_match_type; eauto.
(* symbols *)
  inv H2. econstructor; eauto. 
  eapply eventval_match_preserved; eauto.
(* valid blocks *)
  inv H; auto.
(* perms *)
  inv H; auto.
(* readonly *)
  inv H. apply Mem.unchanged_on_refl.
(* mem extends *)
  inv H. inv H1. inv H6. 
  exists v2; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_match_lessdef; eauto.
(* mem inject *)
  inv H1. inv H3. inv H8.
  exists f; exists v'; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_match_inject; eauto.
  red; intros; congruence.
(* trace length *)
  inv H; simpl; omega.
(* receptive *)
  assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
(* determ *)
  inv H; inv H0.
  assert (arg = arg0). eapply eventval_match_determ_2; eauto. subst arg0.
  split. constructor. auto.
Qed.

(** ** Semantics of external functions. *)

(** For functions defined outside the program ([EF_external] and [EF_builtin]),
  we do not define their semantics, but only assume that it satisfies
  [extcall_properties]. *)

Parameter external_functions_sem: ident -> signature -> extcall_sem.

Axiom external_functions_properties:
  forall id sg, extcall_properties (external_functions_sem id sg) sg nil.

(** We treat inline assembly similarly. *)

Parameter inline_assembly_sem: ident -> signature -> extcall_sem.

Axiom inline_assembly_properties:
  forall id sg, extcall_properties (inline_assembly_sem id sg) sg nil.

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

Definition external_call (ef: external_function): extcall_sem :=
  match ef with
  | EF_external name sg  => external_functions_sem name sg
  | EF_builtin name sg   => external_functions_sem name sg
  | EF_vload chunk       => volatile_load_sem chunk
  | EF_vstore chunk      => volatile_store_sem chunk
  | EF_vload_global chunk id ofs => volatile_load_global_sem chunk id ofs
  | EF_vstore_global chunk id ofs => volatile_store_global_sem chunk id ofs
  | EF_malloc            => extcall_malloc_sem 
  | EF_free              => extcall_free_sem
  | EF_memcpy sz al      => extcall_memcpy_sem sz al
  | EF_annot txt targs   => extcall_annot_sem txt targs
  | EF_annot_val txt targ => extcall_annot_val_sem txt targ
  | EF_inline_asm txt sg clb => inline_assembly_sem txt sg
  end.

Theorem external_call_spec:
  forall ef, 
  extcall_properties (external_call ef) (ef_sig ef) (globals_external ef).
Proof.
  intros. unfold external_call, ef_sig, globals_external; destruct ef.
  apply external_functions_properties.
  apply external_functions_properties.
  apply volatile_load_ok.
  apply volatile_store_ok.
  apply volatile_load_global_ok.
  apply volatile_store_global_ok.
  apply extcall_malloc_ok.
  apply extcall_free_ok.
  apply extcall_memcpy_ok.
  apply extcall_annot_ok.
  apply extcall_annot_val_ok.
  apply inline_assembly_properties.
Qed.

Definition external_call_well_typed ef := ec_well_typed (external_call_spec ef).
Definition external_call_symbols_preserved_gen ef := ec_symbols_preserved (external_call_spec ef).
Definition external_call_valid_block ef := ec_valid_block (external_call_spec ef).
Definition external_call_max_perm ef := ec_max_perm (external_call_spec ef).
Definition external_call_readonly ef := ec_readonly (external_call_spec ef).
Definition external_call_mem_extends ef := ec_mem_extends (external_call_spec ef).
Definition external_call_mem_inject_gen ef := ec_mem_inject (external_call_spec ef).
Definition external_call_trace_length ef := ec_trace_length (external_call_spec ef).
Definition external_call_receptive ef := ec_receptive (external_call_spec ef).
Definition external_call_determ ef := ec_determ (external_call_spec ef).

(** Special cases of [external_call_symbols_preserved_gen]. *)

Lemma external_call_symbols_preserved:
  forall ef F1 F2 V (ge1: Genv.t F1 V) (ge2: Genv.t F2 V) vargs m1 t vres m2,
  external_call ef ge1 vargs m1 t vres m2 ->
  (forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id) ->
  (forall id, Genv.public_symbol ge2 id = Genv.public_symbol ge1 id) ->
  (forall b, Genv.find_var_info ge2 b = Genv.find_var_info ge1 b) ->
  external_call ef ge2 vargs m1 t vres m2.
Proof.
  intros. apply external_call_symbols_preserved_gen with (ge1 := ge1); auto.
  intros. simpl. unfold Genv.block_is_volatile. rewrite H2. auto.
Qed.

(** Corollary of [external_call_valid_block]. *)

Lemma external_call_nextblock:
  forall ef ge vargs m1 t vres m2,
  external_call ef ge vargs m1 t vres m2 ->
  Ple (Mem.nextblock m1) (Mem.nextblock m2).
Proof.
  intros. destruct (plt (Mem.nextblock m2) (Mem.nextblock m1)).
  exploit external_call_valid_block; eauto. intros.
  eelim Plt_strict; eauto.
  unfold Plt, Ple in *; zify; omega.
Qed.

(** Special case of [external_call_mem_inject_gen] (for backward compatibility) *)

Definition meminj_preserves_globals (F V: Type) (ge: Genv.t F V) (f: block -> option (block * Z)) : Prop :=
     (forall id b, Genv.find_symbol ge id = Some b -> f b = Some(b, 0))
  /\ (forall b gv, Genv.find_var_info ge b = Some gv -> f b = Some(b, 0))
  /\ (forall b1 b2 delta gv, Genv.find_var_info ge b2 = Some gv -> f b1 = Some(b2, delta) -> b2 = b1).

Lemma external_call_mem_inject:
  forall ef F V (ge: Genv.t F V) vargs m1 t vres m2 f m1' vargs',
  meminj_preserves_globals ge f ->
  external_call ef ge vargs m1 t vres m2 ->
  Mem.inject f m1 m1' ->
  Val.inject_list f vargs vargs' ->
  exists f', exists vres', exists m2',
     external_call ef ge vargs' m1' t vres' m2'
    /\ Val.inject f' vres vres'
    /\ Mem.inject f' m2 m2'
    /\ Mem.unchanged_on (loc_unmapped f) m1 m2
    /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'
    /\ inject_incr f f'
    /\ inject_separated f f' m1 m1'.
Proof.
  intros. destruct H as (A & B & C). eapply external_call_mem_inject_gen with (ge1 := ge); eauto. 
- repeat split; intros.
  + simpl in H3. exploit A; eauto. intros EQ; rewrite EQ in H; inv H. auto.
  + simpl in H3. exploit A; eauto. intros EQ; rewrite EQ in H; inv H. auto.
  + simpl in H3. exists b1; split; eauto.
  + simpl; unfold Genv.block_is_volatile.
    destruct (Genv.find_var_info ge b1) as [gv1|] eqn:V1.
    * exploit B; eauto. intros EQ; rewrite EQ in H; inv H. rewrite V1; auto.
    * destruct (Genv.find_var_info ge b2) as [gv2|] eqn:V2; auto.
      exploit C; eauto. intros EQ; subst b2. congruence.
- intros. exists b1; split; auto. apply A with id; auto. 
Qed.

(** Corollaries of [external_call_determ]. *)

Lemma external_call_match_traces:
  forall ef ge vargs m t1 vres1 m1 t2 vres2 m2,
  external_call ef ge vargs m t1 vres1 m1 ->
  external_call ef ge vargs m t2 vres2 m2 ->
  match_traces ge t1 t2.
Proof.
  intros. exploit external_call_determ. eexact H. eexact H0. tauto.
Qed.

Lemma external_call_deterministic:
  forall ef ge vargs m t vres1 m1 vres2 m2,
  external_call ef ge vargs m t vres1 m1 ->
  external_call ef ge vargs m t vres2 m2 ->
  vres1 = vres2 /\ m1 = m2.
Proof.
  intros. exploit external_call_determ. eexact H. eexact H0. intuition.
Qed.

(** Late in the back-end, calling conventions for external calls change:
  arguments and results of type [Tlong] are passed as two integers.
  We now wrap [external_call] to adapt to this convention. *)

Fixpoint decode_longs (tyl: list typ) (vl: list val) : list val :=
  match tyl with
  | nil => nil
  | Tlong :: tys =>
      match vl with
      | v1 :: v2 :: vs => Val.longofwords v1 v2 :: decode_longs tys vs
      | _ => nil
      end
  | ty :: tys =>
      match vl with
      | v1 :: vs => v1 :: decode_longs tys vs
      | _ => nil
      end
  end.

Definition encode_long (oty: option typ) (v: val) : list val :=
  match oty with
  | Some Tlong => Val.hiword v :: Val.loword v :: nil
  | _ => v :: nil
  end.

Definition proj_sig_res' (s: signature) : list typ :=
  match s.(sig_res) with
  | Some Tlong => Tint :: Tint :: nil
  | Some ty => ty :: nil
  | None => Tint :: nil
  end.

Inductive external_call'
      (ef: external_function) (ge: Senv.t)
      (vargs: list val) (m1: mem) (t: trace) (vres: list val) (m2: mem) : Prop :=
  external_call'_intro: forall v,
    external_call ef ge (decode_longs (sig_args (ef_sig ef)) vargs) m1 t v m2 ->
    vres = encode_long (sig_res (ef_sig ef)) v ->
    external_call' ef ge vargs m1 t vres m2.

Lemma decode_longs_lessdef:
  forall tyl vl1 vl2, Val.lessdef_list vl1 vl2 -> Val.lessdef_list (decode_longs tyl vl1) (decode_longs tyl vl2).
Proof.
  induction tyl; simpl; intros. 
  auto.
  destruct a; inv H; auto. inv H1; auto. constructor; auto. apply Val.longofwords_lessdef; auto. 
Qed.

Lemma decode_longs_inject:
  forall f tyl vl1 vl2, Val.inject_list f vl1 vl2 -> Val.inject_list f (decode_longs tyl vl1) (decode_longs tyl vl2).
Proof.
  induction tyl; simpl; intros. 
  auto.
  destruct a; inv H; auto. inv H1; auto. constructor; auto. apply Val.longofwords_inject; auto. 
Qed.

Lemma encode_long_lessdef:
  forall oty v1 v2, Val.lessdef v1 v2 -> Val.lessdef_list (encode_long oty v1) (encode_long oty v2).
Proof.
  intros. destruct oty as [[]|]; simpl; auto. 
  constructor. apply Val.hiword_lessdef; auto. constructor. apply Val.loword_lessdef; auto. auto.
Qed.

Lemma encode_long_inject:
  forall f oty v1 v2, Val.inject f v1 v2 -> Val.inject_list f (encode_long oty v1) (encode_long oty v2).
Proof.
  intros. destruct oty as [[]|]; simpl; auto. 
  constructor. apply Val.hiword_inject; auto. constructor. apply Val.loword_inject; auto. auto.
Qed.

Lemma encode_long_has_type:
  forall v sg,
  Val.has_type v (proj_sig_res sg) ->
  Val.has_type_list (encode_long (sig_res sg) v) (proj_sig_res' sg).
Proof.
  unfold proj_sig_res, proj_sig_res', encode_long; intros.
  destruct (sig_res sg) as [[] | ]; simpl; auto.
  destruct v; simpl; auto.
Qed.

Lemma external_call_well_typed':
  forall ef ge vargs m1 t vres m2,
  external_call' ef ge vargs m1 t vres m2 ->
  Val.has_type_list vres (proj_sig_res' (ef_sig ef)).
Proof.
  intros. inv H. apply encode_long_has_type. 
  eapply external_call_well_typed; eauto. 
Qed.

Lemma external_call_symbols_preserved':
  forall ef F1 F2 V (ge1: Genv.t F1 V) (ge2: Genv.t F2 V) vargs m1 t vres m2,
  external_call' ef ge1 vargs m1 t vres m2 ->
  (forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id) ->
  (forall id, Genv.public_symbol ge2 id = Genv.public_symbol ge1 id) ->
  (forall b, Genv.find_var_info ge2 b = Genv.find_var_info ge1 b) ->
  external_call' ef ge2 vargs m1 t vres m2.
Proof.
  intros. inv H. exists v; auto. eapply external_call_symbols_preserved; eauto.
Qed.

Lemma external_call_valid_block':
  forall ef ge vargs m1 t vres m2 b,
  external_call' ef ge vargs m1 t vres m2 ->
  Mem.valid_block m1 b -> Mem.valid_block m2 b.
Proof.
  intros. inv H. eapply external_call_valid_block; eauto.
Qed.

Lemma external_call_nextblock':
  forall ef ge vargs m1 t vres m2,
  external_call' ef ge vargs m1 t vres m2 ->
  Ple (Mem.nextblock m1) (Mem.nextblock m2).
Proof.
  intros. inv H. eapply external_call_nextblock; eauto.
Qed.

Lemma external_call_mem_extends':
  forall ef ge vargs m1 t vres m2 m1' vargs',
  external_call' ef ge vargs m1 t vres m2 ->
  Mem.extends m1 m1' ->
  Val.lessdef_list vargs vargs' ->
  exists vres' m2',
     external_call' ef ge vargs' m1' t vres' m2'
  /\ Val.lessdef_list vres vres'
  /\ Mem.extends m2 m2'
  /\ Mem.unchanged_on (loc_out_of_bounds m1) m1' m2'.
Proof.
  intros. inv H. 
  exploit external_call_mem_extends; eauto.
  eapply decode_longs_lessdef; eauto. 
  intros (v' & m2' & A & B & C & D).
  exists (encode_long (sig_res (ef_sig ef)) v'); exists m2'; intuition.
  econstructor; eauto.
  eapply encode_long_lessdef; eauto.
Qed.

Lemma external_call_mem_inject':
  forall ef F V (ge: Genv.t F V) vargs m1 t vres m2 f m1' vargs',
  meminj_preserves_globals ge f ->
  external_call' ef ge vargs m1 t vres m2 ->
  Mem.inject f m1 m1' ->
  Val.inject_list f vargs vargs' ->
  exists f' vres' m2',
     external_call' ef ge vargs' m1' t vres' m2'
  /\ Val.inject_list f' vres vres'
  /\ Mem.inject f' m2 m2'
  /\ Mem.unchanged_on (loc_unmapped f) m1 m2
  /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'
  /\ inject_incr f f'
  /\ inject_separated f f' m1 m1'.
Proof.
  intros. inv H0. 
  exploit external_call_mem_inject; eauto.
  eapply decode_longs_inject; eauto.
  intros (f' & v' & m2' & A & B & C & D & E & P & Q).
  exists f'; exists (encode_long (sig_res (ef_sig ef)) v'); exists m2'; intuition.
  econstructor; eauto.
  apply encode_long_inject; auto.
Qed.

Lemma external_call_determ':
  forall ef ge vargs m t1 vres1 m1 t2 vres2 m2,
  external_call' ef ge vargs m t1 vres1 m1 ->
  external_call' ef ge vargs m t2 vres2 m2 ->
  match_traces ge t1 t2 /\ (t1 = t2 -> vres1 = vres2 /\ m1 = m2).
Proof.
  intros. inv H; inv H0. exploit external_call_determ. eexact H1. eexact H. 
  intros [A B]. split. auto. intros. destruct B as [C D]; auto. subst. auto. 
Qed.

Lemma external_call_match_traces':
  forall ef ge vargs m t1 vres1 m1 t2 vres2 m2,
  external_call' ef ge vargs m t1 vres1 m1 ->
  external_call' ef ge vargs m t2 vres2 m2 ->
  match_traces ge t1 t2.
Proof.
  intros. inv H; inv H0. eapply external_call_match_traces; eauto.
Qed.

Lemma external_call_deterministic':
  forall ef ge vargs m t vres1 m1 vres2 m2,
  external_call' ef ge vargs m t vres1 m1 ->
  external_call' ef ge vargs m t vres2 m2 ->
  vres1 = vres2 /\ m1 = m2.
Proof.
  intros. inv H; inv H0. 
  exploit external_call_deterministic. eexact H1. eexact H. intros [A B].
  split; congruence.
Qed.

(** * Evaluation of annotation arguments *)

Section EVAL_ANNOT_ARG.

Variable A: Type.
Variable ge: Senv.t.
Variable e: A -> val.
Variable sp: val.
Variable m: mem.

Inductive eval_annot_arg: annot_arg A -> val -> Prop :=
  | eval_AA_base: forall x,
      eval_annot_arg (AA_base x) (e x)
  | eval_AA_int: forall n,
      eval_annot_arg (AA_int n) (Vint n)
  | eval_AA_long: forall n,
      eval_annot_arg (AA_long n) (Vlong n)
  | eval_AA_float: forall n,
      eval_annot_arg (AA_float n) (Vfloat n)
  | eval_AA_single: forall n,
      eval_annot_arg (AA_single n) (Vsingle n)
  | eval_AA_loadstack: forall chunk ofs v,
      Mem.loadv chunk m (Val.add sp (Vint ofs)) = Some v ->
      eval_annot_arg (AA_loadstack chunk ofs) v
  | eval_AA_addrstack: forall ofs,
      eval_annot_arg (AA_addrstack ofs) (Val.add sp (Vint ofs))
  | eval_AA_loadglobal: forall chunk id ofs v,
      Mem.loadv chunk m (Senv.symbol_address ge id ofs) = Some v ->
      eval_annot_arg (AA_loadglobal chunk id ofs) v
  | eval_AA_addrglobal: forall id ofs,
      eval_annot_arg (AA_addrglobal id ofs) (Senv.symbol_address ge id ofs)
  | eval_AA_longofwords: forall hi lo vhi vlo,
      eval_annot_arg hi vhi -> eval_annot_arg lo vlo ->
      eval_annot_arg (AA_longofwords hi lo) (Val.longofwords vhi vlo).

Definition eval_annot_args (al: list (annot_arg A)) (vl: list val) : Prop :=
  list_forall2 eval_annot_arg al vl.

Lemma eval_annot_arg_determ:
  forall a v, eval_annot_arg a v -> forall v', eval_annot_arg a v' -> v' = v.
Proof.
  induction 1; intros v' EV; inv EV; try congruence.
  f_equal; eauto.
Qed.

Lemma eval_annot_args_determ:
  forall al vl, eval_annot_args al vl -> forall vl', eval_annot_args al vl' -> vl' = vl.
Proof.
  induction 1; intros v' EV; inv EV; f_equal; eauto using eval_annot_arg_determ.
Qed.

End EVAL_ANNOT_ARG.

Hint Constructors eval_annot_arg: aarg.

(** Invariance by change of global environment. *)

Section EVAL_ANNOT_ARG_PRESERVED.

Variables A F1 V1 F2 V2: Type.
Variable ge1: Genv.t F1 V1.
Variable ge2: Genv.t F2 V2.
Variable e: A -> val.
Variable sp: val.
Variable m: mem.

Hypothesis symbols_preserved:
  forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.

Lemma eval_annot_arg_preserved:
  forall a v, eval_annot_arg ge1 e sp m a v -> eval_annot_arg ge2 e sp m a v.
Proof.
  assert (EQ: forall id ofs, Senv.symbol_address ge2 id ofs = Senv.symbol_address ge1 id ofs).
  { unfold Senv.symbol_address; simpl; intros. rewrite symbols_preserved; auto. }
  induction 1; eauto with aarg. rewrite <- EQ in H; eauto with aarg. rewrite <- EQ; eauto with aarg. 
Qed. 

Lemma eval_annot_args_preserved:
  forall al vl, eval_annot_args ge1 e sp m al vl -> eval_annot_args ge2 e sp m al vl.
Proof.
  induction 1; constructor; auto; eapply eval_annot_arg_preserved; eauto. 
Qed.

End EVAL_ANNOT_ARG_PRESERVED.

(** Compatibility with the "is less defined than" relation. *)

Section EVAL_ANNOT_ARG_LESSDEF.

Variable A: Type.
Variable ge: Senv.t.
Variables e1 e2: A -> val.
Variable sp: val.
Variables m1 m2: mem.

Hypothesis env_lessdef: forall x, Val.lessdef (e1 x) (e2 x).
Hypothesis mem_extends: Mem.extends m1 m2.

Lemma eval_annot_arg_lessdef:
  forall a v1, eval_annot_arg ge e1 sp m1 a v1 ->
  exists v2, eval_annot_arg ge e2 sp m2 a v2 /\ Val.lessdef v1 v2.
Proof.
  induction 1.
- exists (e2 x); auto with aarg.
- econstructor; eauto with aarg.
- econstructor; eauto with aarg.
- econstructor; eauto with aarg.
- econstructor; eauto with aarg.
- exploit Mem.loadv_extends; eauto. intros (v' & P & Q). exists v'; eauto with aarg. 
- econstructor; eauto with aarg.
- exploit Mem.loadv_extends; eauto. intros (v' & P & Q). exists v'; eauto with aarg.
- econstructor; eauto with aarg.
- destruct IHeval_annot_arg1 as (vhi' & P & Q).
  destruct IHeval_annot_arg2 as (vlo' & R & S).
  econstructor; split; eauto with aarg. apply Val.longofwords_lessdef; auto. 
Qed.

Lemma eval_annot_args_lessdef:
  forall al vl1, eval_annot_args ge e1 sp m1 al vl1 ->
  exists vl2, eval_annot_args ge e2 sp m2 al vl2 /\ Val.lessdef_list vl1 vl2.
Proof.
  induction 1.
- econstructor; split. constructor. auto.
- exploit eval_annot_arg_lessdef; eauto. intros (v1' & P & Q). 
  destruct IHlist_forall2 as (vl' & U & V).
  exists (v1'::vl'); split; constructor; auto.
Qed.

End EVAL_ANNOT_ARG_LESSDEF.

