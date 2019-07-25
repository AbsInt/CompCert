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

Require Import String.
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
  | EVptr_global: ident -> ptrofs -> eventval.


(*
  Delta Permission Maps:
  A change in memory permissions.
  - They have the same shape as the memories
  - they return [None], if the permission doesn't change at that location
  - return [Some perm], if the new permission is [perm].
*)
Notation delta_perm_map := (Maps.PTree.t (Z -> option (option permission))).
Inductive inject_Z_map {A} (delt: Z) (f1 f2: (Z -> A)): Prop:=
| InjectZ: (forall ofs x, f1 ofs = x ->
                     f2 (ofs+ delt) = x) ->
           inject_Z_map delt f1 f2.
    
                            
Record inject_delta_map (mu: meminj)(dpm1 dpm2: delta_perm_map): Prop:=
  { DPM_image: forall b1 b2 delt f1,
      mu b1 = Some (b2, delt) ->
      (Maps.PTree.get b1 dpm1) = Some f1 ->
      exists f2, Maps.PTree.get b2 dpm2 = Some f2 /\
            inject_Z_map delt f1 f2
    ;DPM_preimage:
       forall b2 ofs2 f2 p,
         Maps.PTree.get b2 dpm2 = Some f2 ->
         f2 ofs2 = p ->
         exists b1 f1 ofs1 delt,
           mu b1 = Some(b2, delt) /\
           Maps.PTree.get b1 dpm1 = Some f1 /\
           f1 ofs1 = p /\
           ofs2 = ofs1 + delt
  }.

(* New memory events:
   * These events are injectable
   * They can indicate changes to memory with an mem_effect
   * or changes to permissions with a delta_map.
   NOTE: alloc records the new block. This helps on injections.
*)
Inductive mem_effect :=
  Write : forall (b : block) (ofs : Z) (bytes : list memval), mem_effect
| Alloc: forall (b : block)(lo hi:Z), mem_effect
| Free: forall (l: list (block * Z * Z)), mem_effect.

Inductive list_map_rel {A B} (r:A-> B -> Prop): list A -> list B-> Prop:=
| list_rel_nil:
    list_map_rel r nil nil
| list_rel_cons: forall a b l1 l2,
                   r a b ->
                   list_map_rel r (l1) (l2)->
                   list_map_rel r (a::l1) (b::l2).

Inductive inject_strong (mi : meminj) : val -> val -> Prop :=
    inject_int : forall i : int, inject_strong mi (Vint i) (Vint i)
  | inject_long : forall i : int64, inject_strong mi (Vlong i) (Vlong i)
  | inject_float : forall f : float, inject_strong mi (Vfloat f) (Vfloat f)
  | inject_single : forall f : float32, inject_strong mi (Vsingle f) (Vsingle f)
  | inject_ptr : forall (b1 : block) (ofs1 : ptrofs) (b2 : block) (ofs2 : ptrofs) (delta : Z),
                 mi b1 = Some (b2, delta) ->
                 ofs2 = Ptrofs.add ofs1 (Ptrofs.repr delta) ->
                 inject_strong mi (Vptr b1 ofs1) (Vptr b2 ofs2)
  | val_inject_undef : inject_strong mi Vundef Vundef.
Inductive memval_inject_strong (f : meminj) : memval -> memval -> Prop :=
    memval_inject_byte_str : forall n : byte, memval_inject_strong f (Byte n) (Byte n)
  | memval_inject_frag_str : forall (v1 v2 : val) (q : quantity) (n : nat),
                         inject_strong f v1 v2 ->
                         memval_inject_strong f (Fragment v1 q n) (Fragment v2 q n)
  | memval_inject_undef_str : memval_inject_strong f Undef Undef.
                                              
Definition list_memval_inject mu:= list_map_rel (memval_inject mu).
Definition list_memval_inject_strong mu:= list_map_rel (memval_inject_strong mu).

Inductive inject_hi_low (mu:meminj): (block * Z * Z) -> (block * Z * Z) -> Prop:=
| HiLow: forall b1 b2 hi low delt,
    mu b1 = Some(b2, delt) ->
    inject_hi_low mu (b1, hi, low) (b2, hi+delt, low+delt).
Definition list_inject_hi_low mu := list_map_rel (inject_hi_low mu).
  
Inductive inject_mem_effect (mu: meminj): mem_effect -> mem_effect -> Prop :=
| InjectWrites: forall b1 b2 ofs1 delt vals1 vals2,
    mu b1 = Some (b2, delt) ->
    list_memval_inject mu vals1 vals2 ->
    inject_mem_effect mu (Write b1 ofs1 vals1) (Write b2 (ofs1 + delt) vals2)
| InjectAlloc: forall lo hi b1 b2,
    mu b1 = Some (b2, 0) ->
    inject_mem_effect mu (Alloc b1 hi lo) (Alloc b2 hi lo)
| InjectFree: forall l1 l2,
    list_inject_hi_low mu l1 l2 ->
    inject_mem_effect mu (Free l1) (Free l2).
Definition list_inject_mem_effect (mu:meminj):= list_map_rel (inject_mem_effect mu).

Inductive inject_mem_effect_strong (mu: meminj): mem_effect -> mem_effect -> Prop :=
| InjectWritesStrong: forall b1 b2 ofs1 delt vals1 vals2,
    mu b1 = Some (b2, delt) ->
    list_memval_inject_strong mu vals1 vals2 ->
    inject_mem_effect_strong mu (Write b1 ofs1 vals1) (Write b2 (ofs1 + delt) vals2)
| InjectAllocStrong:forall lo hi b1 b2,
    mu b1 = Some (b2, 0) ->
    inject_mem_effect_strong mu (Alloc b1 hi lo) (Alloc b2 hi lo)
| InjectFreeStrong: forall l1 l2,
    list_inject_hi_low mu l1 l2 ->
    inject_mem_effect_strong mu (Free l1) (Free l2).
Definition list_inject_mem_effect_strong (mu:meminj):= list_map_rel (inject_mem_effect_strong mu).


Inductive event: Type :=
  | Event_syscall: string -> list eventval -> eventval -> event
  | Event_vload: memory_chunk -> ident -> ptrofs -> eventval -> event
  | Event_vstore: memory_chunk -> ident -> ptrofs -> eventval -> event
  | Event_annot: string -> list eventval -> event
  | Event_acq_rel: list mem_effect -> delta_perm_map -> list mem_effect -> event
  | Event_spawn: block -> delta_perm_map -> delta_perm_map -> event.

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
      eventval_match (EVptr_global id ofs) Tptr (Vptr b ofs).

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
  intros. inv H; simpl; auto. unfold Tptr; destruct Archi.ptr64; auto.
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
  | EVptr_global id ofs => Tptr
  end.

Lemma eventval_match_receptive:
  forall ev1 ty v1 ev2,
  eventval_match ev1 ty v1 ->
  eventval_valid ev1 -> eventval_valid ev2 -> eventval_type ev1 = eventval_type ev2 ->
  exists v2, eventval_match ev2 ty v2.
Proof.
  intros. unfold eventval_type, Tptr in H2. remember Archi.ptr64 as ptr64.
  inversion H; subst ev1 ty v1; clear H; destruct ev2; simpl in H2; inv H2.
- exists (Vint i0); constructor.
- simpl in H1; exploit Senv.public_symbol_exists; eauto. intros [b FS].
  exists (Vptr b i1); rewrite H3. constructor; auto.
- exists (Vlong i0); constructor.
- simpl in H1; exploit Senv.public_symbol_exists; eauto. intros [b FS].
  exists (Vptr b i1); rewrite H3; constructor; auto.
- exists (Vfloat f0); constructor.
- destruct Archi.ptr64; discriminate.
- exists (Vsingle f0); constructor; auto.
- destruct Archi.ptr64; discriminate.
- exists (Vint i); unfold Tptr; rewrite H5; constructor.
- exists (Vlong i); unfold Tptr; rewrite H5; constructor.
- destruct Archi.ptr64; discriminate.
- destruct Archi.ptr64; discriminate.
- exploit Senv.public_symbol_exists. eexact H1. intros [b' FS].
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
  rewrite Ptrofs.add_zero. constructor; auto. rewrite A; auto.
Qed.

Lemma eventval_match_inject_2:
  forall ev ty v1,
  eventval_match ge1 ev ty v1 ->
  exists v2, eventval_match ge2 ev ty v2 /\ Val.inject f v1 v2.
Proof.
  intros. inv H; try (econstructor; split; eauto; constructor; fail).
  destruct symb_inj as (A & B & C & D). exploit C; eauto. intros [b2 [EQ FS]].
  exists (Vptr b2 ofs); split. econstructor; eauto.
  econstructor; eauto. rewrite Ptrofs.add_zero; auto.
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
  | _ => False
  end.

Fixpoint output_trace (t: trace) : Prop :=
  match t with
  | nil => True
  | ev :: t' => output_event ev /\ output_trace t'
  end.

(** * Semantics of volatile memory accesses *)

Inductive volatile_load (ge: Senv.t):
                   memory_chunk -> mem -> block -> ptrofs -> trace -> val -> Prop :=
  | volatile_load_vol: forall chunk m b ofs id ev v,
      Senv.block_is_volatile ge b = true ->
      Senv.find_symbol ge id = Some b ->
      eventval_match ge ev (type_of_chunk chunk) v ->
      volatile_load ge chunk m b ofs
                      (Event_vload chunk id ofs ev :: nil)
                      (Val.load_result chunk v)
  | volatile_load_nonvol: forall chunk m b ofs v,
      Senv.block_is_volatile ge b = false ->
      Mem.load chunk m b (Ptrofs.unsigned ofs) = Some v ->
      volatile_load ge chunk m b ofs E0 v.

Inductive volatile_store (ge: Senv.t):
                  memory_chunk -> mem -> block -> ptrofs -> val -> trace -> mem -> Prop :=
  | volatile_store_vol: forall chunk m b ofs id ev v,
      Senv.block_is_volatile ge b = true ->
      Senv.find_symbol ge id = Some b ->
      eventval_match ge ev (type_of_chunk chunk) (Val.load_result chunk v) ->
      volatile_store ge chunk m b ofs v
                      (Event_vstore chunk id ofs ev :: nil)
                      m
  | volatile_store_nonvol: forall chunk m b ofs v m',
      Senv.block_is_volatile ge b = false ->
      Mem.store chunk m b (Ptrofs.unsigned ofs) v = Some m' ->
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

Inductive inject_event: meminj -> event -> event -> Prop :=
  | INJ_syscall: forall f s t v, inject_event f (Event_syscall s t v) (Event_syscall s t v)
  | INJ_vload : forall f mc id n v, inject_event f (Event_vload mc id n v) (Event_vload mc id n v)
  | INJ_vstore : forall f mc id n v, inject_event f (Event_vstore mc id n v) (Event_vstore mc id n v)
  | INJ_annot : forall f st t, inject_event f (Event_annot st t) (Event_annot st t)
  | INJ_acq : forall f ls1 ls2 ls1' ls2' dpm1 dpm2,
      list_inject_mem_effect f ls1 ls2 ->
      inject_delta_map f dpm1 dpm2 ->
      list_inject_mem_effect f ls1' ls2' ->
      inject_event f (Event_acq_rel ls1 dpm1 ls1') (Event_acq_rel ls2 dpm2 ls2')
  | INJ_spawn : forall f b1 dm1 dm2 b2 delt dm1' dm2',
      f b1 = Some (b2, delt) ->
      inject_delta_map f dm1 dm1' ->
      inject_delta_map f dm2 dm2' ->
      inject_event f (Event_spawn b1 dm1 dm2) (Event_spawn b2 dm1' dm2').
Ltac trivial_inject_event:=
  match goal with
  | [H: inject_event ?f ?e ?e' |- _ ] =>
    inversion H; subst; clear H
  end.

Inductive inject_event_strong: meminj -> event -> event -> Prop :=
| INJ_syscall_strong:
    forall f s t v, inject_event_strong f (Event_syscall s t v) (Event_syscall s t v)
| INJ_vload_strong :
    forall f mc id n v, inject_event_strong f (Event_vload mc id n v) (Event_vload mc id n v)
| INJ_vstore_strong :
    forall f mc id n v, inject_event_strong f (Event_vstore mc id n v) (Event_vstore mc id n v)
  | INJ_annot_strong : forall f st t, inject_event_strong f (Event_annot st t) (Event_annot st t)
  | INJ_acq_strong : forall f ls1 ls2 ls1' ls2' dpm1 dpm2,
      list_inject_mem_effect_strong f ls1 ls2 ->
      inject_delta_map f dpm1 dpm2 ->
      list_inject_mem_effect_strong f ls1' ls2' ->
      inject_event_strong f (Event_acq_rel ls1 dpm1 ls1') (Event_acq_rel ls2 dpm2 ls2')
  | INJ_spawn_strong : forall f b1 dm1 dm2 b2 delt dm1' dm2',
      f b1 = Some (b2, delt) ->
      inject_delta_map f dm1 dm1' ->
      inject_delta_map f dm2 dm2' ->
      inject_event_strong f (Event_spawn b1 dm1 dm2) (Event_spawn b2 dm1' dm2').

Definition inject_trace mu:= list_map_rel (inject_event mu). 
Definition inject_trace_strong mu:= list_map_rel (inject_event_strong mu).

Section StrongRelaxedInjections.

Lemma val_inject_strong_compose:
  forall j12 j23 v1 v2 v3,
    inject_strong j12 v1 v2 ->
    Val.inject j23 v2 v3 ->
    Val.inject (compose_meminj j12 j23) v1 v3.
Proof.
  
  Ltac composition_arithmetic:=
    (* Solves the Ptrofs.add... goal that results from 
       injecting a pointer twice: the offsets are added 
       in two different ways
     *)
    rewrite Ptrofs.add_assoc; decEq;
    unfold Ptrofs.add; apply Ptrofs.eqm_samerepr; auto with ints.
  Ltac composed_injections_injection_case j12 j23:=
    match goal with
    |[ H12: j12 _ = Some _, H23: j23 _ = Some _ |-
       context[compose_meminj j12 j23]
     ] =>
     econstructor;
     try (unfold compose_meminj; rewrite H12; rewrite H23); eauto;
     try composition_arithmetic
    end.
  Ltac composed_injections:=
     match goal with
     |[|- forall j12 j23 _ _ _, _ -> _ -> ?R (compose_meminj j12 j23) _ _] =>
      
     let H1:= fresh "H1" in
      let H2:= fresh "H2" in 
      intros ????? H1 H2; inv H1;
      auto; inv H2; auto;
      try solve[econstructor; auto];
      try composed_injections_injection_case j12 j23
     | _ => fail "Not the shape expected"
     end.
  composed_injections.
  
Qed.

Lemma val_inject_strong_compose':
  forall j12 j23 v1 v2 v3,
    inject_strong j23 v2 v3 ->
    Val.inject j12 v1 v2 ->
    Val.inject (compose_meminj j12 j23) v1 v3.
Proof. composed_injections. Qed.

Lemma val_inject_strong_interpolation:
  forall j12 j23 v1 v3,
    Val.inject (compose_meminj j12 j23) v1 v3 ->
    exists v2,
    inject_strong j12 v1 v2 /\ Val.inject j23 v2 v3.
Proof.
  intros.
  inv H; try solve[ eexists; split; econstructor].
  - (* ptr *)
    unfold compose_meminj in H0.
    destruct (j12 b1) as [[??]|] eqn:H12; try congruence.
    destruct (j23 b) as [[??]|] eqn:H23; try congruence.
    inversion H0; subst.
    eexists; split; try econstructor; eauto.
    rewrite Ptrofs.add_assoc. decEq. unfold Ptrofs.add.
    apply Ptrofs.eqm_samerepr. auto with ints.    
Qed.

Lemma list_map_rel_trans:
  forall {A B C},
  forall (R12: A -> B -> Prop)
    (R23: B -> C -> Prop)
    (R13: A -> C -> Prop),
    (forall x1 x2 x3,
        R12 x1 x2 ->
        R23 x2 x3 ->
        R13 x1 x3) ->
    (forall l1 l2 l3,
        list_map_rel R12 l1 l2 ->
        list_map_rel R23 l2 l3 ->
        list_map_rel R13 l1 l3).
Proof.
  intros. revert l3 H1; induction H0; intros.
  - inv H1. constructor.
  - inv H2. constructor.
    + eapply H; eauto.
    + eapply IHlist_map_rel; auto.
Qed.


Lemma inject_hi_low_compose:
  forall (j12 j23 : meminj) (x1 x2 x3 : block * Z * Z),
    inject_hi_low j12 x1 x2 ->
    inject_hi_low j23 x2 x3 -> inject_hi_low (compose_meminj j12 j23) x1 x3.
Proof.
  composed_injections.
  do 2 rewrite Zplus_assoc_reverse.
  econstructor.
  Ltac rewrite_compose_meminj:=
    match goal with
    |[ H12: ?j12 _ = Some _, H23: ?j23 _ = Some _ |-
       context[compose_meminj ?j12 ?j23]
     ] => unfold compose_meminj; rewrite H12, H23
    end.
  rewrite_compose_meminj; reflexivity.
Qed.
Lemma inject_delta_map_compose:
  forall j12 j23 dpm1 dpm2 dpm3,
    inject_delta_map j12 dpm1 dpm2 ->
    inject_delta_map j23 dpm2 dpm3 ->
    inject_delta_map (compose_meminj j12 j23) dpm1 dpm3.
Admitted.
Lemma list_inject_hi_low_compose:
  forall j12 j23 le1 le2 le3,
    list_inject_hi_low j12 le1 le2 ->
    list_inject_hi_low j23 le2 le3 ->
    list_inject_hi_low (compose_meminj j12 j23) le1 le3.
Proof.
  intros ??; eapply list_map_rel_trans.
  apply inject_hi_low_compose.
Qed.
Lemma memval_inject_strong_compose:
  forall (j12 j23 : meminj) (x1 x2 x3 : memval),
    memval_inject_strong j12 x1 x2 ->
    memval_inject j23 x2 x3 -> memval_inject (compose_meminj j12 j23) x1 x3.
Proof.
  composed_injections.
  econstructor; eapply val_inject_strong_compose; eassumption.
Qed.

Lemma list_memval_inject_strong_compose:
  forall j12 j23 vals1 vals2 vals3,
    list_memval_inject_strong j12 vals1 vals2 ->
    list_memval_inject j23 vals2 vals3 ->
    list_memval_inject (compose_meminj j12 j23) vals1 vals3.
Proof.
  intros ??; eapply list_map_rel_trans.
  eapply memval_inject_strong_compose.
Qed.

Lemma inject_mem_effect_strong_compose:
  forall (j12 j23 : meminj) (x1 x2 x3 : mem_effect),
    inject_mem_effect_strong j12 x1 x2 ->
    inject_mem_effect j23 x2 x3 -> inject_mem_effect (compose_meminj j12 j23) x1 x3.
Proof.
  composed_injections.
  - rewrite Zplus_assoc_reverse.
    eapply InjectWrites; auto.
    (unfold compose_meminj; rewrite H; rewrite H6); auto.
    eapply list_memval_inject_strong_compose; eassumption.
  - econstructor.
    eapply list_inject_hi_low_compose; eassumption.
Qed.


Lemma list_inject_event_strong_compose:
  forall j12 j23 le1 le2 le3,
    list_inject_mem_effect_strong j12 le1 le2 ->
    list_inject_mem_effect j23 le2 le3 ->
    list_inject_mem_effect (compose_meminj j12 j23) le1 le3.
Proof.
  intros ??; eapply list_map_rel_trans.
  eapply inject_mem_effect_strong_compose.
Qed.

Lemma inject_event_strong_compose:
  forall j12 j23 v1 v2 v3,
    inject_event_strong j12 v1 v2 ->
    inject_event j23 v2 v3 ->
    inject_event (compose_meminj j12 j23) v1 v3.
Proof.
  intros. inv H; auto; inv H0; auto; try solve[econstructor].
  -  econstructor.
     + eapply list_inject_event_strong_compose; eassumption.
     + eapply inject_delta_map_compose; eassumption.
     + eapply list_inject_event_strong_compose; eassumption.
  - econstructor; try eassumption.
    + rewrite_compose_meminj; reflexivity.
    + eapply inject_delta_map_compose; eassumption. 
    + eapply inject_delta_map_compose; eassumption.
Qed.

Lemma inject_event_strong_interpolation:
  forall j12 j23 v1 v3,
    inject_event (compose_meminj j12 j23) v1 v3 ->
    exists v2,
      inject_event_strong j12 v1 v2 /\ inject_event j23 v2 v3.
Proof.
  intros.
  inv H; try solve[ eexists; split; econstructor].
Admitted.

Lemma inject_trace_strong_compose:
  forall j12 j23 l1 l2 l3,
    inject_trace_strong j12 l1 l2 ->
    inject_trace j23 l2 l3 ->
    inject_trace (compose_meminj j12 j23) l1 l3.
Proof.
  intros ??; eapply list_map_rel_trans.
  apply inject_event_strong_compose.
Qed.

Lemma list_map_rel_interpolation:
  forall {A B C},
  forall (R12: A -> B -> Prop)
    (R23: B -> C -> Prop)
    (R13: A -> C -> Prop),
    (forall x1 x3, R13 x1 x3 ->
              exists x2, R12 x1 x2 /\
                    R23 x2 x3) ->
    (forall l1 l3, list_map_rel R13 l1 l3 ->
              exists l2, list_map_rel R12 l1 l2 /\
                    list_map_rel R23 l2 l3).
Proof.
  intros.
  induction H0; intros.
  - repeat econstructor.
  - rename l2 into l3.
    destruct (H _ _ H0) as (x2&H12&H23).
    destruct IHlist_map_rel as (l2&HH12&HH23).
    do 3 econstructor; eauto.
Qed.

Lemma inject_trace_strong_interpolation:
  forall j12 j23 v1 v3,
    inject_trace (compose_meminj j12 j23) v1 v3 ->
    exists v2,
      inject_trace_strong j12 v1 v2 /\ inject_trace j23 v2 v3.
Proof.
  intros ??; eapply list_map_rel_interpolation.
  apply inject_event_strong_interpolation.
Qed.

Section DETERMINISM.

  
  Definition deterministic {A B} (R: A -> B -> Prop):=
    forall a b b', R a b -> R a b' -> b = b'.
  Lemma  list_map_rel_determ:
    forall {A B} (R: A -> B -> Prop),
      deterministic R ->
      deterministic (list_map_rel R).
  Proof.
    unfold deterministic;
      intros. revert b' H1.
    induction H0; intros.
    - inv H1; auto.
    - inv H2; f_equal.
      + eapply H; eassumption.
      + eapply IHlist_map_rel; assumption.
  Qed.
  Lemma inject_mem_effect_strong_determ:
    forall (f12 : meminj),
      deterministic (inject_mem_effect_strong f12).
  Proof.
  Admitted.
  Lemma list_inject_mem_effect_strong_determ:
    forall (f12 : meminj),
      deterministic (list_inject_mem_effect_strong f12).
  Proof.
    intros ????; eapply list_map_rel_determ.
    intros ???; eapply inject_mem_effect_strong_determ.
  Qed.
  Lemma inject_delta_map_determ:
    forall (f12 : meminj),
      deterministic (inject_delta_map f12).  
  Admitted.
  Lemma inject_event_strong_determ:
    forall (f12 : meminj),
      deterministic (inject_event_strong f12).
  Proof.
    unfold deterministic; intros.
    inv H; auto; inv H0; auto.
    - (*Event_acq_rel *)
      f_equal.
      + eapply list_inject_mem_effect_strong_determ; eassumption.
      + eapply inject_delta_map_determ; eassumption.
      + eapply list_inject_mem_effect_strong_determ; eassumption.
    - f_equal.
      + rewrite H1 in H7; inversion H7; reflexivity.
      + eapply inject_delta_map_determ; eassumption.
      + eapply inject_delta_map_determ; eassumption.
  Qed.
  Lemma inject_trace_strong_determ:
    forall (f12 : meminj),
      deterministic (inject_trace_strong f12).
  Proof.
    intros ????; eapply list_map_rel_determ.
    eapply inject_event_strong_determ.
  Qed.
End DETERMINISM.

  
End StrongRelaxedInjections.

Definition trivial_inject t:=
  forall f t',
    inject_trace f t t' -> t' = t.
Ltac trivial_inject_trace:=
  match goal with
  | [H: inject_trace ?f ?t ?t' |- _  ] =>
    inversion H; subst; clear H;
    try trivial_inject_event
  end.
Ltac solve_trivial_inject:=
  lazymatch goal with
  | [|- trivial_inject ?T] =>
    match goal with
    |[H:context[T] |- _ ] =>
     intros ???;
            inversion H; subst;
     repeat trivial_inject_trace; reflexivity             
    end
  | _ => fail "Not an noninjectable goal."
  end.

Definition injection_full (f:meminj) (m:mem):=
  forall b ,
    Mem.valid_block m b ->
    ~ f b = None.

Lemma flat_injection_full:
  forall m0, injection_full (Mem.flat_inj (Mem.nextblock m0)) m0.
Proof.
  intros ? ? ? ?.
  unfold Mem.flat_inj in *.
  destruct (plt b (Mem.nextblock m0)); inv H0.
  eapply n; auto.
Qed.

Lemma nextblock_full: forall f m m',
    injection_full f m ->
    Mem.nextblock m' = Mem.nextblock m ->
    injection_full f m'.
Proof. intros ? ? ? H ? ? ?; apply H.
       unfold Mem.valid_block;
         rewrite <- H0; auto.
Qed.
Lemma store_full: forall f chunk m b ofs v m',
    injection_full f m ->
    Mem.store chunk m b ofs v = Some m' ->
    injection_full f m'.
Proof.
  intros. eapply nextblock_full; eauto.
  eapply Mem.nextblock_store; eauto.
Qed.
Lemma storebytes_full: forall f m b ofs ls m',
    injection_full f m ->
    Mem.storebytes m b ofs ls = Some m' ->
    injection_full f m'.
Proof.
  intros. eapply nextblock_full; eauto.
  eapply Mem.nextblock_storebytes; eauto.
Qed.
Lemma free_full: forall f m ls lo hi m',
    injection_full f m ->
    Mem.free m ls lo hi = Some m' ->
    injection_full f m'.
Proof.
  intros. eapply nextblock_full; eauto.
  eapply Mem.nextblock_free; eauto.
Qed.
Lemma free_list_full: forall f ls m m',
    injection_full f m ->
    Mem.free_list m ls = Some m' ->
    injection_full f m'.
Proof.
  induction ls.
  - intros; inv H0; auto.
  - intros. destruct a as [[b lo] hi];
              simpl in H0. 
    destruct (Mem.free m b lo hi) eqn:HH; inv H0.
    eapply IHls in H2; eauto.
    eapply free_full; eauto.
Qed.
Lemma alloc_full m lo hi m' b (ALLOC: Mem.alloc m lo hi = (m',b))
      j1 (FULL : injection_full j1 m) j' sp' z
      (J : j' b = Some (sp', z)) (K : inject_incr j1 j'):
  injection_full j' m'.
Proof. 
  red; intros bb Hbb.
  destruct (Mem.valid_block_alloc_inv _ _ _ _ _ ALLOC _ Hbb).
  * subst. rewrite J; congruence.
  * apply FULL in H. remember (j1 bb) as d; destruct d; [| congruence].
    symmetry in Heqd; destruct p. apply K in Heqd; congruence.
Qed.

Record extcall_properties (sem: extcall_sem) (sg: signature) : Prop :=
  mk_extcall_properties {

      (** The return value of an external call must agree with its signature. *)
      ec_well_typed:
        forall ge vargs m1 t vres m2,
          sem ge vargs m1 t vres m2 ->
          Val.has_type vres (proj_sig_res sg);

      (** The semantics is invariant under change of global environment that preserves symbols. *)
      ec_symbols_preserved:
        forall ge1 ge2 vargs m1 t vres m2,
          Senv.equiv ge1 ge2 ->
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
          sem ge1 vargs m1 t vres m2 ->
          Mem.inject f m1 m1' ->
          injection_full f m1 ->
          Val.inject_list f vargs vargs' ->
          exists f', exists vres', exists m2', exists t',
                  sem ge2 vargs' m1' t' vres' m2'
                  /\ Val.inject f' vres vres'
                  /\ Mem.inject f' m2 m2'
                  /\ Mem.unchanged_on (loc_unmapped f) m1 m2
                  /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'
                  /\ inject_incr f f'
                  /\ inject_separated f f' m1 m1'
                  /\ inject_trace f' t t'
                  /\ injection_full f' m2;
      
      (** External calls must commute with memory injections,
  in the following sense. *)
      ec_mem_inject':
        forall ge1 ge2 vargs m1 t vres m2 f m1' vargs',
          symbols_inject f ge1 ge2 ->
          sem ge1 vargs m1 t vres m2 ->
          Mem.inject f m1 m1' ->
          Val.inject_list f vargs vargs' ->
          exists f', exists vres', exists m2', exists t',
                  sem ge2 vargs' m1' t' vres' m2'
                  /\ Val.inject f' vres vres'
                  /\ Mem.inject f' m2 m2'
                  /\ Mem.unchanged_on (loc_unmapped f) m1 m2
                  /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'
                  /\ inject_incr f f'
                  /\ inject_separated f f' m1 m1'
                  /\ inject_trace f' t t';

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
    Senv.equiv ge1 ge2 ->
    volatile_load ge1 chunk m b ofs t v ->
    volatile_load ge2 chunk m b ofs t v.
Proof.
  intros. destruct H as (A & B & C). inv H0; constructor; auto.
  rewrite C; auto.
  rewrite A; auto.
  eapply eventval_match_preserved; eauto.
  rewrite C; auto.
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
    rewrite Ptrofs.add_zero. exists (Val.load_result chunk v2); split.
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

  
(* Lemma volatile_load_trivial_inject:
  forall {ge chunk m b ofs t vres},
    volatile_load ge chunk m b ofs t vres ->
    trivial_inject t.
Proof. intros; solve_trivial_inject. Qed. *)

Lemma volatile_load_ok:
  forall chunk,
  extcall_properties (volatile_load_sem chunk)
                     (mksignature (Tptr :: nil) (Some (type_of_chunk chunk)) cc_default).
Proof.
  intros; constructor; intros.
(* well typed *)
- unfold proj_sig_res; simpl. inv H. inv H0. apply Val.load_result_type.
  eapply Mem.load_type; eauto.
(* symbols *)
- inv H0. constructor. eapply volatile_load_preserved; eauto.
(* valid blocks *)
- inv H; auto.
(* max perms *)
- inv H; auto.
(* readonly *)
- inv H. apply Mem.unchanged_on_refl.
(* mem extends *)
- inv H. inv H1. inv H6. inv H4.
  exploit volatile_load_extends; eauto. intros [v' [A B]].
  exists v'; exists m1'; intuition. constructor; auto.
(* mem injects *)
- inv H0. inv H3. inv H8. inversion H6; subst.
  exploit volatile_load_inject; eauto. intros [v' [A B]].
  exists f; (*intros.
  rewrite (volatile_load_trivial_inject A H0). *)
  exists v'; exists m1', t;  intuition. constructor; auto.
  red; intros. congruence.
  inversion H4; repeat constructor.
(* mem injects *)
- inv H0. inv H2. inv H7. inversion H5; subst.
  exploit volatile_load_inject; eauto. intros [v' [A B]].
  exists f; exists v'; exists m1'; exists t; intuition. constructor; auto.
  red; intros. congruence.
  inversion H3; repeat constructor.  
(* trace length *)
- inv H; inv H0; simpl; omega.
(* receptive *)
- inv H. exploit volatile_load_receptive; eauto. intros [v2 A].
  exists v2; exists m1; constructor; auto.
(* determ *)
- inv H; inv H0. inv H1; inv H7; try congruence.
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

(** ** Semantics of volatile stores *)

Inductive volatile_store_sem (chunk: memory_chunk) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | volatile_store_sem_intro: forall b ofs m1 v t m2,
      volatile_store ge chunk m1 b ofs v t m2 ->
      volatile_store_sem chunk ge (Vptr b ofs :: v :: nil) m1 t Vundef m2.

Lemma volatile_store_preserved:
  forall ge1 ge2 chunk m1 b ofs v t m2,
  Senv.equiv ge1 ge2 ->
  volatile_store ge1 chunk m1 b ofs v t m2 ->
  volatile_store ge2 chunk m1 b ofs v t m2.
Proof.
  intros. destruct H as (A & B & C). inv H0; constructor; auto.
  rewrite C; auto.
  rewrite A; auto.
  eapply eventval_match_preserved; eauto.
  rewrite C; auto.
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
  rewrite Ptrofs.add_zero. exists m1'; split.
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
  assert (EQ: Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta)) = Ptrofs.unsigned ofs + delta)
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

Lemma volatile_store_full:
  forall f ge chunk m b ofs v t1 m1,
    injection_full f m ->
  volatile_store ge chunk m b ofs v t1 m1 ->
  injection_full f m1.
Proof.
  intros. inv H0; auto.
  eapply store_full; eauto.
Qed.
(*Lemma volatile_store_trivial_inject:
  forall {ge chunk m b ofs v t m'},
    volatile_store ge chunk m b ofs v t m' ->
    trivial_inject t.
Proof. intros; solve_trivial_inject. Qed.*)
Lemma volatile_store_ok:
  forall chunk,
  extcall_properties (volatile_store_sem chunk)
                     (mksignature (Tptr :: type_of_chunk chunk :: nil) None cc_default).
Proof.
  intros; constructor; intros.
(* well typed *)
- unfold proj_sig_res; simpl. inv H; constructor.
(* symbols preserved *)
- inv H0. constructor. eapply volatile_store_preserved; eauto.
(* valid block *)
- inv H. inv H1. auto. eauto with mem.
(* perms *)
- inv H. inv H2. auto. eauto with mem.
(* readonly *)
- inv H. eapply volatile_store_readonly; eauto.
(* mem extends*)
- inv H. inv H1. inv H6. inv H7. inv H4.
  exploit volatile_store_extends; eauto. intros [m2' [A [B C]]].
  exists Vundef; exists m2'; intuition. constructor; auto.
(* mem inject *)
- inv H0. inv H3. inv H8. inv H9. inversion H6; subst.
  exploit volatile_store_inject; eauto. intros [m2' [A [B [C D]]]].
  exists f; exists Vundef; exists m2'; exists t; intuition. constructor; auto. red; intros; congruence.
  inversion A; repeat constructor.
  eapply volatile_store_full; eauto.
(* mem inject *)
- inv H0. inv H2. inv H7. inv H8. inversion H5; subst.
  exploit volatile_store_inject; eauto. intros [m2' [A [B [C D]]]].
  exists f; exists Vundef; exists m2'; exists t; intuition. constructor; auto. red; intros; congruence.
  inversion A; repeat constructor.
(* trace length *)
- inv H; inv H0; simpl; omega.
(* receptive *)
- assert (t1 = t2). inv H. eapply volatile_store_receptive; eauto.
  subst t2; exists vres1; exists m1; auto.
(* determ *)
- inv H; inv H0. inv H1; inv H8; try congruence.
  assert (id = id0) by (eapply Senv.find_symbol_injective; eauto). subst id0.
  assert (ev = ev0) by (eapply eventval_match_determ_2; eauto). subst ev0.
  split. constructor. auto.
  split. constructor. intuition congruence.
Qed.

(** ** Semantics of dynamic memory allocation (malloc) *)

Inductive extcall_malloc_sem (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_malloc_sem_intro: forall sz m m' b m'',
      Mem.alloc m (- size_chunk Mptr) (Ptrofs.unsigned sz) = (m', b) ->
      Mem.store Mptr m' b (- size_chunk Mptr) (Vptrofs sz) = Some m'' ->
      extcall_malloc_sem ge (Vptrofs sz :: nil) m E0 (Vptr b Ptrofs.zero) m''.


Lemma alloc_parallel_inject'
     : forall (f : meminj) (m1 m2 : mem) (lo1 hi1 : Z) (m1' : Mem.mem') 
         (b1 : block) (lo2 hi2 : Z),
       Mem.inject f m1 m2 ->
       Mem.alloc m1 lo1 hi1 = (m1', b1) ->
       injection_full f m1 ->
       lo2 <= lo1 ->
       hi1 <= hi2 ->
       exists (f' : meminj) (m2' : Mem.mem') (b2 : block),
         Mem.alloc m2 lo2 hi2 = (m2', b2) /\
         Mem.inject f' m1' m2' /\
         inject_incr f f' /\
         f' b1 = Some (b2, 0) /\ (forall b : block, b <> b1 -> f' b = f b)
         /\ injection_full f' m1'.
  intros. exploit Mem.alloc_parallel_inject; eauto.
  intros [? [? [? [? [? [? [? ?]]]]]]].
  repeat (econstructor; eauto).
  intros b HH.
  destruct (ident_eq b b1).
  - subst. rewrite H7; discriminate.
  - rewrite H8; auto. eapply H1.
    eapply Mem.valid_block_alloc_inv in H0; eauto.
    destruct H0; auto. subst; contradict n; auto.
Qed.

Theorem alloc_left_mapped_inject':
  forall f m1 m2 lo hi m1' b1 b2 delta,
    Mem.inject f m1 m2 ->
    injection_full f m1 ->
  Mem.alloc m1 lo hi = (m1', b1) ->
  Mem.valid_block m2 b2 ->
  0 <= delta <= Ptrofs.max_unsigned ->
  (forall ofs k p, Mem.perm m2 b2 ofs k p -> delta = 0 \/ 0 <= ofs < Ptrofs.max_unsigned) ->
  (forall ofs k p, lo <= ofs < hi -> Mem.perm m2 b2 (ofs + delta) k p) ->
  Mem.inj_offset_aligned delta (hi-lo) ->
  (forall b delta' ofs k p,
   f b = Some (b2, delta') ->
   Mem.perm m1 b ofs k p ->
   lo + delta <= ofs + delta' < hi + delta -> False) ->
  exists f',
     Mem.inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, delta)
  /\ (forall b, b <> b1 -> f' b = f b)
  /\ injection_full f' m1'.
Proof.
  intros. inversion H.
  set (f' := fun b => if eq_block b b1 then Some(b2, delta) else f b).
  assert (inject_incr f f').
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
    assert (Mem.mem_inj f' m1 m2).
    inversion mi_inj; constructor; eauto with mem.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H9. subst b0 b3 delta0.
      elim (Mem.fresh_block_alloc _ _ _ _ _ H1). eauto with mem.
      eauto.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H9. subst b0 b3 delta0.
      elim (Mem.fresh_block_alloc _ _ _ _ _ H1).
      eapply Mem.perm_valid_block with (ofs := ofs). apply H10. generalize (size_chunk_pos chunk); omega.
      eauto.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H9. subst b0 b3 delta0.
      elim (Mem.fresh_block_alloc _ _ _ _ _ H1). eauto with mem.
      apply memval_inject_incr with f; auto.
  exists f'. split. constructor.
(* inj *)
  eapply Mem.alloc_left_mapped_inj; eauto. unfold f'; apply dec_eq_true.
(* freeblocks *)
  unfold f'; intros. destruct (eq_block b b1). subst b.
  elim H10. eauto with mem.
  eauto with mem.
(* mappedblocks *)
  unfold f'; intros. destruct (eq_block b b1). congruence. eauto.
(* overlap *)
  unfold f'; red; intros.
  exploit Mem.perm_alloc_inv. eauto. eexact H13. intros P1.
  exploit Mem.perm_alloc_inv. eauto. eexact H14. intros P2.
  destruct (eq_block b0 b1); destruct (eq_block b3 b1).
  congruence.
  inversion H11; subst b0 b1' delta1.
    destruct (eq_block b2 b2'); auto. subst b2'. right; red; intros.
    eapply H7; eauto. omega.
  inversion H12; subst b3 b2' delta2.
    destruct (eq_block b1' b2); auto. subst b1'. right; red; intros.
    eapply H7; eauto. omega.
  eauto.
(* representable *)
  unfold f'; intros.
  destruct (eq_block b b1).
   subst. injection H10; intros; subst b' delta0. destruct H11.
    exploit Mem.perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
    exploit H4. apply H5 with (k := Max) (p := Nonempty); eauto.
    generalize (Ptrofs.unsigned_range_2 ofs). omega.
   exploit Mem.perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
   exploit H4. apply H5 with (k := Max) (p := Nonempty); eauto.
   generalize (Ptrofs.unsigned_range_2 ofs). omega.
  eapply mi_representable; try eassumption.
  destruct H11; eauto using Mem.perm_alloc_4.
(* perm inv *)
  intros. unfold f' in H10; destruct (eq_block b0 b1).
  inversion H10; clear H10; subst b0 b3 delta0.
  assert (EITHER: lo <= ofs < hi \/ ~(lo <= ofs < hi)) by omega.
  destruct EITHER.
  left. apply Mem.perm_implies with Freeable; auto with mem. eapply Mem.perm_alloc_2; eauto.
  right; intros A. eapply Mem.perm_alloc_inv in A; eauto. rewrite dec_eq_true in A. tauto.
  exploit mi_perm_inv; eauto. intuition eauto using Mem.perm_alloc_1, Mem.perm_alloc_4.
(* incr *)
  split. auto.
(* image of b1 *)
  split. unfold f'; apply dec_eq_true.
(* image of others *)
  split; intros. unfold f'; apply dec_eq_false; auto.
  (*full*)
  intros b HH.
  unfold f'.
  destruct (eq_block b b1).
  - subst; discriminate.
  - eapply H0.
    eapply Mem.valid_block_alloc_inv in H1; eauto.
    destruct H1; auto. subst; contradict n; auto.
Qed.
    
Lemma extcall_malloc_ok:
  extcall_properties extcall_malloc_sem
                     (mksignature (Tptr :: nil) (Some Tptr) cc_default).
Proof.
  assert (UNCHANGED:
    forall (P: block -> Z -> Prop) m lo hi v m' b m'',
    Mem.alloc m lo hi = (m', b) ->
    Mem.store Mptr m' b lo v = Some m'' ->
    Mem.unchanged_on P m m'').
  {
    intros.
    apply Mem.unchanged_on_implies with (fun b1 ofs1 => b1 <> b).
    apply Mem.unchanged_on_trans with m'.
    eapply Mem.alloc_unchanged_on; eauto.
    eapply Mem.store_unchanged_on; eauto.
    intros. eapply Mem.valid_not_valid_diff; eauto with mem.
  }
  constructor; intros.
(* well typed *)
- inv H. unfold proj_sig_res, Tptr; simpl. destruct Archi.ptr64; auto.
(* symbols preserved *)
- inv H0; econstructor; eauto.
(* valid block *)
- inv H. eauto with mem.
(* perms *)
- inv H. exploit Mem.perm_alloc_inv. eauto. eapply Mem.perm_store_2; eauto.
  rewrite dec_eq_false. auto.
  apply Mem.valid_not_valid_diff with m1; eauto with mem.
(* readonly *)
- inv H. eapply UNCHANGED; eauto.
(* mem extends *)
- inv H. inv H1. inv H7.
  assert (SZ: v2 = Vptrofs sz).
  { unfold Vptrofs in *. destruct Archi.ptr64; inv H5; auto. }
  subst v2.
  exploit Mem.alloc_extends; eauto. apply Z.le_refl. apply Z.le_refl.
  intros [m3' [A B]].
  exploit Mem.store_within_extends. eexact B. eauto. eauto.
  intros [m2' [C D]].
  exists (Vptr b Ptrofs.zero); exists m2'; intuition.
  econstructor; eauto.
  eapply UNCHANGED; eauto.
  (* mem injects full *)
- inv H0. inv H3. inv H7. inv H9.
  exploit alloc_parallel_inject'; eauto. apply Z.le_refl. apply Z.le_refl.
  intros [f' [m3' [b' [ALLOC [A [B [C [D E]]]]]]]].
  exploit Mem.store_mapped_inject. eexact A. eauto. eauto.
  instantiate (1 := Vptrofs sz). auto.
  intros [m2' [F HH]].
  exists f'; exists (Vptr b' Ptrofs.zero); exists m2'; exists E0; intuition.
  econstructor; eauto.
  econstructor. eauto. auto.
  eapply UNCHANGED; eauto.
  eapply UNCHANGED; eauto.
  red; intros. destruct (eq_block b1 b).
  subst b1. rewrite C in H6. inv H6. eauto with mem.
  rewrite D in H6 by auto. congruence.
  constructor.
  eapply store_full; eauto.
(* mem injects *)
- inv H0. inv H2. inv H6. inv H8.
  exploit Mem.alloc_parallel_inject; eauto. apply Z.le_refl. apply Z.le_refl.
  intros [f' [m3' [b' [ALLOC [A [B [C D]]]]]]].
  exploit Mem.store_mapped_inject. eexact A. eauto. eauto.
  instantiate (1 := Vptrofs sz). auto.
  intros [m2' [F HH]].
  exists f'; exists (Vptr b' Ptrofs.zero); exists m2'; exists E0; intuition.
  econstructor; eauto.
  econstructor. eauto. auto.
  eapply UNCHANGED; eauto.
  eapply UNCHANGED; eauto.
  red; intros. destruct (eq_block b1 b).
  subst b1. rewrite C in H5. inv H5. eauto with mem.
  rewrite D in H5 by auto. congruence.
  constructor.
(* trace length *)
- inv H; simpl; omega.
(* receptive *)
- assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
(* determ *)
- inv H. simple inversion H0.
  assert (EQ2: sz0 = sz).
  { unfold Vptrofs in H4; destruct Archi.ptr64 eqn:SF.
    rewrite <- (Ptrofs.of_int64_to_int64 SF sz0), <- (Ptrofs.of_int64_to_int64 SF sz). congruence.
    rewrite <- (Ptrofs.of_int_to_int SF sz0), <- (Ptrofs.of_int_to_int SF sz). congruence.
  }
  subst.
  split. constructor. intuition congruence.
Qed.

(** ** Semantics of dynamic memory deallocation (free) *)

Inductive extcall_free_sem (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_free_sem_intro: forall b lo sz m m',
      Mem.load Mptr m b (Ptrofs.unsigned lo - size_chunk Mptr) = Some (Vptrofs sz) ->
      Ptrofs.unsigned sz > 0 ->
      Mem.free m b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) = Some m' ->
      extcall_free_sem ge (Vptr b lo :: nil) m E0 Vundef m'.

Lemma extcall_free_ok:
  extcall_properties extcall_free_sem
                     (mksignature (Tptr :: nil) None cc_default).
Proof.
  constructor; intros.
(* well typed *)
- inv H. unfold proj_sig_res. simpl. auto.
(* symbols preserved *)
- inv H0; econstructor; eauto.
(* valid block *)
- inv H. eauto with mem.
(* perms *)
- inv H. eapply Mem.perm_free_3; eauto.
(* readonly *)
- inv H. eapply Mem.free_unchanged_on; eauto.
  intros. red; intros. elim H3.
  apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.free_range_perm; eauto.
(* mem extends *)
- inv H. inv H1. inv H8. inv H6.
  exploit Mem.load_extends; eauto. intros [v' [A B]].
  assert (v' = Vptrofs sz).
  { unfold Vptrofs in *; destruct Archi.ptr64; inv B; auto. }
  subst v'.
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
- inv H0. inv H3. inv H8. inv H10.
  exploit Mem.load_inject; eauto. intros [v' [A B]].
  assert (v' = Vptrofs sz).
  { unfold Vptrofs in *; destruct Archi.ptr64; inv B; auto. }
  subst v'.
  assert (P: Mem.range_perm m1 b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) Cur Freeable).
    eapply Mem.free_range_perm; eauto.
  exploit Mem.address_inject; eauto.
    apply Mem.perm_implies with Freeable; auto with mem.
    apply P. instantiate (1 := lo).
    generalize (size_chunk_pos Mptr); omega.
  intro EQ.
  exploit Mem.free_parallel_inject; eauto. intros (m2' & C & D).
  exists f, Vundef, m2', E0; split.
  apply extcall_free_sem_intro with (sz := sz) (m' := m2').
    rewrite EQ. rewrite <- A. f_equal. omega.
    auto. auto.
    rewrite ! EQ. rewrite <- C. f_equal; omega.
  split. auto.
  split. auto.
  split. eapply Mem.free_unchanged_on; eauto. unfold loc_unmapped. intros; congruence.
  split. eapply Mem.free_unchanged_on; eauto. unfold loc_out_of_reach.
    intros. red; intros. eelim H3; eauto.
    apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
    apply P. omega.
  split. auto.
  split. red; intros. congruence.
  split. constructor.
  auto. eapply free_full; eauto.
(* mem inject *)
- inv H0. inv H2. inv H7. inv H9.
  exploit Mem.load_inject; eauto. intros [v' [A B]].
  assert (v' = Vptrofs sz).
  { unfold Vptrofs in *; destruct Archi.ptr64; inv B; auto. }
  subst v'.
  assert (P: Mem.range_perm m1 b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) Cur Freeable).
    eapply Mem.free_range_perm; eauto.
  exploit Mem.address_inject; eauto.
    apply Mem.perm_implies with Freeable; auto with mem.
    apply P. instantiate (1 := lo).
    generalize (size_chunk_pos Mptr); omega.
  intro EQ.
  exploit Mem.free_parallel_inject; eauto. intros (m2' & C & D).
  exists f, Vundef, m2',E0; split.
  apply extcall_free_sem_intro with (sz := sz) (m' := m2').
    rewrite EQ. rewrite <- A. f_equal. omega.
    auto. auto.
    rewrite ! EQ. rewrite <- C. f_equal; omega.
  split. auto.
  split. auto.
  split. eapply Mem.free_unchanged_on; eauto. unfold loc_unmapped. intros; congruence.
  split. eapply Mem.free_unchanged_on; eauto. unfold loc_out_of_reach.
    intros. red; intros. eelim H2; eauto.
    apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
    apply P. omega.
  split. auto.
  split. red; intros. congruence.
  constructor.
(* trace length *)
- inv H; simpl; omega.
(* receptive *)
- assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
(* determ *)
- inv H; inv H0.
  assert (EQ1: Vptrofs sz0 = Vptrofs sz) by congruence.
  assert (EQ2: sz0 = sz).
  { unfold Vptrofs in EQ1; destruct Archi.ptr64 eqn:SF.
    rewrite <- (Ptrofs.of_int64_to_int64 SF sz0), <- (Ptrofs.of_int64_to_int64 SF sz). congruence.
    rewrite <- (Ptrofs.of_int_to_int SF sz0), <- (Ptrofs.of_int_to_int SF sz). congruence.
  }
  subst sz0.
  split. constructor. intuition congruence.
Qed.

(** ** Semantics of [memcpy] operations. *)

Inductive extcall_memcpy_sem (sz al: Z) (ge: Senv.t):
                        list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_memcpy_sem_intro: forall bdst odst bsrc osrc m bytes m',
      al = 1 \/ al = 2 \/ al = 4 \/ al = 8 -> sz >= 0 -> (al | sz) ->
      (sz > 0 -> (al | Ptrofs.unsigned osrc)) ->
      (sz > 0 -> (al | Ptrofs.unsigned odst)) ->
      bsrc <> bdst \/ Ptrofs.unsigned osrc = Ptrofs.unsigned odst
                   \/ Ptrofs.unsigned osrc + sz <= Ptrofs.unsigned odst
                   \/ Ptrofs.unsigned odst + sz <= Ptrofs.unsigned osrc ->
      Mem.loadbytes m bsrc (Ptrofs.unsigned osrc) sz = Some bytes ->
      Mem.storebytes m bdst (Ptrofs.unsigned odst) bytes = Some m' ->
      extcall_memcpy_sem sz al ge (Vptr bdst odst :: Vptr bsrc osrc :: nil) m E0 Vundef m'.

Lemma extcall_memcpy_ok:
  forall sz al,
  extcall_properties (extcall_memcpy_sem sz al)
                     (mksignature (Tptr :: Tptr :: nil) None cc_default).
Proof.
  intros. constructor.
- (* return type *)
  intros. inv H. constructor.
- (* change of globalenv *)
  intros. inv H0. econstructor; eauto.
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
  intros. inv H0. inv H3. inv H15. inv H16. inv H12. inv H13.
  destruct (zeq sz 0).
+ (* special case sz = 0 *)
  assert (bytes = nil).
  { exploit (Mem.loadbytes_empty m1 bsrc (Ptrofs.unsigned osrc) sz). omega. congruence. }
  subst.
  destruct (Mem.range_perm_storebytes m1' b0 (Ptrofs.unsigned (Ptrofs.add odst (Ptrofs.repr delta0))) nil)
  as [m2' SB].
  simpl. red; intros; omegaContradiction.
  exists f, Vundef, m2', E0.
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
  split.
  red; intros; congruence.
  split. constructor.
  eapply storebytes_full; eauto. 
+ (* general case sz > 0 *)
  exploit Mem.loadbytes_length; eauto. intros LEN.
  assert (RPSRC: Mem.range_perm m1 bsrc (Ptrofs.unsigned osrc) (Ptrofs.unsigned osrc + sz) Cur Nonempty).
    eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm; eauto. auto with mem.
  assert (RPDST: Mem.range_perm m1 bdst (Ptrofs.unsigned odst) (Ptrofs.unsigned odst + sz) Cur Nonempty).
    replace sz with (Z_of_nat (length bytes)).
    eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. auto with mem.
    rewrite LEN. apply Z2Nat.id. omega.
  assert (PSRC: Mem.perm m1 bsrc (Ptrofs.unsigned osrc) Cur Nonempty).
    apply RPSRC. omega.
  assert (PDST: Mem.perm m1 bdst (Ptrofs.unsigned odst) Cur Nonempty).
    apply RPDST. omega.
  exploit Mem.address_inject.  eauto. eexact PSRC. eauto. intros EQ1.
  exploit Mem.address_inject.  eauto. eexact PDST. eauto. intros EQ2.
  exploit Mem.loadbytes_inject; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_mapped_inject; eauto. intros [m2' [C D]].
  exists f; exists Vundef; exists m2'; exists E0.
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
  split. red; intros; congruence.
  split. constructor. 
  eapply storebytes_full; eauto.
  
- (* injections *)
  intros. inv H0. inv H2. inv H14. inv H15. inv H11. inv H12.
  destruct (zeq sz 0).
+ (* special case sz = 0 *)
  assert (bytes = nil).
  { exploit (Mem.loadbytes_empty m1 bsrc (Ptrofs.unsigned osrc) sz). omega. congruence. }
  subst.
  destruct (Mem.range_perm_storebytes m1' b0 (Ptrofs.unsigned (Ptrofs.add odst (Ptrofs.repr delta0))) nil)
  as [m2' SB].
  simpl. red; intros; omegaContradiction.
  exists f, Vundef, m2', E0.
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
  split.
  red; intros; congruence.
   constructor.
+ (* general case sz > 0 *)
  exploit Mem.loadbytes_length; eauto. intros LEN.
  assert (RPSRC: Mem.range_perm m1 bsrc (Ptrofs.unsigned osrc) (Ptrofs.unsigned osrc + sz) Cur Nonempty).
    eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm; eauto. auto with mem.
  assert (RPDST: Mem.range_perm m1 bdst (Ptrofs.unsigned odst) (Ptrofs.unsigned odst + sz) Cur Nonempty).
    replace sz with (Z.of_nat (length bytes)).
    eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. auto with mem.
    rewrite LEN. apply Z2Nat.id. omega.
  assert (PSRC: Mem.perm m1 bsrc (Ptrofs.unsigned osrc) Cur Nonempty).
    apply RPSRC. omega.
  assert (PDST: Mem.perm m1 bdst (Ptrofs.unsigned odst) Cur Nonempty).
    apply RPDST. omega.
  exploit Mem.address_inject.  eauto. eexact PSRC. eauto. intros EQ1.
  exploit Mem.address_inject.  eauto. eexact PDST. eauto. intros EQ2.
  exploit Mem.loadbytes_inject; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_mapped_inject; eauto. intros [m2' [C D]].
  exists f; exists Vundef; exists m2'; exists E0.
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
  eelim H2; eauto.
  apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
  eapply Mem.storebytes_range_perm; eauto.
  erewrite list_forall2_length; eauto.
  omega.
  split. apply inject_incr_refl.
  split. red; intros; congruence.
  constructor. 
  
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

Inductive extcall_annot_sem (text: string) (targs: list typ) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_annot_sem_intro: forall vargs m args,
      eventval_list_match ge args targs vargs ->
      extcall_annot_sem text targs ge vargs m (Event_annot text args :: E0) Vundef m.

Lemma extcall_annot_ok:
  forall text targs,
  extcall_properties (extcall_annot_sem text targs)
                     (mksignature targs None cc_default).
Proof.
  intros; constructor; intros.
(* well typed *)
- inv H. simpl. auto.
(* symbols *)
- destruct H as (A & B & C). inv H0. econstructor; eauto.
  eapply eventval_list_match_preserved; eauto.
(* valid blocks *)
- inv H; auto.
(* perms *)
- inv H; auto.
(* readonly *)
- inv H. apply Mem.unchanged_on_refl.
(* mem extends *)
- inv H.
  exists Vundef; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_list_match_lessdef; eauto.
(* mem injects *)
- inv H0.
  exists f; exists Vundef; exists m1'; exists (Event_annot text args :: E0); intuition.
  econstructor; eauto.
  eapply eventval_list_match_inject; eauto.
  red; intros; congruence.
  repeat constructor.
(* mem injects *)
- inv H0.
  exists f; exists Vundef; exists m1'; exists (Event_annot text args :: E0); intuition.
  econstructor; eauto.
  eapply eventval_list_match_inject; eauto.
  red; intros; congruence.
  repeat constructor.
(* trace length *)
- inv H; simpl; omega.
(* receptive *)
- assert (t1 = t2). inv H; inv H0; auto.
  exists vres1; exists m1; congruence.
(* determ *)
- inv H; inv H0.
  assert (args = args0). eapply eventval_list_match_determ_2; eauto. subst args0.
  split. constructor. auto.
Qed.

Inductive extcall_annot_val_sem (text: string) (targ: typ) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_annot_val_sem_intro: forall varg m arg,
      eventval_match ge arg targ varg ->
      extcall_annot_val_sem text targ ge (varg :: nil) m (Event_annot text (arg :: nil) :: E0) varg m.

Lemma extcall_annot_val_ok:
  forall text targ,
  extcall_properties (extcall_annot_val_sem text targ)
                     (mksignature (targ :: nil) (Some targ) cc_default).
Proof.
  intros; constructor; intros.
(* well typed *)
- inv H. unfold proj_sig_res; simpl. eapply eventval_match_type; eauto.
(* symbols *)
- destruct H as (A & B & C). inv H0. econstructor; eauto.
  eapply eventval_match_preserved; eauto.
(* valid blocks *)
- inv H; auto.
(* perms *)
- inv H; auto.
(* readonly *)
- inv H. apply Mem.unchanged_on_refl.
(* mem extends *)
- inv H. inv H1. inv H6.
  exists v2; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_match_lessdef; eauto.
(* mem inject *)
- inv H0. inv H3. inv H8.
  exists f; exists v'; exists m1'; exists (Event_annot text (arg :: nil) :: E0); intuition.
  econstructor; eauto.
  eapply eventval_match_inject; eauto.
  red; intros; congruence.
  repeat constructor.
(* mem inject *)
- inv H0. inv H2. inv H7.
  exists f; exists v'; exists m1'; exists (Event_annot text (arg :: nil) :: E0); intuition.
  econstructor; eauto.
  eapply eventval_match_inject; eauto.
  red; intros; congruence.
  repeat constructor.
(* trace length *)
- inv H; simpl; omega.
(* receptive *)
- assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
(* determ *)
- inv H; inv H0.
  assert (arg = arg0). eapply eventval_match_determ_2; eauto. subst arg0.
  split. constructor. auto.
Qed.

Inductive extcall_debug_sem (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_debug_sem_intro: forall vargs m,
      extcall_debug_sem ge vargs m E0 Vundef m.

Lemma extcall_debug_ok:
  forall targs,
  extcall_properties extcall_debug_sem
                     (mksignature targs None cc_default).
Proof.
  intros; constructor; intros.
(* well typed *)
- inv H. simpl. auto.
(* symbols *)
- inv H0. econstructor; eauto.
(* valid blocks *)
- inv H; auto.
(* perms *)
- inv H; auto.
(* readonly *)
- inv H. apply Mem.unchanged_on_refl.
(* mem extends *)
- inv H.
  exists Vundef; exists m1'; intuition.
  econstructor; eauto.
(* mem injects *)
- inv H0.
  exists f; exists Vundef; exists m1'; exists E0; intuition.
  econstructor; eauto.
  red; intros; congruence.
  constructor.
(* mem injects *)
- inv H0.
  exists f; exists Vundef; exists m1'; exists E0; intuition.
  econstructor; eauto.
  red; intros; congruence.
  constructor.
(* trace length *)
- inv H; simpl; omega.
(* receptive *)
- inv H; inv H0. exists Vundef, m1; constructor.
(* determ *)
- inv H; inv H0.
  split. constructor. auto.
Qed.

(** ** Semantics of external functions. *)

(** For functions defined outside the program ([EF_external],
  [EF_builtin] and [EF_runtime]), we do not define their
  semantics, but only assume that it satisfies
  [extcall_properties]. *)

Parameter external_functions_sem: String.string -> signature -> extcall_sem.

Axiom external_functions_properties:
  forall id sg, extcall_properties (external_functions_sem id sg) sg.

(** We treat inline assembly similarly. *)

Parameter inline_assembly_sem: String.string -> signature -> extcall_sem.

Axiom inline_assembly_properties:
  forall id sg, extcall_properties (inline_assembly_sem id sg) sg.

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
  | EF_runtime name sg   => external_functions_sem name sg
  | EF_vload chunk       => volatile_load_sem chunk
  | EF_vstore chunk      => volatile_store_sem chunk
  | EF_malloc            => extcall_malloc_sem
  | EF_free              => extcall_free_sem
  | EF_memcpy sz al      => extcall_memcpy_sem sz al
  | EF_annot kind txt targs   => extcall_annot_sem txt targs
  | EF_annot_val kind txt targ => extcall_annot_val_sem txt targ
  | EF_inline_asm txt sg clb => inline_assembly_sem txt sg
  | EF_debug kind txt targs => extcall_debug_sem
  end.

Theorem external_call_spec:
  forall ef,
  extcall_properties (external_call ef) (ef_sig ef).
Proof.
  intros. unfold external_call, ef_sig; destruct ef.
  apply external_functions_properties.
  apply external_functions_properties.
  apply external_functions_properties.
  apply volatile_load_ok.
  apply volatile_store_ok.
  apply extcall_malloc_ok.
  apply extcall_free_ok.
  apply extcall_memcpy_ok.
  apply extcall_annot_ok.
  apply extcall_annot_val_ok.
  apply inline_assembly_properties.
  apply extcall_debug_ok.
Qed.

Definition external_call_well_typed ef := ec_well_typed (external_call_spec ef).
Definition external_call_symbols_preserved ef := ec_symbols_preserved (external_call_spec ef).
Definition external_call_valid_block ef := ec_valid_block (external_call_spec ef).
Definition external_call_max_perm ef := ec_max_perm (external_call_spec ef).
Definition external_call_readonly ef := ec_readonly (external_call_spec ef).
Definition external_call_mem_extends ef := ec_mem_extends (external_call_spec ef).
Definition external_call_mem_inject_gen ef := ec_mem_inject (external_call_spec ef).
Definition external_call_mem_inject_gen' ef := ec_mem_inject' (external_call_spec ef).
Definition external_call_trace_length ef := ec_trace_length (external_call_spec ef).
Definition external_call_receptive ef := ec_receptive (external_call_spec ef).
Definition external_call_determ ef := ec_determ (external_call_spec ef).

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
  injection_full f m1 ->
  Val.inject_list f vargs vargs' ->
  exists f', exists vres', exists m2', exists t',
     external_call ef ge vargs' m1' t' vres' m2'
    /\ Val.inject f' vres vres'
    /\ Mem.inject f' m2 m2'
    /\ Mem.unchanged_on (loc_unmapped f) m1 m2
    /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'
    /\ inject_incr f f'
    /\ inject_separated f f' m1 m1'
    /\ inject_trace f' t t' /\ injection_full f' m2.
Proof.
  intros. destruct H as (A & B & C).
  eapply external_call_mem_inject_gen with (ge1 := ge); eauto.
  repeat split; intros.
  + simpl in H4. exploit A; eauto. intros EQ; rewrite EQ in H; inv H. auto.
  + simpl in H4. exploit A; eauto. intros EQ; rewrite EQ in H; inv H. auto.
  + simpl in H4. exists b1; split; eauto.
  + simpl; unfold Genv.block_is_volatile.
    destruct (Genv.find_var_info ge b1) as [gv1|] eqn:V1.
    * exploit B; eauto. intros EQ; rewrite EQ in H; inv H. rewrite V1; auto.
    * destruct (Genv.find_var_info ge b2) as [gv2|] eqn:V2; auto.
      exploit C; eauto. intros EQ; subst b2. congruence.
Qed.

Lemma external_call_mem_inject':
  forall ef F V (ge: Genv.t F V) vargs m1 t vres m2 f m1' vargs',
  meminj_preserves_globals ge f ->
  external_call ef ge vargs m1 t vres m2 ->
  Mem.inject f m1 m1' ->
  Val.inject_list f vargs vargs' ->
  exists f', exists vres', exists m2', exists t',
     external_call ef ge vargs' m1' t' vres' m2'
    /\ Val.inject f' vres vres'
    /\ Mem.inject f' m2 m2'
    /\ Mem.unchanged_on (loc_unmapped f) m1 m2
    /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'
    /\ inject_incr f f'
    /\ inject_separated f f' m1 m1'
    /\ inject_trace f' t t'.
Proof.
  intros. destruct H as (A & B & C).
  eapply external_call_mem_inject_gen' with (ge1 := ge); eauto.
  repeat split; intros.
  + simpl in H3. exploit A; eauto. intros EQ; rewrite EQ in H; inv H. auto.
  + simpl in H3. exploit A; eauto. intros EQ; rewrite EQ in H; inv H. auto.
  + simpl in H3. exists b1; split; eauto.
  + simpl; unfold Genv.block_is_volatile.
    destruct (Genv.find_var_info ge b1) as [gv1|] eqn:V1.
    * exploit B; eauto. intros EQ; rewrite EQ in H; inv H. rewrite V1; auto.
    * destruct (Genv.find_var_info ge b2) as [gv2|] eqn:V2; auto.
      exploit C; eauto. intros EQ; subst b2. congruence.
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

(** * Evaluation of builtin arguments *)

Section EVAL_BUILTIN_ARG.

Variable A: Type.
Variable ge: Senv.t.
Variable e: A -> val.
Variable sp: val.
Variable m: mem.

Inductive eval_builtin_arg: builtin_arg A -> val -> Prop :=
  | eval_BA: forall x,
      eval_builtin_arg (BA x) (e x)
  | eval_BA_int: forall n,
      eval_builtin_arg (BA_int n) (Vint n)
  | eval_BA_long: forall n,
      eval_builtin_arg (BA_long n) (Vlong n)
  | eval_BA_float: forall n,
      eval_builtin_arg (BA_float n) (Vfloat n)
  | eval_BA_single: forall n,
      eval_builtin_arg (BA_single n) (Vsingle n)
  | eval_BA_loadstack: forall chunk ofs v,
      Mem.loadv chunk m (Val.offset_ptr sp ofs) = Some v ->
      eval_builtin_arg (BA_loadstack chunk ofs) v
  | eval_BA_addrstack: forall ofs,
      eval_builtin_arg (BA_addrstack ofs) (Val.offset_ptr sp ofs)
  | eval_BA_loadglobal: forall chunk id ofs v,
      Mem.loadv chunk m (Senv.symbol_address ge id ofs) = Some v ->
      eval_builtin_arg (BA_loadglobal chunk id ofs) v
  | eval_BA_addrglobal: forall id ofs,
      eval_builtin_arg (BA_addrglobal id ofs) (Senv.symbol_address ge id ofs)
  | eval_BA_splitlong: forall hi lo vhi vlo,
      eval_builtin_arg hi vhi -> eval_builtin_arg lo vlo ->
      eval_builtin_arg (BA_splitlong hi lo) (Val.longofwords vhi vlo)
  | eval_BA_addptr: forall a1 a2 v1 v2,
      eval_builtin_arg a1 v1 -> eval_builtin_arg a2 v2 ->
      eval_builtin_arg (BA_addptr a1 a2)
                       (if Archi.ptr64 then Val.addl v1 v2 else Val.add v1 v2).

Definition eval_builtin_args (al: list (builtin_arg A)) (vl: list val) : Prop :=
  list_forall2 eval_builtin_arg al vl.

Lemma eval_builtin_arg_determ:
  forall a v, eval_builtin_arg a v -> forall v', eval_builtin_arg a v' -> v' = v.
Proof.
  induction 1; intros v' EV; inv EV; try congruence.
  f_equal; eauto.
  apply IHeval_builtin_arg1 in H3. apply IHeval_builtin_arg2 in H5. subst; auto. 
Qed.

Lemma eval_builtin_args_determ:
  forall al vl, eval_builtin_args al vl -> forall vl', eval_builtin_args al vl' -> vl' = vl.
Proof.
  induction 1; intros v' EV; inv EV; f_equal; eauto using eval_builtin_arg_determ.
Qed.

End EVAL_BUILTIN_ARG.

Hint Constructors eval_builtin_arg: barg.

(** Invariance by change of global environment. *)

Section EVAL_BUILTIN_ARG_PRESERVED.

Variables A F1 V1 F2 V2: Type.
Variable ge1: Genv.t F1 V1.
Variable ge2: Genv.t F2 V2.
Variable e: A -> val.
Variable sp: val.
Variable m: mem.

Hypothesis symbols_preserved:
  forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.

Lemma eval_builtin_arg_preserved:
  forall a v, eval_builtin_arg ge1 e sp m a v -> eval_builtin_arg ge2 e sp m a v.
Proof.
  assert (EQ: forall id ofs, Senv.symbol_address ge2 id ofs = Senv.symbol_address ge1 id ofs).
  { unfold Senv.symbol_address; simpl; intros. rewrite symbols_preserved; auto. }
  induction 1; eauto with barg. rewrite <- EQ in H; eauto with barg. rewrite <- EQ; eauto with barg.
Qed.

Lemma eval_builtin_args_preserved:
  forall al vl, eval_builtin_args ge1 e sp m al vl -> eval_builtin_args ge2 e sp m al vl.
Proof.
  induction 1; constructor; auto; eapply eval_builtin_arg_preserved; eauto.
Qed.

End EVAL_BUILTIN_ARG_PRESERVED.

(** Compatibility with the "is less defined than" relation. *)

Section EVAL_BUILTIN_ARG_LESSDEF.

Variable A: Type.
Variable ge: Senv.t.
Variables e1 e2: A -> val.
Variable sp: val.
Variables m1 m2: mem.

Hypothesis env_lessdef: forall x, Val.lessdef (e1 x) (e2 x).
Hypothesis mem_extends: Mem.extends m1 m2.

Lemma eval_builtin_arg_lessdef:
  forall a v1, eval_builtin_arg ge e1 sp m1 a v1 ->
  exists v2, eval_builtin_arg ge e2 sp m2 a v2 /\ Val.lessdef v1 v2.
Proof.
  induction 1.
- exists (e2 x); auto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- exploit Mem.loadv_extends; eauto. intros (v' & P & Q). exists v'; eauto with barg.
- econstructor; eauto with barg.
- exploit Mem.loadv_extends; eauto. intros (v' & P & Q). exists v'; eauto with barg.
- econstructor; eauto with barg.
- destruct IHeval_builtin_arg1 as (vhi' & P & Q).
  destruct IHeval_builtin_arg2 as (vlo' & R & S).
  econstructor; split; eauto with barg. apply Val.longofwords_lessdef; auto.
- destruct IHeval_builtin_arg1 as (vhi' & P & Q).
  destruct IHeval_builtin_arg2 as (vlo' & R & S).
  econstructor; split; eauto with barg. 
  destruct Archi.ptr64; auto using Val.add_lessdef, Val.addl_lessdef.
Qed.

Lemma eval_builtin_args_lessdef:
  forall al vl1, eval_builtin_args ge e1 sp m1 al vl1 ->
  exists vl2, eval_builtin_args ge e2 sp m2 al vl2 /\ Val.lessdef_list vl1 vl2.
Proof.
  induction 1.
- econstructor; split. constructor. auto.
- exploit eval_builtin_arg_lessdef; eauto. intros (v1' & P & Q).
  destruct IHlist_forall2 as (vl' & U & V).
  exists (v1'::vl'); split; constructor; auto.
Qed.

End EVAL_BUILTIN_ARG_LESSDEF.

