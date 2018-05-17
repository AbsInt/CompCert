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

(** Tools for small-step operational semantics *)

(** This module defines generic operations and theorems over
  the one-step transition relations that are used to specify
  operational semantics in small-step style. *)

Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.
Require Import Smallstep.


Require Import Values. (*for meminj, compose_meminj,...*)

Set Implicit Arguments.


(** * Transition semantics *)

(** The general form of a transition semantics. *)
Require Import compcert.common.Memory.

Section ExposingMemory.
  
  Variables L1 L2: semantics.
  Variable get_mem1: state L1 -> mem.
  Variable get_mem2: state L2 -> mem.

  (** *Equality Phases*)
  Section Equality.
    Record fsim_properties_eq: Type :=
      {
        Eqindex: Type;
        Eqorder: Eqindex -> Eqindex -> Prop;
        Eqmatch_states: Eqindex -> state L1 -> state L2 -> Prop;  
        Eqfsim_order_wf: well_founded Eqorder;
        Eqfsim_match_meminj: forall i s1 s2, Eqmatch_states i s1 s2 ->  (get_mem1 s1) = (get_mem2 s2);
        (*    fsim_match_initial_states:
      forall s1 m1 f m2, initial_state L1 (s1,m1) -> Mem.inject f m1 m2 ->
      exists i, exists s2, initial_state L2 (s2,m2) /\ match_states i f (s1,m1) (s2,m2);*)
        Eqfsim_match_initial_states:
          forall s1, initial_state L1 s1 -> 
                exists i s2, initial_state L2 s2 /\ Eqmatch_states i s1 s2;
        Eqfsim_match_final_states:
          forall i s1 s2 r ,
            Eqmatch_states i s1 s2 -> final_state L1 s1 r -> (final_state L2 s2 r);
        Eqfsim_simulation:
          forall s1 t s1', Step L1 s1 t s1' ->
                      forall i s2, Eqmatch_states i s1 s2 ->
                              exists i', exists s2',
                                  (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ Eqorder i' i))
                                  /\ Eqmatch_states i' s1' s2';
        Eqfsim_public_preserved:
          forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id
      }.
  
    
    Lemma sim_eqSim':
      forall index order (match_states:index -> state L1 -> state L2 -> Prop),
      (forall i s1 s2, match_states i s1 s2 ->  (get_mem1 s1) = (get_mem2 s2)) ->
      fsim_properties L1 L2 index order match_states ->
      fsim_properties_eq.
    Proof.
      intros ? ? ? H HH; inv HH.
      econstructor; eauto.
    Qed.
  End Equality.

  
  (** *Extension Phases*)
  Section Extensions.
    
   Record fsim_properties_ext: Type :=
  {
    Extindex: Type;
    Extorder: Extindex -> Extindex -> Prop;
    Extmatch_states: Extindex -> state L1 -> state L2 -> Prop;  
    Extfsim_order_wf: well_founded Extorder;
    Extfsim_match_meminj: forall i s1 s2, Extmatch_states i s1 s2 ->  Mem.extends (get_mem1 s1) (get_mem2 s2);
(*    fsim_match_initial_states:
      forall s1 m1 f m2, initial_state L1 (s1,m1) -> Mem.inject f m1 m2 ->
      exists i, exists s2, initial_state L2 (s2,m2) /\ match_states i f (s1,m1) (s2,m2);*)
    Extfsim_match_initial_states:
      forall s1, initial_state L1 s1 -> 
               exists i s2, initial_state L2 s2 /\ Extmatch_states i s1 s2;
    Extfsim_match_final_states:
      forall i s1 s2 r ,
      Extmatch_states i s1 s2 -> final_state L1 s1 r -> (final_state L2 s2 r);
    Extfsim_simulation:
      forall s1 t s1', Step L1 s1 t s1' ->
      forall i s2, Extmatch_states i s1 s2 ->
      exists i', exists s2',
         (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ Extorder i' i))
         /\ Extmatch_states i' s1' s2';
    Extfsim_public_preserved:
      forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id
  }.

   (** An alternate form of the simulation diagram *)
   Lemma Extfsim_simulation':
       forall (SIM:fsim_properties_ext),
       forall i s1 t s1',
         Step L1 s1 t s1' ->
         forall s2, Extmatch_states SIM i s1 s2 ->
               (exists i', exists s2', Plus L2 s2 t s2' /\
                                   Extmatch_states SIM i' s1' s2')
               \/ (exists i', Extorder SIM i' i /\ t = E0 /\ Extmatch_states SIM i' s1' s2).
   Proof.
     intros. exploit Extfsim_simulation; eauto.
     intros [i' [s2' [A B ]]]. intuition.
     left; exists i'; exists s2'; auto .
     inv H2. 
     right; exists i'; eauto.
     left; exists i'; exists s2'; split; auto. econstructor; eauto.
   Qed.

   (** *Star version of simulation*)
    Lemma Extsimulation_star:
      forall (SIM:fsim_properties_ext),
      forall s1 t s1', Star L1 s1 t s1' ->
                  forall i s2,
                    Extmatch_states SIM  i s1 s2 ->
                    exists i', exists s2', Star L2 s2 t s2' /\ Extmatch_states SIM  i' s1' s2'.
    Proof.
      intros S.
      induction 1; intros.
      exists i; exists s2; split; auto. apply star_refl.

      (*split; auto; constructor.
      apply inject_incr_refl. constructor.*)

      exploit Extfsim_simulation; eauto.
      intros [i' [s2' [A B]]].
      exploit IHstar; eauto. intros [i'' [s2'' [E F ]]].
      exists i'';exists s2''; split; auto. eapply star_trans; eauto.
      intuition auto. apply plus_star; auto.
    Qed.
    
    (** *Plus version of simulation*)
    Lemma Extsimulation_plus:
      forall (SIM: fsim_properties_ext),
      forall s1 t s1', Plus L1 s1 t s1' ->
                  forall i s2, Extmatch_states SIM  i s1 s2 -> 
            (exists i', exists s2', Plus L2 s2 t s2' /\ Extmatch_states SIM  i' s1' s2')
            \/ (exists i', clos_trans _ (Extorder SIM) i' i /\ t = E0 /\ Extmatch_states SIM  i' s1' s2).
    Proof.
      intros S.
      induction 1 using plus_ind2; intros.
      (* base case *)
      exploit Extfsim_simulation'; eauto.
      intros [[i' [s2' [A B ]]] | [i'  A]].
      left. exists i', s2'; auto.
      right; exists i'; intuition.
      (* inductive case *)
      exploit Extfsim_simulation'; eauto.
      intros [[i' [s2' [A B]]] | [i' [A [B C] ]]].
      exploit Extsimulation_star; eauto. apply plus_star; eauto. eauto.
      intros [i'' [s2'' [P Q ]]].
      left; exists i''; exists s2''; split; auto. eapply plus_star_trans; eauto.
      repeat split; auto.
      
      exploit IHplus; eauto.
      intros [[i'' [s2'' [P Q ]]] | [i'' [P Q]]].
      subst. simpl. left; exists i''; exists s2''; auto.
      repeat split; eauto.

      subst. simpl. right; exists i''; intuition auto.
      eapply t_trans; eauto. eapply t_step; eauto.
    Qed.
    
    Lemma EqEx_sim': 
        fsim_properties_eq ->
        fsim_properties_ext.
    Proof.
      intros H; inv H.
      econstructor; eauto.
      intros.
      erewrite Eqfsim_match_meminj0; eauto.
      eapply Mem.extends_refl.
    Qed.

    Lemma sim_extSim:
      forall index order (match_states:index -> state L1 -> state L2 -> Prop),
      (forall i s1 s2, match_states i s1 s2 ->  Mem.extends (get_mem1 s1) (get_mem2 s2)) ->
      fsim_properties L1 L2 index order match_states ->
      fsim_properties_ext.
    Proof.
      intros ? ? ? H HH; inv HH.
      econstructor; eauto.
    Qed.

  End Extensions.

  (** *Injection Phases*)
  Section Injection.
    Record fsim_properties_inj: Type :=
      {  Injindex: Type;
        Injorder: Injindex -> Injindex -> Prop;
        Injmatch_states: Injindex -> meminj -> state L1 -> state L2 -> Prop;  
        Injfsim_order_wf: well_founded Injorder;
        Injfsim_match_meminj: forall i f s1 s2, Injmatch_states i f s1 s2 ->  Mem.inject f (get_mem1 s1) (get_mem2 s2);
        Injfsim_match_full: forall i f s1 s2, Injmatch_states i f s1 s2 ->  injection_full f (get_mem1 s1);
        (*    fsim_match_initial_states:
      forall s1 m1 f m2, initial_state L1 (s1,m1) -> Mem.inject f m1 m2 ->
      exists i, exists s2, initial_state L2 (s2,m2) /\ match_states i f (s1,m1) (s2,m2);*)
        Injfsim_match_initial_states:
          forall s1, initial_state L1 s1 -> 
                exists i f s2, initial_state L2 s2 /\ Injmatch_states i f s1 s2;
        Injfsim_match_final_states:
          forall i s1 s2 r f,
            Injmatch_states i f s1 s2 -> final_state L1 s1 r -> (final_state L2 s2 r);
        Injfsim_simulation:
          forall s1 t s1' f, Step L1 s1 t s1' ->
                        forall i s2, Injmatch_states i f s1 s2 ->
                                exists i', exists s2' f' t',
                                    (Plus L2 s2 t' s2' \/ (Star L2 s2 t' s2' /\ Injorder i' i))
                                    /\ Injmatch_states i' f' s1' s2' /\
                                    Values.inject_incr f f' /\
                                    inject_trace f' t t';
        Injfsim_public_preserved:
          forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id
      }.

   (** An alternate form of the simulation diagram *)

    Lemma Injfsim_simulation':
        forall (SIM:fsim_properties_inj),
        forall i s1 t s1' f,
          Step L1 s1 t s1' ->
          forall s2, Injmatch_states SIM i f s1 s2 ->
                (exists i', exists s2' f' t',
                      Plus L2 s2 t' s2' /\
                      Injmatch_states SIM i' f' s1' s2'
                      /\ inject_incr f f' /\ inject_trace f' t t')
                \/ (exists i' f', Injorder SIM i' i /\ t = E0 /\ Injmatch_states SIM i' f' s1' s2
                  /\ inject_incr f f').
    Proof.
      intros. exploit Injfsim_simulation; eauto.
      intros [i' [s2' [f' [t'[A [B [C D]]]]]]]. intuition.
      left; exists i'; exists s2'; auto. exists f', t'; eauto.
      inv H2. inversion D; subst.
      right; exists i'; eauto.
      left; exists i'; exists s2',f', (t1 ** t2); split; auto. econstructor; eauto.
    Qed.

    
    (** *Star version of simulation*)
    Lemma Injsimulation_star:
        forall (SIM:fsim_properties_inj),
      forall s1 t s1', Star L1 s1 t s1' ->
                  forall i f s2,
                    Injmatch_states SIM i f s1 s2 ->
                    exists i' f', exists s2' t', Star L2 s2 t' s2' /\ Injmatch_states SIM i' f' s1' s2'
                                       /\ inject_incr f f' /\ inject_trace f' t t'.
    Proof.
      intros S.
      induction 1; intros.
      exists i, f; exists s2 , nil; split; auto. apply star_refl.
      split; auto; constructor.
      apply inject_incr_refl. constructor.
      exploit Injfsim_simulation; eauto.
      intros [i' [s2' [f'[t' [A [B [C D]]]]]]].
      exploit IHstar; eauto. intros [i'' [f'' [s2'' [t'' [E [F [G HH]]]]]]].
      exists i'';exists f''; exists s2'', (t' ** t''); split; auto. eapply star_trans; eauto.
      intuition auto. apply plus_star; auto.
      split; auto. subst t.
      split; auto.
      eapply inject_incr_trans; eauto.
      admit. (*inject trace properties*)
    Admitted.
    
    (** *Plus version of simulation*)
    Lemma Injsimulation_plus:
      forall (SIM:fsim_properties_inj),
      forall s1 t s1', Plus L1 s1 t s1' ->
                  forall i f s2, Injmatch_states SIM i f s1 s2 -> 
            (exists i', exists f', exists s2' t', Plus L2 s2 t' s2' /\ Injmatch_states SIM i' f' s1' s2'
            /\ inject_incr f f' /\ inject_trace f' t t')
            \/ (exists i', exists f', clos_trans _ (Injorder SIM) i' i /\ t = E0 /\ Injmatch_states SIM i' f' s1' s2
                           /\ inject_incr f f').
    Proof.
      intros S.
      induction 1 using plus_ind2; intros.
      (* base case *)
      exploit Injfsim_simulation'; eauto.
      intros [[i' [s2' [f' [t' [A [B [C D]]]]]]] | [i' [f' [t' A]]]].
      left. exists i', f', s2', t'; auto.
      right; exists i', f' ; intuition.
      (* inductive case *)
      exploit Injfsim_simulation'; eauto.
      intros [[i' [s2' [f' [t' [A [B [C D]]]]]]] | [i' [f' [A [B [C D]]]]]].
      exploit Injsimulation_star; eauto. apply plus_star; eauto. eauto.
      intros [i'' [f'' [s2'' [t'' [P [Q [R SS]]]]]]].
      left; exists i''; exists f''; exists s2'', (t'**t''); split; auto. eapply plus_star_trans; eauto.
      repeat split; auto.
      eapply inject_incr_trans; eauto.
      subst t.
      admit. (*Some properties about inject_trace*)
 
      
      exploit IHplus; eauto.
      intros [[i'' [f'' [s2'' [t' [P [Q [R SS]]]]]]] | [i'' [f'' [P [Q R]]]]].
      subst. simpl. left; exists i''; exists f''; exists s2'', (t'); auto.
      repeat split; eauto.
      eapply inject_incr_trans; eauto.
      subst. simpl. right; exists i''; exists f''; intuition auto.
      eapply t_trans; eauto. eapply t_step; eauto.
      eapply inject_incr_trans; eauto.
    Admitted.
    
  End Injection.
End ExposingMemory.

(*
Section InductiveDefinitions.
  
  
  Variables L1 L2: semantics.
  Variable get_mem1: state L1 -> mem.
  Variable get_mem2: state L2 -> mem.
  
Arguments fsim_properties_eq: clear implicits.

Inductive forward_equality: Prop :=
  Forward_equality (index: Type)
                   (order: index -> index -> Prop)
                   (match_states: index -> state L1 -> state L2 -> Prop)
                   (props: fsim_properties_eq
                             L1 L2 get_mem1 get_mem2
                             index order match_states).

Arguments fsim_properties_ext: clear implicits.

Inductive forward_extension: Prop :=
  Forward_extension (index: Type)
                   (order: index -> index -> Prop)
                   (match_states: index -> state L1 -> state L2 -> Prop)
                   (props: fsim_properties_ext
                             L1 L2 get_mem1 get_mem2
                             index order match_states).

Lemma EqEx_sim: forward_equality -> forward_extension.
Proof.
  intros H; inv H.
  apply EqEx_sim' in props; econstructor; eauto.
Qed.


Arguments fsim_properties_inj: clear implicits.

Inductive forward_injection: Prop :=
  Forward_injection (index: Type)
                   (order: index -> index -> Prop)
                   (match_states: index -> meminj -> state L1 -> state L2 -> Prop)
                   (props: fsim_properties_inj
                             L1 L2 get_mem1 get_mem2
                             index order match_states).

End InductiveDefinitions. *)

Section Composition.
    
  Variables L1 L2 L3: semantics.
  Variable get_mem1: state L1 -> mem.
  Variable get_mem2: state L2 -> mem.
  Variable get_mem3: state L3 -> mem.

  Lemma injection_extension_composition:
    @fsim_properties_inj L1 L2 get_mem1 get_mem2 ->
    @fsim_properties_ext L2 L3 get_mem2 get_mem3 ->
    @fsim_properties_inj L1 L3 get_mem1 get_mem3.
  Proof.
    intros SIM12 SIM23.
    set (index13:= (Extindex SIM23 * Injindex SIM12)%type).
    set (order13:=  (lex_ord (clos_trans _ (Extorder SIM23)) (Injorder SIM12))).
    set (match_states13:=
           (fun (i: _ ) f (s1: state L1) (s3: state L3) =>
              exists s2, Injmatch_states SIM12 (snd i) f s1 s2 /\ Extmatch_states SIM23 (fst i) s2 s3) ).
    eapply Build_fsim_properties_inj with (Injindex:= index13) (Injorder:=order13) (Injmatch_states:=match_states13).
- (* well founded *)
  apply wf_lex_ord. apply wf_clos_trans.
  eapply Extfsim_order_wf; eauto. eapply Injfsim_order_wf; eauto.
- (* inject. *)
  intros ? ? ? ? [s2' [MATCH12 MATCH23]].
  eapply Mem.inject_extends_compose; [eapply SIM12| eapply SIM23]; eauto.
- (* Full *)
  intros ? ? ? ? [s2' [MATCH12 MATCH23]] b VALID.
  eapply SIM12; eauto.
- (* initial states *)
  intros. exploit (Injfsim_match_initial_states SIM12); eauto. intros [i [ f [s2 [A B]]]].
  exploit (Extfsim_match_initial_states SIM23); eauto. intros [i' [s3 [C D]]].
  exists (i', i); exists f; exists s3; split; auto. exists s2; auto.
- (* final states *)
  intros. destruct H as [s3 [A B]].
  eapply (Extfsim_match_final_states SIM23); eauto.
  eapply (Injfsim_match_final_states SIM12); eauto.
- (* simulation *)
    intros. destruct H0 as [s3 [A B]]. destruct i as [i2 i1]; simpl in *.
  exploit (Injfsim_simulation' SIM12); eauto.
  intros [[i1' [s3'[ f' [t' [C [D [E F]]]]]]] | [i1' [f' [C [D [E F]]]]]].
  + (* L2 makes one or several steps. *)
    exploit Extsimulation_plus; eauto. intros [[i2' [s2' [P Q]]] | [i2' [P [Q R]]]].
* (* L3 makes one or several steps *)
  exists (i2', i1'); exists s2'; exists f', t'. repeat (split; auto).
  exists s3'; auto.
* (* L3 makes no step *)
  exists (i2', i1'); exists s2; exists f', t'. repeat (split; auto).
  right; split. subst t'; apply star_refl. left. auto.
  exists s3'; auto.
+ (* L2 makes no step *)
  exists (i2, i1'); exists s2; exists f', t. repeat (split; auto).
  right; split. subst t; apply star_refl. right. auto.
  exists s3; auto.
  subst t; constructor.
- (* symbols *)
  intros. transitivity (Senv.public_symbol (symbolenv L2) id);
            [eapply Extfsim_public_preserved|eapply Injfsim_public_preserved]; eauto.
  Qed.

  (*
  Lemma injection_extension_composition:
    forward_injection L1 L2 get_mem1 get_mem2 ->
    forward_extension L2 L3 get_mem2 get_mem3 ->
    forward_injection L1 L3 get_mem1 get_mem3.
  Proof.
    intros S12 S23.
    inv S12; inv S23.
    econstructor.
    eapply injection_extension_composition'; eauto.
  Qed. *)
  
    Lemma extension_injection_composition:
    @fsim_properties_ext L1 L2 get_mem1 get_mem2 ->
    @fsim_properties_inj L2 L3 get_mem2 get_mem3 ->
    @fsim_properties_inj L1 L3 get_mem1 get_mem3.
  Proof.
    intros SIM12 SIM23.
    set (index13:= (Injindex SIM23 * Extindex SIM12)%type).
    set (order13:=  (lex_ord (clos_trans _ (Injorder SIM23)) (Extorder SIM12))).
    set (match_states13:=
           (fun (i: _ ) f (s1: state L1) (s3: state L3) =>
              exists s2, Extmatch_states SIM12 (snd i) s1 s2 /\ Injmatch_states SIM23 (fst i) f s2 s3) ).
    
    eapply Build_fsim_properties_inj with (Injindex:= index13) (Injorder:=order13) (Injmatch_states:=match_states13).
- (* well founded *)
  apply wf_lex_ord. apply wf_clos_trans.
  eapply Injfsim_order_wf; eauto. eapply Extfsim_order_wf; eauto.
- (* inject. *)
  intros ? ? ? ? [s2' [MATCH12 MATCH23]].
  eapply Mem.extends_inject_compose; [eapply SIM12| eapply SIM23]; eauto.
- (* Full *)
  intros ? ? ? ? [s2' [MATCH12 MATCH23]] b VALID.
  eapply SIM23; eauto.
  eapply Extfsim_match_meminj in MATCH12; eauto.
  inv MATCH12. unfold Mem.valid_block; rewrite <- mext_next; auto.
  
- (* initial states *)
  intros. exploit (Extfsim_match_initial_states SIM12); eauto. intros [i [s2 [A B]]].
  exploit (Injfsim_match_initial_states SIM23); eauto. intros [i' [f [s3 [C D]]]].
  exists (i', i); exists f; exists s3; split; auto. exists s2; auto.
- (* final states *)
  intros. destruct H as [s3 [A B]].
  eapply (Injfsim_match_final_states SIM23); eauto.
  eapply (Extfsim_match_final_states SIM12); eauto.
- (* simulation *)
    intros. destruct H0 as [s3 [A B]]. destruct i as [i2 i1]; simpl in *.
  exploit (Extfsim_simulation' SIM12); eauto.
  intros [[i1' [s3'[C D ]]] | [i1' [C [D E]]]]. 
  + (* L2 makes one or several steps. *)
    exploit Injsimulation_plus; eauto.
    intros [[i2' [f' [s2' [t' [P [Q [? ?]]]]]]] | [i2' [f' [P [Q [R ?]]]]]].
* (* L3 makes one or several steps *)
  exists (i2', i1'); exists s2'; exists f', t'. repeat (split; auto).
  exists s3'; repeat (split; auto).
* (* L3 makes no step *)
  exists (i2', i1'); exists s2; exists f', t. repeat (split; auto).
  right; split. subst t; apply star_refl. left. auto.
  exists s3'; (split; auto).
  subst t; constructor.
+ (* L2 makes no step *)
  exists (i2, i1'); exists s2; exists f, t. repeat (split; auto).
  right; split. subst t; apply star_refl. right. auto.
  exists s3; auto.
  subst t; constructor.
- (* symbols *)
  intros. transitivity (Senv.public_symbol (symbolenv L2) id);
            [eapply Injfsim_public_preserved|eapply Extfsim_public_preserved]; eauto.
  Qed.

 (* Lemma extension_injection_composition:
    forward_extension L1 L2 get_mem1 get_mem2 ->
    forward_injection L2 L3 get_mem2 get_mem3 ->
    forward_injection L1 L3 get_mem1 get_mem3.
  Proof.
    intros S12 S23.
    inv S12; inv S23.
    econstructor.
    eapply extension_injection_composition'; eauto.
  Qed. *)

  Lemma compose_inject_incr: forall f1 f2 f1' f2',
      inject_incr f1 f1' ->
      inject_incr f2 f2' ->
      inject_incr (compose_meminj f1 f2) (compose_meminj f1' f2').
  Proof.
    intros.
    unfold compose_meminj;
              intros b b' ofs AA.
    destruct (f1 b) eqn:F1; try solve[inv AA]; destruct p.
    eapply H in F1. rewrite F1.
    destruct (f2 b0) eqn:F2; inv AA; destruct p.
    eapply H0 in F2.
    rewrite F2.
    reflexivity.
  Qed.
  
  Lemma inject_trace_compose:
    forall f12 f23 t1 t2 t3,
      inject_trace f12 t1 t2 ->
      inject_trace f23 t2 t3 ->
      inject_trace (compose_meminj f12 f23) t1 t3.
  Proof.
  Admitted.

  
  Lemma injection_injection_composition:
    @fsim_properties_inj L1 L2 get_mem1 get_mem2->
    @fsim_properties_inj L2 L3 get_mem2 get_mem3 ->
    @fsim_properties_inj L1 L3 get_mem1 get_mem3.
    
    intros SIM12 SIM23.
    set (index13:= (Injindex SIM23 * Injindex SIM12)%type).
    set (order13:=  (lex_ord (clos_trans _ (Injorder SIM23)) (Injorder SIM12))).
    set (match_states13:=
           (fun (i: _ ) f (s1: state L1) (s3: state L3) =>
              exists s2 f12 f23,  Injmatch_states SIM12 (snd i) f12 s1 s2 /\ Injmatch_states SIM23 (fst i) f23 s2 s3
        /\ f = compose_meminj f12 f23)).
    eapply Build_fsim_properties_inj with (Injindex:= index13) (Injorder:=order13) (Injmatch_states:=match_states13).
- (* well founded *)
  apply wf_lex_ord. apply wf_clos_trans.
  eapply Injfsim_order_wf; eauto. eapply Injfsim_order_wf; eauto.
- (* inject. *)
  intros ? ? ? ? [s2' [f12 [f23 [MATCH12 [MATCH23 INJCOMP]]]]].
  subst.
  eapply Mem.inject_compose; [eapply SIM12| eapply SIM23]; eauto.
- (* Full *)
  intros ? ? ? s3 [s2 [f12 [f23 [MATCH12 [MATCH23 INJCOMP]]]]] b VALID.
  subst f.
  eapply SIM12 in VALID; try (exact MATCH12).
  destruct (f12 b) eqn:F12; auto. destruct p.
  unfold compose_meminj; rewrite F12.
  assert (VALID2 : Mem.valid_block (get_mem2 s2) b0).
  { eapply SIM12; eauto. }
  eapply SIM23 in VALID2; try (exact MATCH23).
  intros HH. apply VALID2. destruct (f23 b0); inversion HH; auto.
  destruct p. inversion HH.
- (* initial states *)
  intros. exploit (Injfsim_match_initial_states SIM12); eauto.
  intros [i [ f12 [s2 [A B]]]].
  exploit (Injfsim_match_initial_states SIM23); eauto. intros [i' [f23 [s3 [C D]]]].
  exists (i', i); exists (compose_meminj f12 f23); exists s3; split; auto. exists s2; auto.
  exists f12, f23; repeat (split; auto). 
- (* final states *)
  intros. destruct H as [s3 [ f12 [ f23 [A [B C]]]]].
  eapply (Injfsim_match_final_states SIM23); eauto.
  eapply (Injfsim_match_final_states SIM12); eauto.
- (* simulation *)
  intros. destruct H0 as [s3 [f12 [f23 [A [B C]]]]].
  destruct i as [i2 i1]; simpl in *.
  exploit (Injfsim_simulation' SIM12); eauto.
  intros [[i1' [s3'[ f' [t' [D [E [F G]]]]]]] | [i1' [f' [D [E [F G]]]]]].
  + (* L2 makes one or several steps. *)
    exploit Injsimulation_plus; eauto.
    intros [[i2' [f'' [s2' [t'' [P [? [? ?]]]]]]] | [i2' [f'' [P [Q [R SS]]]]]].
* (* L3 makes one or several steps *)
  exists (i2', i1').
  exists s2'; exists (compose_meminj f' f''), t''. repeat (split; auto).
  exists s3', f', f''; repeat (split; auto).
  subst f.
  eapply compose_inject_incr; eauto.
  
  eapply inject_trace_compose; eauto.
  
* (* L3 makes no step *)
  exists (i2', i1'); exists s2; exists (compose_meminj f' f''), t'. repeat (split; auto).
  right; split. subst t'; apply star_refl. left. auto.
  exists s3', f', f''; auto.
  repeat (split;auto).
  subst f.
  eapply compose_inject_incr; eauto.
  subst t'; inv G. constructor.
+ (* L2 makes no step *)
  exists (i2, i1'); exists s2; exists (compose_meminj f' f23), t. repeat (split; auto).
  right; split. subst t; apply star_refl. right. auto.
  exists s3, f', f23; auto.
  subst f.
  eapply compose_inject_incr; eauto.
  subst t; constructor.
- (* symbols *)
  intros. transitivity (Senv.public_symbol (symbolenv L2) id);
            [eapply Injfsim_public_preserved|eapply Injfsim_public_preserved]; eauto.
  Qed.

  
  (* Lemma injection_injection_composition:
    forward_injection L1 L2 get_mem1 get_mem2 ->
    forward_injection L2 L3 get_mem2 get_mem3 ->
    forward_injection L1 L3 get_mem1 get_mem3.
  Proof.
    intros S12 S23.
    inv S12; inv S23.
    econstructor.
    eapply injection_injection_composition'; eauto.
  Qed. *)
  
  End Composition.
