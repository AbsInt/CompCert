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

(** Tactics to reason about list inclusion. *)

(** This file (contributed by Laurence Rideau) defines a tactic [in_tac]
  to reason over list inclusion.  It expects goals of the following form:
<<
  id : In x l1
  ============================
     In x l2
>>
and succeeds if it can prove that [l1] is included in [l2].  
The lists [l1] and [l2] must belong to the following sub-language [L]
<<
  L ::= L++L | E | E::L
>>
The tactic uses no extra fact.

A second tactic, [incl_tac], handles goals of the form
<<
  =============================
    incl l1 l2
>>
*)

Require Import List.
Require Import Bool.
Require Import ArithRing.

Ltac all_app e :=
  match e with
  | cons ?x nil => constr:(cons x nil)
  | cons ?x ?tl => 
      let v := all_app tl in constr:(app (cons x nil) v)
  | app ?e1 ?e2 =>
    let v1 := all_app e1 with v2 := all_app e2 in
    constr:(app v1 v2)
  | _ => e
  end.

(** This data type, [flatten], [insert_bin], [sort_bin] and a few theorem
  are taken from the CoqArt book, chapt. 16. *)

Inductive bin : Type := node : bin->bin->bin | leaf : nat->bin.

Fixpoint flatten_aux (t fin:bin){struct t} : bin :=
  match t with
  | node t1 t2 => flatten_aux t1 (flatten_aux t2 fin)
  | x => node x fin
  end.

Fixpoint flatten (t:bin) : bin :=
  match t with
  | node t1 t2 => flatten_aux t1 (flatten t2)
  | x => x
  end.

Fixpoint nat_le_bool (n m:nat){struct m} : bool :=
  match n, m with
  | O, _ => true
  | S _, O => false
  | S n, S m => nat_le_bool n m
  end.

Fixpoint insert_bin (n:nat)(t:bin){struct t} : bin :=
  match t with
  | leaf m => 
    if nat_le_bool n m then
       node (leaf n)(leaf m)
    else
       node (leaf m)(leaf n)
  | node (leaf m) t' =>
    if nat_le_bool n m then node (leaf n) t else node (leaf m)(insert_bin n t')
  | t => node (leaf n) t
  end.

Fixpoint sort_bin (t:bin) : bin :=
  match t with
  | node (leaf n) t' => insert_bin n (sort_bin t')
  | t => t
  end.

Section assoc_eq.
 Variables (A : Type)(f : A->A->A).
 Hypothesis assoc : forall x y z:A, f x (f y z) = f (f x y) z.

 Fixpoint bin_A (l:list A)(def:A)(t:bin){struct t} : A :=
   match t with
   | node t1 t2 => f (bin_A l def t1)(bin_A l def t2)
   | leaf n => nth n l def
   end.

 Theorem flatten_aux_valid_A :
  forall (l:list A)(def:A)(t t':bin),
   f (bin_A l def t)(bin_A l def t') = bin_A l def (flatten_aux t t').
 Proof.
  intros l def t; elim t; simpl; auto.
  intros t1 IHt1 t2 IHt2 t';  rewrite <- IHt1; rewrite <- IHt2.
  symmetry; apply assoc.
 Qed.

 Theorem flatten_valid_A :
  forall (l:list A)(def:A)(t:bin),
    bin_A l def t = bin_A l def (flatten t).
 Proof.
  intros l def t; elim t; simpl; trivial.
  intros t1 IHt1 t2 IHt2; rewrite <- flatten_aux_valid_A; rewrite <- IHt2.
  trivial.
 Qed.

End assoc_eq.

Ltac compute_rank l n v :=
  match l with
  | (cons ?X1 ?X2) =>
    let tl := constr:X2 in
    match constr:(X1 = v) with
    | (?X1 = ?X1) => n
    | _ => compute_rank tl (S n) v
    end
  end.

Ltac term_list_app l v :=
  match v with
  | (app ?X1 ?X2) =>
    let l1 := term_list_app l X2 in term_list_app l1 X1
  | ?X1 => constr:(cons X1 l)
  end.

Ltac model_aux_app l v :=
  match v with
  | (app ?X1 ?X2) =>
    let r1 := model_aux_app l X1 with r2 := model_aux_app l X2 in
      constr:(node r1 r2)
  | ?X1 => let n := compute_rank l 0 X1 in constr:(leaf n)
  | _ => constr:(leaf 0)
  end.

Theorem In_permute_app_head :
  forall A:Type, forall r:A, forall x y l:list A,
   In r (x++y++l) -> In r (y++x++l).
intros A r x y l; generalize r; change (incl (x++y++l)(y++x++l)).
repeat rewrite ass_app; auto with datatypes.
Qed.

Theorem insert_bin_included : 
  forall x:nat, forall t2:bin,
  forall (A:Type) (r:A) (l:list (list A))(def:list A), 
     In r (bin_A (list A) (app (A:=A)) l def (insert_bin x t2)) ->
     In r (bin_A (list A) (app (A:=A)) l def (node (leaf x) t2)).
intros x t2; induction t2.
intros A r l def.
destruct t2_1 as [t2_11 t2_12|y].
simpl.
repeat rewrite app_ass.
auto.
simpl; repeat rewrite app_ass.
simpl; case (nat_le_bool x y); simpl.
auto.
intros H; apply In_permute_app_head.
elim in_app_or with (1:= H); clear H; intros H.
apply in_or_app; left; assumption.
apply in_or_app; right;apply (IHt2_2 A r l);assumption.
intros A r l def; simpl.
case (nat_le_bool x n); simpl.
auto.
intros H.
rewrite (app_nil_end (nth x l def)) in H.
rewrite (app_nil_end (nth n l def)).
apply In_permute_app_head; assumption.
Qed.

Theorem in_or_insert_bin :
  forall (n:nat) (t2:bin) (A:Type)(r:A)(l:list (list A)) (def:list A),
  In r (nth n l def) \/ In r (bin_A (list A)(app (A:=A)) l def t2) ->
  In r (bin_A (list A)(app (A:=A)) l def (insert_bin n t2)).
intros n t2 A r l def; induction t2.
destruct t2_1 as [t2_11 t2_12| y].
simpl; apply in_or_app.
simpl; case (nat_le_bool n y); simpl.
intros H.
apply in_or_app.
exact H.
intros [H|H].
apply in_or_app; right; apply IHt2_2; auto.
elim in_app_or with (1:= H);clear H; intros H; apply in_or_app; auto.
simpl; intros [H|H]; case (nat_le_bool n n0); simpl; apply in_or_app; auto.
Qed.

Theorem sort_included :
  forall t:bin, forall (A:Type)(r:A)(l:list(list A))(def:list A),
    In r (bin_A (list A) (app (A:=A)) l def (sort_bin t)) ->
    In r (bin_A (list A) (app (A:=A)) l def t).
induction t.
destruct t1.
simpl;intros; assumption.
intros A r l def H; simpl in H; apply insert_bin_included.
generalize (insert_bin_included _ _ _ _ _ _ H); clear H; intros H.
simpl in H.
elim in_app_or with (1 := H);clear H; intros H;
apply in_or_insert_bin; auto.
simpl;intros;assumption.
Qed.

Theorem sort_included2 :
  forall t:bin, forall (A:Type)(r:A)(l:list(list A))(def:list A),
    In r (bin_A (list A) (app (A:=A)) l def t) ->
    In r (bin_A (list A) (app (A:=A)) l def (sort_bin t)).
induction t.
destruct t1.
simpl; intros; assumption.
intros A r l def H; simpl in H.
simpl; apply in_or_insert_bin.
elim in_app_or with (1:= H); auto.
simpl; auto.
Qed.

Theorem in_remove_head :
  forall (A:Type)(x:A)(l1 l2 l3:list A),
  In x (l1++l2) -> (In x l2 -> In x l3) -> In x (l1++l3).
intros A x l1 l2 l3 H H1.
elim in_app_or with (1:= H);clear H; intros H; apply in_or_app; auto.
Qed.

Fixpoint check_all_leaves (n:nat)(t:bin) {struct t} : bool :=
  match t with
    leaf n1 => nateq n n1
  | node t1 t2 => andb (check_all_leaves n t1)(check_all_leaves n t2)
  end.

Fixpoint remove_all_leaves (n:nat)(t:bin){struct t} : bin :=
  match t with
    leaf n => leaf n
  | node (leaf n1) t2 =>
    if nateq n n1 then remove_all_leaves n t2 else t
  | _ => t
  end.

Fixpoint test_inclusion (t1 t2:bin) {struct t1} : bool :=
  match t1 with
    leaf n => check_all_leaves n t2
  | node (leaf n1) t1' =>
     check_all_leaves n1 t2 || test_inclusion t1' (remove_all_leaves n1 t2)
  | _ => false
  end.

Theorem check_all_leaves_sound :
  forall x t2,
    check_all_leaves x t2 = true ->
    forall (A:Type)(r:A)(l:list(list A))(def:list A),
    In r (bin_A (list A) (app (A:=A)) l def t2) ->
    In r (nth x l def).
intros x t2; induction t2; simpl.
destruct (check_all_leaves x t2_1);
destruct (check_all_leaves x t2_2); simpl; intros Heq; try discriminate.
intros A r l def H; elim in_app_or with (1:= H); clear H; intros H; auto.
intros Heq A r l def; rewrite (nateq_prop x n); auto.
rewrite Heq; unfold Is_true; auto.
Qed.

Theorem remove_all_leaves_sound :
  forall x t2,
  forall (A:Type)(r:A)(l:list(list A))(def:list A),
  In r (bin_A (list A) (app(A:=A)) l def t2) ->
  In r (bin_A (list A) (app(A:=A)) l def (remove_all_leaves x t2)) \/
  In r (nth x l def).
intros x t2; induction t2; simpl.
destruct t2_1.
simpl; auto.
intros A r l def.
generalize (refl_equal (nateq x n)); pattern (nateq x n) at -1;
 case (nateq x n); simpl; auto.
intros Heq_nateq.
assert (Heq_xn : x=n).
apply nateq_prop; rewrite Heq_nateq;unfold Is_true;auto.
rewrite Heq_xn.
intros H; elim in_app_or with (1:= H); auto.
clear H; intros H.
rewrite Heq_xn in IHt2_2; auto.
auto.
Qed.

Theorem test_inclusion_sound :
  forall t1 t2:bin,
  test_inclusion t1 t2 = true ->
  forall (A:Type)(r:A)(l:list(list A))(def:list A),
  In r (bin_A (list A)(app(A:=A)) l def t2) ->
  In r (bin_A (list A)(app(A:=A)) l def t1).
intros t1; induction t1.
destruct t1_1 as [t1_11 t1_12|x].
simpl; intros; discriminate.
simpl; intros t2 Heq A r l def H.
assert 
 (check_all_leaves x t2 = true \/ 
  test_inclusion t1_2 (remove_all_leaves x t2) = true).
destruct (check_all_leaves x t2);
destruct (test_inclusion t1_2 (remove_all_leaves x t2));
simpl in Heq; try discriminate Heq; auto.
elim H0; clear H0; intros H0.
apply in_or_app; left; apply check_all_leaves_sound with (1:= H0); auto.
elim remove_all_leaves_sound with (x:=x)(1:= H); intros H'.
apply in_or_app; right; apply IHt1_2 with (1:= H0); auto.
apply in_or_app; auto.
simpl; apply check_all_leaves_sound.
Qed.

Theorem inclusion_theorem :
  forall t1 t2 : bin,
    test_inclusion (sort_bin (flatten t1)) (sort_bin (flatten t2)) = true ->
    forall (A:Type)(r:A)(l:list(list A))(def:list A),
    In r (bin_A (list A) (app(A:=A)) l def t2) ->
    In r (bin_A (list A) (app(A:=A)) l def t1).
intros t1 t2 Heq A r l def H.
rewrite flatten_valid_A with (t:= t1)(1:= (ass_app (A:= A))).
apply sort_included.
apply test_inclusion_sound with (t2 := sort_bin (flatten t2)).
assumption.
apply sort_included2.
rewrite <- flatten_valid_A with (1:= (ass_app (A:= A))).
assumption.
Qed.

Ltac in_tac :=
  match goal with
  | id : In ?x nil |- _ => elim id
  | id : In ?x ?l1 |- In ?x ?l2 =>
    let t := type of x in
    let v1 := all_app l1 in
    let v2 := all_app l2 in
    (let l := term_list_app (nil (A:=list t)) v2 in
     let term1 := model_aux_app l v1 with
         term2 := model_aux_app l v2 in
        (change (In x (bin_A (list t) (app(A:=t)) l (nil(A:=t)) term2));
        apply inclusion_theorem with (t2:= term1);[apply refl_equal|exact id]))
  end.

Ltac incl_tac :=
  match goal with
  |- incl _ _ => intro; intro; in_tac
  end.
   
(* Usage examples.

Theorem ex1 : forall x y z:nat, forall l1 l2 : list nat,
   In x (y::l1++l2) -> In x (l2++z::l1++(y::nil)).
intros.
in_tac.
Qed.

Fixpoint mklist (f:nat->nat)(n:nat){struct n} : list nat :=
 match n with 0 => nil | S p => mklist f p++(f p::nil) end.

(* At the time of writing these lines, this example takes about 5 seconds
     for 40 elements and 22 seconds for 60 elements.
   A variant to the example is to replace mklist f p++(f p::nil) with
   f p::mklist f p, in this case the time is 6 seconds for 40 elements and
   35 seconds for 60 elements. *)

Theorem ex2 : 
  forall x : nat, In x (mklist (fun y => y) 40) ->
     In x (mklist (fun y => (40 - 1) - y) 40).
lazy beta iota zeta delta [mklist minus].
intros.
in_tac.
Qed.

(* The tactic could be made more efficient by using binary trees and
   numbers of type positive instead of lists and natural numbers. *)

*)
