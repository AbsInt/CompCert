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

(** Relational specification of expression simplification. *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import AST.
Require Import Csyntax.
Require Import Clight.
Require Import SimplExpr.

Section SPEC.

Local Open Scope gensym_monad_scope.

(** * Relational specification of the translation. *)

(** ** Translation of expressions *)

(** This specification covers:
- all cases of [transl_lvalue] and [transl_rvalue];
- two additional cases for [C.Eparen], so that reductions of [C.Econdition]
  expressions are properly tracked;
- three additional cases allowing [C.Eval v] C expressions to match
  any Clight expression [a] that evaluates to [v] in any environment
  matching the given temporary environment [le].
*)

Definition final (dst: purpose) (a: expr) : list statement :=
  match dst with
  | For_val => nil
  | For_effects => nil
  | For_test s1 s2 => makeif a s1 s2 :: nil
  end.

Inductive tr_expr: temp_env -> purpose -> C.expr -> list statement -> expr -> list ident -> Prop :=
  | tr_var: forall le dst id ty tmp,
      tr_expr le dst (C.Evar id ty)
              (final dst (Evar id ty)) (Evar id ty) tmp
  | tr_deref: forall le dst e1 ty sl1 a1 tmp,
      tr_expr le For_val e1 sl1 a1 tmp ->
      tr_expr le dst (C.Ederef e1 ty)
              (sl1 ++ final dst (Ederef a1 ty)) (Ederef a1 ty) tmp
  | tr_field: forall le dst e1 f ty sl1 a1 tmp,
      tr_expr le For_val e1 sl1 a1 tmp ->
      tr_expr le dst (C.Efield e1 f ty)
              (sl1 ++ final dst (Efield a1 f ty)) (Efield a1 f ty) tmp
  | tr_val_effect: forall le v ty any tmp,
      tr_expr le For_effects (C.Eval v ty) nil any tmp
  | tr_val_value: forall le v ty a tmp,
      typeof a = ty ->
      (forall tge e le' m,
         (forall id, In id tmp -> le'!id = le!id) ->
         eval_expr tge e le' m a v) ->
      tr_expr le For_val (C.Eval v ty) 
                           nil a tmp
  | tr_val_test: forall le s1 s2 v ty a any tmp,
      typeof a = ty ->
      (forall tge e le' m,
         (forall id, In id tmp -> le'!id = le!id) ->
         eval_expr tge e le' m a v) ->
      tr_expr le (For_test s1 s2) (C.Eval v ty) 
                   (makeif a s1 s2 :: nil) any tmp
  | tr_sizeof: forall le dst ty' ty tmp,
      tr_expr le dst (C.Esizeof ty' ty)
                   (final dst (Esizeof ty' ty))
                   (Esizeof ty' ty) tmp
  | tr_valof: forall le dst e1 ty tmp sl1 a1,
      tr_expr le For_val e1 sl1 a1 tmp ->
      tr_expr le dst (C.Evalof e1 ty)
                   (sl1 ++ final dst a1)
                   a1 tmp
  | tr_addrof: forall le dst e1 ty tmp sl1 a1,
      tr_expr le For_val e1 sl1 a1 tmp ->
      tr_expr le dst (C.Eaddrof e1 ty) 
                   (sl1 ++ final dst (Eaddrof a1 ty))
                   (Eaddrof a1 ty) tmp
  | tr_unop: forall le dst op e1 ty tmp sl1 a1,
      tr_expr le For_val e1 sl1 a1 tmp ->
      tr_expr le dst (C.Eunop op e1 ty)
                   (sl1 ++ final dst (Eunop op a1 ty))
                   (Eunop op a1 ty) tmp
  | tr_binop: forall le dst op e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_val e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 -> incl tmp1 tmp -> incl tmp2 tmp ->
      tr_expr le dst (C.Ebinop op e1 e2 ty)
                   (sl1 ++ sl2 ++ final dst (Ebinop op a1 a2 ty))
                   (Ebinop op a1 a2 ty) tmp
  | tr_cast: forall le dst e1 ty sl1 a1 tmp,
      tr_expr le For_val e1 sl1 a1 tmp ->
      tr_expr le dst (C.Ecast e1 ty)
                   (sl1 ++ final dst (Ecast a1 ty))
                   (Ecast a1 ty) tmp
  | tr_condition_val: forall le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_val e2 sl2 a2 tmp2 ->
      tr_expr le For_val e3 sl3 a3 tmp3 ->
      list_disjoint tmp1 tmp2 ->
      list_disjoint tmp1 tmp3 ->
      incl tmp1 tmp -> incl tmp2 tmp ->  incl tmp3 tmp ->
      In t tmp -> ~In t tmp1 ->
      tr_expr le For_val (C.Econdition e1 e2 e3 ty)
                      (sl1 ++ makeif a1 
                                (Ssequence (makeseq sl2) (Sset t a2))
                                (Ssequence (makeseq sl3) (Sset t a3)) :: nil)
                      (Etempvar t ty) tmp
  | tr_condition_effects: forall le dst e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp,
      dst <> For_val ->
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le dst e2 sl2 a2 tmp2 ->
      tr_expr le dst e3 sl3 a3 tmp3 ->
      list_disjoint tmp1 tmp2 ->
      list_disjoint tmp1 tmp3 ->
      incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp ->
      tr_expr le dst (C.Econdition e1 e2 e3 ty)
                       (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil)
                       any tmp
  | tr_assign_effects: forall le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_val e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->  
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_expr le For_effects (C.Eassign e1 e2 ty)
                      (sl1 ++ sl2 ++ Sassign a1 a2 :: nil)
                      any tmp
  | tr_assign_val: forall le dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 t tmp ty1 ty2,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_val e2 sl2 a2 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      list_disjoint tmp1 tmp2 ->  
      In t tmp -> ~In t tmp1 -> ~In t tmp2 ->
      ty1 = C.typeof e1 ->
      ty2 = C.typeof e2 ->
      tr_expr le dst (C.Eassign e1 e2 ty)
                   (sl1 ++ sl2 ++ 
                    Sset t a2 ::
                    Sassign a1 (Etempvar t ty2) ::
                    final dst (Ecast (Etempvar t ty2) ty1))
                   (Ecast (Etempvar t ty2) ty1) tmp
  | tr_assignop_effects: forall le op e1 e2 tyres ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_val e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->  
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_expr le For_effects (C.Eassignop op e1 e2 tyres ty)
                      (sl1 ++ sl2 ++ Sassign a1 (Ebinop op a1 a2 tyres) :: nil)
                      any tmp
  | tr_assignop_val: forall le dst op e1 e2 tyres ty sl1 a1 tmp1 sl2 a2 tmp2 t tmp ty1,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_val e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->  
      incl tmp1 tmp -> incl tmp2 tmp ->
      In t tmp -> ~In t tmp1 -> ~In t tmp2 ->
      ty1 = C.typeof e1 ->
      tr_expr le dst (C.Eassignop op e1 e2 tyres ty)
                   (sl1 ++ sl2 ++ 
                    Sset t (Ebinop op a1 a2 tyres) ::
                    Sassign a1 (Etempvar t tyres) ::
                    final dst (Ecast (Etempvar t tyres) ty1))
                   (Ecast (Etempvar t tyres) ty1) tmp
  | tr_postincr_effects: forall le id e1 ty sl1 a1 tmp any,
      tr_expr le For_val e1 sl1 a1 tmp ->
      tr_expr le For_effects (C.Epostincr id e1 ty)
                      (sl1 ++ Sassign a1 (transl_incrdecr id a1 (C.typeof e1)) :: nil)
                      any tmp
  | tr_postincr_val: forall le dst id e1 ty sl1 a1 tmp1 t ty1 tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      incl tmp1 tmp -> In t tmp -> ~In t tmp1 ->
      ty1 = C.typeof e1 ->
      tr_expr le dst (C.Epostincr id e1 ty)
                   (sl1 ++ Sset t a1 ::
                    Sassign a1 (transl_incrdecr id (Etempvar t ty1) ty1) ::
                    final dst (Etempvar t ty1))
                   (Etempvar t ty1) tmp
  | tr_comma: forall le dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp,
      tr_expr le For_effects e1 sl1 a1 tmp1 ->
      tr_expr le dst e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->  
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_expr le dst (C.Ecomma e1 e2 ty) (sl1 ++ sl2) a2 tmp
  | tr_call_effects: forall le e1 el2 ty sl1 a1 tmp1 sl2 al2 tmp2 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_exprlist le el2 sl2 al2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_expr le For_effects (C.Ecall e1 el2 ty)
                   (sl1 ++ sl2 ++ Scall None a1 al2 :: nil)
                   any tmp
  | tr_call_val: forall le dst e1 el2 ty sl1 a1 tmp1 sl2 al2 tmp2 t tmp,
      dst <> For_effects ->
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_exprlist le el2 sl2 al2 tmp2 ->
      list_disjoint tmp1 tmp2 -> In t tmp ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_expr le dst (C.Ecall e1 el2 ty)
                   (sl1 ++ sl2 ++ Scall (Some t) a1 al2 :: final dst (Etempvar t ty))
                   (Etempvar t ty) tmp
  | tr_paren_val: forall le e1 ty sl1 a1 tmp1 t tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      incl tmp1 tmp -> In t tmp -> 
      tr_expr le For_val (C.Eparen e1 ty)
                       (sl1 ++ Sset t a1 :: nil)
                       (Etempvar t ty) tmp
  | tr_paren_effects: forall le dst e1 ty sl1 a1 tmp any,
      dst <> For_val ->
      tr_expr le dst e1 sl1 a1 tmp ->
      tr_expr le dst (C.Eparen e1 ty) sl1 any tmp

with tr_exprlist: temp_env -> C.exprlist -> list statement -> list expr -> list ident -> Prop :=
  | tr_nil: forall le tmp,
      tr_exprlist le C.Enil nil nil tmp
  | tr_cons: forall le e1 el2 sl1 a1 tmp1 sl2 al2 tmp2 tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_exprlist le el2 sl2 al2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_exprlist le (C.Econs e1 el2) (sl1 ++ sl2) (a1 :: al2) tmp.

Scheme tr_expr_ind2 := Minimality for tr_expr Sort Prop
  with tr_exprlist_ind2 := Minimality for tr_exprlist Sort Prop.
Combined Scheme tr_expr_exprlist from tr_expr_ind2, tr_exprlist_ind2.

(** Useful invariance properties. *)

Lemma tr_expr_invariant:
  forall le dst r sl a tmps, tr_expr le dst r sl a tmps ->
  forall le', (forall x, In x tmps -> le'!x = le!x) ->
  tr_expr le' dst r sl a tmps
with tr_exprlist_invariant:
  forall le rl sl al tmps, tr_exprlist le rl sl al tmps ->
  forall le', (forall x, In x tmps -> le'!x = le!x) ->
  tr_exprlist le' rl sl al tmps.
Proof.
  induction 1; intros; econstructor; eauto.
    intros. apply H0. intros. transitivity (le'!id); auto.
    intros. apply H0. intros. transitivity (le'!id); auto.
  induction 1; intros; econstructor; eauto.
Qed.

Lemma tr_expr_monotone:
  forall le dst r sl a tmps, tr_expr le dst r sl a tmps ->
  forall tmps', incl tmps tmps' -> tr_expr le dst r sl a tmps'
with tr_exprlist_monotone:
  forall le rl sl al tmps, tr_exprlist le rl sl al tmps ->
  forall tmps', incl tmps tmps' -> tr_exprlist le rl sl al tmps'.
Proof.
  induction 1; intros; econstructor; unfold incl in *; eauto.
  induction 1; intros; econstructor; unfold incl in *; eauto.
Qed.

(** ** Top-level translation *)

(** The "top-level" translation is equivalent to [tr_expr] above
  for source terms.  It brings additional flexibility in the matching
  between C values and Cminor expressions: in the case of
  [tr_expr], the Cminor expression must not depend on memory,
  while in the case of [tr_top] it can depend on the current memory
  state.  This special case is extended to values occurring under
  one or several [C.Eparen]. *)

Section TR_TOP.

Variable ge: genv.
Variable e: env.
Variable le: temp_env.
Variable m: mem.

Inductive tr_top: purpose -> C.expr -> list statement -> expr -> list ident -> Prop :=
  | tr_top_val_val: forall v ty a tmp,
      typeof a = ty -> eval_expr ge e le m a v ->
      tr_top For_val (C.Eval v ty) nil a tmp
  | tr_top_val_test: forall s1 s2 v ty a any tmp,
      typeof a = ty -> eval_expr ge e le m a v ->
      tr_top (For_test s1 s2) (C.Eval v ty) (makeif a s1 s2 :: nil) any tmp
  | tr_top_base: forall dst r sl a tmp,
      tr_expr le dst r sl a tmp ->
      tr_top dst r sl a tmp
  | tr_top_paren_test: forall s1 s2 r ty sl a tmp,
      tr_top (For_test s1 s2) r sl a tmp ->
      tr_top (For_test s1 s2) (C.Eparen r ty) sl a tmp.

End TR_TOP.

(** ** Translation of statements *)

Inductive tr_expression: C.expr -> statement -> expr -> Prop :=
  | tr_expression_intro: forall r sl a tmps,
      (forall ge e le m, tr_top ge e le m For_val r sl a tmps) ->
      tr_expression r (makeseq sl) a.

Inductive tr_expr_stmt: C.expr -> statement -> Prop :=
  | tr_expr_stmt_intro: forall r sl a tmps,
      (forall ge e le m, tr_top ge e le m For_effects r sl a tmps) ->
      tr_expr_stmt r (makeseq sl).

Inductive tr_if: C.expr -> statement -> statement -> statement -> Prop :=
  | tr_if_intro: forall r s1 s2 sl a tmps,
      (forall ge e le m, tr_top ge e le m (For_test s1 s2) r sl a tmps) ->
      tr_if r s1 s2 (makeseq sl).

Inductive tr_stmt: C.statement -> statement -> Prop :=
  | tr_skip:
      tr_stmt C.Sskip Sskip
  | tr_do: forall r s,
      tr_expr_stmt r s ->
      tr_stmt (C.Sdo r) s
  | tr_seq: forall s1 s2 ts1 ts2,
      tr_stmt s1 ts1 -> tr_stmt s2 ts2 ->
      tr_stmt (C.Ssequence s1 s2) (Ssequence ts1 ts2)
  | tr_ifthenelse_big: forall r s1 s2 s' a ts1 ts2,
      tr_expression r s' a ->
      tr_stmt s1 ts1 -> tr_stmt s2 ts2 ->
      tr_stmt (C.Sifthenelse r s1 s2) (Ssequence s' (Sifthenelse a ts1 ts2))
  | tr_ifthenelse_small: forall r s1 s2 ts1 ts2 ts,
      tr_stmt s1 ts1 -> tr_stmt s2 ts2 ->
      small_stmt ts1 = true -> small_stmt ts2 = true ->
      tr_if r ts1 ts2 ts ->
      tr_stmt (C.Sifthenelse r s1 s2) ts
  | tr_while: forall r s1 s' ts1,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s1 ts1 ->
      tr_stmt (C.Swhile r s1)
              (Swhile expr_true (Ssequence s' ts1))
  | tr_dowhile: forall r s1 s' ts1,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s1 ts1 ->
      tr_stmt (C.Sdowhile r s1)
              (Sfor' expr_true s' ts1)
  | tr_for_1: forall r s3 s4 s' ts3 ts4,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s3 ts3 ->
      tr_stmt s4 ts4 ->
      tr_stmt (C.Sfor C.Sskip r s3 s4)
              (Sfor' expr_true ts3 (Ssequence s' ts4))
  | tr_for_2: forall s1 r s3 s4 s' ts1 ts3 ts4,
      tr_if r Sskip Sbreak s' ->
      s1 <> C.Sskip ->
      tr_stmt s1 ts1 ->
      tr_stmt s3 ts3 ->
      tr_stmt s4 ts4 ->
      tr_stmt (C.Sfor s1 r s3 s4)
              (Ssequence ts1 (Sfor' expr_true ts3 (Ssequence s' ts4)))
  | tr_break:
      tr_stmt C.Sbreak Sbreak
  | tr_continue:
      tr_stmt C.Scontinue Scontinue
  | tr_return_none:
      tr_stmt (C.Sreturn None) (Sreturn None)
  | tr_return_some: forall r s' a,
      tr_expression r s' a ->
      tr_stmt (C.Sreturn (Some r)) (Ssequence s' (Sreturn (Some a)))
  | tr_switch: forall r ls s' a tls,
      tr_expression r s' a ->
      tr_lblstmts ls tls ->
      tr_stmt (C.Sswitch r ls) (Ssequence s' (Sswitch a tls))
  | tr_label: forall lbl s ts,
      tr_stmt s ts ->
      tr_stmt (C.Slabel lbl s) (Slabel lbl ts)
  | tr_goto: forall lbl,
      tr_stmt (C.Sgoto lbl) (Sgoto lbl)

with tr_lblstmts: C.labeled_statements -> labeled_statements -> Prop :=
  | tr_default: forall s ts,
      tr_stmt s ts ->
      tr_lblstmts (C.LSdefault s) (LSdefault ts)
  | tr_case: forall n s ls ts tls,
      tr_stmt s ts ->
      tr_lblstmts ls tls ->
      tr_lblstmts (C.LScase n s ls) (LScase n ts tls).

(** * Correctness proof with respect to the specification. *)

(** ** Properties of the monad *)

Remark bind_inversion:
  forall (A B: Type) (f: mon A) (g: A -> mon B) (y: B) (z1 z3: generator) I,
  bind f g z1 = Res y z3 I ->
  exists x, exists z2, exists I1, exists I2,
  f z1 = Res x z2 I1 /\ g x z2 = Res y z3 I2.
Proof.
  intros until I. unfold bind. destruct (f z1).
  congruence.
  caseEq (g a g'); intros; inv H0.
  econstructor; econstructor; econstructor; econstructor; eauto. 
Qed.

Remark bind2_inversion:
  forall (A B C: Type) (f: mon (A*B)) (g: A -> B -> mon C) (y: C) (z1 z3: generator) I,
  bind2 f g z1 = Res y z3 I ->
  exists x1, exists x2, exists z2, exists I1, exists I2,
  f z1 = Res (x1,x2) z2 I1 /\ g x1 x2 z2 = Res y z3 I2.
Proof.
  unfold bind2. intros. 
  exploit bind_inversion; eauto. 
  intros [[x1 x2] [z2 [I1 [I2 [P Q]]]]]. simpl in Q. 
  exists x1; exists x2; exists z2; exists I1; exists I2; auto.
Qed.

Ltac monadInv1 H :=
  match type of H with
  | (Res _ _ _ = Res _ _ _) =>
      inversion H; clear H; try subst
  | (@ret _ _ _ = Res _ _ _) =>
      inversion H; clear H; try subst
  | (@error _ _ _ = Res _ _ _) =>
      inversion H
  | (bind ?F ?G ?Z = Res ?X ?Z' ?I) =>
      let x := fresh "x" in (
      let z := fresh "z" in (
      let I1 := fresh "I" in (
      let I2 := fresh "I" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion _ _ F G X Z Z' I H) as [x [z [I1 [I2 [EQ1 EQ2]]]]];
      clear H;
      try (monadInv1 EQ2)))))))
   | (bind2 ?F ?G ?Z = Res ?X ?Z' ?I) =>
      let x := fresh "x" in (
      let y := fresh "y" in (
      let z := fresh "z" in (
      let I1 := fresh "I" in (
      let I2 := fresh "I" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion _ _ _ F G X Z Z' I H) as [x [y [z [I1 [I2 [EQ1 EQ2]]]]]];
      clear H;
      try (monadInv1 EQ2))))))))
 end.

Ltac monadInv H :=
  match type of H with
  | (@ret _ _ _ = Res _ _ _) => monadInv1 H
  | (@error _ _ _ = Res _ _ _) => monadInv1 H
  | (bind ?F ?G ?Z = Res ?X ?Z' ?I) => monadInv1 H
  | (bind2 ?F ?G ?Z = Res ?X ?Z' ?I) => monadInv1 H
  | (?F _ _ _ _ _ _ _ _ = Res _ _ _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  end.

(** ** Freshness and separation properties. *)

Definition within (id: ident) (g1 g2: generator) : Prop :=
  Ple (gen_next g1) id /\ Plt id (gen_next g2).

Lemma gensym_within:
  forall ty g1 id g2 I,
  gensym ty g1 = Res id g2 I -> within id g1 g2.
Proof.
  intros. monadInv H. split. apply Ple_refl. apply Plt_succ.
Qed.

Lemma within_widen:
  forall id g1 g2 g1' g2',
  within id g1 g2 ->
  Ple (gen_next g1') (gen_next g1) ->
  Ple (gen_next g2) (gen_next g2') ->
  within id g1' g2'.
Proof.
  intros. destruct H. split. 
  eapply Ple_trans; eauto.
  unfold Plt, Ple in *. omega. 
Qed.

Definition contained (l: list ident) (g1 g2: generator) : Prop :=
  forall id, In id l -> within id g1 g2.

Lemma contained_nil:
  forall g1 g2, contained nil g1 g2.
Proof.
  intros; red; intros; contradiction.
Qed.

Lemma contained_widen:
  forall l g1 g2 g1' g2',
  contained l g1 g2 ->
  Ple (gen_next g1') (gen_next g1) ->
  Ple (gen_next g2) (gen_next g2') ->
  contained l g1' g2'.
Proof.
  intros; red; intros. eapply within_widen; eauto. 
Qed.

Lemma contained_cons:
  forall id l g1 g2,
  within id g1 g2 -> contained l g1 g2 -> contained (id :: l) g1 g2.
Proof.
  intros; red; intros. simpl in H1; destruct H1. subst id0. auto. auto. 
Qed.

Lemma contained_app:
  forall l1 l2 g1 g2,
  contained l1 g1 g2 -> contained l2 g1 g2 -> contained (l1 ++ l2) g1 g2.
Proof.
  intros; red; intros. destruct (in_app_or _ _ _ H1); auto.
Qed.

Lemma contained_disjoint:
  forall g1 l1 g2 l2 g3,
  contained l1 g1 g2 -> contained l2 g2 g3 -> list_disjoint l1 l2.
Proof.
  intros; red; intros. red; intro; subst y. 
  exploit H; eauto. intros [A B]. exploit H0; eauto. intros [C D].
  elim (Plt_strict x). apply Plt_Ple_trans with (gen_next g2); auto.
Qed.

Lemma contained_notin:
  forall g1 l g2 id g3,
  contained l g1 g2 -> within id g2 g3 -> ~In id l.
Proof.
  intros; red; intros. exploit H; eauto. intros [C D]. destruct H0 as [A B].
  elim (Plt_strict id). apply Plt_Ple_trans with (gen_next g2); auto.
Qed.

Hint Resolve gensym_within within_widen contained_widen
             contained_cons contained_app contained_disjoint
             contained_notin contained_nil 
             incl_refl incl_tl incl_app incl_appl incl_appr
             in_eq in_cons
             Ple_trans Ple_refl: gensym.

(** ** Correctness of the translation functions *)

Lemma finish_meets_spec_1:
  forall dst sl a sl' a',
  finish dst sl a = (sl', a') -> sl' = sl ++ final dst a.
Proof.
  intros. destruct dst; simpl in *; inv H. apply app_nil_end. apply app_nil_end. auto.
Qed.

Lemma finish_meets_spec_2:
  forall dst sl a sl' a',
  finish dst sl a = (sl', a') -> a' = a.
Proof.
  intros. destruct dst; simpl in *; inv H; auto.
Qed.

Ltac UseFinish :=
  match goal with
  | [ H: finish _ _ _ = (_, _) |- _ ] =>
      try (rewrite (finish_meets_spec_2 _ _ _ _ _ H));
      try (rewrite (finish_meets_spec_1 _ _ _ _ _ H));
      repeat rewrite app_ass
  end.

Scheme expr_ind2 := Induction for C.expr Sort Prop
  with exprlist_ind2 := Induction for C.exprlist Sort Prop.
Combined Scheme expr_exprlist_ind from expr_ind2, exprlist_ind2.

Lemma transl_meets_spec:
   (forall r dst g sl a g' I,
    transl_expr dst r g = Res (sl, a) g' I ->
    exists tmps, (forall le, tr_expr le dst r sl a tmps) /\ contained tmps g g')
  /\
   (forall rl g sl al g' I,
    transl_exprlist rl g = Res (sl, al) g' I ->
    exists tmps, (forall le, tr_exprlist le rl sl al tmps) /\ contained tmps g g').
Proof.
  apply expr_exprlist_ind; intros.
(* val *)
  simpl in H. destruct v; monadInv H; exists (@nil ident); split; auto with gensym.
Opaque makeif.
  intros. destruct dst; simpl in H1; inv H1. 
    constructor. auto. intros; constructor.
    constructor.
    constructor. auto. intros; constructor.
  intros. destruct dst; simpl in H1; inv H1. 
    constructor. auto. intros; constructor.
    constructor.
    constructor. auto. intros; constructor.
(* var *)
  monadInv H; econstructor; split; auto with gensym. UseFinish. constructor.
(* field *)
  monadInv H0. exploit H; eauto. intros [tmp [A B]]. UseFinish. 
  econstructor; split; eauto. constructor; auto. 
(* valof *)
  monadInv H0. exploit H; eauto. intros [tmp [A B]]. UseFinish.  
  econstructor; split.
  econstructor; eauto. eauto with gensym.
(* deref *)
  monadInv H0. exploit H; eauto. intros [tmp [A B]]. UseFinish. 
  econstructor; split; eauto. constructor; auto. 
(* addrof *)
  monadInv H0. exploit H; eauto. intros [tmp [A B]]. UseFinish. 
  econstructor; split; eauto. econstructor; eauto.
(* unop *)
  monadInv H0. exploit H; eauto. intros [tmp [A B]]. UseFinish. 
  econstructor; split; eauto. constructor; auto. 
(* binop *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  exploit H0; eauto. intros [tmp2 [C D]]. UseFinish.
  exists (tmp1 ++ tmp2); split. 
  econstructor; eauto with gensym.
  eauto with gensym.
(* cast *)
  monadInv H0. exploit H; eauto. intros [tmp [A B]]. UseFinish. 
  econstructor; split; eauto. constructor; auto.
(* condition *) 
  monadInv H2. exploit H; eauto. intros [tmp1 [A B]].
  exploit H0; eauto. intros [tmp2 [C D]].
  exploit H1; eauto. intros [tmp3 [E F]].
  destruct dst; monadInv EQ3.
  (* for value *)
  exists (x2 :: tmp1 ++ tmp2 ++ tmp3); split. 
  econstructor; eauto with gensym.
  apply contained_cons. eauto with gensym. 
  apply contained_app. eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for effects *)
  exists (tmp1 ++ tmp2 ++ tmp3); split.
  econstructor; eauto with gensym. congruence.
  apply contained_app; eauto with gensym.
  (* for test *)
  exists (tmp1 ++ tmp2 ++ tmp3); split.
  econstructor; eauto with gensym. congruence.
  apply contained_app; eauto with gensym.
(* sizeof *)
  monadInv H. UseFinish.
  exists (@nil ident); split; auto with gensym. constructor.
(* assign *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  exploit H0; eauto. intros [tmp2 [C D]].
  destruct dst; monadInv EQ2.
  (* for value *)
  exists (x1 :: tmp1 ++ tmp2); split. 
  intros. eapply tr_assign_val with (dst := For_val); eauto with gensym.
  apply contained_cons. eauto with gensym. 
  apply contained_app; eauto with gensym.
  (* for effects *)
  exists (tmp1 ++ tmp2); split. 
  econstructor; eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for test *)
  exists (x1 :: tmp1 ++ tmp2); split.
  repeat rewrite app_ass. simpl. 
  intros. eapply tr_assign_val with (dst := For_test s1 s2); eauto with gensym.
  apply contained_cons. eauto with gensym. 
  apply contained_app; eauto with gensym.
(* assignop *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  exploit H0; eauto. intros [tmp2 [C D]].
  destruct dst; monadInv EQ2.
  (* for value *)
  exists (x1 :: tmp1 ++ tmp2); split.
  intros. eapply tr_assignop_val with (dst := For_val); eauto with gensym.
  apply contained_cons. eauto with gensym. 
  apply contained_app; eauto with gensym.
  (* for effects *)
  exists (tmp1 ++ tmp2); split. 
  econstructor; eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for test *)
  exists (x1 :: tmp1 ++ tmp2); split.
  repeat rewrite app_ass. simpl.
  intros. eapply tr_assignop_val with (dst := For_test s1 s2); eauto with gensym.
  apply contained_cons. eauto with gensym. 
  apply contained_app; eauto with gensym.
(* postincr *)
  monadInv H0. exploit H; eauto. intros [tmp1 [A B]].
  destruct dst; monadInv EQ0.
  (* for value *)
  exists (x0 :: tmp1); split. 
  econstructor; eauto with gensym.
  apply contained_cons; eauto with gensym. 
  (* for effects *)
  exists tmp1; split. 
  econstructor; eauto with gensym. auto.
  (* for test *)
  repeat rewrite app_ass; simpl.
  exists (x0 :: tmp1); split. 
  econstructor; eauto with gensym.
  apply contained_cons; eauto with gensym. 
(* comma *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  exploit H0; eauto. intros [tmp2 [C D]].
  exists (tmp1 ++ tmp2); split. 
  econstructor; eauto with gensym.
  apply contained_app; eauto with gensym.
(* call *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  exploit H0; eauto. intros [tmp2 [C D]].
  destruct dst; monadInv EQ2.
  (* for value *)
  exists (x1 :: tmp1 ++ tmp2); split. 
  econstructor; eauto with gensym. congruence.
  apply contained_cons. eauto with gensym. 
  apply contained_app; eauto with gensym.
  (* for effects *)
  exists (tmp1 ++ tmp2); split. 
  econstructor; eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for test *)
  exists (x1 :: tmp1 ++ tmp2); split. 
  repeat rewrite app_ass. econstructor; eauto with gensym. congruence.
  apply contained_cons. eauto with gensym. 
  apply contained_app; eauto with gensym.
(* loc *)
  monadInv H.

(* paren *)
  monadInv H0. 
(* nil *)
  monadInv H; exists (@nil ident); split; auto with gensym. constructor.
(* cons *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  exploit H0; eauto. intros [tmp2 [C D]].
  exists (tmp1 ++ tmp2); split. 
  econstructor; eauto with gensym.
  eauto with gensym.
Qed.

Lemma transl_expr_meets_spec:
   forall r dst g sl a g' I,
   transl_expr dst r g = Res (sl, a) g' I ->
   exists tmps, forall ge e le m, tr_top ge e le m dst r sl a tmps.
Proof.
  intros. exploit (proj1 transl_meets_spec); eauto. intros [tmps [A B]].
  exists tmps; intros. apply tr_top_base. auto. 
Qed.

Lemma transl_expression_meets_spec:
  forall r g s a g' I,
  transl_expression r g = Res (s, a) g' I ->
  tr_expression r s a.
Proof.
  intros. monadInv H. exploit transl_expr_meets_spec; eauto. 
  intros [tmps A]. econstructor; eauto. 
Qed.

Lemma transl_expr_stmt_meets_spec:
  forall r g s g' I,
  transl_expr_stmt r g = Res s g' I ->
  tr_expr_stmt r s.
Proof.
  intros. monadInv H. exploit transl_expr_meets_spec; eauto. 
  intros [tmps A]. econstructor; eauto. 
Qed.

Lemma transl_if_meets_spec:
  forall r s1 s2 g s g' I,
  transl_if r s1 s2 g = Res s g' I ->
  tr_if r s1 s2 s.
Proof.
  intros. monadInv H. exploit transl_expr_meets_spec; eauto. 
  intros [tmps A]. econstructor; eauto. 
Qed.

Lemma transl_stmt_meets_spec:
  forall s g ts g' I, transl_stmt s g = Res ts g' I -> tr_stmt s ts
with transl_lblstmt_meets_spec:
  forall s g ts g' I, transl_lblstmt s g = Res ts g' I -> tr_lblstmts s ts.
Proof.
  generalize transl_expression_meets_spec transl_expr_stmt_meets_spec transl_if_meets_spec; intros T1 T2 T3.
Opaque transl_expression transl_expr_stmt.
  clear transl_stmt_meets_spec.
  induction s; simpl; intros until I; intros TR; 
  try (monadInv TR); try (constructor; eauto).
  remember (small_stmt x && small_stmt x0). destruct b.
  exploit andb_prop; eauto. intros [A B]. 
  eapply tr_ifthenelse_small; eauto.
  monadInv EQ2. eapply tr_ifthenelse_big; eauto. 
  destruct (is_Sskip s1); monadInv EQ4.
  apply tr_for_1; eauto.
  apply tr_for_2; eauto. 
  destruct o; monadInv TR; constructor; eauto.

  clear transl_lblstmt_meets_spec.
  induction s; simpl; intros until I; intros TR;
  monadInv TR; constructor; eauto.
Qed.

Theorem transl_function_spec:
  forall f tf,
  transl_function f = OK tf ->
  tr_stmt f.(C.fn_body) tf.(fn_body)
  /\ fn_return tf = C.fn_return f
  /\ fn_params tf = C.fn_params f
  /\ fn_vars tf = C.fn_vars f.
Proof.
  intros until tf. unfold transl_function.
  case_eq (transl_stmt (C.fn_body f) initial_generator); intros; inv H0.
  simpl. intuition. eapply transl_stmt_meets_spec; eauto.
Qed.

End SPEC.

