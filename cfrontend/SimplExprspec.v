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
Require Import Memory.
Require Import AST.
Require Import Ctypes.
Require Import Cop.
Require Import Csyntax.
Require Import Clight.
Require Import SimplExpr.

Section SPEC.

Local Open Scope gensym_monad_scope.

(** * Relational specification of the translation. *)

(** ** Translation of expressions *)

(** This specification covers:
- all cases of [transl_lvalue] and [transl_rvalue];
- two additional cases for [Csyntax.Eparen], so that reductions of [Csyntax.Econdition]
  expressions are properly tracked;
- three additional cases allowing [Csyntax.Eval v] C expressions to match
  any Clight expression [a] that evaluates to [v] in any environment
  matching the given temporary environment [le].
*)

Definition final (dst: destination) (a: expr) : list statement :=
  match dst with
  | For_val => nil
  | For_effects => nil
  | For_set tyl t => do_set t tyl a
  end.

Inductive tr_rvalof: type -> expr -> list statement -> expr -> list ident -> Prop :=
  | tr_rvalof_nonvol: forall ty a tmp,
      type_is_volatile ty = false ->
      tr_rvalof ty a nil a tmp
  | tr_rvalof_vol: forall ty a t tmp,
      type_is_volatile ty = true -> In t tmp ->
      tr_rvalof ty a (make_set t a :: nil) (Etempvar t ty) tmp.

Inductive tr_expr: temp_env -> destination -> Csyntax.expr -> list statement -> expr -> list ident -> Prop :=
  | tr_var: forall le dst id ty tmp,
      tr_expr le dst (Csyntax.Evar id ty)
              (final dst (Evar id ty)) (Evar id ty) tmp
  | tr_deref: forall le dst e1 ty sl1 a1 tmp,
      tr_expr le For_val e1 sl1 a1 tmp ->
      tr_expr le dst (Csyntax.Ederef e1 ty)
              (sl1 ++ final dst (Ederef a1 ty)) (Ederef a1 ty) tmp
  | tr_field: forall le dst e1 f ty sl1 a1 tmp,
      tr_expr le For_val e1 sl1 a1 tmp ->
      tr_expr le dst (Csyntax.Efield e1 f ty)
              (sl1 ++ final dst (Efield a1 f ty)) (Efield a1 f ty) tmp
  | tr_val_effect: forall le v ty any tmp,
      tr_expr le For_effects (Csyntax.Eval v ty) nil any tmp
  | tr_val_value: forall le v ty a tmp,
      typeof a = ty ->
      (forall tge e le' m,
         (forall id, In id tmp -> le'!id = le!id) ->
         eval_expr tge e le' m a v) ->
      tr_expr le For_val (Csyntax.Eval v ty) 
                           nil a tmp
  | tr_val_set: forall le tyl t v ty a any tmp,
      typeof a = ty ->
      (forall tge e le' m,
         (forall id, In id tmp -> le'!id = le!id) ->
         eval_expr tge e le' m a v) ->
      tr_expr le (For_set tyl t) (Csyntax.Eval v ty) 
                   (do_set t tyl a) any tmp
  | tr_sizeof: forall le dst ty' ty tmp,
      tr_expr le dst (Csyntax.Esizeof ty' ty)
                   (final dst (Esizeof ty' ty))
                   (Esizeof ty' ty) tmp
  | tr_alignof: forall le dst ty' ty tmp,
      tr_expr le dst (Csyntax.Ealignof ty' ty)
                   (final dst (Ealignof ty' ty))
                   (Ealignof ty' ty) tmp
  | tr_valof: forall le dst e1 ty tmp sl1 a1 tmp1 sl2 a2 tmp2,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_rvalof (Csyntax.typeof e1) a1 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 -> incl tmp1 tmp -> incl tmp2 tmp ->
      tr_expr le dst (Csyntax.Evalof e1 ty)
                    (sl1 ++ sl2 ++ final dst a2)
                    a2 tmp
  | tr_addrof: forall le dst e1 ty tmp sl1 a1,
      tr_expr le For_val e1 sl1 a1 tmp ->
      tr_expr le dst (Csyntax.Eaddrof e1 ty) 
                   (sl1 ++ final dst (Eaddrof a1 ty))
                   (Eaddrof a1 ty) tmp
  | tr_unop: forall le dst op e1 ty tmp sl1 a1,
      tr_expr le For_val e1 sl1 a1 tmp ->
      tr_expr le dst (Csyntax.Eunop op e1 ty)
                   (sl1 ++ final dst (Eunop op a1 ty))
                   (Eunop op a1 ty) tmp
  | tr_binop: forall le dst op e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_val e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 -> incl tmp1 tmp -> incl tmp2 tmp ->
      tr_expr le dst (Csyntax.Ebinop op e1 e2 ty)
                   (sl1 ++ sl2 ++ final dst (Ebinop op a1 a2 ty))
                   (Ebinop op a1 a2 ty) tmp
  | tr_cast: forall le dst e1 ty sl1 a1 tmp,
      tr_expr le For_val e1 sl1 a1 tmp ->
      tr_expr le dst (Csyntax.Ecast e1 ty)
                   (sl1 ++ final dst (Ecast a1 ty))
                   (Ecast a1 ty) tmp
  | tr_seqand_val: forall le e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le (For_set (type_bool :: ty :: nil) t) e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
      tr_expr le For_val (Csyntax.Eseqand e1 e2 ty)
                    (sl1 ++ makeif a1 (makeseq sl2)
                                      (Sset t (Econst_int Int.zero ty)) :: nil)
                    (Etempvar t ty) tmp
  | tr_seqand_effects: forall le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_effects e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_expr le For_effects (Csyntax.Eseqand e1 e2 ty)
                    (sl1 ++ makeif a1 (makeseq sl2) Sskip :: nil)
                    any tmp
  | tr_seqand_set: forall le tyl t e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le (For_set (type_bool :: ty :: tyl) t) e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
      tr_expr le (For_set tyl t) (Csyntax.Eseqand e1 e2 ty)
                    (sl1 ++ makeif a1 (makeseq sl2)
                                      (makeseq (do_set t tyl (Econst_int Int.zero ty))) :: nil)
                    any tmp
  | tr_seqor_val: forall le e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le (For_set (type_bool :: ty :: nil) t) e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
      tr_expr le For_val (Csyntax.Eseqor e1 e2 ty)
                    (sl1 ++ makeif a1 (Sset t (Econst_int Int.one ty))
                                      (makeseq sl2) :: nil)
                    (Etempvar t ty) tmp
  | tr_seqor_effects: forall le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_effects e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_expr le For_effects (Csyntax.Eseqor e1 e2 ty)
                    (sl1 ++ makeif a1 Sskip (makeseq sl2) :: nil)
                    any tmp
  | tr_seqor_set: forall le tyl t e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le (For_set (type_bool :: ty :: tyl) t) e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
      tr_expr le (For_set tyl t) (Csyntax.Eseqor e1 e2 ty)
                    (sl1 ++ makeif a1 (makeseq (do_set t tyl (Econst_int Int.one ty)))
                                      (makeseq sl2) :: nil)
                    any tmp
  | tr_condition_val: forall le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le (For_set (ty::nil) t) e2 sl2 a2 tmp2 ->
      tr_expr le (For_set (ty::nil) t) e3 sl3 a3 tmp3 ->
      list_disjoint tmp1 tmp2 ->
      list_disjoint tmp1 tmp3 ->
      incl tmp1 tmp -> incl tmp2 tmp ->  incl tmp3 tmp -> In t tmp ->
      tr_expr le For_val (Csyntax.Econdition e1 e2 e3 ty)
                      (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil)
                      (Etempvar t ty) tmp
  | tr_condition_effects: forall le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_effects e2 sl2 a2 tmp2 ->
      tr_expr le For_effects e3 sl3 a3 tmp3 ->
      list_disjoint tmp1 tmp2 ->
      list_disjoint tmp1 tmp3 ->
      incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp ->
      tr_expr le For_effects (Csyntax.Econdition e1 e2 e3 ty)
                       (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil)
                       any tmp
  | tr_condition_set: forall le tyl t e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le (For_set (ty::tyl) t) e2 sl2 a2 tmp2 ->
      tr_expr le (For_set (ty::tyl) t) e3 sl3 a3 tmp3 ->
      list_disjoint tmp1 tmp2 ->
      list_disjoint tmp1 tmp3 ->
      incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp -> In t tmp ->
      tr_expr le (For_set tyl t) (Csyntax.Econdition e1 e2 e3 ty)
                       (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil)
                       any tmp
  | tr_assign_effects: forall le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_val e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->  
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_expr le For_effects (Csyntax.Eassign e1 e2 ty)
                      (sl1 ++ sl2 ++ make_assign a1 a2 :: nil)
                      any tmp
  | tr_assign_val: forall le dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 t tmp ty1 ty2,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_val e2 sl2 a2 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      list_disjoint tmp1 tmp2 ->  
      In t tmp -> ~In t tmp1 -> ~In t tmp2 ->
      ty1 = Csyntax.typeof e1 ->
      ty2 = Csyntax.typeof e2 ->
      tr_expr le dst (Csyntax.Eassign e1 e2 ty)
                   (sl1 ++ sl2 ++ 
                    Sset t a2 ::
                    make_assign a1 (Etempvar t ty2) ::
                    final dst (Ecast (Etempvar t ty2) ty1))
                   (Ecast (Etempvar t ty2) ty1) tmp
  | tr_assignop_effects: forall le op e1 e2 tyres ty ty1 sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_val e2 sl2 a2 tmp2 ->
      ty1 = Csyntax.typeof e1 ->
      tr_rvalof ty1 a1 sl3 a3 tmp3 ->
      list_disjoint tmp1 tmp2 -> list_disjoint tmp1 tmp3 -> list_disjoint tmp2 tmp3 ->
      incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp ->
      tr_expr le For_effects (Csyntax.Eassignop op e1 e2 tyres ty)
                      (sl1 ++ sl2 ++ sl3 ++ make_assign a1 (Ebinop op a3 a2 tyres) :: nil)
                      any tmp
  | tr_assignop_val: forall le dst op e1 e2 tyres ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t tmp ty1,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_val e2 sl2 a2 tmp2 ->
      tr_rvalof ty1 a1 sl3 a3 tmp3 ->
      list_disjoint tmp1 tmp2 -> list_disjoint tmp1 tmp3 -> list_disjoint tmp2 tmp3 ->
      incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp ->
      In t tmp -> ~In t tmp1 -> ~In t tmp2 -> ~In t tmp3 ->
      ty1 = Csyntax.typeof e1 ->
      tr_expr le dst (Csyntax.Eassignop op e1 e2 tyres ty)
                   (sl1 ++ sl2 ++ sl3 ++
                    Sset t (Ebinop op a3 a2 tyres) ::
                    make_assign a1 (Etempvar t tyres) ::
                    final dst (Ecast (Etempvar t tyres) ty1))
                   (Ecast (Etempvar t tyres) ty1) tmp
  | tr_postincr_effects: forall le id e1 ty ty1 sl1 a1 tmp1 sl2 a2 tmp2 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_rvalof ty1 a1 sl2 a2 tmp2 ->
      ty1 = Csyntax.typeof e1 ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      list_disjoint tmp1 tmp2 ->  
      tr_expr le For_effects (Csyntax.Epostincr id e1 ty)
                      (sl1 ++ sl2 ++ make_assign a1 (transl_incrdecr id a2 ty1) :: nil)
                      any tmp
  | tr_postincr_val: forall le dst id e1 ty sl1 a1 tmp1 t ty1 tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      incl tmp1 tmp -> In t tmp -> ~In t tmp1 ->
      ty1 = Csyntax.typeof e1 ->
      tr_expr le dst (Csyntax.Epostincr id e1 ty)
                   (sl1 ++ make_set t a1 ::
                    make_assign a1 (transl_incrdecr id (Etempvar t ty1) ty1) ::
                    final dst (Etempvar t ty1))
                   (Etempvar t ty1) tmp
  | tr_comma: forall le dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp,
      tr_expr le For_effects e1 sl1 a1 tmp1 ->
      tr_expr le dst e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->  
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_expr le dst (Csyntax.Ecomma e1 e2 ty) (sl1 ++ sl2) a2 tmp
  | tr_call_effects: forall le e1 el2 ty sl1 a1 tmp1 sl2 al2 tmp2 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_exprlist le el2 sl2 al2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_expr le For_effects (Csyntax.Ecall e1 el2 ty)
                   (sl1 ++ sl2 ++ Scall None a1 al2 :: nil)
                   any tmp
  | tr_call_val: forall le dst e1 el2 ty sl1 a1 tmp1 sl2 al2 tmp2 t tmp,
      dst <> For_effects ->
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_exprlist le el2 sl2 al2 tmp2 ->
      list_disjoint tmp1 tmp2 -> In t tmp ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_expr le dst (Csyntax.Ecall e1 el2 ty)
                   (sl1 ++ sl2 ++ Scall (Some t) a1 al2 :: final dst (Etempvar t ty))
                   (Etempvar t ty) tmp
  | tr_builtin_effects: forall le ef tyargs el ty sl al tmp1 any tmp,
      tr_exprlist le el sl al tmp1 ->
      incl tmp1 tmp ->
      tr_expr le For_effects (Csyntax.Ebuiltin ef tyargs el ty)
                   (sl ++ Sbuiltin None ef tyargs al :: nil)
                   any tmp
  | tr_builtin_val: forall le dst ef tyargs el ty sl al tmp1 t tmp,
      dst <> For_effects ->
      tr_exprlist le el sl al tmp1 ->
      In t tmp -> incl tmp1 tmp ->
      tr_expr le dst (Csyntax.Ebuiltin ef tyargs el ty)
                   (sl ++ Sbuiltin (Some t) ef tyargs al :: final dst (Etempvar t ty))
                   (Etempvar t ty) tmp
  | tr_paren_val: forall le e1 ty sl1 a1 t tmp,
      tr_expr le (For_set (ty :: nil) t) e1 sl1 a1 tmp ->
      In t tmp -> 
      tr_expr le For_val (Csyntax.Eparen e1 ty)
                       sl1
                       (Etempvar t ty) tmp
  | tr_paren_effects: forall le e1 ty sl1 a1 tmp any,
      tr_expr le For_effects e1 sl1 a1 tmp ->
      tr_expr le For_effects (Csyntax.Eparen e1 ty) sl1 any tmp
  | tr_paren_set: forall le tyl t e1 ty sl1 a1 tmp any,
      tr_expr le (For_set (ty::tyl) t) e1 sl1 a1 tmp ->
      In t tmp ->
      tr_expr le (For_set tyl t) (Csyntax.Eparen e1 ty) sl1 any tmp

with tr_exprlist: temp_env -> Csyntax.exprlist -> list statement -> list expr -> list ident -> Prop :=
  | tr_nil: forall le tmp,
      tr_exprlist le Csyntax.Enil nil nil tmp
  | tr_cons: forall le e1 el2 sl1 a1 tmp1 sl2 al2 tmp2 tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_exprlist le el2 sl2 al2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_exprlist le (Csyntax.Econs e1 el2) (sl1 ++ sl2) (a1 :: al2) tmp.

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
    intros. apply H0. auto. intros. transitivity (le'!id); auto.
  induction 1; intros; econstructor; eauto.
Qed.

Lemma tr_rvalof_monotone:
  forall ty a sl b tmps, tr_rvalof ty a sl b tmps ->
  forall tmps', incl tmps tmps' -> tr_rvalof ty a sl b tmps'.
Proof.
  induction 1; intros; econstructor; unfold incl in *; eauto.
Qed.

Lemma tr_expr_monotone:
  forall le dst r sl a tmps, tr_expr le dst r sl a tmps ->
  forall tmps', incl tmps tmps' -> tr_expr le dst r sl a tmps'
with tr_exprlist_monotone:
  forall le rl sl al tmps, tr_exprlist le rl sl al tmps ->
  forall tmps', incl tmps tmps' -> tr_exprlist le rl sl al tmps'.
Proof.
  specialize tr_rvalof_monotone. intros RVALOF.
  induction 1; intros; econstructor; unfold incl in *; eauto.
  induction 1; intros; econstructor; unfold incl in *; eauto.
Qed.

(** ** Top-level translation *)

(** The "top-level" translation is equivalent to [tr_expr] above
  for source terms.  It brings additional flexibility in the matching
  between Csyntax values and Cminor expressions: in the case of
  [tr_expr], the Cminor expression must not depend on memory,
  while in the case of [tr_top] it can depend on the current memory
  state.  This special case is extended to values occurring under
  one or several [Csyntax.Eparen]. *)

Section TR_TOP.

Variable ge: genv.
Variable e: env.
Variable le: temp_env.
Variable m: mem.

Inductive tr_top: destination -> Csyntax.expr -> list statement -> expr -> list ident -> Prop :=
  | tr_top_val_val: forall v ty a tmp,
      typeof a = ty -> eval_expr ge e le m a v ->
      tr_top For_val (Csyntax.Eval v ty) nil a tmp
(*
  | tr_top_val_set: forall t tyl v ty a any tmp,
      typeof a = ty -> eval_expr ge e le m a v ->
      tr_top (For_set tyl t) (Csyntax.Eval v ty) (Sset t (fold_left Ecast tyl a) :: nil) any tmp
*)
  | tr_top_base: forall dst r sl a tmp,
      tr_expr le dst r sl a tmp ->
      tr_top dst r sl a tmp.
(*
  | tr_top_paren_test: forall tyl t r ty sl a tmp,
      tr_top (For_set (ty :: tyl) t) r sl a tmp ->
      tr_top (For_set tyl t) (Csyntax.Eparen r ty) sl a tmp.
*)

End TR_TOP.

(** ** Translation of statements *)

Inductive tr_expression: Csyntax.expr -> statement -> expr -> Prop :=
  | tr_expression_intro: forall r sl a tmps,
      (forall ge e le m, tr_top ge e le m For_val r sl a tmps) ->
      tr_expression r (makeseq sl) a.

Inductive tr_expr_stmt: Csyntax.expr -> statement -> Prop :=
  | tr_expr_stmt_intro: forall r sl a tmps,
      (forall ge e le m, tr_top ge e le m For_effects r sl a tmps) ->
      tr_expr_stmt r (makeseq sl).

Inductive tr_if: Csyntax.expr -> statement -> statement -> statement -> Prop :=
  | tr_if_intro: forall r s1 s2 sl a tmps,
      (forall ge e le m, tr_top ge e le m For_val r sl a tmps) ->
      tr_if r s1 s2 (makeseq (sl ++ makeif a s1 s2 :: nil)).

Inductive tr_stmt: Csyntax.statement -> statement -> Prop :=
  | tr_skip:
      tr_stmt Csyntax.Sskip Sskip
  | tr_do: forall r s,
      tr_expr_stmt r s ->
      tr_stmt (Csyntax.Sdo r) s
  | tr_seq: forall s1 s2 ts1 ts2,
      tr_stmt s1 ts1 -> tr_stmt s2 ts2 ->
      tr_stmt (Csyntax.Ssequence s1 s2) (Ssequence ts1 ts2)
  | tr_ifthenelse: forall r s1 s2 s' a ts1 ts2,
      tr_expression r s' a ->
      tr_stmt s1 ts1 -> tr_stmt s2 ts2 ->
      tr_stmt (Csyntax.Sifthenelse r s1 s2) (Ssequence s' (Sifthenelse a ts1 ts2))
  | tr_while: forall r s1 s' ts1,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s1 ts1 ->
      tr_stmt (Csyntax.Swhile r s1)
              (Sloop (Ssequence s' ts1) Sskip)
  | tr_dowhile: forall r s1 s' ts1,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s1 ts1 ->
      tr_stmt (Csyntax.Sdowhile r s1)
              (Sloop ts1 s')
  | tr_for_1: forall r s3 s4 s' ts3 ts4,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s3 ts3 ->
      tr_stmt s4 ts4 ->
      tr_stmt (Csyntax.Sfor Csyntax.Sskip r s3 s4)
              (Sloop (Ssequence s' ts4) ts3)
  | tr_for_2: forall s1 r s3 s4 s' ts1 ts3 ts4,
      tr_if r Sskip Sbreak s' ->
      s1 <> Csyntax.Sskip ->
      tr_stmt s1 ts1 ->
      tr_stmt s3 ts3 ->
      tr_stmt s4 ts4 ->
      tr_stmt (Csyntax.Sfor s1 r s3 s4)
              (Ssequence ts1 (Sloop (Ssequence s' ts4) ts3))
  | tr_break:
      tr_stmt Csyntax.Sbreak Sbreak
  | tr_continue:
      tr_stmt Csyntax.Scontinue Scontinue
  | tr_return_none:
      tr_stmt (Csyntax.Sreturn None) (Sreturn None)
  | tr_return_some: forall r s' a,
      tr_expression r s' a ->
      tr_stmt (Csyntax.Sreturn (Some r)) (Ssequence s' (Sreturn (Some a)))
  | tr_switch: forall r ls s' a tls,
      tr_expression r s' a ->
      tr_lblstmts ls tls ->
      tr_stmt (Csyntax.Sswitch r ls) (Ssequence s' (Sswitch a tls))
  | tr_label: forall lbl s ts,
      tr_stmt s ts ->
      tr_stmt (Csyntax.Slabel lbl s) (Slabel lbl ts)
  | tr_goto: forall lbl,
      tr_stmt (Csyntax.Sgoto lbl) (Sgoto lbl)

with tr_lblstmts: Csyntax.labeled_statements -> labeled_statements -> Prop :=
  | tr_default: forall s ts,
      tr_stmt s ts ->
      tr_lblstmts (Csyntax.LSdefault s) (LSdefault ts)
  | tr_case: forall n s ls ts tls,
      tr_stmt s ts ->
      tr_lblstmts ls tls ->
      tr_lblstmts (Csyntax.LScase n s ls) (LScase n ts tls).

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
  forall (A B Csyntax: Type) (f: mon (A*B)) (g: A -> B -> mon Csyntax) (y: Csyntax) (z1 z3: generator) I,
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
  eapply Plt_Ple_trans; eauto.
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
  exploit H; eauto. intros [A B]. exploit H0; eauto. intros [Csyntax D].
  elim (Plt_strict x). apply Plt_Ple_trans with (gen_next g2); auto.
Qed.

Lemma contained_notin:
  forall g1 l g2 id g3,
  contained l g1 g2 -> within id g2 g3 -> ~In id l.
Proof.
  intros; red; intros. exploit H; eauto. intros [Csyntax D]. destruct H0 as [A B].
  elim (Plt_strict id). apply Plt_Ple_trans with (gen_next g2); auto.
Qed.

Definition dest_below (dst: destination) (g: generator) : Prop :=
  match dst with
  | For_set tyl tmp => Plt tmp g.(gen_next)
  | _ => True
  end.

Remark dest_for_val_below: forall g, dest_below For_val g.
Proof. intros; simpl; auto. Qed.

Remark dest_for_effect_below: forall g, dest_below For_effects g.
Proof. intros; simpl; auto. Qed.

Lemma dest_below_notin:
  forall tyl tmp g1 g2 l,
  dest_below (For_set tyl tmp) g1 -> contained l g1 g2 -> ~In tmp l.
Proof.
  simpl; intros. red in H0. red; intros. destruct (H0 _ H1). 
  elim (Plt_strict tmp). apply Plt_Ple_trans with (gen_next g1); auto.
Qed.

Lemma within_dest_below:
  forall tyl tmp g1 g2,
  within tmp g1 g2 -> dest_below (For_set tyl tmp) g2.
Proof.
  intros; simpl. destruct H. tauto.
Qed. 

Lemma dest_below_le:
  forall dst g1 g2,
  dest_below dst g1 -> Ple g1.(gen_next) g2.(gen_next) -> dest_below dst g2.
Proof.
  intros. destruct dst; simpl in *; auto. eapply Plt_Ple_trans; eauto.
Qed.

Hint Resolve gensym_within within_widen contained_widen
             contained_cons contained_app contained_disjoint
             contained_notin contained_nil dest_below_notin
             incl_refl incl_tl incl_app incl_appl incl_appr incl_same_head
             in_eq in_cons within_dest_below dest_below_le
             Ple_trans Ple_refl: gensym.

Hint Resolve dest_for_val_below dest_for_effect_below.

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

Definition add_dest (dst: destination) (tmps: list ident) :=
  match dst with
  | For_set tyl t => t :: tmps
  | _ => tmps
  end.

Lemma add_dest_incl:
  forall dst tmps, incl tmps (add_dest dst tmps).
Proof.
  intros. destruct dst; simpl; auto with coqlib.
Qed.

Lemma tr_expr_add_dest:
  forall le dst r sl a tmps,
  tr_expr le dst r sl a tmps ->
  tr_expr le dst r sl a (add_dest dst tmps).
Proof.
  intros. apply tr_expr_monotone with tmps; auto. apply add_dest_incl.
Qed.

Lemma transl_valof_meets_spec:
  forall ty a g sl b g' I,
  transl_valof ty a g = Res (sl, b) g' I ->
  exists tmps, tr_rvalof ty a sl b tmps /\ contained tmps g g'.
Proof.
  unfold transl_valof; intros.
  destruct (type_is_volatile ty) eqn:?; monadInv H.
  exists (x :: nil); split; eauto with gensym. econstructor; eauto with coqlib.
  exists (@nil ident); split; eauto with gensym. constructor; auto.
Qed.

Scheme expr_ind2 := Induction for Csyntax.expr Sort Prop
  with exprlist_ind2 := Induction for Csyntax.exprlist Sort Prop.
Combined Scheme expr_exprlist_ind from expr_ind2, exprlist_ind2.

Lemma transl_meets_spec:
   (forall r dst g sl a g' I,
    transl_expr dst r g = Res (sl, a) g' I ->
    dest_below dst g ->
    exists tmps, (forall le, tr_expr le dst r sl a (add_dest dst tmps)) /\ contained tmps g g')
  /\
   (forall rl g sl al g' I,
    transl_exprlist rl g = Res (sl, al) g' I ->
    exists tmps, (forall le, tr_exprlist le rl sl al tmps) /\ contained tmps g g').
Proof.
  apply expr_exprlist_ind; simpl add_dest; intros.
(* val *)
  simpl in H. destruct v; monadInv H; exists (@nil ident); split; auto with gensym.
Opaque makeif.
  intros. destruct dst; simpl in *; inv H2. 
    constructor. auto. intros; constructor.
    constructor.
    constructor. auto. intros; constructor.
  intros. destruct dst; simpl in *; inv H2. 
    constructor. auto. intros; constructor.
    constructor.
    constructor. auto. intros; constructor.
(* var *)
  monadInv H; econstructor; split; auto with gensym. UseFinish. constructor.
(* field *)
  monadInv H0. exploit H; eauto. auto. intros [tmp [A B]]. UseFinish. 
  econstructor; split; eauto. intros; apply tr_expr_add_dest. constructor; auto. 
(* valof *)
  monadInv H0. exploit H; eauto. intros [tmp1 [A B]].
  exploit transl_valof_meets_spec; eauto. intros [tmp2 [Csyntax D]]. UseFinish.
  exists (tmp1 ++ tmp2); split.
  intros; apply tr_expr_add_dest. econstructor; eauto with gensym.
  eauto with gensym.
(* deref *)
  monadInv H0. exploit H; eauto. intros [tmp [A B]]. UseFinish. 
  econstructor; split; eauto. intros; apply tr_expr_add_dest. constructor; auto. 
(* addrof *)
  monadInv H0. exploit H; eauto. intros [tmp [A B]]. UseFinish. 
  econstructor; split; eauto. intros; apply tr_expr_add_dest. econstructor; eauto.
(* unop *)
  monadInv H0. exploit H; eauto. intros [tmp [A B]]. UseFinish. 
  econstructor; split; eauto. intros; apply tr_expr_add_dest. constructor; auto. 
(* binop *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  exploit H0; eauto. intros [tmp2 [Csyntax D]]. UseFinish.
  exists (tmp1 ++ tmp2); split. 
  intros; apply tr_expr_add_dest. econstructor; eauto with gensym.
  eauto with gensym.
(* cast *)
  monadInv H0. exploit H; eauto. intros [tmp [A B]]. UseFinish. 
  econstructor; split; eauto. intros; apply tr_expr_add_dest. constructor; auto.
(* seqand *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  destruct dst; monadInv EQ0.
  (* for value *)
  exploit H0; eauto with gensym. intros [tmp2 [Csyntax D]].
  simpl add_dest in *.
  exists (x0 :: tmp1 ++ tmp2); split.
  intros; eapply tr_seqand_val; eauto with gensym.
  apply list_disjoint_cons_r; eauto with gensym.
  apply contained_cons. eauto with gensym. 
  apply contained_app; eauto with gensym.
  (* for effects *)
  exploit H0; eauto with gensym. intros [tmp2 [Csyntax D]].
  simpl add_dest in *.
  exists (tmp1 ++ tmp2); split.
  intros; eapply tr_seqand_effects; eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for set *)
  exploit H0; eauto with gensym. intros [tmp2 [Csyntax D]].
  simpl add_dest in *.
  exists (tmp1 ++ tmp2); split.
  intros; eapply tr_seqand_set; eauto with gensym.
  apply list_disjoint_cons_r; eauto with gensym.
  apply contained_app; eauto with gensym.
(* seqor *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  destruct dst; monadInv EQ0.
  (* for value *)
  exploit H0; eauto with gensym. intros [tmp2 [Csyntax D]].
  simpl add_dest in *.
  exists (x0 :: tmp1 ++ tmp2); split.
  intros; eapply tr_seqor_val; eauto with gensym.
  apply list_disjoint_cons_r; eauto with gensym.
  apply contained_cons. eauto with gensym. 
  apply contained_app; eauto with gensym.
  (* for effects *)
  exploit H0; eauto with gensym. intros [tmp2 [Csyntax D]].
  simpl add_dest in *.
  exists (tmp1 ++ tmp2); split.
  intros; eapply tr_seqor_effects; eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for set *)
  exploit H0; eauto with gensym. intros [tmp2 [Csyntax D]].
  simpl add_dest in *.
  exists (tmp1 ++ tmp2); split.
  intros; eapply tr_seqor_set; eauto with gensym.
  apply list_disjoint_cons_r; eauto with gensym.
  apply contained_app; eauto with gensym.
(* condition *) 
  monadInv H2. exploit H; eauto. intros [tmp1 [A B]].
  destruct dst; monadInv EQ0.
  (* for value *)
  exploit H0; eauto with gensym. intros [tmp2 [Csyntax D]].
  exploit H1; eauto with gensym. intros [tmp3 [E F]].
  simpl add_dest in *.
  exists (x0 :: tmp1 ++ tmp2 ++ tmp3); split. 
  simpl; intros; eapply tr_condition_val; eauto with gensym.
  apply list_disjoint_cons_r; eauto with gensym.
  apply list_disjoint_cons_r; eauto with gensym.
  apply contained_cons. eauto with gensym. 
  apply contained_app. eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for effects *)
  exploit H0; eauto. intros [tmp2 [Csyntax D]].
  exploit H1; eauto. intros [tmp3 [E F]].
  simpl add_dest in *.
  exists (tmp1 ++ tmp2 ++ tmp3); split.
  intros; eapply tr_condition_effects; eauto with gensym. 
  apply contained_app; eauto with gensym.
  (* for test *)
  exploit H0; eauto with gensym. intros [tmp2 [Csyntax D]].
  exploit H1; eauto with gensym. intros [tmp3 [E F]].
  simpl add_dest in *.
  exists (tmp1 ++ tmp2 ++ tmp3); split.
  intros; eapply tr_condition_set; eauto with gensym.
  apply list_disjoint_cons_r; eauto with gensym.
  apply list_disjoint_cons_r; eauto with gensym.
  apply contained_app; eauto with gensym.
(* sizeof *)
  monadInv H. UseFinish.
  exists (@nil ident); split; auto with gensym. constructor.
(* alignof *)
  monadInv H. UseFinish.
  exists (@nil ident); split; auto with gensym. constructor.
(* assign *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  exploit H0; eauto. intros [tmp2 [Csyntax D]].
  destruct dst; monadInv EQ2; simpl add_dest in *.
  (* for value *)
  exists (x1 :: tmp1 ++ tmp2); split. 
  intros. eapply tr_assign_val with (dst := For_val); eauto with gensym.
  apply contained_cons. eauto with gensym. 
  apply contained_app; eauto with gensym.
  (* for effects *)
  exists (tmp1 ++ tmp2); split. 
  econstructor; eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for set *)
  exists (x1 :: tmp1 ++ tmp2); split.
  repeat rewrite app_ass. simpl. 
  intros. eapply tr_assign_val with (dst := For_set tyl tmp); eauto with gensym.
  apply contained_cons. eauto with gensym. 
  apply contained_app; eauto with gensym.
(* assignop *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  exploit H0; eauto. intros [tmp2 [Csyntax D]].
  exploit transl_valof_meets_spec; eauto. intros [tmp3 [E F]].
  destruct dst; monadInv EQ3; simpl add_dest in *.
  (* for value *)
  exists (x2 :: tmp1 ++ tmp2 ++ tmp3); split.
  intros. eapply tr_assignop_val with (dst := For_val); eauto with gensym.
  apply contained_cons. eauto with gensym. 
  apply contained_app; eauto with gensym.
  (* for effects *)
  exists (tmp1 ++ tmp2 ++ tmp3); split. 
  econstructor; eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for set *)
  exists (x2 :: tmp1 ++ tmp2 ++ tmp3); split.
  repeat rewrite app_ass. simpl.
  intros. eapply tr_assignop_val with (dst := For_set tyl tmp); eauto with gensym.
  apply contained_cons. eauto with gensym. 
  apply contained_app; eauto with gensym.
(* postincr *)
  monadInv H0. exploit H; eauto. intros [tmp1 [A B]].
  destruct dst; monadInv EQ0; simpl add_dest in *.
  (* for value *)
  exists (x0 :: tmp1); split. 
  econstructor; eauto with gensym.
  apply contained_cons; eauto with gensym. 
  (* for effects *)
  exploit transl_valof_meets_spec; eauto. intros [tmp2 [Csyntax D]].
  exists (tmp1 ++ tmp2); split. 
  econstructor; eauto with gensym.
  eauto with gensym. 
  (* for set *)
  repeat rewrite app_ass; simpl.
  exists (x0 :: tmp1); split. 
  econstructor; eauto with gensym.
  apply contained_cons; eauto with gensym. 
(* comma *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  exploit H0; eauto with gensym. intros [tmp2 [Csyntax D]].
  exists (tmp1 ++ tmp2); split. 
  econstructor; eauto with gensym.
  destruct dst; simpl; eauto with gensym. 
  apply list_disjoint_cons_r; eauto with gensym.
  simpl. eapply incl_tran. 2: apply add_dest_incl. auto with gensym. 
  destruct dst; simpl; auto with gensym.
  apply contained_app; eauto with gensym.
(* call *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  exploit H0; eauto. intros [tmp2 [Csyntax D]].
  destruct dst; monadInv EQ2; simpl add_dest in *.
  (* for value *)
  exists (x1 :: tmp1 ++ tmp2); split. 
  econstructor; eauto with gensym. congruence.
  apply contained_cons. eauto with gensym. 
  apply contained_app; eauto with gensym.
  (* for effects *)
  exists (tmp1 ++ tmp2); split. 
  econstructor; eauto with gensym.
  apply contained_app; eauto with gensym.
  (* for set *)
  exists (x1 :: tmp1 ++ tmp2); split. 
  repeat rewrite app_ass. econstructor; eauto with gensym. congruence.
  apply contained_cons. eauto with gensym. 
  apply contained_app; eauto with gensym.
(* builtin *)
  monadInv H0. exploit H; eauto. intros [tmp1 [A B]].
  destruct dst; monadInv EQ0; simpl add_dest in *.
  (* for value *)
  exists (x0 :: tmp1); split. 
  econstructor; eauto with gensym. congruence.
  apply contained_cons; eauto with gensym. 
  (* for effects *)
  exists tmp1; split. 
  econstructor; eauto with gensym.
  auto.
  (* for set *)
  exists (x0 :: tmp1); split. 
  repeat rewrite app_ass. econstructor; eauto with gensym. congruence.
  apply contained_cons; eauto with gensym. 
(* loc *)
  monadInv H.
(* paren *)
  monadInv H0. 
(* nil *)
  monadInv H; exists (@nil ident); split; auto with gensym. constructor.
(* cons *)
  monadInv H1. exploit H; eauto. intros [tmp1 [A B]].
  exploit H0; eauto. intros [tmp2 [Csyntax D]].
  exists (tmp1 ++ tmp2); split. 
  econstructor; eauto with gensym.
  eauto with gensym.
Qed.

Lemma transl_expr_meets_spec:
   forall r dst g sl a g' I,
   transl_expr dst r g = Res (sl, a) g' I ->
   dest_below dst g ->
   exists tmps, forall ge e le m, tr_top ge e le m dst r sl a tmps.
Proof.
  intros. exploit (proj1 transl_meets_spec); eauto. intros [tmps [A B]].
  exists (add_dest dst tmps); intros. apply tr_top_base. auto. 
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
  tr_stmt f.(Csyntax.fn_body) tf.(fn_body)
  /\ fn_return tf = Csyntax.fn_return f
  /\ fn_params tf = Csyntax.fn_params f
  /\ fn_vars tf = Csyntax.fn_vars f.
Proof.
  intros until tf. unfold transl_function.
  case_eq (transl_stmt (Csyntax.fn_body f) (initial_generator tt)); intros; inv H0.
  simpl. intuition. eapply transl_stmt_meets_spec; eauto.
Qed.

End SPEC.

