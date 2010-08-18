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

(** Translation from Compcert C to Clight. 
    Side effects are pulled out of Compcert C expressions. *)

Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Csyntax.
Require Import Clight.

Module C := Csyntax.

Open Local Scope string_scope.

(** State and error monad for generating fresh identifiers. *)

Record generator : Type := mkgenerator {
  gen_next: ident;
  gen_trail: list (ident * type)
}.

Inductive result (A: Type) (g: generator) : Type :=
  | Err: Errors.errmsg -> result A g
  | Res: A -> forall (g': generator), Ple (gen_next g) (gen_next g') -> result A g.

Implicit Arguments Err [A g].
Implicit Arguments Res [A g].

Definition mon (A: Type) := forall (g: generator), result A g.

Definition ret (A: Type) (x: A) : mon A :=
  fun g => Res x g (Ple_refl (gen_next g)).

Implicit Arguments ret [A].

Definition error (A: Type) (msg: Errors.errmsg) : mon A :=
  fun g => Err msg.

Implicit Arguments error [A].

Definition bind (A B: Type) (x: mon A) (f: A -> mon B) : mon B :=
  fun g =>
    match x g with
      | Err msg => Err msg
      | Res a g' i =>
          match f a g' with
          | Err msg => Err msg
          | Res b g'' i' => Res b g'' (Ple_trans _ _ _ i i')
      end
    end.

Implicit Arguments bind [A B].

Definition bind2 (A B C: Type) (x: mon (A * B)) (f: A -> B -> mon C) : mon C :=
  bind x (fun p => f (fst p) (snd p)).

Implicit Arguments bind2 [A B C].

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.

Definition initial_generator : generator := 
  mkgenerator 1%positive nil.

Definition gensym (ty: type): mon ident :=
  fun (g: generator) => 
    Res (gen_next g)
        (mkgenerator (Psucc (gen_next g)) ((gen_next g, ty) :: gen_trail g))
        (Ple_succ (gen_next g)).

(** Construct a sequence from a list of statements.  To facilitate the
   proof, the sequence is nested to the left and starts with a [Sskip]. *)

Fixpoint makeseq_rec (s: statement) (l: list statement) : statement :=
  match l with
  | nil => s
  | s' :: l' => makeseq_rec (Ssequence s s') l'
  end.

Definition makeseq (l: list statement) : statement :=
  makeseq_rec Sskip l.

(** Smart constructor for [if ... then ... else]. *)

Function makeif (a: expr) (s1 s2: statement) : statement :=
  match a with
  | Econst_int n _ => if Int.eq_dec n Int.zero then s2 else s1
  | _              => Sifthenelse a s1 s2
  end.

(** Translation of pre/post-increment/decrement. *)

Definition transl_incrdecr (id: incr_or_decr) (a: expr) (ty: type) : expr :=
  match id with
  | Incr => Ebinop Oadd a (Econst_int Int.one (Tint I32 Signed)) (typeconv ty)
  | Decr => Ebinop Osub a (Econst_int Int.one (Tint I32 Signed)) (typeconv ty)
  end.

(** Translation of expressions.  Return a pair [(sl, a)] of
    a list of statements [sl] and a pure expression [a].
- If the [dst] argument is [For_val], the statements [sl]
  perform the side effects of the original expression,
  and [a] evaluates to the same value as the original expression.
- If the [dst] argument is [For_effects], the statements [sl]
  perform the side effects of the original expression,
  and [a] is meaningless.
- If the [dst] argument is [For_test s1 s2], the statements [sl]
  perform the side effects of the original expression, followed
  by an [if (v) { s1 } else { s2 }] test, where [v] is the value
  of the original expression.  [a] is meaningless.
*)

Inductive purpose : Type := 
  | For_val
  | For_effects
  | For_test (s1 s2: statement).

Definition dummy_expr := Econst_int Int.zero (Tint I32 Signed).

Definition finish (dst: purpose) (sl: list statement) (a: expr) :=
  match dst with
  | For_val => (sl, a)
  | For_effects => (sl, a)
  | For_test s1 s2 => (sl ++ makeif a s1 s2 :: nil, a)
  end.

Fixpoint transl_expr (dst: purpose) (a: C.expr) : mon (list statement * expr) :=
  match a with
  | C.Eloc b ofs ty =>
      error (msg "SimplExpr.transl_expr: C.Eloc")
  | C.Evar x ty =>
      ret (finish dst nil (Evar x ty))
  | C.Ederef r ty =>
      do (sl, a) <- transl_expr For_val r;
      ret (finish dst sl (Ederef a ty))
  | C.Efield l1 f ty =>
      do (sl, a) <- transl_expr For_val l1;
      ret (finish dst sl (Efield a f ty))
  | C.Eval (Vint n) ty =>
      ret (finish dst nil (Econst_int n ty))
  | C.Eval (Vfloat n) ty =>
      ret (finish dst nil (Econst_float n ty))
  | C.Eval _ ty =>
      error (msg "SimplExpr.transl_expr: val")
  | C.Esizeof ty' ty =>
      ret (finish dst nil (Esizeof ty' ty))
  | C.Evalof l ty =>
      do (sl, a) <- transl_expr For_val l;
      ret (finish dst sl a)
  | C.Eaddrof l ty =>
      do (sl, a) <- transl_expr For_val l;
      ret (finish dst sl (Eaddrof a ty))
  | C.Eunop op r1 ty =>
      do (sl1, a1) <- transl_expr For_val r1;
      ret (finish dst sl1 (Eunop op a1 ty))
  | C.Ebinop op r1 r2 ty =>
      do (sl1, a1) <- transl_expr For_val r1;
      do (sl2, a2) <- transl_expr For_val r2;
      ret (finish dst (sl1 ++ sl2) (Ebinop op a1 a2 ty))
  | C.Ecast r1 ty =>
      do (sl1, a1) <- transl_expr For_val r1;
      ret (finish dst sl1 (Ecast a1 ty))
  | C.Econdition r1 r2 r3 ty =>
      do (sl1, a1) <- transl_expr For_val r1;
      do (sl2, a2) <- transl_expr dst r2;
      do (sl3, a3) <- transl_expr dst r3;
      match dst with
      | For_val =>
          do t <- gensym ty;
          ret (sl1 ++ makeif a1 (Ssequence (makeseq sl2) (Sset t a2))
                                (Ssequence (makeseq sl3) (Sset t a3)) :: nil,
               Etempvar t ty)
      | For_effects | For_test _ _ =>
          ret (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil,
               dummy_expr)
      end
  | C.Eassign l1 r2 ty =>
      do (sl1, a1) <- transl_expr For_val l1;
      do (sl2, a2) <- transl_expr For_val r2;
      let ty1 := C.typeof l1 in
      let ty2 := C.typeof r2 in
      match dst with
      | For_val | For_test _ _ =>
          do t <- gensym ty2;
          ret (finish dst 
                 (sl1 ++ sl2 ++ Sset t a2 :: Sassign a1 (Etempvar t ty2) :: nil)
                 (Ecast (Etempvar t ty2) ty1))
      | For_effects =>
          ret (sl1 ++ sl2 ++ Sassign a1 a2 :: nil,
               dummy_expr)
      end
  | C.Eassignop op l1 r2 tyres ty =>
      do (sl1, a1) <- transl_expr For_val l1;
      do (sl2, a2) <- transl_expr For_val r2;
      let ty1 := C.typeof l1 in
      match dst with
      | For_val | For_test _ _ =>
          do t <- gensym tyres;
          ret (finish dst
                 (sl1 ++ sl2 ++
                  Sset t (Ebinop op a1 a2 tyres) ::
                  Sassign a1 (Etempvar t tyres) :: nil)
                 (Ecast (Etempvar t tyres) ty1))
      | For_effects =>
          ret (sl1 ++ sl2 ++ Sassign a1 (Ebinop op a1 a2 tyres) :: nil,
               dummy_expr)
      end
  | C.Epostincr id l1 ty =>
      do (sl1, a1) <- transl_expr For_val l1;
      let ty1 := C.typeof l1 in
      match dst with
      | For_val | For_test _ _ =>
          do t <- gensym ty1;
          ret (finish dst
                 (sl1 ++ Sset t a1 ::
                  Sassign a1 (transl_incrdecr id (Etempvar t ty1) ty1) :: nil)
                 (Etempvar t ty1))
      | For_effects =>
          ret (sl1 ++ Sassign a1 (transl_incrdecr id a1 ty1) :: nil,
               dummy_expr)
      end
  | C.Ecomma r1 r2 ty =>
      do (sl1, a1) <- transl_expr For_effects r1;
      do (sl2, a2) <- transl_expr dst r2;
      ret (sl1 ++ sl2, a2)
  | C.Ecall r1 rl2 ty =>
      do (sl1, a1) <- transl_expr For_val r1;
      do (sl2, al2) <- transl_exprlist rl2;
      match dst with
      | For_val | For_test _ _ =>
          do t <- gensym ty;
          ret (finish dst (sl1 ++ sl2 ++ Scall (Some t) a1 al2 :: nil)
                          (Etempvar t ty))
      | For_effects =>
          ret (sl1 ++ sl2 ++ Scall None a1 al2 :: nil, dummy_expr)
      end
  | C.Eparen r1 ty =>
      error (msg "SimplExpr.transl_expr: paren")
  end

with transl_exprlist (rl: exprlist) : mon (list statement * list expr) :=
  match rl with
  | C.Enil =>
      ret (nil, nil)
  | C.Econs r1 rl2 =>
      do (sl1, a1) <- transl_expr For_val r1;
      do (sl2, al2) <- transl_exprlist rl2;
      ret (sl1 ++ sl2, a1 :: al2)
  end.

Definition transl_expression (r: C.expr) : mon (statement * expr) :=
  do (sl, a) <- transl_expr For_val r; ret (makeseq sl, a).

Definition transl_expr_stmt (r: C.expr) : mon statement :=
  do (sl, a) <- transl_expr For_effects r; ret (makeseq sl).

Definition transl_if (r: C.expr) (s1 s2: statement) : mon statement :=
  do (sl, a) <- transl_expr (For_test s1 s2) r; ret (makeseq sl).

(** Translation of statements *)

Definition expr_true := Econst_int Int.one (Tint I32 Signed).

Definition is_Sskip:
  forall s, {s = C.Sskip} + {s <> C.Sskip}.
Proof.
  destruct s; ((left; reflexivity) || (right; congruence)).
Defined.

(** There are two possible translations for an "if then else" statement.
  One is more efficient if the condition contains "?" constructors
  but can duplicate the "then" and "else" branches.
  The other produces no code duplication.  We choose between the
  two based on the shape of the "then" and "else" branches. *)

Fixpoint small_stmt (s: statement) : bool :=
  match s with
  | Sskip => true
  | Sbreak => true
  | Scontinue => true
  | Sgoto _ => true
  | Sreturn None => true
  | Ssequence s1 s2 => small_stmt s1 && small_stmt s2
  | _ => false
  end.

Fixpoint transl_stmt (s: C.statement) : mon statement :=
  match s with
  | C.Sskip => ret Sskip
  | C.Sdo e => transl_expr_stmt e
  | C.Ssequence s1 s2 =>
      do ts1 <- transl_stmt s1;
      do ts2 <- transl_stmt s2;
      ret (Ssequence ts1 ts2)
  | C.Sifthenelse e s1 s2 =>
      do ts1 <- transl_stmt s1;
      do ts2 <- transl_stmt s2;
      if small_stmt ts1 && small_stmt ts2 then
        transl_if e ts1 ts2
      else
       (do (s', a) <- transl_expression e;
        ret (Ssequence s' (Sifthenelse a ts1 ts2)))
  | C.Swhile e s1 =>
      do s' <- transl_if e Sskip Sbreak;
      do ts1 <- transl_stmt s1;
      ret (Swhile expr_true (Ssequence s' ts1))
  | C.Sdowhile e s1 =>
      do s' <- transl_if e Sskip Sbreak;
      do ts1 <- transl_stmt s1;
      ret (Sfor' expr_true s' ts1)
  | C.Sfor s1 e2 s3 s4 =>
      do ts1 <- transl_stmt s1;
      do s' <- transl_if e2 Sskip Sbreak;
      do ts3 <- transl_stmt s3;
      do ts4 <- transl_stmt s4;
      if is_Sskip s1 then
        ret (Sfor' expr_true ts3 (Ssequence s' ts4))
      else
        ret (Ssequence ts1 (Sfor' expr_true ts3 (Ssequence s' ts4)))
  | C.Sbreak =>
      ret Sbreak
  | C.Scontinue =>
      ret Scontinue
  | C.Sreturn None =>
      ret (Sreturn None)
  | C.Sreturn (Some e) =>
      do (s', a) <- transl_expression e;
      ret (Ssequence s' (Sreturn (Some a)))
  | C.Sswitch e ls =>
      do (s', a) <- transl_expression e;
      do tls <- transl_lblstmt ls;
      ret (Ssequence s' (Sswitch a tls))
  | C.Slabel lbl s1 =>
      do ts1 <- transl_stmt s1;
      ret (Slabel lbl ts1)
  | C.Sgoto lbl =>
      ret (Sgoto lbl)
  end

with transl_lblstmt (ls: C.labeled_statements) : mon labeled_statements :=
  match ls with
  | C.LSdefault s =>
      do ts <- transl_stmt s;
      ret (LSdefault ts)
  | C.LScase n s ls1 =>
      do ts <- transl_stmt s;
      do tls1 <- transl_lblstmt ls1;
      ret (LScase n ts tls1)
  end.

(** Translation of a function *)

Definition transl_function (f: C.function) : res function :=
  match transl_stmt f.(C.fn_body) initial_generator with
  | Err msg =>
      Error msg
  | Res tbody g i =>
      OK (mkfunction
              f.(C.fn_return)
              f.(C.fn_params)
              f.(C.fn_vars)
              g.(gen_trail)
              tbody)
  end.

Local Open Scope error_monad_scope.

Definition transl_fundef (fd: C.fundef) : res fundef :=
  match fd with
  | C.Internal f =>
      do tf <- transl_function f; OK (Internal tf)
  | C.External ef targs tres =>
      OK (External ef targs tres)
  end.

Definition transl_program (p: C.program) : res program :=
  transform_partial_program transl_fundef p.



      


