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
Require Import Memory.
Require Import AST.
Require Import Ctypes.
Require Import Cop.
Require Import Csyntax.
Require Import Clight.

Local Open Scope string_scope.
Local Open Scope list_scope.

(** State and error monad for generating fresh identifiers. *)

Record generator : Type := mkgenerator {
  gen_next: ident;
  gen_trail: list (ident * type)
}.

Inductive result (A: Type) (g: generator) : Type :=
  | Err: Errors.errmsg -> result A g
  | Res: A -> forall (g': generator), Ple (gen_next g) (gen_next g') -> result A g.

Arguments Err [A g].
Arguments Res [A g].

Definition mon (A: Type) := forall (g: generator), result A g.

Definition ret {A: Type} (x: A) : mon A :=
  fun g => Res x g (Ple_refl (gen_next g)).

Definition error {A: Type} (msg: Errors.errmsg) : mon A :=
  fun g => Err msg.

Definition bind {A B: Type} (x: mon A) (f: A -> mon B) : mon B :=
  fun g =>
    match x g with
      | Err msg => Err msg
      | Res a g' i =>
          match f a g' with
          | Err msg => Err msg
          | Res b g'' i' => Res b g'' (Ple_trans _ _ _ i i')
      end
    end.

Definition bind2 {A B C: Type} (x: mon (A * B)) (f: A -> B -> mon C) : mon C :=
  bind x (fun p => f (fst p) (snd p)).

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.

Parameter first_unused_ident: unit -> ident.

Definition initial_generator (x: unit) : generator :=
  mkgenerator (first_unused_ident x) nil.

Definition gensym (ty: type): mon ident :=
  fun (g: generator) =>
    Res (gen_next g)
        (mkgenerator (Pos.succ (gen_next g)) ((gen_next g, ty) :: gen_trail g))
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

Fixpoint eval_simpl_expr (a: expr) : option val :=
  match a with
  | Econst_int n _ => Some(Vint n)
  | Econst_float n _ => Some(Vfloat n)
  | Econst_single n _ => Some(Vsingle n)
  | Econst_long n _ => Some(Vlong n)
  | Ecast b ty =>
      match eval_simpl_expr b with
      | None => None
      | Some v => sem_cast v (typeof b) ty Mem.empty
      end
  | _ => None
  end.

Function makeif (a: expr) (s1 s2: statement) : statement :=
  match eval_simpl_expr a with
  | Some v =>
      match bool_val v (typeof a) Mem.empty with
      | Some b => if b then s1 else s2
      | None   => Sifthenelse a s1 s2
      end
  | None => Sifthenelse a s1 s2
  end.

(** Smart constructors for [&] and [*].  They optimize away [&*] and [*&] sequences. *)

Definition Ederef' (a: expr) (t: type) : expr :=
  match a with
  | Eaddrof a' t' => if type_eq t (typeof a') then a' else Ederef a t
  | _ => Ederef a t
  end.

Definition Eaddrof' (a: expr) (t: type) : expr :=
  match a with
  | Ederef a' t' => if type_eq t (typeof a') then a' else Eaddrof a t
  | _ => Eaddrof a t
  end.

(** Translation of pre/post-increment/decrement. *)

Definition transl_incrdecr (id: incr_or_decr) (a: expr) (ty: type) : expr :=
  match id with
  | Incr => Ebinop Oadd a (Econst_int Int.one type_int32s) (incrdecr_type ty)
  | Decr => Ebinop Osub a (Econst_int Int.one type_int32s) (incrdecr_type ty)
  end.

(** Generate a [Sset] or [Sbuiltin] operation as appropriate
  to dereference a l-value [l] and store its result in temporary variable [id]. *)

Definition chunk_for_volatile_type (ty: type) : option memory_chunk :=
  if type_is_volatile ty
  then match access_mode ty with By_value chunk => Some chunk | _ => None end
  else None.

Definition make_set (id: ident) (l: expr) : statement :=
  match chunk_for_volatile_type (typeof l) with
  | None => Sset id l
  | Some chunk =>
      let typtr := Tpointer (typeof l) noattr in
      Sbuiltin (Some id) (EF_vload chunk) (Tcons typtr Tnil) ((Eaddrof l typtr):: nil)
  end.

(** Translation of a "valof" operation.
  If the l-value accessed is of volatile type, we go through a temporary. *)

Definition transl_valof (ty: type) (l: expr) : mon (list statement * expr) :=
  if type_is_volatile ty
  then do t <- gensym ty; ret (make_set t l :: nil, Etempvar t ty)
  else ret (nil, l).

(** Translation of an assignment. *)

Definition make_assign (l r: expr) : statement :=
  match chunk_for_volatile_type (typeof l) with
  | None =>
      Sassign l r
  | Some chunk =>
      let ty := typeof l in
      let typtr := Tpointer ty noattr in
      Sbuiltin None (EF_vstore chunk) (Tcons typtr (Tcons ty Tnil))
                    (Eaddrof l typtr :: r :: nil)
  end.

(** Translation of expressions.  Return a pair [(sl, a)] of
    a list of statements [sl] and a pure expression [a].
- If the [dst] argument is [For_val], the statements [sl]
  perform the side effects of the original expression,
  and [a] evaluates to the same value as the original expression.
- If the [dst] argument is [For_effects], the statements [sl]
  perform the side effects of the original expression,
  and [a] is meaningless.
- If the [dst] argument is [For_set tyl tvar], the statements [sl]
  perform the side effects of the original expression, then
  assign the value of the original expression to the temporary [tvar].
  The value is casted according to the list of types [tyl] before
  assignment.  In this case, [a] is meaningless.
*)

Inductive set_destination : Type :=
  | SDbase (tycast ty: type) (tmp: ident)
  | SDcons (tycast ty: type) (tmp: ident) (sd: set_destination).

Inductive destination : Type :=
  | For_val
  | For_effects
  | For_set (sd: set_destination).

Definition dummy_expr := Econst_int Int.zero type_int32s.

Fixpoint do_set (sd: set_destination) (a: expr) : list statement :=
  match sd with
  | SDbase tycast ty tmp => Sset tmp (Ecast a tycast) :: nil
  | SDcons tycast ty tmp sd' => Sset tmp (Ecast a tycast) :: do_set sd' (Etempvar tmp ty)
  end.

Definition finish (dst: destination) (sl: list statement) (a: expr) :=
  match dst with
  | For_val => (sl, a)
  | For_effects => (sl, a)
  | For_set sd => (sl ++ do_set sd a, a)
  end.

Definition sd_temp (sd: set_destination) :=
  match sd with SDbase _ _ tmp => tmp | SDcons _ _ tmp _ => tmp end.
Definition sd_seqbool_val (tmp: ident) (ty: type) :=
  SDbase type_bool ty tmp.
Definition sd_seqbool_set (ty: type) (sd: set_destination) :=
  let tmp :=  sd_temp sd in SDcons type_bool ty tmp sd.

Fixpoint transl_expr (dst: destination) (a: Csyntax.expr) : mon (list statement * expr) :=
  match a with
  | Csyntax.Eloc b ofs ty =>
      error (msg "SimplExpr.transl_expr: Eloc")
  | Csyntax.Evar x ty =>
      ret (finish dst nil (Evar x ty))
  | Csyntax.Ederef r ty =>
      do (sl, a) <- transl_expr For_val r;
      ret (finish dst sl (Ederef' a ty))
  | Csyntax.Efield r f ty =>
      do (sl, a) <- transl_expr For_val r;
      ret (finish dst sl (Efield a f ty))
  | Csyntax.Eval (Vint n) ty =>
      ret (finish dst nil (Econst_int n ty))
  | Csyntax.Eval (Vfloat n) ty =>
      ret (finish dst nil (Econst_float n ty))
  | Csyntax.Eval (Vsingle n) ty =>
      ret (finish dst nil (Econst_single n ty))
  | Csyntax.Eval (Vlong n) ty =>
      ret (finish dst nil (Econst_long n ty))
  | Csyntax.Eval _ ty =>
      error (msg "SimplExpr.transl_expr: Eval")
  | Csyntax.Esizeof ty' ty =>
      ret (finish dst nil (Esizeof ty' ty))
  | Csyntax.Ealignof ty' ty =>
      ret (finish dst nil (Ealignof ty' ty))
  | Csyntax.Evalof l ty =>
      do (sl1, a1) <- transl_expr For_val l;
      do (sl2, a2) <- transl_valof (Csyntax.typeof l) a1;
      ret (finish dst (sl1 ++ sl2) a2)
  | Csyntax.Eaddrof l ty =>
      do (sl, a) <- transl_expr For_val l;
      ret (finish dst sl (Eaddrof' a ty))
  | Csyntax.Eunop op r1 ty =>
      do (sl1, a1) <- transl_expr For_val r1;
      ret (finish dst sl1 (Eunop op a1 ty))
  | Csyntax.Ebinop op r1 r2 ty =>
      do (sl1, a1) <- transl_expr For_val r1;
      do (sl2, a2) <- transl_expr For_val r2;
      ret (finish dst (sl1 ++ sl2) (Ebinop op a1 a2 ty))
  | Csyntax.Ecast r1 ty =>
      do (sl1, a1) <- transl_expr For_val r1;
      ret (finish dst sl1 (Ecast a1 ty))
  | Csyntax.Eseqand r1 r2 ty =>
      do (sl1, a1) <- transl_expr For_val r1;
      match dst with
      | For_val =>
          do t <- gensym ty;
          do (sl2, a2) <- transl_expr (For_set (sd_seqbool_val t ty)) r2;
          ret (sl1 ++
               makeif a1 (makeseq sl2) (Sset t (Econst_int Int.zero ty)) :: nil,
               Etempvar t ty)
      | For_effects =>
          do (sl2, a2) <- transl_expr For_effects r2;
          ret (sl1 ++ makeif a1 (makeseq sl2) Sskip :: nil, dummy_expr)
      | For_set sd =>
          do (sl2, a2) <- transl_expr (For_set (sd_seqbool_set ty sd)) r2;
          ret (sl1 ++
               makeif a1 (makeseq sl2) (makeseq (do_set sd (Econst_int Int.zero ty))) :: nil,
               dummy_expr)
      end
  | Csyntax.Eseqor r1 r2 ty =>
      do (sl1, a1) <- transl_expr For_val r1;
      match dst with
      | For_val =>
          do t <- gensym ty;
          do (sl2, a2) <- transl_expr (For_set (sd_seqbool_val t ty)) r2;
          ret (sl1 ++
               makeif a1 (Sset t (Econst_int Int.one ty)) (makeseq sl2) :: nil,
               Etempvar t ty)
      | For_effects =>
          do (sl2, a2) <- transl_expr For_effects r2;
          ret (sl1 ++ makeif a1 Sskip (makeseq sl2) :: nil, dummy_expr)
      | For_set sd =>
          do (sl2, a2) <- transl_expr (For_set (sd_seqbool_set ty sd)) r2;
          ret (sl1 ++
               makeif a1 (makeseq (do_set sd (Econst_int Int.one ty))) (makeseq sl2) :: nil,
               dummy_expr)
      end
  | Csyntax.Econdition r1 r2 r3 ty =>
      do (sl1, a1) <- transl_expr For_val r1;
      match dst with
      | For_val =>
          do t <- gensym ty;
          do (sl2, a2) <- transl_expr (For_set (SDbase ty ty t)) r2;
          do (sl3, a3) <- transl_expr (For_set (SDbase ty ty t)) r3;
          ret (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil,
               Etempvar t ty)
      | For_effects =>
          do (sl2, a2) <- transl_expr For_effects r2;
          do (sl3, a3) <- transl_expr For_effects r3;
          ret (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil,
               dummy_expr)
      | For_set sd =>
          do t <- gensym ty;
          do (sl2, a2) <- transl_expr (For_set (SDcons ty ty t sd)) r2;
          do (sl3, a3) <- transl_expr (For_set (SDcons ty ty t sd)) r3;
          ret (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil,
               dummy_expr)
      end
  | Csyntax.Eassign l1 r2 ty =>
      do (sl1, a1) <- transl_expr For_val l1;
      do (sl2, a2) <- transl_expr For_val r2;
      let ty1 := Csyntax.typeof l1 in
      let ty2 := Csyntax.typeof r2 in
      match dst with
      | For_val | For_set _ =>
          do t <- gensym ty1;
          ret (finish dst
                 (sl1 ++ sl2 ++ Sset t (Ecast a2 ty1) :: make_assign a1 (Etempvar t ty1) :: nil)
                 (Etempvar t ty1))
      | For_effects =>
          ret (sl1 ++ sl2 ++ make_assign a1 a2 :: nil,
               dummy_expr)
      end
  | Csyntax.Eassignop op l1 r2 tyres ty =>
      let ty1 := Csyntax.typeof l1 in
      do (sl1, a1) <- transl_expr For_val l1;
      do (sl2, a2) <- transl_expr For_val r2;
      do (sl3, a3) <- transl_valof ty1 a1;
      match dst with
      | For_val | For_set _ =>
          do t <- gensym ty1;
          ret (finish dst
                 (sl1 ++ sl2 ++ sl3 ++
                  Sset t (Ecast (Ebinop op a3 a2 tyres) ty1) ::
                  make_assign a1 (Etempvar t ty1) :: nil)
                 (Etempvar t ty1))
      | For_effects =>
          ret (sl1 ++ sl2 ++ sl3 ++ make_assign a1 (Ebinop op a3 a2 tyres) :: nil,
               dummy_expr)
      end
  | Csyntax.Epostincr id l1 ty =>
      let ty1 := Csyntax.typeof l1 in
      do (sl1, a1) <- transl_expr For_val l1;
      match dst with
      | For_val | For_set _ =>
          do t <- gensym ty1;
          ret (finish dst
                 (sl1 ++ make_set t a1 ::
                  make_assign a1 (transl_incrdecr id (Etempvar t ty1) ty1) :: nil)
                 (Etempvar t ty1))
      | For_effects =>
          do (sl2, a2) <- transl_valof ty1 a1;
          ret (sl1 ++ sl2 ++ make_assign a1 (transl_incrdecr id a2 ty1) :: nil,
               dummy_expr)
      end
  | Csyntax.Ecomma r1 r2 ty =>
      do (sl1, a1) <- transl_expr For_effects r1;
      do (sl2, a2) <- transl_expr dst r2;
      ret (sl1 ++ sl2, a2)
  | Csyntax.Ecall r1 rl2 ty =>
      do (sl1, a1) <- transl_expr For_val r1;
      do (sl2, al2) <- transl_exprlist rl2;
      match dst with
      | For_val | For_set _ =>
          do t <- gensym ty;
          ret (finish dst (sl1 ++ sl2 ++ Scall (Some t) a1 al2 :: nil)
                          (Etempvar t ty))
      | For_effects =>
          ret (sl1 ++ sl2 ++ Scall None a1 al2 :: nil, dummy_expr)
      end
  | Csyntax.Ebuiltin ef tyargs rl ty =>
      do (sl, al) <- transl_exprlist rl;
      match dst with
      | For_val | For_set _ =>
          do t <- gensym ty;
          ret (finish dst (sl ++ Sbuiltin (Some t) ef tyargs al :: nil)
                          (Etempvar t ty))
      | For_effects =>
          ret (sl ++ Sbuiltin None ef tyargs al :: nil, dummy_expr)
      end
  | Csyntax.Eparen r1 tycast ty =>
      error (msg "SimplExpr.transl_expr: paren")
  end

with transl_exprlist (rl: exprlist) : mon (list statement * list expr) :=
  match rl with
  | Csyntax.Enil =>
      ret (nil, nil)
  | Csyntax.Econs r1 rl2 =>
      do (sl1, a1) <- transl_expr For_val r1;
      do (sl2, al2) <- transl_exprlist rl2;
      ret (sl1 ++ sl2, a1 :: al2)
  end.

Definition transl_expression (r: Csyntax.expr) : mon (statement * expr) :=
  do (sl, a) <- transl_expr For_val r; ret (makeseq sl, a).

Definition transl_expr_stmt (r: Csyntax.expr) : mon statement :=
  do (sl, a) <- transl_expr For_effects r; ret (makeseq sl).

(*
Definition transl_if (r: Csyntax.expr) (s1 s2: statement) : mon statement :=
  do (sl, a) <- transl_expr For_val r;
  ret (makeseq (sl ++ makeif a s1 s2 :: nil)).
*)

Definition transl_if (r: Csyntax.expr) (s1 s2: statement) : mon statement :=
  do (sl, a) <- transl_expr For_val r;
  ret (makeseq (sl ++ makeif a s1 s2 :: nil)).

(** Translation of statements *)

Definition expr_true := Econst_int Int.one type_int32s.

Definition is_Sskip:
  forall s, {s = Csyntax.Sskip} + {s <> Csyntax.Sskip}.
Proof.
  destruct s; ((left; reflexivity) || (right; congruence)).
Defined.

Fixpoint transl_stmt (s: Csyntax.statement) : mon statement :=
  match s with
  | Csyntax.Sskip => ret Sskip
  | Csyntax.Sdo e => transl_expr_stmt e
  | Csyntax.Ssequence s1 s2 =>
      do ts1 <- transl_stmt s1;
      do ts2 <- transl_stmt s2;
      ret (Ssequence ts1 ts2)
  | Csyntax.Sifthenelse e s1 s2 =>
      do ts1 <- transl_stmt s1;
      do ts2 <- transl_stmt s2;
      do (s', a) <- transl_expression e;
      if is_Sskip s1 && is_Sskip s2 then
        ret (Ssequence s' Sskip)
      else
        ret (Ssequence s' (Sifthenelse a ts1 ts2))
  | Csyntax.Swhile e s1 =>
      do s' <- transl_if e Sskip Sbreak;
      do ts1 <- transl_stmt s1;
      ret (Sloop (Ssequence s' ts1) Sskip)
  | Csyntax.Sdowhile e s1 =>
      do s' <- transl_if e Sskip Sbreak;
      do ts1 <- transl_stmt s1;
      ret (Sloop ts1 s')
  | Csyntax.Sfor s1 e2 s3 s4 =>
      do ts1 <- transl_stmt s1;
      do s' <- transl_if e2 Sskip Sbreak;
      do ts3 <- transl_stmt s3;
      do ts4 <- transl_stmt s4;
      if is_Sskip s1 then
        ret (Sloop (Ssequence s' ts4) ts3)
      else
        ret (Ssequence ts1 (Sloop (Ssequence s' ts4) ts3))
  | Csyntax.Sbreak =>
      ret Sbreak
  | Csyntax.Scontinue =>
      ret Scontinue
  | Csyntax.Sreturn None =>
      ret (Sreturn None)
  | Csyntax.Sreturn (Some e) =>
      do (s', a) <- transl_expression e;
      ret (Ssequence s' (Sreturn (Some a)))
  | Csyntax.Sswitch e ls =>
      do (s', a) <- transl_expression e;
      do tls <- transl_lblstmt ls;
      ret (Ssequence s' (Sswitch a tls))
  | Csyntax.Slabel lbl s1 =>
      do ts1 <- transl_stmt s1;
      ret (Slabel lbl ts1)
  | Csyntax.Sgoto lbl =>
      ret (Sgoto lbl)
  end

with transl_lblstmt (ls: Csyntax.labeled_statements) : mon labeled_statements :=
  match ls with
  | Csyntax.LSnil =>
      ret LSnil
  | Csyntax.LScons c s ls1 =>
      do ts <- transl_stmt s;
      do tls1 <- transl_lblstmt ls1;
      ret (LScons c ts tls1)
  end.

(** Translation of a function *)

Definition transl_function (f: Csyntax.function) : res function :=
  match transl_stmt f.(Csyntax.fn_body) (initial_generator tt) with
  | Err msg =>
      Error msg
  | Res tbody g i =>
      OK (mkfunction
              f.(Csyntax.fn_return)
              f.(Csyntax.fn_callconv)
              f.(Csyntax.fn_params)
              f.(Csyntax.fn_vars)
              g.(gen_trail)
              tbody)
  end.

Local Open Scope error_monad_scope.

Definition transl_fundef (fd: Csyntax.fundef) : res fundef :=
  match fd with
  | Internal f =>
      do tf <- transl_function f; OK (Internal tf)
  | External ef targs tres cc =>
      OK (External ef targs tres cc)
  end.

Definition transl_program (p: Csyntax.program) : res program :=
  do p1 <- AST.transform_partial_program transl_fundef p;
  OK {| prog_defs := AST.prog_defs p1;
        prog_public := AST.prog_public p1;
        prog_main := AST.prog_main p1;
        prog_types := prog_types p;
        prog_comp_env := prog_comp_env p;
        prog_comp_env_eq := prog_comp_env_eq p |}.
