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

(** The Cminor language after instruction selection. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Events.
Require Import Values.
Require Import Memory.
Require Import Cminor.
Require Import Op.
Require Import Globalenvs.
Require Import Switch.
Require Import Smallstep.

(** * Abstract syntax *)

(** CminorSel programs share the general structure of Cminor programs:
  functions, statements and expressions.  However, CminorSel uses
  machine-dependent operations, addressing modes and conditions,
  as defined in module [Op] and used in lower-level intermediate
  languages ([RTL] and below).  Moreover, to express sharing of
  sub-computations, a "let" binding is provided (constructions
  [Elet] and [Eletvar]), using de Bruijn indices to refer to "let"-bound
  variables. *)

Inductive expr : Type :=
  | Evar : ident -> expr
  | Eop : operation -> exprlist -> expr
  | Eload : memory_chunk -> addressing -> exprlist -> expr
  | Econdition : condition -> exprlist -> expr -> expr -> expr
  | Elet : expr -> expr -> expr
  | Eletvar : nat -> expr

with exprlist : Type :=
  | Enil: exprlist
  | Econs: expr -> exprlist -> exprlist.

Infix ":::" := Econs (at level 60, right associativity) : cminorsel_scope.

(** Statements are as in Cminor, except that the [Sifthenelse]
  construct uses a machine-dependent condition (with multiple
  arguments), and the [Sstore] construct uses a machine-dependent
  addressing mode. *)

Inductive stmt : Type :=
  | Sskip: stmt
  | Sassign : ident -> expr -> stmt
  | Sstore : memory_chunk -> addressing -> exprlist -> expr -> stmt
  | Scall : option ident -> signature -> expr + ident -> exprlist -> stmt
  | Stailcall: signature -> expr + ident -> exprlist -> stmt
  | Sbuiltin : option ident -> external_function -> exprlist -> stmt
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: condition -> exprlist -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt
  | Sswitch: expr -> list (int * nat) -> nat -> stmt
  | Sreturn: option expr -> stmt
  | Slabel: label -> stmt -> stmt
  | Sgoto: label -> stmt.

Record function : Type := mkfunction {
  fn_sig: signature;
  fn_params: list ident;
  fn_vars: list ident;
  fn_stackspace: Z;
  fn_body: stmt
}.

Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

(** * Operational semantics *)

(** Three kinds of evaluation environments are involved:
- [genv]: global environments, define symbols and functions;
- [env]: local environments, map local variables to values;
- [lenv]: let environments, map de Bruijn indices to values.
*)

Definition genv := Genv.t fundef unit.
Definition letenv := list val.

(** Continuations *)

Inductive cont: Type :=
  | Kstop: cont                         (**r stop program execution *)
  | Kseq: stmt -> cont -> cont          (**r execute stmt, then cont *)
  | Kblock: cont -> cont                (**r exit a block, then do cont *)
  | Kcall: option ident -> function -> val -> env -> cont -> cont.
                                        (**r return to caller *)

(** States *)

Inductive state: Type :=
  | State:                              (**r execution within a function *)
      forall (f: function)              (**r currently executing function  *)
             (s: stmt)                  (**r statement under consideration *)
             (k: cont)                  (**r its continuation -- what to do next *)
             (sp: val)                  (**r current stack pointer *)
             (e: env)                   (**r current local environment *)
             (m: mem),                  (**r current memory state *)
      state
  | Callstate:                          (**r invocation of a fundef  *)
      forall (f: fundef)                (**r fundef to invoke *)
             (args: list val)           (**r arguments provided by caller *)
             (k: cont)                  (**r what to do next  *)
             (m: mem),                  (**r memory state *)
      state
  | Returnstate:
      forall (v: val)                   (**r return value *)
             (k: cont)                  (**r what to do next *)
             (m: mem),                  (**r memory state *)
      state.

Section RELSEM.

Variable ge: genv.

(** The evaluation predicates have the same general shape as those
    of Cminor.  Refer to the description of Cminor semantics for
    the meaning of the parameters of the predicates. *)

Section EVAL_EXPR.

Variable sp: val.
Variable e: env.
Variable m: mem.

Inductive eval_expr: letenv -> expr -> val -> Prop :=
  | eval_Evar: forall le id v,
      PTree.get id e = Some v ->
      eval_expr le (Evar id) v
  | eval_Eop: forall le op al vl v,
      eval_exprlist le al vl ->
      eval_operation ge sp op vl m = Some v ->
      eval_expr le (Eop op al) v
  | eval_Eload: forall le chunk addr al vl vaddr v,
      eval_exprlist le al vl ->
      eval_addressing ge sp addr vl = Some vaddr ->
      Mem.loadv chunk m vaddr = Some v ->     
      eval_expr le (Eload chunk addr al) v
  | eval_Econdition: forall le cond al b c vl vb v,
      eval_exprlist le al vl ->
      eval_condition cond vl m = Some vb ->
      eval_expr le (if vb then b else c) v ->
      eval_expr le (Econdition cond al b c) v
  | eval_Elet: forall le a b v1 v2,
      eval_expr le a v1 ->
      eval_expr (v1 :: le) b v2 ->
      eval_expr le (Elet a b) v2
  | eval_Eletvar: forall le n v,
      nth_error le n = Some v ->
      eval_expr le (Eletvar n) v

with eval_exprlist: letenv -> exprlist -> list val -> Prop :=
  | eval_Enil: forall le,
      eval_exprlist le Enil nil
  | eval_Econs: forall le a1 al v1 vl,
      eval_expr le a1 v1 -> eval_exprlist le al vl ->
      eval_exprlist le (Econs a1 al) (v1 :: vl).

Scheme eval_expr_ind2 := Minimality for eval_expr Sort Prop
  with eval_exprlist_ind2 := Minimality for eval_exprlist Sort Prop.

Inductive eval_expr_or_symbol: letenv -> expr + ident -> val -> Prop :=
  | eval_eos_e: forall le e v,
      eval_expr le e v ->
      eval_expr_or_symbol le (inl _ e) v
  | eval_eos_s: forall le id b,
      Genv.find_symbol ge id = Some b ->
      eval_expr_or_symbol le (inr _ id) (Vptr b Int.zero).

End EVAL_EXPR.

(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kblock k => call_cont k
  | _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.

(** Find the statement and manufacture the continuation 
  corresponding to a label *)

Fixpoint find_label (lbl: label) (s: stmt) (k: cont) 
                    {struct s}: option (stmt * cont) :=
  match s with
  | Sseq s1 s2 =>
      match find_label lbl s1 (Kseq s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sifthenelse cond al s1 s2 =>
      match find_label lbl s1 k with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sloop s1 =>
      find_label lbl s1 (Kseq (Sloop s1) k)
  | Sblock s1 =>
      find_label lbl s1 (Kblock k)
  | Slabel lbl' s' =>
      if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
  | _ => None
  end.

(** One step of execution *)

Inductive step: state -> trace -> state -> Prop :=

  | step_skip_seq: forall f s k sp e m,
      step (State f Sskip (Kseq s k) sp e m)
        E0 (State f s k sp e m)
  | step_skip_block: forall f k sp e m,
      step (State f Sskip (Kblock k) sp e m)
        E0 (State f Sskip k sp e m)
  | step_skip_call: forall f k sp e m m',
      is_call_cont k ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f Sskip k (Vptr sp Int.zero) e m)
        E0 (Returnstate Vundef k m')

  | step_assign: forall f id a k sp e m v,
      eval_expr sp e m nil a v ->
      step (State f (Sassign id a) k sp e m)
        E0 (State f Sskip k sp (PTree.set id v e) m)

  | step_store: forall f chunk addr al b k sp e m vl v vaddr m',
      eval_exprlist sp e m nil al vl ->
      eval_expr sp e m nil b v ->
      eval_addressing ge sp addr vl = Some vaddr ->
      Mem.storev chunk m vaddr v = Some m' ->
      step (State f (Sstore chunk addr al b) k sp e m)
        E0 (State f Sskip k sp e m')

  | step_call: forall f optid sig a bl k sp e m vf vargs fd,
      eval_expr_or_symbol sp e m nil a vf ->
      eval_exprlist sp e m nil bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      step (State f (Scall optid sig a bl) k sp e m)
        E0 (Callstate fd vargs (Kcall optid f sp e k) m)

  | step_tailcall: forall f sig a bl k sp e m vf vargs fd m',
      eval_expr_or_symbol (Vptr sp Int.zero) e m nil a vf ->
      eval_exprlist (Vptr sp Int.zero) e m nil bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f (Stailcall sig a bl) k (Vptr sp Int.zero) e m)
        E0 (Callstate fd vargs (call_cont k) m')

  | step_builtin: forall f optid ef al k sp e m vl t v m',
      eval_exprlist sp e m nil al vl ->
      external_call ef ge vl m t v m' ->
      step (State f (Sbuiltin optid ef al) k sp e m)
         t (State f Sskip k sp (set_optvar optid v e) m')

  | step_seq: forall f s1 s2 k sp e m,
      step (State f (Sseq s1 s2) k sp e m)
        E0 (State f s1 (Kseq s2 k) sp e m)

  | step_ifthenelse: forall f cond al s1 s2 k sp e m vl b,
      eval_exprlist sp e m nil al vl ->
      eval_condition cond vl m = Some b ->
      step (State f (Sifthenelse cond al s1 s2) k sp e m)
        E0 (State f (if b then s1 else s2) k sp e m)

  | step_loop: forall f s k sp e m,
      step (State f (Sloop s) k sp e m)
        E0 (State f s (Kseq (Sloop s) k) sp e m)

  | step_block: forall f s k sp e m,
      step (State f (Sblock s) k sp e m)
        E0 (State f s (Kblock k) sp e m)

  | step_exit_seq: forall f n s k sp e m,
      step (State f (Sexit n) (Kseq s k) sp e m)
        E0 (State f (Sexit n) k sp e m)
  | step_exit_block_0: forall f k sp e m,
      step (State f (Sexit O) (Kblock k) sp e m)
        E0 (State f Sskip k sp e m)
  | step_exit_block_S: forall f n k sp e m,
      step (State f (Sexit (S n)) (Kblock k) sp e m)
        E0 (State f (Sexit n) k sp e m)

  | step_switch: forall f a cases default k sp e m n,
      eval_expr sp e m nil a (Vint n) ->
      step (State f (Sswitch a cases default) k sp e m)
        E0 (State f (Sexit (switch_target n default cases)) k sp e m)

  | step_return_0: forall f k sp e m m',
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f (Sreturn None) k (Vptr sp Int.zero) e m)
        E0 (Returnstate Vundef (call_cont k) m')
  | step_return_1: forall f a k sp e m v m',
      eval_expr (Vptr sp Int.zero) e m nil a v ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f (Sreturn (Some a)) k (Vptr sp Int.zero) e m)
        E0 (Returnstate v (call_cont k) m')

  | step_label: forall f lbl s k sp e m,
      step (State f (Slabel lbl s) k sp e m)
        E0 (State f s k sp e m)

  | step_goto: forall f lbl k sp e m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some(s', k') ->
      step (State f (Sgoto lbl) k sp e m)
        E0 (State f s' k' sp e m)

  | step_internal_function: forall f vargs k m m' sp e,
      Mem.alloc m 0 f.(fn_stackspace) = (m', sp) ->
      set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
      step (Callstate (Internal f) vargs k m)
        E0 (State f f.(fn_body) k (Vptr sp Int.zero) e m')
  | step_external_function: forall ef vargs k m t vres m',
      external_call ef ge vargs m t vres m' ->
      step (Callstate (External ef) vargs k m)
         t (Returnstate vres k m')        

  | step_return: forall v optid f sp e k m,
      step (Returnstate v (Kcall optid f sp e k) m)
        E0 (State f Sskip k sp (set_optvar optid v e) m).

End RELSEM.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      initial_state p (Callstate f nil Kstop m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (Returnstate (Vint r) Kstop m) r.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

Hint Constructors eval_expr eval_exprlist: evalexpr.

(** * Lifting of let-bound variables *)

(** Instruction selection sometimes generate [Elet] constructs to
  share the evaluation of a subexpression.  Owing to the use of de
  Bruijn indices for let-bound variables, we need to shift de Bruijn
  indices when an expression [b] is put in a [Elet a b] context. *)

Fixpoint lift_expr (p: nat) (a: expr) {struct a}: expr :=
  match a with
  | Evar id => Evar id
  | Eop op bl => Eop op (lift_exprlist p bl)
  | Eload chunk addr bl => Eload chunk addr (lift_exprlist p bl)
  | Econdition cond al b c =>
      Econdition cond (lift_exprlist p al) (lift_expr p b) (lift_expr p c)
  | Elet b c => Elet (lift_expr p b) (lift_expr (S p) c)
  | Eletvar n =>
      if le_gt_dec p n then Eletvar (S n) else Eletvar n
  end

with lift_exprlist (p: nat) (a: exprlist) {struct a}: exprlist :=
  match a with
  | Enil => Enil
  | Econs b cl => Econs (lift_expr p b) (lift_exprlist p cl)
  end.

Definition lift (a: expr): expr := lift_expr O a.

(** We now relate the evaluation of a lifted expression with that
    of the original expression. *)

Inductive insert_lenv: letenv -> nat -> val -> letenv -> Prop :=
  | insert_lenv_0:
      forall le v,
      insert_lenv le O v (v :: le)
  | insert_lenv_S:
      forall le p w le' v,
      insert_lenv le p w le' ->
      insert_lenv (v :: le) (S p) w (v :: le').

Lemma insert_lenv_lookup1:
  forall le p w le',
  insert_lenv le p w le' ->
  forall n v,
  nth_error le n = Some v -> (p > n)%nat ->
  nth_error le' n = Some v.
Proof.
  induction 1; intros.
  omegaContradiction.
  destruct n; simpl; simpl in H0. auto. 
  apply IHinsert_lenv. auto. omega.
Qed.

Lemma insert_lenv_lookup2:
  forall le p w le',
  insert_lenv le p w le' ->
  forall n v,
  nth_error le n = Some v -> (p <= n)%nat ->
  nth_error le' (S n) = Some v.
Proof.
  induction 1; intros.
  simpl. assumption.
  simpl. destruct n. omegaContradiction. 
  apply IHinsert_lenv. exact H0. omega.
Qed.

Lemma eval_lift_expr:
  forall ge sp e m w le a v,
  eval_expr ge sp e m le a v ->
  forall p le', insert_lenv le p w le' ->
  eval_expr ge sp e m le' (lift_expr p a) v.
Proof.
  intros until w.
  apply (eval_expr_ind2 ge sp e m
    (fun le a v =>
      forall p le', insert_lenv le p w le' ->
      eval_expr ge sp e m le' (lift_expr p a) v)
    (fun le al vl =>
      forall p le', insert_lenv le p w le' ->
      eval_exprlist ge sp e m le' (lift_exprlist p al) vl));
  simpl; intros; eauto with evalexpr.

  eapply eval_Econdition; eauto. destruct vb; eauto.

  eapply eval_Elet. eauto. apply H2. apply insert_lenv_S; auto.

  case (le_gt_dec p n); intro. 
  apply eval_Eletvar. eapply insert_lenv_lookup2; eauto.
  apply eval_Eletvar. eapply insert_lenv_lookup1; eauto.
Qed.

Lemma eval_lift:
  forall ge sp e m le a v w,
  eval_expr ge sp e m le a v ->
  eval_expr ge sp e m (w::le) (lift a) v.
Proof.
  intros. unfold lift. eapply eval_lift_expr.
  eexact H. apply insert_lenv_0. 
Qed.

Hint Resolve eval_lift: evalexpr.

