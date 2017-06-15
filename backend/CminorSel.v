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
  | Econdition : condexpr -> expr -> expr -> expr
  | Elet : expr -> expr -> expr
  | Eletvar : nat -> expr
  | Ebuiltin : external_function -> exprlist -> expr
  | Eexternal : ident -> signature -> exprlist -> expr

with exprlist : Type :=
  | Enil: exprlist
  | Econs: expr -> exprlist -> exprlist

with condexpr : Type :=
  | CEcond : condition -> exprlist -> condexpr
  | CEcondition : condexpr -> condexpr -> condexpr -> condexpr
  | CElet: expr -> condexpr -> condexpr.

Infix ":::" := Econs (at level 60, right associativity) : cminorsel_scope.

(** Conditional expressions [condexpr] are expressions that are evaluated
  not for their exact value, but for their [true]/[false] Boolean value.
  Likewise, exit expressions [exitexpr] are expressions that evaluate
  to an exit number.  They are used to compile the [Sswitch] statement
  of Cminor. *)

Inductive exitexpr : Type :=
  | XEexit: nat -> exitexpr
  | XEjumptable: expr -> list nat -> exitexpr
  | XEcondition: condexpr -> exitexpr -> exitexpr -> exitexpr
  | XElet: expr -> exitexpr -> exitexpr.

(** Statements are as in Cminor, except that the [Sifthenelse]
  construct uses a conditional expression, and the [Sstore] construct
  uses a machine-dependent addressing mode. *)

Inductive stmt : Type :=
  | Sskip: stmt
  | Sassign : ident -> expr -> stmt
  | Sstore : memory_chunk -> addressing -> exprlist -> expr -> stmt
  | Scall : option ident -> signature -> expr + ident -> exprlist -> stmt
  | Stailcall: signature -> expr + ident -> exprlist -> stmt
  | Sbuiltin : builtin_res ident -> external_function -> list (builtin_arg expr) -> stmt
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: condexpr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt
  | Sswitch: exitexpr -> stmt
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
  | eval_Econdition: forall le a b c va v,
      eval_condexpr le a va ->
      eval_expr le (if va then b else c) v ->
      eval_expr le (Econdition a b c) v
  | eval_Elet: forall le a b v1 v2,
      eval_expr le a v1 ->
      eval_expr (v1 :: le) b v2 ->
      eval_expr le (Elet a b) v2
  | eval_Eletvar: forall le n v,
      nth_error le n = Some v ->
      eval_expr le (Eletvar n) v
  | eval_Ebuiltin: forall le ef al vl v,
      eval_exprlist le al vl ->
      external_call ef ge vl m E0 v m ->
      eval_expr le (Ebuiltin ef al) v
  | eval_Eexternal: forall le id sg al b ef vl v,
      Genv.find_symbol ge id = Some b ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      ef_sig ef = sg ->
      eval_exprlist le al vl ->
      external_call ef ge vl m E0 v m ->
      eval_expr le (Eexternal id sg al) v

with eval_exprlist: letenv -> exprlist -> list val -> Prop :=
  | eval_Enil: forall le,
      eval_exprlist le Enil nil
  | eval_Econs: forall le a1 al v1 vl,
      eval_expr le a1 v1 -> eval_exprlist le al vl ->
      eval_exprlist le (Econs a1 al) (v1 :: vl)

with eval_condexpr: letenv -> condexpr -> bool -> Prop :=
  | eval_CEcond: forall le cond al vl vb,
      eval_exprlist le al vl ->
      eval_condition cond vl m = Some vb ->
      eval_condexpr le (CEcond cond al) vb
  | eval_CEcondition: forall le a b c va v,
      eval_condexpr le a va ->
      eval_condexpr le (if va then b else c) v ->
      eval_condexpr le (CEcondition a b c) v
  | eval_CElet: forall le a b v1 v2,
      eval_expr le a v1 ->
      eval_condexpr (v1 :: le) b v2 ->
      eval_condexpr le (CElet a b) v2.

Scheme eval_expr_ind3 := Minimality for eval_expr Sort Prop
  with eval_exprlist_ind3 := Minimality for eval_exprlist Sort Prop
  with eval_condexpr_ind3 := Minimality for eval_condexpr Sort Prop.

Inductive eval_exitexpr: letenv -> exitexpr -> nat -> Prop :=
  | eval_XEexit: forall le x,
      eval_exitexpr le (XEexit x) x
  | eval_XEjumptable: forall le a tbl n x,
      eval_expr le a (Vint n) ->
      list_nth_z tbl (Int.unsigned n) = Some x ->
      eval_exitexpr le (XEjumptable a tbl) x
  | eval_XEcondition: forall le a b c va x,
      eval_condexpr le a va ->
      eval_exitexpr le (if va then b else c) x ->
      eval_exitexpr le (XEcondition a b c) x
  | eval_XElet: forall le a b v x,
      eval_expr le a v ->
      eval_exitexpr (v :: le) b x ->
      eval_exitexpr le (XElet a b) x.

Inductive eval_expr_or_symbol: letenv -> expr + ident -> val -> Prop :=
  | eval_eos_e: forall le e v,
      eval_expr le e v ->
      eval_expr_or_symbol le (inl _ e) v
  | eval_eos_s: forall le id b,
      Genv.find_symbol ge id = Some b ->
      eval_expr_or_symbol le (inr _ id) (Vptr b Ptrofs.zero).

Inductive eval_builtin_arg: builtin_arg expr -> val -> Prop :=
  | eval_BA: forall a v,
      eval_expr nil a v ->
      eval_builtin_arg (BA a) v
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
      Mem.loadv chunk m (Genv.symbol_address ge id ofs) = Some v ->
      eval_builtin_arg (BA_loadglobal chunk id ofs) v
  | eval_BA_addrglobal: forall id ofs,
      eval_builtin_arg (BA_addrglobal id ofs) (Genv.symbol_address ge id ofs)
  | eval_BA_splitlong: forall a1 a2 v1 v2,
      eval_expr nil a1 v1 -> eval_expr nil a2 v2 ->
      eval_builtin_arg (BA_splitlong (BA a1) (BA a2)) (Val.longofwords v1 v2)
  | eval_BA_addptr: forall a1 v1 a2 v2,
      eval_builtin_arg a1 v1 -> eval_builtin_arg a2 v2 ->
      eval_builtin_arg (BA_addptr a1 a2)
                       (if Archi.ptr64 then Val.addl v1 v2 else Val.add v1 v2).

End EVAL_EXPR.

(** Update local environment with the result of a builtin. *)

Definition set_builtin_res (res: builtin_res ident) (v: val) (e: env) : env :=
  match res with
  | BR id => PTree.set id v e
  | _ => e
  end.

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
  | Sifthenelse c s1 s2 =>
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
      step (State f Sskip k (Vptr sp Ptrofs.zero) e m)
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
      eval_expr_or_symbol (Vptr sp Ptrofs.zero) e m nil a vf ->
      eval_exprlist (Vptr sp Ptrofs.zero) e m nil bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f (Stailcall sig a bl) k (Vptr sp Ptrofs.zero) e m)
        E0 (Callstate fd vargs (call_cont k) m')

  | step_builtin: forall f res ef al k sp e m vl t v m',
      list_forall2 (eval_builtin_arg sp e m) al vl ->
      external_call ef ge vl m t v m' ->
      step (State f (Sbuiltin res ef al) k sp e m)
         t (State f Sskip k sp (set_builtin_res res v e) m')

  | step_seq: forall f s1 s2 k sp e m,
      step (State f (Sseq s1 s2) k sp e m)
        E0 (State f s1 (Kseq s2 k) sp e m)

  | step_ifthenelse: forall f c s1 s2 k sp e m b,
      eval_condexpr sp e m nil c b ->
      step (State f (Sifthenelse c s1 s2) k sp e m)
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

  | step_switch: forall f a k sp e m n,
      eval_exitexpr sp e m nil a n ->
      step (State f (Sswitch a) k sp e m)
        E0 (State f (Sexit n) k sp e m)

  | step_return_0: forall f k sp e m m',
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f (Sreturn None) k (Vptr sp Ptrofs.zero) e m)
        E0 (Returnstate Vundef (call_cont k) m')
  | step_return_1: forall f a k sp e m v m',
      eval_expr (Vptr sp Ptrofs.zero) e m nil a v ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f (Sreturn (Some a)) k (Vptr sp Ptrofs.zero) e m)
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
        E0 (State f f.(fn_body) k (Vptr sp Ptrofs.zero) e m')
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
      funsig f = signature_main ->
      initial_state p (Callstate f nil Kstop m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (Returnstate (Vint r) Kstop m) r.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

Hint Constructors eval_expr eval_exprlist eval_condexpr: evalexpr.

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
  | Econdition a b c =>
      Econdition (lift_condexpr p a) (lift_expr p b) (lift_expr p c)
  | Elet b c => Elet (lift_expr p b) (lift_expr (S p) c)
  | Eletvar n =>
      if le_gt_dec p n then Eletvar (S n) else Eletvar n
  | Ebuiltin ef bl => Ebuiltin ef (lift_exprlist p bl)
  | Eexternal id sg bl => Eexternal id sg (lift_exprlist p bl)
  end

with lift_exprlist (p: nat) (a: exprlist) {struct a}: exprlist :=
  match a with
  | Enil => Enil
  | Econs b cl => Econs (lift_expr p b) (lift_exprlist p cl)
  end

with lift_condexpr (p: nat) (a: condexpr) {struct a}: condexpr :=
  match a with
  | CEcond c al => CEcond c (lift_exprlist p al)
  | CEcondition a b c => CEcondition (lift_condexpr p a) (lift_condexpr p b) (lift_condexpr p c)
  | CElet a b => CElet (lift_expr p a) (lift_condexpr (S p) b)
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
  apply (eval_expr_ind3 ge sp e m
    (fun le a v =>
      forall p le', insert_lenv le p w le' ->
      eval_expr ge sp e m le' (lift_expr p a) v)
    (fun le al vl =>
      forall p le', insert_lenv le p w le' ->
      eval_exprlist ge sp e m le' (lift_exprlist p al) vl)
    (fun le a b =>
      forall p le', insert_lenv le p w le' ->
      eval_condexpr ge sp e m le' (lift_condexpr p a) b));
  simpl; intros; eauto with evalexpr.

  eapply eval_Econdition; eauto. destruct va; eauto.

  eapply eval_Elet. eauto. apply H2. apply insert_lenv_S; auto.

  case (le_gt_dec p n); intro.
  apply eval_Eletvar. eapply insert_lenv_lookup2; eauto.
  apply eval_Eletvar. eapply insert_lenv_lookup1; eauto.

  eapply eval_CEcondition; eauto. destruct va; eauto.
  eapply eval_CElet; eauto. apply H2. constructor; auto.
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
