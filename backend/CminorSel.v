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
Require Import Floats.
Require Import Events.
Require Import Values.
Require Import Mem.
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
  variables.  Finally, a variant [condexpr] of [expr]
  is used to represent expressions which are evaluated for their
  boolean value only and not their exact value.
*)

Inductive expr : Set :=
  | Evar : ident -> expr
  | Eop : operation -> exprlist -> expr
  | Eload : memory_chunk -> addressing -> exprlist -> expr
  | Econdition : condexpr -> expr -> expr -> expr
  | Elet : expr -> expr -> expr
  | Eletvar : nat -> expr

with condexpr : Set :=
  | CEtrue: condexpr
  | CEfalse: condexpr
  | CEcond: condition -> exprlist -> condexpr
  | CEcondition : condexpr -> condexpr -> condexpr -> condexpr

with exprlist : Set :=
  | Enil: exprlist
  | Econs: expr -> exprlist -> exprlist.

(** Statements are as in Cminor, except that the condition of an
  if/then/else conditional is a [condexpr], and the [Sstore] construct
  uses a machine-dependent addressing mode. *)

Inductive stmt : Set :=
  | Sskip: stmt
  | Sassign : ident -> expr -> stmt
  | Sstore : memory_chunk -> addressing -> exprlist -> expr -> stmt
  | Scall : option ident -> signature -> expr -> exprlist -> stmt
  | Salloc : ident -> expr -> stmt
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: condexpr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt
  | Sswitch: expr -> list (int * nat) -> nat -> stmt
  | Sreturn: option expr -> stmt
  | Stailcall: signature -> expr -> exprlist -> stmt.

Record function : Set := mkfunction {
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
  | Internal f => f.(fn_sig)
  | External ef => ef.(ef_sig)
  end.

(** * Operational semantics *)

(** Three kinds of evaluation environments are involved:
- [genv]: global environments, define symbols and functions;
- [env]: local environments, map local variables to values;
- [lenv]: let environments, map de Bruijn indices to values.
*)

Definition genv := Genv.t fundef.
Definition letenv := list val.

Section RELSEM.

Variable ge: genv.

(** The evaluation predicates have the same general shape as those
    of Cminor.  Refer to the description of Cminor semantics for
    the meaning of the parameters of the predicates.
    One additional predicate is introduced:
    [eval_condexpr ge sp e m le a b], meaning that the conditional
    expression [a] evaluates to the boolean [b]. *)

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
  | eval_Econdition: forall le a b c v1 v2,
      eval_condexpr le a v1 ->
      eval_expr le (if v1 then b else c) v2 ->
      eval_expr le (Econdition a b c) v2
  | eval_Elet: forall le a b v1 v2,
      eval_expr le a v1 ->
      eval_expr (v1 :: le) b v2 ->
      eval_expr le (Elet a b) v2
  | eval_Eletvar: forall le n v,
      nth_error le n = Some v ->
      eval_expr le (Eletvar n) v

with eval_condexpr: letenv -> condexpr -> bool -> Prop :=
  | eval_CEtrue: forall le,
      eval_condexpr le CEtrue true
  | eval_CEfalse: forall le,
      eval_condexpr le CEfalse false
  | eval_CEcond: forall le cond al vl b,
      eval_exprlist le al vl ->
      eval_condition cond vl m = Some b ->
      eval_condexpr le (CEcond cond al) b
  | eval_CEcondition: forall le a b c vb1 vb2,
      eval_condexpr le a vb1 ->
      eval_condexpr le (if vb1 then b else c) vb2 ->
      eval_condexpr le (CEcondition a b c) vb2

with eval_exprlist: letenv -> exprlist -> list val -> Prop :=
  | eval_Enil: forall le,
      eval_exprlist le Enil nil
  | eval_Econs: forall le a1 al v1 vl,
      eval_expr le a1 v1 -> eval_exprlist le al vl ->
      eval_exprlist le (Econs a1 al) (v1 :: vl).

Scheme eval_expr_ind3 := Minimality for eval_expr Sort Prop
  with eval_condexpr_ind3 := Minimality for eval_condexpr Sort Prop
  with eval_exprlist_ind3 := Minimality for eval_exprlist Sort Prop.

End EVAL_EXPR.

Inductive eval_funcall:
        mem -> fundef -> list val -> trace ->
        mem -> val -> Prop :=
  | eval_funcall_internal:
      forall m f vargs m1 sp e t e2 m2 out vres,
      Mem.alloc m 0 f.(fn_stackspace) = (m1, sp) ->
      set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
      exec_stmt (Vptr sp Int.zero) e m1 f.(fn_body) t e2 m2 out ->
      outcome_result_value out f.(fn_sig).(sig_res) vres ->
      eval_funcall m (Internal f) vargs t (outcome_free_mem out m2 sp) vres
  | eval_funcall_external:
      forall ef m args t res,
      event_match ef args t res ->
      eval_funcall m (External ef) args t m res

with exec_stmt:
         val ->
         env -> mem -> stmt -> trace ->
         env -> mem -> outcome -> Prop :=
  | exec_Sskip:
      forall sp e m,
      exec_stmt sp e m Sskip E0 e m Out_normal
  | exec_Sassign:
      forall sp e m id a v,
      eval_expr sp e m nil a v ->
      exec_stmt sp e m (Sassign id a) E0 (PTree.set id v e) m Out_normal
  | exec_Sstore:
      forall sp e m chunk addr al b vl v vaddr m',
      eval_exprlist sp e m nil al vl ->
      eval_expr sp e m nil b v ->
      eval_addressing ge sp addr vl = Some vaddr ->
      Mem.storev chunk m vaddr v = Some m' ->
      exec_stmt sp e m (Sstore chunk addr al b) E0 e m' Out_normal
  | exec_Scall:
      forall sp e m optid sig a bl vf vargs f t m' vres e',
      eval_expr sp e m nil a vf ->
      eval_exprlist sp e m nil bl vargs ->
      Genv.find_funct ge vf = Some f ->
      funsig f = sig ->
      eval_funcall m f vargs t m' vres ->
      e' = set_optvar optid vres e ->
      exec_stmt sp e m (Scall optid sig a bl) t e' m' Out_normal
  | exec_Salloc:
      forall sp e m id a n m' b,
      eval_expr sp e m nil a (Vint n) ->
      Mem.alloc m 0 (Int.signed n) = (m', b) ->
      exec_stmt sp e m (Salloc id a) 
                E0 (PTree.set id (Vptr b Int.zero) e) m' Out_normal
  | exec_Sifthenelse:
      forall sp e m a s1 s2 v t e' m' out,
      eval_condexpr sp e m nil a v ->
      exec_stmt sp e m (if v then s1 else s2) t e' m' out ->
      exec_stmt sp e m (Sifthenelse a s1 s2) t e' m' out
  | exec_Sseq_continue:
      forall sp e m t s1 t1 e1 m1 s2 t2 e2 m2 out,
      exec_stmt sp e m s1 t1 e1 m1 Out_normal ->
      exec_stmt sp e1 m1 s2 t2 e2 m2 out ->
      t = t1 ** t2 ->
      exec_stmt sp e m (Sseq s1 s2) t e2 m2 out
  | exec_Sseq_stop:
      forall sp e m t s1 s2 e1 m1 out,
      exec_stmt sp e m s1 t e1 m1 out ->
      out <> Out_normal ->
      exec_stmt sp e m (Sseq s1 s2) t e1 m1 out
  | exec_Sloop_loop:
      forall sp e m s t t1 e1 m1 t2 e2 m2 out,
      exec_stmt sp e m s t1 e1 m1 Out_normal ->
      exec_stmt sp e1 m1 (Sloop s) t2 e2 m2 out ->
      t = t1 ** t2 ->
      exec_stmt sp e m (Sloop s) t e2 m2 out
  | exec_Sloop_stop:
      forall sp e m t s e1 m1 out,
      exec_stmt sp e m s t e1 m1 out ->
      out <> Out_normal ->
      exec_stmt sp e m (Sloop s) t e1 m1 out
  | exec_Sblock:
      forall sp e m s t e1 m1 out,
      exec_stmt sp e m s t e1 m1 out ->
      exec_stmt sp e m (Sblock s) t e1 m1 (outcome_block out)
  | exec_Sexit:
      forall sp e m n,
      exec_stmt sp e m (Sexit n) E0 e m (Out_exit n)
  | exec_Sswitch:
      forall sp e m a cases default n,
      eval_expr sp e m nil a (Vint n) ->
      exec_stmt sp e m (Sswitch a cases default)
                E0 e m (Out_exit (switch_target n default cases))
  | exec_Sreturn_none:
      forall sp e m,
      exec_stmt sp e m (Sreturn None) E0 e m (Out_return None)
  | exec_Sreturn_some:
      forall sp e m a v,
      eval_expr sp e m nil a v ->
      exec_stmt sp e m (Sreturn (Some a)) E0 e m (Out_return (Some v))
  | exec_Stailcall:
      forall sp e m sig a bl vf vargs f t m' vres,
      eval_expr (Vptr sp Int.zero) e m nil a vf ->
      eval_exprlist (Vptr sp Int.zero) e m nil bl vargs ->
      Genv.find_funct ge vf = Some f ->
      funsig f = sig ->
      eval_funcall (Mem.free m sp) f vargs t m' vres ->
      exec_stmt (Vptr sp Int.zero) e m (Stailcall sig a bl) t e m' (Out_tailcall_return vres).

Scheme eval_funcall_ind2 := Minimality for eval_funcall Sort Prop
  with exec_stmt_ind2 := Minimality for exec_stmt Sort Prop.

(** Coinductive semantics for divergence. *)

CoInductive evalinf_funcall:
        mem -> fundef -> list val -> traceinf -> Prop :=
  | evalinf_funcall_internal:
      forall m f vargs m1 sp e t,
      Mem.alloc m 0 f.(fn_stackspace) = (m1, sp) ->
      set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
      execinf_stmt (Vptr sp Int.zero) e m1 f.(fn_body) t ->
      evalinf_funcall m (Internal f) vargs t

(** [execinf_stmt ge sp e m s t] means that statement [s] diverges.
  [e] is the initial environment, [m] is the initial memory state,
  and [t] the trace of observable events performed during the execution. *)

with execinf_stmt:
         val -> env -> mem -> stmt -> traceinf -> Prop :=
  | execinf_Scall:
      forall sp e m optid sig a bl vf vargs f t,
      eval_expr sp e m nil a vf ->
      eval_exprlist sp e m nil bl vargs ->
      Genv.find_funct ge vf = Some f ->
      funsig f = sig ->
      evalinf_funcall m f vargs t ->
      execinf_stmt sp e m (Scall optid sig a bl) t
  | execinf_Sifthenelse:
      forall sp e m a s1 s2 v t,
      eval_condexpr sp e m nil a v ->
      execinf_stmt sp e m (if v then s1 else s2) t ->
      execinf_stmt sp e m (Sifthenelse a s1 s2) t
  | execinf_Sseq_1:
      forall sp e m t s1 s2,
      execinf_stmt sp e m s1 t ->
      execinf_stmt sp e m (Sseq s1 s2) t
  | execinf_Sseq_2:
      forall sp e m t s1 t1 e1 m1 s2 t2,
      exec_stmt sp e m s1 t1 e1 m1 Out_normal ->
      execinf_stmt sp e1 m1 s2 t2 ->
      t = t1 *** t2 ->
      execinf_stmt sp e m (Sseq s1 s2) t
  | execinf_Sloop_body:
      forall sp e m s t,
      execinf_stmt sp e m s t ->
      execinf_stmt sp e m (Sloop s) t
  | execinf_Sloop_loop:
      forall sp e m s t t1 e1 m1 t2,
      exec_stmt sp e m s t1 e1 m1 Out_normal ->
      execinf_stmt sp e1 m1 (Sloop s) t2 ->
      t = t1 *** t2 ->
      execinf_stmt sp e m (Sloop s) t
  | execinf_Sblock:
      forall sp e m s t,
      execinf_stmt sp e m s t ->
      execinf_stmt sp e m (Sblock s) t
  | execinf_Stailcall:
      forall sp e m sig a bl vf vargs f t,
      eval_expr (Vptr sp Int.zero) e m nil a vf ->
      eval_exprlist (Vptr sp Int.zero) e m nil bl vargs ->
      Genv.find_funct ge vf = Some f ->
      funsig f = sig ->
      evalinf_funcall (Mem.free m sp) f vargs t ->
      execinf_stmt (Vptr sp Int.zero) e m (Stailcall sig a bl) t.

End RELSEM.

(** Execution of a whole program: [exec_program p beh]
  holds if the application of [p]'s main function to no arguments
  in the initial memory state for [p] has [beh] as observable
  behavior. *)

Inductive exec_program (p: program): program_behavior -> Prop :=
  | program_terminates:
      forall b f t m r,
      let ge := Genv.globalenv p in
      let m0 := Genv.init_mem p in
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      eval_funcall ge m0 f nil t m (Vint r) ->
      exec_program p (Terminates t r)
  | program_diverges:
      forall b f t,
      let ge := Genv.globalenv p in
      let m0 := Genv.init_mem p in
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      evalinf_funcall ge m0 f nil t ->
      exec_program p (Diverges t).
