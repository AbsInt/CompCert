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
  | Stailcall: signature -> expr -> exprlist -> stmt
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: condexpr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt
  | Sswitch: expr -> list (int * nat) -> nat -> stmt
  | Sreturn: option expr -> stmt
  | Slabel: label -> stmt -> stmt
  | Sgoto: label -> stmt.

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

(** Continuations *)

Inductive cont: Set :=
  | Kstop: cont                         (**r stop program execution *)
  | Kseq: stmt -> cont -> cont          (**r execute stmt, then cont *)
  | Kblock: cont -> cont                (**r exit a block, then do cont *)
  | Kcall: option ident -> function -> val -> env -> cont -> cont.
                                        (**r return to caller *)

(** States *)

Inductive state: Set :=
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
      eval_operation ge sp op vl = Some v ->
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
      eval_condition cond vl = Some b ->
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
  | Sifthenelse a s1 s2 =>
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
  | step_skip_call: forall f k sp e m,
      is_call_cont k ->
      f.(fn_sig).(sig_res) = None ->
      step (State f Sskip k (Vptr sp Int.zero) e m)
        E0 (Returnstate Vundef k (Mem.free m sp))

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
      eval_expr sp e m nil a vf ->
      eval_exprlist sp e m nil bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      step (State f (Scall optid sig a bl) k sp e m)
        E0 (Callstate fd vargs (Kcall optid f sp e k) m)

  | step_tailcall: forall f sig a bl k sp e m vf vargs fd,
      eval_expr (Vptr sp Int.zero) e m nil a vf ->
      eval_exprlist (Vptr sp Int.zero) e m nil bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      step (State f (Stailcall sig a bl) k (Vptr sp Int.zero) e m)
        E0 (Callstate fd vargs (call_cont k) (Mem.free m sp))

  | step_seq: forall f s1 s2 k sp e m,
      step (State f (Sseq s1 s2) k sp e m)
        E0 (State f s1 (Kseq s2 k) sp e m)

  | step_ifthenelse: forall f a s1 s2 k sp e m b,
      eval_condexpr sp e m nil a b ->
      step (State f (Sifthenelse a s1 s2) k sp e m)
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

  | step_return_0: forall f k sp e m,
      step (State f (Sreturn None) k (Vptr sp Int.zero) e m)
        E0 (Returnstate Vundef (call_cont k) (Mem.free m sp))
  | step_return_1: forall f a k sp e m v,
      eval_expr (Vptr sp Int.zero) e m nil a v ->
      step (State f (Sreturn (Some a)) k (Vptr sp Int.zero) e m)
        E0 (Returnstate v (call_cont k) (Mem.free m sp))

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
  | step_external_function: forall ef vargs k m t vres,
      event_match ef vargs t vres ->
      step (Callstate (External ef) vargs k m)
         t (Returnstate vres k m)        

  | step_return: forall v optid f sp e k m,
      step (Returnstate v (Kcall optid f sp e k) m)
        E0 (State f Sskip k sp (set_optvar optid v e) m).

End RELSEM.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f,
      let ge := Genv.globalenv p in
      let m0 := Genv.init_mem p in
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      initial_state p (Callstate f nil Kstop m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (Returnstate (Vint r) Kstop m) r.

Definition exec_program (p: program) (beh: program_behavior) : Prop :=
  program_behaves step (initial_state p) final_state (Genv.globalenv p) beh.
