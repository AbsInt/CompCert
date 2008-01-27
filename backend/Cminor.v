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

(** Abstract syntax and semantics for the Cminor language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Events.
Require Import Values.
Require Import Mem.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Switch.

(** * Abstract syntax *)

(** Cminor is a low-level imperative language structured in expressions,
  statements, functions and programs.  We first define the constants
  and operators that occur within expressions. *)

Inductive constant : Set :=
  | Ointconst: int -> constant     (**r integer constant *)
  | Ofloatconst: float -> constant (**r floating-point constant *)
  | Oaddrsymbol: ident -> int -> constant (**r address of the symbol plus the offset *)
  | Oaddrstack: int -> constant.   (**r stack pointer plus the given offset *)

Inductive unary_operation : Set :=
  | Ocast8unsigned: unary_operation        (**r 8-bit zero extension  *)
  | Ocast8signed: unary_operation          (**r 8-bit sign extension  *)
  | Ocast16unsigned: unary_operation       (**r 16-bit zero extension  *)
  | Ocast16signed: unary_operation         (**r 16-bit sign extension *)
  | Onegint: unary_operation               (**r integer opposite *)
  | Onotbool: unary_operation              (**r boolean negation  *)
  | Onotint: unary_operation               (**r bitwise complement  *)
  | Onegf: unary_operation                 (**r float opposite *)
  | Oabsf: unary_operation                 (**r float absolute value *)
  | Osingleoffloat: unary_operation        (**r float truncation *)
  | Ointoffloat: unary_operation           (**r integer to float *)
  | Ofloatofint: unary_operation           (**r float to signed integer *)
  | Ofloatofintu: unary_operation.         (**r float to unsigned integer *)

Inductive binary_operation : Set :=
  | Oadd: binary_operation                 (**r integer addition *)
  | Osub: binary_operation                 (**r integer subtraction *)
  | Omul: binary_operation                 (**r integer multiplication *)
  | Odiv: binary_operation                 (**r integer signed division *)
  | Odivu: binary_operation                (**r integer unsigned division *)
  | Omod: binary_operation                 (**r integer signed modulus *)
  | Omodu: binary_operation                (**r integer unsigned modulus *)
  | Oand: binary_operation                 (**r bitwise ``and'' *)
  | Oor: binary_operation                  (**r bitwise ``or'' *)
  | Oxor: binary_operation                 (**r bitwise ``xor'' *)
  | Oshl: binary_operation                 (**r left shift *)
  | Oshr: binary_operation                 (**r right signed shift *)
  | Oshru: binary_operation                (**r right unsigned shift *)
  | Oaddf: binary_operation                (**r float addition *)
  | Osubf: binary_operation                (**r float subtraction *)
  | Omulf: binary_operation                (**r float multiplication *)
  | Odivf: binary_operation                (**r float division *)
  | Ocmp: comparison -> binary_operation   (**r integer signed comparison *)
  | Ocmpu: comparison -> binary_operation  (**r integer unsigned comparison *)
  | Ocmpf: comparison -> binary_operation. (**r float comparison *)

(** Expressions include reading local variables, constants and
  arithmetic operations, reading store locations, and conditional
  expressions (similar to [e1 ? e2 : e3] in C). *)

Inductive expr : Set :=
  | Evar : ident -> expr
  | Econst : constant -> expr
  | Eunop : unary_operation -> expr -> expr
  | Ebinop : binary_operation -> expr -> expr -> expr
  | Eload : memory_chunk -> expr -> expr
  | Econdition : expr -> expr -> expr -> expr.

(** Statements include expression evaluation, assignment to local variables,
  memory stores, function calls, an if/then/else conditional, infinite
  loops, blocks and early block exits, and early function returns.
  [Sexit n] terminates prematurely the execution of the [n+1]
  enclosing [Sblock] statements. *)

Inductive stmt : Set :=
  | Sskip: stmt
  | Sassign : ident -> expr -> stmt
  | Sstore : memory_chunk -> expr -> expr -> stmt
  | Scall : option ident -> signature -> expr -> list expr -> stmt
  | Salloc : ident -> expr -> stmt
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: expr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt
  | Sswitch: expr -> list (int * nat) -> nat -> stmt
  | Sreturn: option expr -> stmt
  | Stailcall: signature -> expr -> list expr -> stmt.

(** Functions are composed of a signature, a list of parameter names,
  a list of local variables, and a  statement representing
  the function body.  Each function can allocate a memory block of
  size [fn_stackspace] on entrance.  This block will be deallocated
  automatically before the function returns.  Pointers into this block
  can be taken with the [Oaddrstack] operator. *)

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

(** The operational semantics for Cminor is given in big-step operational
  style.  Expressions evaluate to values, and statements evaluate to
  ``outcomes'' indicating how execution should proceed afterwards. *)

Inductive outcome: Set :=
  | Out_normal: outcome                (**r continue in sequence *)
  | Out_exit: nat -> outcome           (**r terminate [n+1] enclosing blocks *)
  | Out_return: option val -> outcome  (**r return immediately to caller *)
  | Out_tailcall_return: val -> outcome. (**r already returned to caller via a tailcall *)

Definition outcome_block (out: outcome) : outcome :=
  match out with
  | Out_exit O => Out_normal
  | Out_exit (S n) => Out_exit n
  | out => out
  end.

Definition outcome_result_value
    (out: outcome) (retsig: option typ) (vres: val) : Prop :=
  match out, retsig with
  | Out_normal, None => vres = Vundef
  | Out_return None, None => vres = Vundef
  | Out_return (Some v), Some ty => vres = v
  | Out_tailcall_return v, _ => vres = v
  | _, _ => False
  end.

Definition outcome_free_mem
    (out: outcome) (m: mem) (sp: block) : mem :=
  match out with
  | Out_tailcall_return _ => m
  | _ => Mem.free m sp
  end.

(** Two kinds of evaluation environments are involved:
- [genv]: global environments, define symbols and functions;
- [env]: local environments, map local variables to values.
*)

Definition genv := Genv.t fundef.
Definition env := PTree.t val.

(** The following functions build the initial local environment at
  function entry, binding parameters to the provided arguments and
  initializing local variables to [Vundef]. *)

Fixpoint set_params (vl: list val) (il: list ident) {struct il} : env :=
  match il, vl with
  | i1 :: is, v1 :: vs => PTree.set i1 v1 (set_params vs is)
  | i1 :: is, nil => PTree.set i1 Vundef (set_params nil is)
  | _, _ => PTree.empty val
  end.

Fixpoint set_locals (il: list ident) (e: env) {struct il} : env :=
  match il with
  | nil => e
  | i1 :: is => PTree.set i1 Vundef (set_locals is e)
  end.

Definition set_optvar (optid: option ident) (v: val) (e: env) : env :=
  match optid with
  | None => e
  | Some id => PTree.set id v e
  end.

Section RELSEM.

Variable ge: genv.

(** Evaluation of constants and operator applications.
    [None] is returned when the computation is undefined, e.g.
    if arguments are of the wrong types, or in case of an integer division
    by zero. *)

Definition eval_constant (sp: val) (cst: constant) : option val :=
  match cst with
  | Ointconst n => Some (Vint n)
  | Ofloatconst n => Some (Vfloat n)
  | Oaddrsymbol s ofs =>
      match Genv.find_symbol ge s with
      | None => None
      | Some b => Some (Vptr b ofs)
      end
  | Oaddrstack ofs =>
      match sp with
      | Vptr b n => Some (Vptr b (Int.add n ofs))
      | _ => None
      end
  end.

Definition eval_unop (op: unary_operation) (arg: val) : option val :=
  match op, arg with
  | Ocast8unsigned, _ => Some (Val.cast8unsigned arg)
  | Ocast8signed, _ => Some (Val.cast8signed arg)
  | Ocast16unsigned, _ => Some (Val.cast16unsigned arg)
  | Ocast16signed, _ => Some (Val.cast16signed arg)
  | Onegint, Vint n1 => Some (Vint (Int.neg n1))
  | Onotbool, Vint n1 => Some (Val.of_bool (Int.eq n1 Int.zero))
  | Onotbool, Vptr b1 n1 => Some Vfalse
  | Onotint, Vint n1 => Some (Vint (Int.not n1))
  | Onegf, Vfloat f1 => Some (Vfloat (Float.neg f1))
  | Oabsf, Vfloat f1 => Some (Vfloat (Float.abs f1))
  | Osingleoffloat, _ => Some (Val.singleoffloat arg)
  | Ointoffloat, Vfloat f1 => Some (Vint (Float.intoffloat f1))
  | Ofloatofint, Vint n1 => Some (Vfloat (Float.floatofint n1))
  | Ofloatofintu, Vint n1 => Some (Vfloat (Float.floatofintu n1))
  | _, _ => None
  end.

Definition eval_compare_null (c: comparison) (n: int) : option val :=
  if Int.eq n Int.zero 
  then match c with Ceq => Some Vfalse | Cne => Some Vtrue | _ => None end
  else None.

Definition eval_binop
            (op: binary_operation) (arg1 arg2: val) (m: mem): option val :=
  match op, arg1, arg2 with
  | Oadd, Vint n1, Vint n2 => Some (Vint (Int.add n1 n2))
  | Oadd, Vint n1, Vptr b2 n2 => Some (Vptr b2 (Int.add n2 n1))
  | Oadd, Vptr b1 n1, Vint n2 => Some (Vptr b1 (Int.add n1 n2))
  | Osub, Vint n1, Vint n2 => Some (Vint (Int.sub n1 n2))
  | Osub, Vptr b1 n1, Vint n2 => Some (Vptr b1 (Int.sub n1 n2))
  | Osub, Vptr b1 n1, Vptr b2 n2 =>
      if eq_block b1 b2 then Some (Vint (Int.sub n1 n2)) else None
  | Omul, Vint n1, Vint n2 => Some (Vint (Int.mul n1 n2))
  | Odiv, Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.divs n1 n2))
  | Odivu, Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.divu n1 n2))
  | Omod, Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.mods n1 n2))
  | Omodu, Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.modu n1 n2))
  | Oand, Vint n1, Vint n2 => Some (Vint (Int.and n1 n2))
  | Oor, Vint n1, Vint n2 => Some (Vint (Int.or n1 n2))
  | Oxor, Vint n1, Vint n2 => Some (Vint (Int.xor n1 n2))
  | Oshl, Vint n1, Vint n2 =>
      if Int.ltu n2 (Int.repr 32) then Some (Vint (Int.shl n1 n2)) else None
  | Oshr, Vint n1, Vint n2 =>
      if Int.ltu n2 (Int.repr 32) then Some (Vint (Int.shr n1 n2)) else None
  | Oshru, Vint n1, Vint n2 =>
      if Int.ltu n2 (Int.repr 32) then Some (Vint (Int.shru n1 n2)) else None
   | Oaddf, Vfloat f1, Vfloat f2 => Some (Vfloat (Float.add f1 f2))
  | Osubf, Vfloat f1, Vfloat f2 => Some (Vfloat (Float.sub f1 f2))
  | Omulf, Vfloat f1, Vfloat f2 => Some (Vfloat (Float.mul f1 f2))
  | Odivf, Vfloat f1, Vfloat f2 => Some (Vfloat (Float.div f1 f2))
  | Ocmp c, Vint n1, Vint n2 =>
      Some (Val.of_bool(Int.cmp c n1 n2))
  | Ocmp c, Vptr b1 n1, Vptr b2 n2 =>
      if valid_pointer m b1 (Int.signed n1)
      && valid_pointer m b2 (Int.signed n2) then
        if eq_block b1 b2 then Some(Val.of_bool(Int.cmp c n1 n2)) else None
      else
        None
  | Ocmp c, Vptr b1 n1, Vint n2 => eval_compare_null c n2
  | Ocmp c, Vint n1, Vptr b2 n2 => eval_compare_null c n1
  | Ocmpu c, Vint n1, Vint n2 =>
      Some (Val.of_bool(Int.cmpu c n1 n2))
  | Ocmpf c, Vfloat f1, Vfloat f2 =>
      Some (Val.of_bool (Float.cmp c f1 f2))
  | _, _, _ => None
  end.

(** Evaluation of an expression: [eval_expr ge sp e m a v]
  states that expression [a] evaluates to value [v].
  [ge] is the global environment, [e] the local environment,
  and [m] the current memory state.  They are unchanged during evaluation.
  [sp] is the pointer to the memory block allocated for this function
  (stack frame).
*)

Section EVAL_EXPR.

Variable sp: val.
Variable e: env.
Variable m: mem.

Inductive eval_expr: expr -> val -> Prop :=
  | eval_Evar: forall id v,
      PTree.get id e = Some v ->
      eval_expr (Evar id) v
  | eval_Econst: forall cst v,
      eval_constant sp cst = Some v ->
      eval_expr (Econst cst) v
  | eval_Eunop: forall op a1 v1 v,
      eval_expr a1 v1 ->
      eval_unop op v1 = Some v ->
      eval_expr (Eunop op a1) v
  | eval_Ebinop: forall op a1 a2 v1 v2 v,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      eval_binop op v1 v2 m = Some v ->
      eval_expr (Ebinop op a1 a2) v
  | eval_Eload: forall chunk addr vaddr v,
      eval_expr addr vaddr ->
      Mem.loadv chunk m vaddr = Some v ->     
      eval_expr (Eload chunk addr) v
  | eval_Econdition: forall a1 a2 a3 v1 b1 v2,
      eval_expr a1 v1 ->
      Val.bool_of_val v1 b1 ->
      eval_expr (if b1 then a2 else a3) v2 ->
      eval_expr (Econdition a1 a2 a3) v2.

Inductive eval_exprlist: list expr -> list val -> Prop :=
  | eval_Enil:
      eval_exprlist nil nil
  | eval_Econs: forall a1 al v1 vl,
      eval_expr a1 v1 -> eval_exprlist al vl ->
      eval_exprlist (a1 :: al) (v1 :: vl).

End EVAL_EXPR.

(** Evaluation of a function invocation: [eval_funcall ge m f args t m' res]
  means that the function [f], applied to the arguments [args] in
  memory state [m], returns the value [res] in modified memory state [m'].
  [t] is the trace of observable events generated during the invocation.
*)

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

(** Execution of a statement: [exec_stmt ge sp e m s t e' m' out]
  means that statement [s] executes with outcome [out].
  [e] is the initial environment and [m] is the initial memory state.
  [e'] is the final environment, reflecting variable assignments performed
  by [s].  [m'] is the final memory state, reflecting memory stores
  performed by [s].  [t] is the trace of I/O events performed during
  the execution.  The other parameters are as in [eval_expr]. *)

with exec_stmt:
         val ->
         env -> mem -> stmt -> trace ->
         env -> mem -> outcome -> Prop :=
  | exec_Sskip:
      forall sp e m,
      exec_stmt sp e m Sskip E0 e m Out_normal
  | exec_Sassign:
      forall sp e m id a v,
      eval_expr sp e m a v ->
      exec_stmt sp e m (Sassign id a) E0 (PTree.set id v e) m Out_normal
  | exec_Sstore:
      forall sp e m chunk addr a vaddr v m',
      eval_expr sp e m addr vaddr ->
      eval_expr sp e m a v ->
      Mem.storev chunk m vaddr v = Some m' ->
      exec_stmt sp e m (Sstore chunk addr a) E0 e m' Out_normal
  | exec_Scall:
      forall sp e m optid sig a bl vf vargs f t m' vres e',
      eval_expr sp e m a vf ->
      eval_exprlist sp e m bl vargs ->
      Genv.find_funct ge vf = Some f ->
      funsig f = sig ->
      eval_funcall m f vargs t m' vres ->
      e' = set_optvar optid vres e ->
      exec_stmt sp e m (Scall optid sig a bl) t e' m' Out_normal
  | exec_Salloc:
      forall sp e m id a n m' b,
      eval_expr sp e m a (Vint n) ->
      Mem.alloc m 0 (Int.signed n) = (m', b) ->
      exec_stmt sp e m (Salloc id a) 
                E0 (PTree.set id (Vptr b Int.zero) e) m' Out_normal
  | exec_Sifthenelse:
      forall sp e m a s1 s2 v b t e' m' out,
      eval_expr sp e m a v ->
      Val.bool_of_val v b ->
      exec_stmt sp e m (if b then s1 else s2) t e' m' out ->
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
      eval_expr sp e m a (Vint n) ->
      exec_stmt sp e m (Sswitch a cases default)
                E0 e m (Out_exit (switch_target n default cases))
  | exec_Sreturn_none:
      forall sp e m,
      exec_stmt sp e m (Sreturn None) E0 e m (Out_return None)
  | exec_Sreturn_some:
      forall sp e m a v,
      eval_expr sp e m a v ->
      exec_stmt sp e m (Sreturn (Some a)) E0 e m (Out_return (Some v))
  | exec_Stailcall:
      forall sp e m sig a bl vf vargs f t m' vres,
      eval_expr (Vptr sp Int.zero) e m a vf ->
      eval_exprlist (Vptr sp Int.zero) e m bl vargs ->
      Genv.find_funct ge vf = Some f ->
      funsig f = sig ->
      eval_funcall (Mem.free m sp) f vargs t m' vres ->
      exec_stmt (Vptr sp Int.zero) e m (Stailcall sig a bl) t e m' (Out_tailcall_return vres).

Scheme eval_funcall_ind2 := Minimality for eval_funcall Sort Prop
  with exec_stmt_ind2 := Minimality for exec_stmt Sort Prop.

(** Coinductive semantics for divergence.
  [evalinf_funcall ge m f args t]
  means that the function [f] diverges when applied to the arguments [args] in
  memory state [m].  The infinite trace [t] is the trace of
  observable events generated during the invocation.
*)

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
      eval_expr sp e m a vf ->
      eval_exprlist sp e m bl vargs ->
      Genv.find_funct ge vf = Some f ->
      funsig f = sig ->
      evalinf_funcall m f vargs t ->
      execinf_stmt sp e m (Scall optid sig a bl) t
  | execinf_Sifthenelse:
      forall sp e m a s1 s2 v b t,
      eval_expr sp e m a v ->
      Val.bool_of_val v b ->
      execinf_stmt sp e m (if b then s1 else s2) t ->
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
      eval_expr (Vptr sp Int.zero) e m a vf ->
      eval_exprlist (Vptr sp Int.zero) e m bl vargs ->
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
