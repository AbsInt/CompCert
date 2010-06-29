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
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Switch.

(** * Abstract syntax *)

(** Cminor is a low-level imperative language structured in expressions,
  statements, functions and programs.  We first define the constants
  and operators that occur within expressions. *)

Inductive constant : Type :=
  | Ointconst: int -> constant     (**r integer constant *)
  | Ofloatconst: float -> constant (**r floating-point constant *)
  | Oaddrsymbol: ident -> int -> constant (**r address of the symbol plus the offset *)
  | Oaddrstack: int -> constant.   (**r stack pointer plus the given offset *)

Inductive unary_operation : Type :=
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
  | Ointoffloat: unary_operation           (**r signed integer to float *)
  | Ointuoffloat: unary_operation          (**r unsigned integer to float *)
  | Ofloatofint: unary_operation           (**r float to signed integer *)
  | Ofloatofintu: unary_operation.         (**r float to unsigned integer *)

Inductive binary_operation : Type :=
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

Inductive expr : Type :=
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

Definition label := ident.

Inductive stmt : Type :=
  | Sskip: stmt
  | Sassign : ident -> expr -> stmt
  | Sstore : memory_chunk -> expr -> expr -> stmt
  | Scall : option ident -> signature -> expr -> list expr -> stmt
  | Stailcall: signature -> expr -> list expr -> stmt
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: expr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt
  | Sswitch: expr -> list (int * nat) -> nat -> stmt
  | Sreturn: option expr -> stmt
  | Slabel: label -> stmt -> stmt
  | Sgoto: label -> stmt.

(** Functions are composed of a signature, a list of parameter names,
  a list of local variables, and a  statement representing
  the function body.  Each function can allocate a memory block of
  size [fn_stackspace] on entrance.  This block will be deallocated
  automatically before the function returns.  Pointers into this block
  can be taken with the [Oaddrstack] operator. *)

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

(** * Operational semantics (small-step) *)

(** Two kinds of evaluation environments are involved:
- [genv]: global environments, define symbols and functions;
- [env]: local environments, map local variables to values.
*)

Definition genv := Genv.t fundef unit.
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

(** Continuations *)

Inductive cont: Type :=
  | Kstop: cont                         (**r stop program execution *)
  | Kseq: stmt -> cont -> cont          (**r execute stmt, then cont *)
  | Kblock: cont -> cont                (**r exit a block, then do cont *)
  | Kcall: option ident -> function -> val -> env -> cont -> cont.
                                        (**r return to caller *)

(** States *)

Inductive state: Type :=
  | State:                      (**r Execution within a function *)
      forall (f: function)              (**r currently executing function  *)
             (s: stmt)                  (**r statement under consideration *)
             (k: cont)                  (**r its continuation -- what to do next *)
             (sp: val)                  (**r current stack pointer *)
             (e: env)                   (**r current local environment *)
             (m: mem),                  (**r current memory state *)
      state
  | Callstate:                  (**r Invocation of a function *)
      forall (f: fundef)                (**r function to invoke *)
             (args: list val)           (**r arguments provided by caller *)
             (k: cont)                  (**r what to do next  *)
             (m: mem),                  (**r memory state *)
      state
  | Returnstate:                (**r Return from a function *)
      forall (v: val)                   (**r Return value *)
             (k: cont)                  (**r what to do next *)
             (m: mem),                  (**r memory state *)
      state.
             
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
  | Ocast8unsigned, _ => Some (Val.zero_ext 8 arg)
  | Ocast8signed, _ => Some (Val.sign_ext 8 arg)
  | Ocast16unsigned, _ => Some (Val.zero_ext 16 arg)
  | Ocast16signed, _ => Some (Val.sign_ext 16 arg)
  | Onegint, Vint n1 => Some (Vint (Int.neg n1))
  | Onotbool, Vint n1 => Some (Val.of_bool (Int.eq n1 Int.zero))
  | Onotbool, Vptr b1 n1 => Some Vfalse
  | Onotint, Vint n1 => Some (Vint (Int.not n1))
  | Onegf, Vfloat f1 => Some (Vfloat (Float.neg f1))
  | Oabsf, Vfloat f1 => Some (Vfloat (Float.abs f1))
  | Osingleoffloat, _ => Some (Val.singleoffloat arg)
  | Ointoffloat, Vfloat f1 => Some (Vint (Float.intoffloat f1))
  | Ointuoffloat, Vfloat f1 => Some (Vint (Float.intuoffloat f1))
  | Ofloatofint, Vint n1 => Some (Vfloat (Float.floatofint n1))
  | Ofloatofintu, Vint n1 => Some (Vfloat (Float.floatofintu n1))
  | _, _ => None
  end.

Definition eval_compare_mismatch (c: comparison) : option val :=
  match c with Ceq => Some Vfalse | Cne => Some Vtrue | _ => None end.

Definition eval_compare_null (c: comparison) (n: int) : option val :=
  if Int.eq n Int.zero then eval_compare_mismatch c else None.

Definition eval_binop
            (op: binary_operation) (arg1 arg2: val): option val :=
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
      if Int.ltu n2 Int.iwordsize then Some (Vint (Int.shl n1 n2)) else None
  | Oshr, Vint n1, Vint n2 =>
      if Int.ltu n2 Int.iwordsize then Some (Vint (Int.shr n1 n2)) else None
  | Oshru, Vint n1, Vint n2 =>
      if Int.ltu n2 Int.iwordsize then Some (Vint (Int.shru n1 n2)) else None
   | Oaddf, Vfloat f1, Vfloat f2 => Some (Vfloat (Float.add f1 f2))
  | Osubf, Vfloat f1, Vfloat f2 => Some (Vfloat (Float.sub f1 f2))
  | Omulf, Vfloat f1, Vfloat f2 => Some (Vfloat (Float.mul f1 f2))
  | Odivf, Vfloat f1, Vfloat f2 => Some (Vfloat (Float.div f1 f2))
  | Ocmp c, Vint n1, Vint n2 =>
      Some (Val.of_bool(Int.cmp c n1 n2))
  | Ocmp c, Vptr b1 n1, Vptr b2 n2 =>
      if eq_block b1 b2
      then Some(Val.of_bool(Int.cmp c n1 n2))
      else eval_compare_mismatch c
  | Ocmp c, Vptr b1 n1, Vint n2 =>
      eval_compare_null c n2
  | Ocmp c, Vint n1, Vptr b2 n2 =>
      eval_compare_null c n1
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
      eval_binop op v1 v2 = Some v ->
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
  | step_skip_call: forall f k sp e m m',
      is_call_cont k ->
      f.(fn_sig).(sig_res) = None ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f Sskip k (Vptr sp Int.zero) e m)
        E0 (Returnstate Vundef k m')

  | step_assign: forall f id a k sp e m v,
      eval_expr sp e m a v ->
      step (State f (Sassign id a) k sp e m)
        E0 (State f Sskip k sp (PTree.set id v e) m)

  | step_store: forall f chunk addr a k sp e m vaddr v m',
      eval_expr sp e m addr vaddr ->
      eval_expr sp e m a v ->
      Mem.storev chunk m vaddr v = Some m' ->
      step (State f (Sstore chunk addr a) k sp e m)
        E0 (State f Sskip k sp e m')

  | step_call: forall f optid sig a bl k sp e m vf vargs fd,
      eval_expr sp e m a vf ->
      eval_exprlist sp e m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      step (State f (Scall optid sig a bl) k sp e m)
        E0 (Callstate fd vargs (Kcall optid f sp e k) m)

  | step_tailcall: forall f sig a bl k sp e m vf vargs fd m',
      eval_expr (Vptr sp Int.zero) e m a vf ->
      eval_exprlist (Vptr sp Int.zero) e m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f (Stailcall sig a bl) k (Vptr sp Int.zero) e m)
        E0 (Callstate fd vargs (call_cont k) m')

  | step_seq: forall f s1 s2 k sp e m,
      step (State f (Sseq s1 s2) k sp e m)
        E0 (State f s1 (Kseq s2 k) sp e m)

  | step_ifthenelse: forall f a s1 s2 k sp e m v b,
      eval_expr sp e m a v ->
      Val.bool_of_val v b ->
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
      eval_expr sp e m a (Vint n) ->
      step (State f (Sswitch a cases default) k sp e m)
        E0 (State f (Sexit (switch_target n default cases)) k sp e m)

  | step_return_0: forall f k sp e m m',
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f (Sreturn None) k (Vptr sp Int.zero) e m)
        E0 (Returnstate Vundef (call_cont k) m')
  | step_return_1: forall f a k sp e m v m',
      eval_expr (Vptr sp Int.zero) e m a v ->
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

(** Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a [Callstate]
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty continuation. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      initial_state p (Callstate f nil Kstop m0).

(** A final state is a [Returnstate] with an empty continuation. *)

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (Returnstate (Vint r) Kstop m) r.

(** Execution of a whole program: [exec_program p beh]
  holds if the application of [p]'s main function to no arguments
  in the initial memory state for [p] has [beh] as observable
  behavior. *)

Definition exec_program (p: program) (beh: program_behavior) : Prop :=
  program_behaves step (initial_state p) final_state (Genv.globalenv p) beh.

(** * Alternate operational semantics (big-step) *)

(** We now define another semantics for Cminor without [goto] that follows
  the ``big-step'' style of semantics, also known as natural semantics.
  In this style, just like expressions evaluate to values, 
  statements evaluate to``outcomes'' indicating how execution should
  proceed afterwards. *)

Inductive outcome: Type :=
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
    (out: outcome) (m: mem) (sp: block) (sz: Z) (m': mem) :=
  match out with
  | Out_tailcall_return _ => m' = m
  | _ => Mem.free m sp 0 sz = Some m'
  end.

Section NATURALSEM.

Variable ge: genv.

(** Evaluation of a function invocation: [eval_funcall ge m f args t m' res]
  means that the function [f], applied to the arguments [args] in
  memory state [m], returns the value [res] in modified memory state [m'].
  [t] is the trace of observable events generated during the invocation.
*)

Inductive eval_funcall:
        mem -> fundef -> list val -> trace ->
        mem -> val -> Prop :=
  | eval_funcall_internal:
      forall m f vargs m1 sp e t e2 m2 out vres m3,
      Mem.alloc m 0 f.(fn_stackspace) = (m1, sp) ->
      set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
      exec_stmt f (Vptr sp Int.zero) e m1 f.(fn_body) t e2 m2 out ->
      outcome_result_value out f.(fn_sig).(sig_res) vres ->
      outcome_free_mem out m2 sp f.(fn_stackspace) m3 ->
      eval_funcall m (Internal f) vargs t m3 vres
  | eval_funcall_external:
      forall ef m args t res m',
      external_call ef ge args m t res m' ->
      eval_funcall m (External ef) args t m' res

(** Execution of a statement: [exec_stmt ge f sp e m s t e' m' out]
  means that statement [s] executes with outcome [out].
  [e] is the initial environment and [m] is the initial memory state.
  [e'] is the final environment, reflecting variable assignments performed
  by [s].  [m'] is the final memory state, reflecting memory stores
  performed by [s].  [t] is the trace of I/O events performed during
  the execution.  The other parameters are as in [eval_expr]. *)

with exec_stmt:
         function -> val ->
         env -> mem -> stmt -> trace ->
         env -> mem -> outcome -> Prop :=
  | exec_Sskip:
      forall f sp e m,
      exec_stmt f sp e m Sskip E0 e m Out_normal
  | exec_Sassign:
      forall f sp e m id a v,
      eval_expr ge sp e m a v ->
      exec_stmt f sp e m (Sassign id a) E0 (PTree.set id v e) m Out_normal
  | exec_Sstore:
      forall f sp e m chunk addr a vaddr v m',
      eval_expr ge sp e m addr vaddr ->
      eval_expr ge sp e m a v ->
      Mem.storev chunk m vaddr v = Some m' ->
      exec_stmt f sp e m (Sstore chunk addr a) E0 e m' Out_normal
  | exec_Scall:
      forall f sp e m optid sig a bl vf vargs fd t m' vres e',
      eval_expr ge sp e m a vf ->
      eval_exprlist ge sp e m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      eval_funcall m fd vargs t m' vres ->
      e' = set_optvar optid vres e ->
      exec_stmt f sp e m (Scall optid sig a bl) t e' m' Out_normal
  | exec_Sifthenelse:
      forall f sp e m a s1 s2 v b t e' m' out,
      eval_expr ge sp e m a v ->
      Val.bool_of_val v b ->
      exec_stmt f sp e m (if b then s1 else s2) t e' m' out ->
      exec_stmt f sp e m (Sifthenelse a s1 s2) t e' m' out
  | exec_Sseq_continue:
      forall f sp e m t s1 t1 e1 m1 s2 t2 e2 m2 out,
      exec_stmt f sp e m s1 t1 e1 m1 Out_normal ->
      exec_stmt f sp e1 m1 s2 t2 e2 m2 out ->
      t = t1 ** t2 ->
      exec_stmt f sp e m (Sseq s1 s2) t e2 m2 out
  | exec_Sseq_stop:
      forall f sp e m t s1 s2 e1 m1 out,
      exec_stmt f sp e m s1 t e1 m1 out ->
      out <> Out_normal ->
      exec_stmt f sp e m (Sseq s1 s2) t e1 m1 out
  | exec_Sloop_loop:
      forall f sp e m s t t1 e1 m1 t2 e2 m2 out,
      exec_stmt f sp e m s t1 e1 m1 Out_normal ->
      exec_stmt f sp e1 m1 (Sloop s) t2 e2 m2 out ->
      t = t1 ** t2 ->
      exec_stmt f sp e m (Sloop s) t e2 m2 out
  | exec_Sloop_stop:
      forall f sp e m t s e1 m1 out,
      exec_stmt f sp e m s t e1 m1 out ->
      out <> Out_normal ->
      exec_stmt f sp e m (Sloop s) t e1 m1 out
  | exec_Sblock:
      forall f sp e m s t e1 m1 out,
      exec_stmt f sp e m s t e1 m1 out ->
      exec_stmt f sp e m (Sblock s) t e1 m1 (outcome_block out)
  | exec_Sexit:
      forall f sp e m n,
      exec_stmt f sp e m (Sexit n) E0 e m (Out_exit n)
  | exec_Sswitch:
      forall f sp e m a cases default n,
      eval_expr ge sp e m a (Vint n) ->
      exec_stmt f sp e m (Sswitch a cases default)
                E0 e m (Out_exit (switch_target n default cases))
  | exec_Sreturn_none:
      forall f sp e m,
      exec_stmt f sp e m (Sreturn None) E0 e m (Out_return None)
  | exec_Sreturn_some:
      forall f sp e m a v,
      eval_expr ge sp e m a v ->
      exec_stmt f sp e m (Sreturn (Some a)) E0 e m (Out_return (Some v))
  | exec_Stailcall:
      forall f sp e m sig a bl vf vargs fd t m' m'' vres,
      eval_expr ge (Vptr sp Int.zero) e m a vf ->
      eval_exprlist ge (Vptr sp Int.zero) e m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      eval_funcall m' fd vargs t m'' vres ->
      exec_stmt f (Vptr sp Int.zero) e m (Stailcall sig a bl) t e m'' (Out_tailcall_return vres).

Scheme eval_funcall_ind2 := Minimality for eval_funcall Sort Prop
  with exec_stmt_ind2 := Minimality for exec_stmt Sort Prop.
Combined Scheme eval_funcall_exec_stmt_ind2 
  from eval_funcall_ind2, exec_stmt_ind2.

(*
Definition eval_funcall_exec_stmt_ind2 
  (P1: mem -> fundef -> list val -> trace -> mem -> val -> Prop)
  (P2: val -> env -> mem -> stmt -> trace ->
              env -> mem -> outcome -> Prop) :=
  fun a b c d e f g h i j k l m n o p q =>
  conj
    (eval_funcall_ind2 ge P1 P2 a b c d e f g h i j k l m n o p q)
    (exec_stmt_ind2 ge P1 P2 a b c d e f g h i j k l m n o p q).
*)

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
      execinf_stmt f (Vptr sp Int.zero) e m1 f.(fn_body) t ->
      evalinf_funcall m (Internal f) vargs t

(** [execinf_stmt ge sp e m s t] means that statement [s] diverges.
  [e] is the initial environment, [m] is the initial memory state,
  and [t] the trace of observable events performed during the execution. *)

with execinf_stmt:
         function -> val -> env -> mem -> stmt -> traceinf -> Prop :=
  | execinf_Scall:
      forall f sp e m optid sig a bl vf vargs fd t,
      eval_expr ge sp e m a vf ->
      eval_exprlist ge sp e m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      evalinf_funcall m fd vargs t ->
      execinf_stmt f sp e m (Scall optid sig a bl) t
  | execinf_Sifthenelse:
      forall f sp e m a s1 s2 v b t,
      eval_expr ge sp e m a v ->
      Val.bool_of_val v b ->
      execinf_stmt f sp e m (if b then s1 else s2) t ->
      execinf_stmt f sp e m (Sifthenelse a s1 s2) t
  | execinf_Sseq_1:
      forall f sp e m t s1 s2,
      execinf_stmt f sp e m s1 t ->
      execinf_stmt f sp e m (Sseq s1 s2) t
  | execinf_Sseq_2:
      forall f sp e m t s1 t1 e1 m1 s2 t2,
      exec_stmt f sp e m s1 t1 e1 m1 Out_normal ->
      execinf_stmt f sp e1 m1 s2 t2 ->
      t = t1 *** t2 ->
      execinf_stmt f sp e m (Sseq s1 s2) t
  | execinf_Sloop_body:
      forall f sp e m s t,
      execinf_stmt f sp e m s t ->
      execinf_stmt f sp e m (Sloop s) t
  | execinf_Sloop_loop:
      forall f sp e m s t t1 e1 m1 t2,
      exec_stmt f sp e m s t1 e1 m1 Out_normal ->
      execinf_stmt f sp e1 m1 (Sloop s) t2 ->
      t = t1 *** t2 ->
      execinf_stmt f sp e m (Sloop s) t
  | execinf_Sblock:
      forall f sp e m s t,
      execinf_stmt f sp e m s t ->
      execinf_stmt f sp e m (Sblock s) t
  | execinf_Stailcall:
      forall f sp e m sig a bl vf vargs fd m' t,
      eval_expr ge (Vptr sp Int.zero) e m a vf ->
      eval_exprlist ge (Vptr sp Int.zero) e m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      evalinf_funcall m' fd vargs t ->
      execinf_stmt f (Vptr sp Int.zero) e m (Stailcall sig a bl) t.

End NATURALSEM.

(** Big-step execution of a whole program *)

Inductive bigstep_program_terminates (p: program): trace -> int -> Prop :=
  | bigstep_program_terminates_intro:
      forall b f m0 t m r,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      eval_funcall ge m0 f nil t m (Vint r) ->
      bigstep_program_terminates p t r.

Inductive bigstep_program_diverges (p: program): traceinf -> Prop :=
  | bigstep_program_diverges_intro:
      forall b f m0 t,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      evalinf_funcall ge m0 f nil t ->
      bigstep_program_diverges p t.

(** ** Correctness of the big-step semantics with respect to the transition semantics *)

Section BIGSTEP_TO_TRANSITION.

Variable prog: program.
Let ge := Genv.globalenv prog.

Inductive outcome_state_match
        (sp: val) (e: env) (m: mem) (f: function) (k: cont):
        outcome -> state -> Prop :=
  | osm_normal:
      outcome_state_match sp e m f k 
                          Out_normal
                          (State f Sskip k sp e m)
  | osm_exit: forall n,
      outcome_state_match sp e m f k 
                          (Out_exit n)
                          (State f (Sexit n) k sp e m)
  | osm_return_none: forall k',
      call_cont k' = call_cont k ->
      outcome_state_match sp e m f k 
                          (Out_return None)
                          (State f (Sreturn None) k' sp e m)
  | osm_return_some: forall k' a v,
      call_cont k' = call_cont k ->
      eval_expr ge sp e m a v ->
      outcome_state_match sp e m f k 
                          (Out_return (Some v))
                          (State f (Sreturn (Some a)) k' sp e m)
  | osm_tail: forall v,
      outcome_state_match sp e m f k
                          (Out_tailcall_return v)
                          (Returnstate v (call_cont k) m).

Remark is_call_cont_call_cont:
  forall k, is_call_cont (call_cont k).
Proof.
  induction k; simpl; auto.
Qed.

Remark call_cont_is_call_cont:
  forall k, is_call_cont k -> call_cont k = k.
Proof.
  destruct k; simpl; intros; auto || contradiction.
Qed.

Lemma eval_funcall_exec_stmt_steps:
  (forall m fd args t m' res,
   eval_funcall ge m fd args t m' res ->
   forall k,
   is_call_cont k ->
   star step ge (Callstate fd args k m)
              t (Returnstate res k m'))
/\(forall f sp e m s t e' m' out,
   exec_stmt ge f sp e m s t e' m' out ->
   forall k,
   exists S,
   star step ge (State f s k sp e m) t S
   /\ outcome_state_match sp e' m' f k out S).
Proof.
  apply eval_funcall_exec_stmt_ind2; intros.

(* funcall internal *)
  destruct (H2 k) as [S [A B]].
  assert (call_cont k = k) by (apply call_cont_is_call_cont; auto).
  eapply star_left. econstructor; eauto. 
  eapply star_trans. eexact A.
  inversion B; clear B; subst out; simpl in H3; simpl; try contradiction.
  (* Out normal *)
  assert (f.(fn_sig).(sig_res) = None /\ vres = Vundef).
    destruct f.(fn_sig).(sig_res). contradiction. auto.
  destruct H7. subst vres.
  apply star_one. apply step_skip_call; auto. 
  (* Out_return None *)
  assert (f.(fn_sig).(sig_res) = None /\ vres = Vundef).
    destruct f.(fn_sig).(sig_res). contradiction. auto.
  destruct H8. subst vres.
  replace k with (call_cont k') by congruence.
  apply star_one. apply step_return_0; auto.
  (* Out_return Some *)
  assert (f.(fn_sig).(sig_res) <> None /\ vres = v).
    destruct f.(fn_sig).(sig_res). split; congruence. contradiction.
  destruct H9. subst vres.
  replace k with (call_cont k') by congruence.
  apply star_one. eapply step_return_1; eauto.
  (* Out_tailcall_return *)
  subst vres. red in H4. subst m3. rewrite H6. apply star_refl.

  reflexivity. traceEq.

(* funcall external *)
  apply star_one. constructor; auto. 

(* skip *)
  econstructor; split.
  apply star_refl. 
  constructor.

(* assign *)
  exists (State f Sskip k sp (PTree.set id v e) m); split.
  apply star_one. constructor. auto.
  constructor.

(* store *)
  econstructor; split.
  apply star_one. econstructor; eauto.
  constructor.

(* call *)
  econstructor; split.
  eapply star_left. econstructor; eauto. 
  eapply star_right. apply H4. red; auto. 
  constructor. reflexivity. traceEq.
  subst e'. constructor.

(* ifthenelse *)
  destruct (H2 k) as [S [A B]].
  exists S; split.
  apply star_left with E0 (State f (if b then s1 else s2) k sp e m) t.
  econstructor; eauto. exact A.
  traceEq.
  auto.

(* seq continue *)
  destruct (H0 (Kseq s2 k)) as [S1 [A1 B1]].
  destruct (H2 k) as [S2 [A2 B2]].
  inv B1.
  exists S2; split.
  eapply star_left. constructor. 
  eapply star_trans. eexact A1. 
  eapply star_left. constructor. eexact A2.
  reflexivity. reflexivity. traceEq.
  auto.

(* seq stop *)
  destruct (H0 (Kseq s2 k)) as [S1 [A1 B1]].
  set (S2 :=
    match out with
    | Out_exit n => State f (Sexit n) k sp e1 m1
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. constructor. eapply star_trans. eexact A1.
  unfold S2; destruct out; try (apply star_refl).
  inv B1. apply star_one. constructor.
  reflexivity. traceEq.
  unfold S2; inv B1; congruence || simpl; constructor; auto.

(* loop loop *)
  destruct (H0 (Kseq (Sloop s) k)) as [S1 [A1 B1]].
  destruct (H2 k) as [S2 [A2 B2]].
  inv B1.
  exists S2; split.
  eapply star_left. constructor. 
  eapply star_trans. eexact A1. 
  eapply star_left. constructor. eexact A2.
  reflexivity. reflexivity. traceEq.
  auto.

(* loop stop *)
  destruct (H0 (Kseq (Sloop s) k)) as [S1 [A1 B1]].
  set (S2 :=
    match out with
    | Out_exit n => State f (Sexit n) k sp e1 m1
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. constructor. eapply star_trans. eexact A1.
  unfold S2; destruct out; try (apply star_refl).
  inv B1. apply star_one. constructor.
  reflexivity. traceEq.
  unfold S2; inv B1; congruence || simpl; constructor; auto.

(* block *)
  destruct (H0 (Kblock k)) as [S1 [A1 B1]].
  set (S2 :=
    match out with
    | Out_normal => State f Sskip k sp e1 m1
    | Out_exit O => State f Sskip k sp e1 m1
    | Out_exit (S m) => State f (Sexit m) k sp e1 m1
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. constructor. eapply star_trans. eexact A1.
  unfold S2; destruct out; try (apply star_refl).
  inv B1. apply star_one. constructor.
  inv B1. apply star_one. destruct n; constructor.
  reflexivity. traceEq.
  unfold S2; inv B1; simpl; try constructor; auto.
  destruct n; constructor.

(* exit *)
  econstructor; split. apply star_refl. constructor.

(* switch *)
  econstructor; split.
  apply star_one. econstructor; eauto. 
  constructor.

(* return none *)
  econstructor; split. apply star_refl. constructor; auto.

(* return some *)
  econstructor; split. apply star_refl. constructor; auto.

(* tailcall *)
  econstructor; split.
  eapply star_left. econstructor; eauto.  
  apply H5. apply is_call_cont_call_cont. traceEq.
  econstructor. 
Qed.

Lemma eval_funcall_steps:
   forall m fd args t m' res,
   eval_funcall ge m fd args t m' res ->
   forall k,
   is_call_cont k ->
   star step ge (Callstate fd args k m)
              t (Returnstate res k m').
Proof (proj1 eval_funcall_exec_stmt_steps).

Lemma exec_stmt_steps:
   forall f sp e m s t e' m' out,
   exec_stmt ge f sp e m s t e' m' out ->
   forall k,
   exists S,
   star step ge (State f s k sp e m) t S
   /\ outcome_state_match sp e' m' f k out S.
Proof (proj2 eval_funcall_exec_stmt_steps).

Lemma evalinf_funcall_forever:
  forall m fd args T k,
  evalinf_funcall ge m fd args T ->
  forever_plus step ge (Callstate fd args k m) T.
Proof.
  cofix CIH_FUN.
  assert (forall sp e m s T f k,
          execinf_stmt ge f sp e m s T ->
          forever_plus step ge (State f s k sp e m) T).
  cofix CIH_STMT.
  intros. inv H.

(* call *)
  eapply forever_plus_intro.
  apply plus_one. econstructor; eauto. 
  apply CIH_FUN. eauto. traceEq.

(* ifthenelse *)
  eapply forever_plus_intro with (s2 := State f (if b then s1 else s2) k sp e m).
  apply plus_one. econstructor; eauto. 
  apply CIH_STMT. eauto. traceEq.

(* seq 1 *)
  eapply forever_plus_intro.
  apply plus_one. constructor.
  apply CIH_STMT. eauto. traceEq.

(* seq 2 *)
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ _ H0 (Kseq s2 k))
  as [S [A B]]. inv B.
  eapply forever_plus_intro.
  eapply plus_left. constructor.
  eapply star_right. eexact A. constructor. 
  reflexivity. reflexivity.
  apply CIH_STMT. eauto. traceEq. 

(* loop body *)
  eapply forever_plus_intro.
  apply plus_one. econstructor; eauto.
  apply CIH_STMT. eauto. traceEq.

(* loop loop *)
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ _ H0 (Kseq (Sloop s0) k))
  as [S [A B]]. inv B.
  eapply forever_plus_intro.
  eapply plus_left. constructor.
  eapply star_right. eexact A. constructor. 
  reflexivity. reflexivity.
  apply CIH_STMT. eauto. traceEq.

(* block *)
  eapply forever_plus_intro.
  apply plus_one. econstructor; eauto.
  apply CIH_STMT. eauto. traceEq.

(* tailcall *)
  eapply forever_plus_intro.
  apply plus_one. econstructor; eauto. 
  apply CIH_FUN. eauto. traceEq.

(* function call *)
  intros. inv H0.
  eapply forever_plus_intro.
  apply plus_one. econstructor; eauto.
  apply H. eauto. 
  traceEq.
Qed.

Theorem bigstep_program_terminates_exec:
  forall t r, bigstep_program_terminates prog t r -> exec_program prog (Terminates t r).
Proof.
  intros. inv H.
  econstructor.
  econstructor; eauto. 
  apply eval_funcall_steps. eauto. red; auto. 
  econstructor.
Qed.

Theorem bigstep_program_diverges_exec:
  forall T, bigstep_program_diverges prog T ->
  exec_program prog (Reacts T) \/
  exists t, exec_program prog (Diverges t) /\ traceinf_prefix t T.
Proof.
  intros. inv H.
  set (st := Callstate f nil Kstop m0).
  assert (forever step ge0 st T). 
    eapply forever_plus_forever.
    eapply evalinf_funcall_forever; eauto. 
  destruct (forever_silent_or_reactive _ _ _ _ _ _ H)
  as [A | [t [s' [T' [B [C D]]]]]]. 
  left. econstructor. econstructor; eauto. auto.
  right. exists t. split.
  econstructor. econstructor; eauto. eauto. auto.  
  subst T. rewrite <- (E0_right t) at 1. apply traceinf_prefix_app. constructor.
Qed.

End BIGSTEP_TO_TRANSITION.
