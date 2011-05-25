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

(** The Clight language: a simplified version of Compcert C where all
  expressions are pure and assignments and function calls are
  statements, not expressions. *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Csyntax.
Require Import Csem.

(** * Abstract syntax *)


(** ** Expressions *)

(** Clight expressions correspond to the "pure" subset of C expressions.
  The main omissions are string literals and assignment operators
  ([=], [+=], [++], etc).  In Clight, assignment is a statement,
  not an expression.  Additionally, an expression can also refer to
  temporary variables, which are a separate class of local variables
  that do not reside in memory and whose address cannot be taken.

  As in Compcert C, all expressions are annotated with their types,
  as needed to resolve operator overloading and type-dependent behaviors. *)

Inductive expr : Type :=
  | Econst_int: int -> type -> expr       (**r integer literal *)
  | Econst_float: float -> type -> expr   (**r float literal *)
  | Evar: ident -> type -> expr           (**r variable *)
  | Etempvar: ident -> type -> expr       (**r temporary variable *)
  | Ederef: expr -> type -> expr          (**r pointer dereference (unary [*]) *)
  | Eaddrof: expr -> type -> expr         (**r address-of operator ([&]) *)
  | Eunop: unary_operation -> expr -> type -> expr  (**r unary operation *)
  | Ebinop: binary_operation -> expr -> expr -> type -> expr (**r binary operation *)
  | Ecast: expr -> type -> expr   (**r type cast ([(ty) e]) *)
  | Econdition: expr -> expr -> expr -> type -> expr (**r conditional ([e1 ? e2 : e3]) *)
  | Esizeof: type -> type -> expr         (**r size of a type *)
  | Efield: expr -> ident -> type -> expr. (**r access to a member of a struct or union *)

(** Extract the type part of a type-annotated Clight expression. *)

Definition typeof (e: expr) : type :=
  match e with
  | Econst_int _ ty => ty
  | Econst_float _ ty => ty
  | Evar _ ty => ty
  | Etempvar _ ty => ty
  | Ederef _ ty => ty
  | Eaddrof _ ty => ty
  | Eunop _ _ ty => ty
  | Ebinop _ _ _ ty => ty
  | Ecast _ ty => ty
  | Econdition _ _ _ ty => ty
  | Esizeof _ ty => ty
  | Efield _ _ ty => ty
  end.

(** ** Statements *)

(** Clight statements are similar to those of Compcert C, with the addition
  of assigment (of a rvalue to a lvalue), assignment to a temporary,
  and function call (with assignment of the result to a temporary).
  The [for] loop is slightly simplified: there is no initial statement. *)

Definition label := ident.

Inductive statement : Type :=
  | Sskip : statement                   (**r do nothing *)
  | Sassign : expr -> expr -> statement (**r assignment [lvalue = rvalue] *)
  | Sset : ident -> expr -> statement   (**r assignment [tempvar = rvalue] *)
  | Scall: option ident -> expr -> list expr -> statement (**r function call *)
  | Ssequence : statement -> statement -> statement  (**r sequence *)
  | Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
  | Swhile : expr -> statement -> statement   (**r [while] loop *)
  | Sdowhile : expr -> statement -> statement (**r [do] loop *)
  | Sfor': expr -> statement -> statement -> statement (**r [for] loop *)
  | Sbreak : statement                      (**r [break] statement *)
  | Scontinue : statement                   (**r [continue] statement *)
  | Sreturn : option expr -> statement      (**r [return] statement *)
  | Sswitch : expr -> labeled_statements -> statement  (**r [switch] statement *)
  | Slabel : label -> statement -> statement
  | Sgoto : label -> statement

with labeled_statements : Type :=            (**r cases of a [switch] *)
  | LSdefault: statement -> labeled_statements
  | LScase: int -> statement -> labeled_statements -> labeled_statements.

(** The full [for] loop is a derived form. *)

Definition Sfor (s1: statement) (e2: expr) (s3 s4: statement) :=
  Ssequence s1 (Sfor' e2 s3 s4).

(** ** Functions *)

(** A function definition is composed of its return type ([fn_return]),
  the names and types of its parameters ([fn_params]), the names
  and types of its local variables ([fn_vars]), and the body of the
  function (a statement, [fn_body]). *)

Record function : Type := mkfunction {
  fn_return: type;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_temps: list (ident * type);
  fn_body: statement
}.

Definition var_names (vars: list(ident * type)) : list ident :=
  List.map (@fst ident type) vars.

(** Functions can either be defined ([Internal]) or declared as
  external functions ([External]). *)

Inductive fundef : Type :=
  | Internal: function -> fundef
  | External: external_function -> typelist -> type -> fundef.

(** ** Programs *)

(** A program is a collection of named functions, plus a collection
  of named global variables, carrying their types and optional initialization 
  data.  See module [AST] for more details. *)

Definition program : Type := AST.program fundef type.

(** * Operations over types *)

(** The type of a function definition. *)

Definition type_of_function (f: function) : type :=
  Tfunction (type_of_params (fn_params f)) (fn_return f).

Definition type_of_fundef (f: fundef) : type :=
  match f with
  | Internal fd => type_of_function fd
  | External id args res => Tfunction args res
  end.

(** * Operational semantics *)

(** The semantics uses two environments.  The global environment
  maps names of functions and global variables to memory block references,
  and function pointers to their definitions.  (See module [Globalenvs].) *)

Definition genv := Genv.t fundef type.

(** The local environment maps local variables to block references
  and types.  The current value of the variable is stored in the associated memory
  block. *)

Definition env := PTree.t (block * type). (* map variable -> location & type *)

Definition empty_env: env := (PTree.empty (block * type)).

(** The temporary environment maps local temporaries to values. *)

Definition temp_env := PTree.t val.


(** Selection of the appropriate case of a [switch], given the value [n]
  of the selector expression. *)

Fixpoint select_switch (n: int) (sl: labeled_statements)
                       {struct sl}: labeled_statements :=
  match sl with
  | LSdefault _ => sl
  | LScase c s sl' => if Int.eq c n then sl else select_switch n sl'
  end.

(** Turn a labeled statement into a sequence *)

Fixpoint seq_of_labeled_statement (sl: labeled_statements) : statement :=
  match sl with
  | LSdefault s => s
  | LScase c s sl' => Ssequence s (seq_of_labeled_statement sl')
  end.

Section SEMANTICS.

Variable ge: genv.

(** [type_of_global b] returns the type of the global variable or function
  at address [b]. *)

Definition type_of_global (b: block) : option type :=
  match Genv.find_var_info ge b with
  | Some gv => Some gv.(gvar_info)
  | None =>
      match Genv.find_funct_ptr ge b with
      | Some fd => Some(type_of_fundef fd)
      | None => None
      end
  end.

(** ** Evaluation of expressions *)

Section EXPR.

Variable e: env.
Variable le: temp_env.
Variable m: mem.

(** [eval_expr ge e m a v] defines the evaluation of expression [a]
  in r-value position.  [v] is the value of the expression.
  [e] is the current environment and [m] is the current memory state. *)

Inductive eval_expr: expr -> val -> Prop :=
  | eval_Econst_int:   forall i ty,
      eval_expr (Econst_int i ty) (Vint i)
  | eval_Econst_float:   forall f ty,
      eval_expr (Econst_float f ty) (Vfloat f)
  | eval_Etempvar:  forall id ty v,
      le!id = Some v ->
      eval_expr (Etempvar id ty) v
  | eval_Eaddrof: forall a ty loc ofs,
      eval_lvalue a loc ofs ->
      eval_expr (Eaddrof a ty) (Vptr loc ofs)
  | eval_Esizeof: forall ty' ty,
      eval_expr (Esizeof ty' ty) (Vint (Int.repr (sizeof ty')))
  | eval_Eunop:  forall op a ty v1 v,
      eval_expr a v1 ->
      sem_unary_operation op v1 (typeof a) = Some v ->
      eval_expr (Eunop op a ty) v
  | eval_Ebinop: forall op a1 a2 ty v1 v2 v,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      sem_binary_operation op v1 (typeof a1) v2 (typeof a2) m = Some v ->
      eval_expr (Ebinop op a1 a2 ty) v
  | eval_Econdition_true: forall a1 a2 a3 ty v1 v2,
      eval_expr a1 v1 ->
      is_true v1 (typeof a1) ->
      eval_expr a2 v2 ->
      eval_expr (Econdition a1 a2 a3 ty) v2
  | eval_Econdition_false: forall a1 a2 a3 ty v1 v3,
      eval_expr a1 v1 ->
      is_false v1 (typeof a1) ->
      eval_expr a3 v3 ->
      eval_expr (Econdition a1 a2 a3 ty) v3
  | eval_Ecast:   forall a ty v1 v,
      eval_expr a v1 ->
      cast v1 (typeof a) ty v ->
      eval_expr (Ecast a ty) v
  | eval_Elvalue: forall a loc ofs v,
      eval_lvalue a loc ofs ->
      load_value_of_type (typeof a) m loc ofs = Some v ->
      eval_expr a v

(** [eval_lvalue ge e m a b ofs] defines the evaluation of expression [a]
  in l-value position.  The result is the memory location [b, ofs]
  that contains the value of the expression [a]. *)

with eval_lvalue: expr -> block -> int -> Prop :=
  | eval_Evar_local:   forall id l ty,
      e!id = Some(l, ty) ->
      eval_lvalue (Evar id ty) l Int.zero
  | eval_Evar_global: forall id l ty,
      e!id = None ->
      Genv.find_symbol ge id = Some l ->
      type_of_global l = Some ty ->
      eval_lvalue (Evar id ty) l Int.zero
  | eval_Ederef: forall a ty l ofs,
      eval_expr a (Vptr l ofs) ->
      eval_lvalue (Ederef a ty) l ofs
 | eval_Efield_struct:   forall a i ty l ofs id fList delta,
      eval_lvalue a l ofs ->
      typeof a = Tstruct id fList ->
      field_offset i fList = OK delta ->
      eval_lvalue (Efield a i ty) l (Int.add ofs (Int.repr delta))
 | eval_Efield_union:   forall a i ty l ofs id fList,
      eval_lvalue a l ofs ->
      typeof a = Tunion id fList ->
      eval_lvalue (Efield a i ty) l ofs.

Scheme eval_expr_ind2 := Minimality for eval_expr Sort Prop
  with eval_lvalue_ind2 := Minimality for eval_lvalue Sort Prop.
Combined Scheme eval_expr_lvalue_ind from eval_expr_ind2, eval_lvalue_ind2.

(** [eval_exprlist ge e m al tyl vl] evaluates a list of r-value
  expressions [al], cast their values to the types given in [tyl],
  and produces the list of cast values [vl].  It is used to
  evaluate the arguments of function calls. *)

Inductive eval_exprlist: list expr -> typelist -> list val -> Prop :=
  | eval_Enil:
      eval_exprlist nil Tnil nil
  | eval_Econs:   forall a bl ty tyl v1 v2 vl,
      eval_expr a v1 ->
      cast v1 (typeof a) ty v2 ->
      eval_exprlist bl tyl vl ->
      eval_exprlist (a :: bl) (Tcons ty tyl) (v2 :: vl).

End EXPR.

(** ** Transition semantics for statements and functions *)

(** Continuations *)

Inductive cont: Type :=
  | Kstop: cont
  | Kseq: statement -> cont -> cont       (**r [Kseq s2 k] = after [s1] in [s1;s2] *)
  | Kwhile: expr -> statement -> cont -> cont       (**r [Kwhile e s k] = after [s] in [while (e) s] *)
  | Kdowhile: expr -> statement -> cont -> cont       (**r [Kdowhile e s k] = after [s] in [do s while (e)] *)
  | Kfor2: expr -> statement -> statement -> cont -> cont       (**r [Kfor2 e2 e3 s k] = after [s] in [for'(e2;e3) s] *)
  | Kfor3: expr -> statement -> statement -> cont -> cont       (**r [Kfor3 e2 e3 s k] = after [e3] in [for'(e2;e3) s] *)
  | Kswitch: cont -> cont       (**r catches [break] statements arising out of [switch] *)
  | Kcall: option ident ->                  (**r where to store result *)
           function ->                      (**r calling function *)
           env ->                           (**r local env of calling function *)
           temp_env ->                      (**r temporary env of calling function *)
           cont -> cont.

(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kwhile e s k => call_cont k
  | Kdowhile e s k => call_cont k
  | Kfor2 e2 e3 s k => call_cont k
  | Kfor3 e2 e3 s k => call_cont k
  | Kswitch k => call_cont k
  | _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.

(** States *)

Inductive state: Type :=
  | State
      (f: function)
      (s: statement)
      (k: cont)
      (e: env)
      (le: temp_env)
      (m: mem) : state
  | Callstate
      (fd: fundef)
      (args: list val)
      (k: cont)
      (m: mem) : state
  | Returnstate
      (res: val)
      (k: cont)
      (m: mem) : state.
                 
(** Find the statement and manufacture the continuation 
  corresponding to a label *)

Fixpoint find_label (lbl: label) (s: statement) (k: cont) 
                    {struct s}: option (statement * cont) :=
  match s with
  | Ssequence s1 s2 =>
      match find_label lbl s1 (Kseq s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sifthenelse a s1 s2 =>
      match find_label lbl s1 k with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Swhile a s1 =>
      find_label lbl s1 (Kwhile a s1 k)
  | Sdowhile a s1 =>
      find_label lbl s1 (Kdowhile a s1 k)
  | Sfor' a2 a3 s1 =>
      match find_label lbl s1 (Kfor2 a2 a3 s1 k) with
      | Some sk => Some sk
      | None => find_label lbl a3 (Kfor3 a2 a3 s1 k)
      end
  | Sswitch e sl =>
      find_label_ls lbl sl (Kswitch k)
  | Slabel lbl' s' =>
      if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
  | _ => None
  end

with find_label_ls (lbl: label) (sl: labeled_statements) (k: cont) 
                    {struct sl}: option (statement * cont) :=
  match sl with
  | LSdefault s => find_label lbl s k
  | LScase _ s sl' =>
      match find_label lbl s (Kseq (seq_of_labeled_statement sl') k) with
      | Some sk => Some sk
      | None => find_label_ls lbl sl' k
      end
  end.

(** Transition relation *)

Inductive step: state -> trace -> state -> Prop :=

  | step_assign:   forall f a1 a2 k e le m loc ofs v2 v m',
      eval_lvalue e le m a1 loc ofs ->
      eval_expr e le m a2 v2 ->
      cast v2 (typeof a2) (typeof a1) v ->
      store_value_of_type (typeof a1) m loc ofs v = Some m' ->
      step (State f (Sassign a1 a2) k e le m)
        E0 (State f Sskip k e le m')

  | step_set:   forall f id a k e le m v,
      eval_expr e le m a v ->
      step (State f (Sset id a) k e le m)
        E0 (State f Sskip k e (PTree.set id v le) m)

  | step_call:   forall f optid a al k e le m tyargs tyres vf vargs fd,
      typeof a = Tfunction tyargs tyres ->
      eval_expr e le m a vf ->
      eval_exprlist e le m al tyargs vargs ->
      Genv.find_funct ge vf = Some fd ->
      type_of_fundef fd = typeof a ->
      step (State f (Scall optid a al) k e le m)
        E0 (Callstate fd vargs (Kcall optid f e le k) m)

  | step_seq:  forall f s1 s2 k e le m,
      step (State f (Ssequence s1 s2) k e le m)
        E0 (State f s1 (Kseq s2 k) e le m)
  | step_skip_seq: forall f s k e le m,
      step (State f Sskip (Kseq s k) e le m)
        E0 (State f s k e le m)
  | step_continue_seq: forall f s k e le m,
      step (State f Scontinue (Kseq s k) e le m)
        E0 (State f Scontinue k e le m)
  | step_break_seq: forall f s k e le m,
      step (State f Sbreak (Kseq s k) e le m)
        E0 (State f Sbreak k e le m)

  | step_ifthenelse_true:  forall f a s1 s2 k e le m v1,
      eval_expr e le m a v1 ->
      is_true v1 (typeof a) ->
      step (State f (Sifthenelse a s1 s2) k e le m)
        E0 (State f s1 k e le m)
  | step_ifthenelse_false: forall f a s1 s2 k e le m v1,
      eval_expr e le m a v1 ->
      is_false v1 (typeof a) ->
      step (State f (Sifthenelse a s1 s2) k e le m)
        E0 (State f s2 k e le m)

  | step_while_false: forall f a s k e le m v,
      eval_expr e le m a v ->
      is_false v (typeof a) ->
      step (State f (Swhile a s) k e le m)
        E0 (State f Sskip k e le m)
  | step_while_true: forall f a s k e le m v,
      eval_expr e le m a v ->
      is_true v (typeof a) ->
      step (State f (Swhile a s) k e le m)
        E0 (State f s (Kwhile a s k) e le m)
  | step_skip_or_continue_while: forall f x a s k e le m,
      x = Sskip \/ x = Scontinue ->
      step (State f x (Kwhile a s k) e le m)
        E0 (State f (Swhile a s) k e le m)
  | step_break_while: forall f a s k e le m,
      step (State f Sbreak (Kwhile a s k) e le m)
        E0 (State f Sskip k e le m)

  | step_dowhile: forall f a s k e le m,
      step (State f (Sdowhile a s) k e le m)
        E0 (State f s (Kdowhile a s k) e le m)
  | step_skip_or_continue_dowhile_false: forall f x a s k e le m v,
      x = Sskip \/ x = Scontinue ->
      eval_expr e le m a v ->
      is_false v (typeof a) ->
      step (State f x (Kdowhile a s k) e le m)
        E0 (State f Sskip k e le m)
  | step_skip_or_continue_dowhile_true: forall f x a s k e le m v,
      x = Sskip \/ x = Scontinue ->
      eval_expr e le m a v ->
      is_true v (typeof a) ->
      step (State f x (Kdowhile a s k) e le m)
        E0 (State f (Sdowhile a s) k e le m)
  | step_break_dowhile: forall f a s k e le m,
      step (State f Sbreak (Kdowhile a s k) e le m)
        E0 (State f Sskip k e le m)

  | step_for_false: forall f a2 a3 s k e le m v,
      eval_expr e le m a2 v ->
      is_false v (typeof a2) ->
      step (State f (Sfor' a2 a3 s) k e le m)
        E0 (State f Sskip k e le m)
  | step_for_true: forall f a2 a3 s k e le m v,
      eval_expr e le m a2 v ->
      is_true v (typeof a2) ->
      step (State f (Sfor' a2 a3 s) k e le m)
        E0 (State f s (Kfor2 a2 a3 s k) e le m)
  | step_skip_or_continue_for2: forall f x a2 a3 s k e le m,
      x = Sskip \/ x = Scontinue ->
      step (State f x (Kfor2 a2 a3 s k) e le m)
        E0 (State f a3 (Kfor3 a2 a3 s k) e le m)
  | step_break_for2: forall f a2 a3 s k e le m,
      step (State f Sbreak (Kfor2 a2 a3 s k) e le m)
        E0 (State f Sskip k e le m)
  | step_skip_for3: forall f a2 a3 s k e le m,
      step (State f Sskip (Kfor3 a2 a3 s k) e le m)
        E0 (State f (Sfor' a2 a3 s) k e le m)
  | step_break_for3: forall f a2 a3 s k e le m,
      step (State f Sbreak (Kfor3 a2 a3 s k) e le m)
        E0 (State f Sskip k e le m)

  | step_return_0: forall f k e le m m',
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f (Sreturn None) k e le m)
        E0 (Returnstate Vundef (call_cont k) m')
  | step_return_1: forall f a k e le m v v' m',
      eval_expr e le m a v -> 
      cast v (typeof a) f.(fn_return) v' ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f (Sreturn (Some a)) k e le m)
        E0 (Returnstate v' (call_cont k) m')
  | step_skip_call: forall f k e le m m',
      is_call_cont k ->
      f.(fn_return) = Tvoid ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f Sskip k e le m)
        E0 (Returnstate Vundef k m')

  | step_switch: forall f a sl k e le m n,
      eval_expr e le m a (Vint n) ->
      step (State f (Sswitch a sl) k e le m)
        E0 (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le m)
  | step_skip_break_switch: forall f x k e le m,
      x = Sskip \/ x = Sbreak ->
      step (State f x (Kswitch k) e le m)
        E0 (State f Sskip k e le m)
  | step_continue_switch: forall f k e le m,
      step (State f Scontinue (Kswitch k) e le m)
        E0 (State f Scontinue k e le m)

  | step_label: forall f lbl s k e le m,
      step (State f (Slabel lbl s) k e le m)
        E0 (State f s k e le m)

  | step_goto: forall f lbl k e le m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
      step (State f (Sgoto lbl) k e le m)
        E0 (State f s' k' e le m)

  | step_internal_function: forall f vargs k m e m1 m2,
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      alloc_variables empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      bind_parameters e m1 f.(fn_params) vargs m2 ->
      step (Callstate (Internal f) vargs k m)
        E0 (State f f.(fn_body) k e (PTree.empty val) m2)

  | step_external_function: forall ef targs tres vargs k m vres t m',
      external_call ef  ge vargs m t vres m' ->
      step (Callstate (External ef targs tres) vargs k m)
         t (Returnstate vres k m')

  | step_returnstate_none: forall v f e le k m,
      step (Returnstate v (Kcall None f e le k) m)
        E0 (State f Sskip k e le m)
  | step_returnstate_some: forall v id f e le k m,
      step (Returnstate v (Kcall (Some id) f e le k) m)
        E0 (State f Sskip k e (PTree.set id v le) m).


(** * Alternate big-step semantics *)

(** ** Big-step semantics for terminating statements and functions *)

(** The execution of a statement produces an ``outcome'', indicating
  how the execution terminated: either normally or prematurely
  through the execution of a [break], [continue] or [return] statement. *)

Inductive outcome: Type :=
   | Out_break: outcome                 (**r terminated by [break] *)
   | Out_continue: outcome              (**r terminated by [continue] *)
   | Out_normal: outcome                (**r terminated normally *)
   | Out_return: option (val * type) -> outcome. (**r terminated by [return] *)

Inductive out_normal_or_continue : outcome -> Prop :=
  | Out_normal_or_continue_N: out_normal_or_continue Out_normal
  | Out_normal_or_continue_C: out_normal_or_continue Out_continue.

Inductive out_break_or_return : outcome -> outcome -> Prop :=
  | Out_break_or_return_B: out_break_or_return Out_break Out_normal
  | Out_break_or_return_R: forall ov,
      out_break_or_return (Out_return ov) (Out_return ov).

Definition outcome_switch (out: outcome) : outcome :=
  match out with
  | Out_break => Out_normal
  | o => o
  end.

Definition outcome_result_value (out: outcome) (t: type) (v: val) : Prop :=
  match out, t with
  | Out_normal, Tvoid => v = Vundef
  | Out_return None, Tvoid => v = Vundef
  | Out_return (Some (v',t')), ty => ty <> Tvoid /\ cast v' t' t v
  | _, _ => False
  end. 

(** [exec_stmt ge e m1 s t m2 out] describes the execution of 
  the statement [s].  [out] is the outcome for this execution.
  [m1] is the initial memory state, [m2] the final memory state.
  [t] is the trace of input/output events performed during this
  evaluation. *)

Inductive exec_stmt: env -> temp_env -> mem -> statement -> trace -> temp_env -> mem -> outcome -> Prop :=
  | exec_Sskip:   forall e le m,
      exec_stmt e le m Sskip
               E0 le m Out_normal
  | exec_Sassign:   forall e le m a1 a2 loc ofs v2 v m',
      eval_lvalue e le m a1 loc ofs ->
      eval_expr e le m a2 v2 ->
      cast v2 (typeof a2) (typeof a1) v ->
      store_value_of_type (typeof a1) m loc ofs v = Some m' ->
      exec_stmt e le m (Sassign a1 a2)
               E0 le m' Out_normal
  | exec_Sset:     forall e le m id a v,
      eval_expr e le m a v ->
      exec_stmt e le m (Sset id a)
               E0 (PTree.set id v le) m Out_normal      
  | exec_Scall_none:   forall e le m a al tyargs tyres vf vargs f t m' vres,
      typeof a = Tfunction tyargs tyres ->
      eval_expr e le m a vf ->
      eval_exprlist e le m al tyargs vargs ->
      Genv.find_funct ge vf = Some f ->
      type_of_fundef f = typeof a ->
      eval_funcall le m f vargs t m' vres ->
      exec_stmt e le m (Scall None a al)
                t le m' Out_normal
  | exec_Scall_some:   forall e le m id a al tyargs tyres vf vargs f t m' vres,
      typeof a = Tfunction tyargs tyres ->
      eval_expr e le m a vf ->
      eval_exprlist e le m al tyargs vargs ->
      Genv.find_funct ge vf = Some f ->
      type_of_fundef f = typeof a ->
      eval_funcall le m f vargs t m' vres ->
      exec_stmt e le m (Scall (Some id) a al)
                t (PTree.set id vres le) m' Out_normal
  | exec_Sseq_1:   forall e le m s1 s2 t1 le1 m1 t2 le2 m2 out,
      exec_stmt e le m s1 t1 le1 m1 Out_normal ->
      exec_stmt e le1 m1 s2 t2 le2 m2 out ->
      exec_stmt e le m (Ssequence s1 s2)
                (t1 ** t2) le2 m2 out
  | exec_Sseq_2:   forall e le m s1 s2 t1 le1 m1 out,
      exec_stmt e le m s1 t1 le1 m1 out ->
      out <> Out_normal ->
      exec_stmt e le m (Ssequence s1 s2)
                t1 le1 m1 out
  | exec_Sifthenelse_true: forall e le m a s1 s2 v1 t le' m' out,
      eval_expr e le m a v1 ->
      is_true v1 (typeof a) ->
      exec_stmt e le m s1 t le' m' out ->
      exec_stmt e le m (Sifthenelse a s1 s2)
                t le' m' out
  | exec_Sifthenelse_false: forall e le m a s1 s2 v1 t le' m' out,
      eval_expr e le m a v1 ->
      is_false v1 (typeof a) ->
      exec_stmt e le m s2 t le' m' out ->
      exec_stmt e le m (Sifthenelse a s1 s2)
                t le' m' out
  | exec_Sreturn_none:   forall e le m,
      exec_stmt e le m (Sreturn None)
               E0 le m (Out_return None)
  | exec_Sreturn_some: forall e le m a v,
      eval_expr e le m a v ->
      exec_stmt e le m (Sreturn (Some a))
                E0 le m (Out_return (Some (v, typeof a)))
  | exec_Sbreak:   forall e le m,
      exec_stmt e le m Sbreak
               E0 le m Out_break
  | exec_Scontinue:   forall e le m,
      exec_stmt e le m Scontinue
               E0 le m Out_continue
  | exec_Swhile_false: forall e le m a s v,
      eval_expr e le m a v ->
      is_false v (typeof a) ->
      exec_stmt e le m (Swhile a s)
               E0 le m Out_normal
  | exec_Swhile_stop: forall e le m a v s t le' m' out' out,
      eval_expr e le m a v ->
      is_true v (typeof a) ->
      exec_stmt e le m s t le' m' out' ->
      out_break_or_return out' out ->
      exec_stmt e le m (Swhile a s)
                t le' m' out
  | exec_Swhile_loop: forall e le m a s v t1 le1 m1 out1 t2 le2 m2 out,
      eval_expr e le m a v ->
      is_true v (typeof a) ->
      exec_stmt e le m s t1 le1 m1 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e le1 m1 (Swhile a s) t2 le2 m2 out ->
      exec_stmt e le m (Swhile a s)
                (t1 ** t2) le2 m2 out
  | exec_Sdowhile_false: forall e le m s a t le1 m1 out1 v,
      exec_stmt e le m s t le1 m1 out1 ->
      out_normal_or_continue out1 ->
      eval_expr e le1 m1 a v ->
      is_false v (typeof a) ->
      exec_stmt e le m (Sdowhile a s)
                t le1 m1 Out_normal
  | exec_Sdowhile_stop: forall e le m s a t le1 m1 out1 out,
      exec_stmt e le m s t le1 m1 out1 ->
      out_break_or_return out1 out ->
      exec_stmt e le m (Sdowhile a s)
                t le1 m1 out
  | exec_Sdowhile_loop: forall e le m s a le1 m1 le2 m2 t1 t2 out out1 v,
      exec_stmt e le m s t1 le1 m1 out1 ->
      out_normal_or_continue out1 ->
      eval_expr e le1 m1 a v ->
      is_true v (typeof a) ->
      exec_stmt e le1 m1 (Sdowhile a s) t2 le2 m2 out ->
      exec_stmt e le m (Sdowhile a s) 
                (t1 ** t2) le2 m2 out

  | exec_Sfor_false: forall e le m s a2 a3 v,
      eval_expr e le m a2 v ->
      is_false v (typeof a2) ->
      exec_stmt e le m (Sfor' a2 a3 s)
               E0 le m Out_normal
  | exec_Sfor_stop: forall e le m s a2 a3 v le1 m1 t out1 out,
      eval_expr e le m a2 v ->
      is_true v (typeof a2) ->
      exec_stmt e le m s t le1 m1 out1 ->
      out_break_or_return out1 out ->
      exec_stmt e le m (Sfor' a2 a3 s)
                t le1 m1 out
  | exec_Sfor_loop: forall e le m s a2 a3 v le1 m1 le2 m2 le3 m3 t1 t2 t3 out1 out,
      eval_expr e le m a2 v ->
      is_true v (typeof a2) ->
      exec_stmt e le m s t1 le1 m1 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e le1 m1 a3 t2 le2 m2 Out_normal ->
      exec_stmt e le2 m2 (Sfor' a2 a3 s) t3 le3 m3 out ->
      exec_stmt e le m (Sfor' a2 a3 s)
                (t1 ** t2 ** t3) le3 m3 out
  | exec_Sswitch:   forall e le m a t n sl le1 m1 out,
      eval_expr e le m a (Vint n) ->
      exec_stmt e le m (seq_of_labeled_statement (select_switch n sl)) t le1 m1 out ->
      exec_stmt e le m (Sswitch a sl)
                t le1 m1 (outcome_switch out)

(** [eval_funcall m1 fd args t m2 res] describes the invocation of
  function [fd] with arguments [args].  [res] is the value returned
  by the call.  *)

with eval_funcall: temp_env -> mem -> fundef -> list val -> trace -> mem -> val -> Prop :=
  | eval_funcall_internal: forall le m f vargs t e m1 m2 m3 out vres m4,
      alloc_variables empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      bind_parameters e m1 f.(fn_params) vargs m2 ->
      exec_stmt e (PTree.empty val) m2 f.(fn_body) t le m3 out ->
      outcome_result_value out f.(fn_return) vres ->
      Mem.free_list m3 (blocks_of_env e) = Some m4 ->
      eval_funcall (PTree.empty val) m (Internal f) vargs t m4 vres
  | eval_funcall_external: forall m ef targs tres vargs t vres m',
      external_call ef ge vargs m t vres m' ->
      eval_funcall (PTree.empty val) m (External ef targs tres) vargs t m' vres.

Scheme exec_stmt_ind2 := Minimality for exec_stmt Sort Prop
  with eval_funcall_ind2 := Minimality for eval_funcall Sort Prop.

(** ** Big-step semantics for diverging statements and functions *)

(** Coinductive semantics for divergence.
  [execinf_stmt ge e m s t] holds if the execution of statement [s]
  diverges, i.e. loops infinitely.  [t] is the possibly infinite
  trace of observable events performed during the execution. *)

CoInductive execinf_stmt: env -> temp_env -> mem -> statement -> traceinf -> Prop :=
  | execinf_Scall_none:   forall e le m a al vf tyargs tyres vargs f t,
      typeof a = Tfunction tyargs tyres ->
      eval_expr e le m a vf ->
      eval_exprlist e le m al tyargs vargs ->
      Genv.find_funct ge vf = Some f ->
      type_of_fundef f = typeof a ->
      evalinf_funcall le m f vargs t ->
      execinf_stmt e le m (Scall None a al) t
  | execinf_Scall_some:   forall e le m id a al vf tyargs tyres vargs f t,
      typeof a = Tfunction tyargs tyres ->
      eval_expr e le m a vf ->
      eval_exprlist e le m al tyargs vargs ->
      Genv.find_funct ge vf = Some f ->
      type_of_fundef f = typeof a ->
      evalinf_funcall le m f vargs t ->
      execinf_stmt e le m (Scall (Some id) a al) t
  | execinf_Sseq_1:   forall e le m s1 s2 t,
      execinf_stmt e le m s1 t ->
      execinf_stmt e le m (Ssequence s1 s2) t
  | execinf_Sseq_2:   forall e le m s1 s2 t1 le1 m1 t2,
      exec_stmt e le m s1 t1 le1 m1 Out_normal ->
      execinf_stmt e le1 m1 s2 t2 ->
      execinf_stmt e le m (Ssequence s1 s2) (t1 *** t2)
  | execinf_Sifthenelse_true: forall e le m a s1 s2 v1 t,
      eval_expr e le m a v1 ->
      is_true v1 (typeof a) ->
      execinf_stmt e le m s1 t ->
      execinf_stmt e le m (Sifthenelse a s1 s2) t
  | execinf_Sifthenelse_false: forall e le m a s1 s2 v1 t,
      eval_expr e le m a v1 ->
      is_false v1 (typeof a) ->
      execinf_stmt e le m s2 t ->
      execinf_stmt e le m (Sifthenelse a s1 s2) t
  | execinf_Swhile_body: forall e le m a v s t,
      eval_expr e le m a v ->
      is_true v (typeof a) ->
      execinf_stmt e le m s t ->
      execinf_stmt e le m (Swhile a s) t
  | execinf_Swhile_loop: forall e le m a s v t1 le1 m1 out1 t2,
      eval_expr e le m a v ->
      is_true v (typeof a) ->
      exec_stmt e le m s t1 le1 m1 out1 ->
      out_normal_or_continue out1 ->
      execinf_stmt e le1 m1 (Swhile a s) t2 ->
      execinf_stmt e le m (Swhile a s) (t1 *** t2)
  | execinf_Sdowhile_body: forall e le m s a t,
      execinf_stmt e le m s t ->
      execinf_stmt e le m (Sdowhile a s) t
  | execinf_Sdowhile_loop: forall e le m s a le1 m1 t1 t2 out1 v,
      exec_stmt e le m s t1 le1 m1 out1 ->
      out_normal_or_continue out1 ->
      eval_expr e le1 m1 a v ->
      is_true v (typeof a) ->
      execinf_stmt e le1 m1 (Sdowhile a s) t2 ->
      execinf_stmt e le m (Sdowhile a s) (t1 *** t2)
  | execinf_Sfor_body: forall e le m s a2 a3 v t,
      eval_expr e le m a2 v ->
      is_true v (typeof a2) ->
      execinf_stmt e le m s t ->
      execinf_stmt e le m (Sfor' a2 a3 s) t
  | execinf_Sfor_next: forall e le m s a2 a3 v le1 m1 t1 t2 out1,
      eval_expr e le m a2 v ->
      is_true v (typeof a2) ->
      exec_stmt e le m s t1 le1 m1 out1 ->
      out_normal_or_continue out1 ->
      execinf_stmt e le1 m1 a3 t2 ->
      execinf_stmt e le m (Sfor' a2 a3 s) (t1 *** t2)
  | execinf_Sfor_loop: forall e le m s a2 a3 v le1 m1 le2 m2 t1 t2 t3 out1,
      eval_expr e le m a2 v ->
      is_true v (typeof a2) ->
      exec_stmt e le m s t1 le1 m1 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e le1 m1 a3 t2 le2 m2 Out_normal ->
      execinf_stmt e le2 m2 (Sfor' a2 a3 s) t3 ->
      execinf_stmt e le m (Sfor' a2 a3 s) (t1 *** t2 *** t3)
  | execinf_Sswitch:   forall e le m a t n sl,
      eval_expr e le m a (Vint n) ->
      execinf_stmt e le m (seq_of_labeled_statement (select_switch n sl)) t ->
      execinf_stmt e le m (Sswitch a sl) t

(** [evalinf_funcall ge m fd args t] holds if the invocation of function
    [fd] on arguments [args] diverges, with observable trace [t]. *)

with evalinf_funcall:temp_env -> mem -> fundef -> list val -> traceinf -> Prop :=
  | evalinf_funcall_internal: forall m f vargs t e m1 m2,
      alloc_variables empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      bind_parameters e m1 f.(fn_params) vargs m2 ->
      execinf_stmt e (PTree.empty val) m2 f.(fn_body) t ->
      evalinf_funcall (PTree.empty val) m (Internal f) vargs t.

End SEMANTICS.

(** * Whole-program semantics *)

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
      type_of_fundef f = Tfunction Tnil (Tint I32 Signed) ->
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

(** Big-step execution of a whole program.  *)

Inductive bigstep_program_terminates (p: program): trace -> int -> Prop :=
  | bigstep_program_terminates_intro: forall b f m0 m1 t r,
      let ge := Genv.globalenv p in 
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil (Tint I32 Signed) ->
      eval_funcall ge (PTree.empty val) m0 f nil t m1 (Vint r) ->
      bigstep_program_terminates p t r.

Inductive bigstep_program_diverges (p: program): traceinf -> Prop :=
  | bigstep_program_diverges_intro: forall b f m0 t,
      let ge := Genv.globalenv p in 
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil (Tint I32 Signed) ->
      evalinf_funcall ge (PTree.empty val) m0 f nil t ->
      bigstep_program_diverges p t.

(** * Implication from big-step semantics to transition semantics *)

Section BIGSTEP_TO_TRANSITIONS.

Variable prog: program.
Let ge : genv := Genv.globalenv prog.

Definition exec_stmt_eval_funcall_ind
  (PS: env -> temp_env -> mem -> statement -> trace -> temp_env -> mem -> outcome -> Prop)
  (PF: temp_env -> mem -> fundef -> list val -> trace -> mem -> val -> Prop) :=
  fun a b c d e f g h i j k l m n o p q r s t u v w x y =>
  conj (exec_stmt_ind2 ge PS PF a b c d e f g h i j k l m n o p q r s t u v w x y)
       (eval_funcall_ind2 ge PS PF a b c d e f g h i j k l m n o p q r s t u v w x y).

Inductive outcome_state_match
       (e: env) (le: temp_env) (m: mem) (f: function) (k: cont): outcome -> state -> Prop :=
  | osm_normal:
      outcome_state_match e le m f k Out_normal (State f Sskip k e le m)
  | osm_break:
      outcome_state_match e le m f k Out_break (State f Sbreak k e le m)
  | osm_continue:
      outcome_state_match e le m f k Out_continue (State f Scontinue k e le m)
  | osm_return_none: forall k',
      call_cont k' = call_cont k ->
      outcome_state_match e le m f k 
        (Out_return None) (State f (Sreturn None) k' e le m)
  | osm_return_some: forall a v k',
      call_cont k' = call_cont k ->
      eval_expr ge e le m a v ->
      outcome_state_match e le m f k
        (Out_return (Some (v,typeof a))) (State f (Sreturn (Some a)) k' e le m).

Lemma is_call_cont_call_cont:
  forall k, is_call_cont k -> call_cont k = k.
Proof.
  destruct k; simpl; intros; contradiction || auto.
Qed.

Lemma exec_stmt_eval_funcall_steps:
  (forall e le m s t le' m' out,
   exec_stmt ge e le m s t le' m' out ->
   forall f k, exists S,
   star step ge (State f s k e le m) t S
   /\ outcome_state_match e le' m' f k out S)
/\
  (forall le m fd args t m' res,
   eval_funcall ge le m fd args t m' res ->
   forall k,
   is_call_cont k ->
   star step ge (Callstate fd args k m) t (Returnstate res k m')).
Proof.
  apply exec_stmt_eval_funcall_ind; intros.

(* skip *)
  econstructor; split. apply star_refl. constructor.

(* assign *)
  econstructor; split. apply star_one. econstructor; eauto. constructor.

(* set *)
  econstructor; split. apply star_one. econstructor; eauto. constructor.

(* call none *)
  econstructor; split.
  eapply star_left. econstructor; eauto. 
  eapply star_right. apply H5. simpl; auto. econstructor. reflexivity. traceEq.
  constructor.

(* call some *)
  econstructor; split.
  eapply star_left. econstructor; eauto. 
  eapply star_right. apply H5. simpl; auto. econstructor; eauto. reflexivity. traceEq.
  constructor.

(* sequence 2 *)
  destruct (H0 f (Kseq s2 k)) as [S1 [A1 B1]]. inv B1.
  destruct (H2 f k) as [S2 [A2 B2]]. 
  econstructor; split.
  eapply star_left. econstructor.
  eapply star_trans. eexact A1. 
  eapply star_left. constructor. eexact A2.
  reflexivity. reflexivity. traceEq.
  auto.

(* sequence 1 *)
  destruct (H0 f (Kseq s2 k)) as [S1 [A1 B1]].
  set (S2 :=
    match out with
    | Out_break => State f Sbreak k e le1 m1
    | Out_continue => State f Scontinue k e le1 m1
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. econstructor.
  eapply star_trans. eexact A1.
  unfold S2; inv B1.
    congruence.
    apply star_one. apply step_break_seq.
    apply star_one. apply step_continue_seq.
    apply star_refl.
    apply star_refl.
  reflexivity. traceEq.
  unfold S2; inv B1; congruence || econstructor; eauto.

(* ifthenelse true *)
  destruct (H2 f k) as [S1 [A1 B1]].
  exists S1; split.
  eapply star_left. eapply step_ifthenelse_true; eauto. eexact A1. traceEq.
  auto.

(* ifthenelse false *)
  destruct (H2 f k) as [S1 [A1 B1]].
  exists S1; split.
  eapply star_left. eapply step_ifthenelse_false; eauto. eexact A1. traceEq.
  auto.

(* return none *)
  econstructor; split. apply star_refl. constructor. auto.

(* return some *)
  econstructor; split. apply star_refl. econstructor; eauto.

(* break *)
  econstructor; split. apply star_refl. constructor.

(* continue *)
  econstructor; split. apply star_refl. constructor.

(* while false *)
  econstructor; split.
  apply star_one. eapply step_while_false; eauto. 
  constructor.

(* while stop *)
  destruct (H2 f (Kwhile a s k)) as [S1 [A1 B1]].
  set (S2 :=
    match out' with
    | Out_break => State f Sskip k e le' m'
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. eapply step_while_true; eauto. 
  eapply star_trans. eexact A1.
  unfold S2. inversion H3; subst.
  inv B1. apply star_one. constructor.    
  apply star_refl.
  reflexivity. traceEq.
  unfold S2. inversion H3; subst. constructor. inv B1; econstructor; eauto.

(* while loop *)
  destruct (H2 f (Kwhile a s k)) as [S1 [A1 B1]].
  destruct (H5 f k) as [S2 [A2 B2]].
  exists S2; split.
  eapply star_left. eapply step_while_true; eauto.
  eapply star_trans. eexact A1.
  eapply star_left.
  inv H3; inv B1; apply step_skip_or_continue_while; auto.
  eexact A2.
  reflexivity. reflexivity. traceEq.
  auto.

(* dowhile false *)
  destruct (H0 f (Kdowhile a s k)) as [S1 [A1 B1]].
  exists (State f Sskip k e le1 m1); split.
  eapply star_left. constructor. 
  eapply star_right. eexact A1.
  inv H1; inv B1; eapply step_skip_or_continue_dowhile_false; eauto.
  reflexivity. traceEq. 
  constructor.

(* dowhile stop *)
  destruct (H0 f (Kdowhile a s k)) as [S1 [A1 B1]].
  set (S2 :=
    match out1 with
    | Out_break => State f Sskip k e le1 m1
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. apply step_dowhile. 
  eapply star_trans. eexact A1.
  unfold S2. inversion H1; subst.
  inv B1. apply star_one. constructor.
  apply star_refl.
  reflexivity. traceEq.
  unfold S2. inversion H1; subst. constructor. inv B1; econstructor; eauto.

(* dowhile loop *)
  destruct (H0 f (Kdowhile a s k)) as [S1 [A1 B1]].
  destruct (H5 f k) as [S2 [A2 B2]].
  exists S2; split.
  eapply star_left. apply step_dowhile. 
  eapply star_trans. eexact A1.
  eapply star_left.
  inv H1; inv B1; eapply step_skip_or_continue_dowhile_true; eauto.
  eexact A2.
  reflexivity. reflexivity. traceEq.
  auto.

(* for false *)
  econstructor; split.
  eapply star_one. eapply step_for_false; eauto. 
  constructor.

(* for stop *)
  destruct (H2 f (Kfor2 a2 a3 s k)) as [S1 [A1 B1]].
  set (S2 :=
    match out1 with
    | Out_break => State f Sskip k e le1 m1
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. eapply step_for_true; eauto. 
  eapply star_trans. eexact A1.
  unfold S2. inversion H3; subst.
  inv B1. apply star_one. constructor. 
  apply star_refl.
  reflexivity. traceEq.
  unfold S2. inversion H3; subst. constructor. inv B1; econstructor; eauto.

(* for loop *)
  destruct (H2 f (Kfor2 a2 a3 s k)) as [S1 [A1 B1]].
  destruct (H5 f (Kfor3 a2 a3 s k)) as [S2 [A2 B2]]. inv B2.
  destruct (H7 f k) as [S3 [A3 B3]].
  exists S3; split.
  eapply star_left. eapply step_for_true; eauto. 
  eapply star_trans. eexact A1.
  eapply star_trans with (s2 := State f a3 (Kfor3 a2 a3 s k) e le1 m1).
  inv H3; inv B1.
  apply star_one. constructor. auto. 
  apply star_one. constructor. auto. 
  eapply star_trans. eexact A2. 
  eapply star_left. constructor.
  eexact A3.
  reflexivity. reflexivity. reflexivity. reflexivity. traceEq.
  auto.

(* switch *)
  destruct (H1 f (Kswitch k)) as [S1 [A1 B1]].
  set (S2 :=
    match out with
    | Out_normal => State f Sskip k e le1 m1
    | Out_break => State f Sskip k e le1 m1
    | Out_continue => State f Scontinue k e le1 m1
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. eapply step_switch; eauto. 
  eapply star_trans. eexact A1. 
  unfold S2; inv B1. 
    apply star_one. constructor. auto. 
    apply star_one. constructor. auto. 
    apply star_one. constructor. 
    apply star_refl.
    apply star_refl.
  reflexivity. traceEq.
  unfold S2. inv B1; simpl; econstructor; eauto.

(* call internal *)
  destruct (H3 f k) as [S1 [A1 B1]].
  eapply star_left. eapply step_internal_function; eauto.
  eapply star_right. eexact A1. 
   inv B1; simpl in H4; try contradiction.
  (* Out_normal *)
  assert (fn_return f = Tvoid /\ vres = Vundef).
    destruct (fn_return f); auto || contradiction.
  destruct H7. subst vres. apply step_skip_call; auto.
  (* Out_return None *)
  assert (fn_return f = Tvoid /\ vres = Vundef).
    destruct (fn_return f); auto || contradiction.
  destruct H8. subst vres.
  rewrite <- (is_call_cont_call_cont k H6). rewrite <- H7.
  apply step_return_0; auto.
  (* Out_return Some *)
  destruct H4.
  rewrite <- (is_call_cont_call_cont k H6). rewrite <- H7.
  eapply step_return_1; eauto.
  reflexivity. traceEq.

(* call external *)
  apply star_one. apply step_external_function; auto. 
Qed.

Lemma exec_stmt_steps:
   forall e le m s t le' m' out,
   exec_stmt ge e le m s t le' m' out ->
   forall f k, exists S,
   star step ge (State f s k e le m) t S
   /\ outcome_state_match e le' m' f k out S.
Proof (proj1 exec_stmt_eval_funcall_steps).

Lemma eval_funcall_steps:
   forall le m fd args t m' res,
   eval_funcall ge le m fd args t m' res ->
   forall k,
   is_call_cont k ->
   star step ge (Callstate fd args k m) t (Returnstate res k m').
Proof (proj2 exec_stmt_eval_funcall_steps).

Definition order (x y: unit) := False.

Lemma evalinf_funcall_forever:
  forall le m fd args T k,
  evalinf_funcall ge le m fd args T ->
  forever_N step order ge tt (Callstate fd args k m) T.
Proof.
  cofix CIH_FUN.
  assert (forall e le m s T f k,
          execinf_stmt ge e le m s T ->
          forever_N step order ge tt (State f s k e le m) T).
  cofix CIH_STMT.
  intros. inv H.

(* call none *)
  eapply forever_N_plus.
  apply plus_one. eapply step_call; eauto. 
  eapply CIH_FUN. eauto. traceEq.
(* call some *)
  eapply forever_N_plus.
  apply plus_one. eapply step_call; eauto. 
  eapply CIH_FUN. eauto. traceEq.

(* seq 1 *)
  eapply forever_N_plus.
  apply plus_one. econstructor.
  apply CIH_STMT; eauto. traceEq.
(* seq 2 *)
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ H0 f (Kseq s2 k)) as [S1 [A1 B1]].
  inv B1.
  eapply forever_N_plus.
  eapply plus_left. constructor. eapply star_trans. eexact A1. 
  apply star_one. constructor. reflexivity. reflexivity.
  apply CIH_STMT; eauto. traceEq.

(* ifthenelse true *)
  eapply forever_N_plus.
  apply plus_one. eapply step_ifthenelse_true; eauto. 
  apply CIH_STMT; eauto. traceEq.
(* ifthenelse false *)
  eapply forever_N_plus.
  apply plus_one. eapply step_ifthenelse_false; eauto. 
  apply CIH_STMT; eauto. traceEq.

(* while body *)
  eapply forever_N_plus.
  eapply plus_one. eapply step_while_true; eauto.
  apply CIH_STMT; eauto. traceEq.
(* while loop *)
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ H2 f (Kwhile a s0 k)) as [S1 [A1 B1]].
  eapply forever_N_plus with (s2 := State f (Swhile a s0) k e le1 m1).
  eapply plus_left. eapply step_while_true; eauto.
  eapply star_right. eexact A1.
  inv H3; inv B1; apply step_skip_or_continue_while; auto. 
  reflexivity. reflexivity.
  apply CIH_STMT; eauto. traceEq.

(* dowhile body *)
  eapply forever_N_plus.
  eapply plus_one. eapply step_dowhile.
  apply CIH_STMT; eauto.
  traceEq.

(* dowhile loop *)
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ H0 f (Kdowhile a s0 k)) as [S1 [A1 B1]].
  eapply forever_N_plus with (s2 := State f (Sdowhile a s0) k e le1 m1).
  eapply plus_left. eapply step_dowhile. 
  eapply star_right. eexact A1.
  inv H1; inv B1; eapply step_skip_or_continue_dowhile_true; eauto. 
  reflexivity. reflexivity.
  apply CIH_STMT. eauto. 
  traceEq.

(* for body *)
  eapply forever_N_plus.
  apply plus_one. eapply step_for_true; eauto. 
  apply CIH_STMT; eauto.
  traceEq.

(* for next *)
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ H2 f (Kfor2 a2 a3 s0 k)) as [S1 [A1 B1]].
  eapply forever_N_plus.
  eapply plus_left. eapply step_for_true; eauto.
  eapply star_trans. eexact A1.
  apply star_one.
  inv H3; inv B1; apply step_skip_or_continue_for2; auto.
  reflexivity. reflexivity. 
  apply CIH_STMT; eauto.
  traceEq.

(* for body *)
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ H2 f (Kfor2 a2 a3 s0 k)) as [S1 [A1 B1]].
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ H4 f (Kfor3 a2 a3 s0 k)) as [S2 [A2 B2]].
  inv B2.
  eapply forever_N_plus.
  eapply plus_left. eapply step_for_true; eauto. 
  eapply star_trans. eexact A1.
  eapply star_left. inv H3; inv B1; apply step_skip_or_continue_for2; auto.
  eapply star_right. eexact A2. 
  constructor. 
  reflexivity. reflexivity. reflexivity. reflexivity.  
  apply CIH_STMT; eauto.
  traceEq.

(* switch *)
  eapply forever_N_plus.
  eapply plus_one. eapply step_switch; eauto.
  apply CIH_STMT; eauto.
  traceEq.

(* call internal *)
  intros. inv H0.
  eapply forever_N_plus.
  eapply plus_one. econstructor; eauto. 
  apply H; eauto.
  traceEq.
Qed.

Theorem bigstep_program_terminates_exec:
  forall t r, bigstep_program_terminates prog t r -> exec_program prog (Terminates t r).
Proof.
  intros. inv H. 
  econstructor.
  econstructor. eauto. eauto. eauto. auto.
  eapply eval_funcall_steps. eauto. red; auto. 
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
    eapply forever_N_forever with (order := order).
    red; intros. constructor; intros. red in H. elim H.
    eapply evalinf_funcall_forever; eauto. 
  destruct (forever_silent_or_reactive _ _ _ _ _ _ H)
  as [A | [t [s' [T' [B [C D]]]]]]. 
  left. econstructor. econstructor; eauto. eauto.
  right. exists t. split.
  econstructor. econstructor; eauto. eauto. auto. 
  subst T. rewrite <- (E0_right t) at 1. apply traceinf_prefix_app. constructor.
Qed.

End BIGSTEP_TO_TRANSITIONS.
