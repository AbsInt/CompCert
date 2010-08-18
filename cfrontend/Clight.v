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
