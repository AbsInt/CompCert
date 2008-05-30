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

(** Dynamic semantics for the Clight language *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Csyntax.
Require Import Smallstep.

(** * Semantics of type-dependent operations *)

(** Interpretation of values as truth values.
  Non-zero integers, non-zero floats and non-null pointers are
  considered as true.  The integer zero (which also represents
  the null pointer) and the float 0.0 are false. *)

Inductive is_false: val -> type -> Prop :=
  | is_false_int: forall sz sg,
      is_false (Vint Int.zero) (Tint sz sg)
  | is_false_pointer: forall t,
      is_false (Vint Int.zero) (Tpointer t)
 | is_false_float: forall sz,
      is_false (Vfloat Float.zero) (Tfloat sz).

Inductive is_true: val -> type -> Prop :=
  | is_true_int_int: forall n sz sg,
      n <> Int.zero ->
      is_true (Vint n) (Tint sz sg)
  | is_true_pointer_int: forall b ofs sz sg,
      is_true (Vptr b ofs) (Tint sz sg)
  | is_true_int_pointer: forall n t,
      n <> Int.zero ->
      is_true (Vint n) (Tpointer t)
  | is_true_pointer_pointer: forall b ofs t,
      is_true (Vptr b ofs) (Tpointer t)
 | is_true_float: forall f sz,
      f <> Float.zero ->
      is_true (Vfloat f) (Tfloat sz).

Inductive bool_of_val : val -> type -> val -> Prop :=
  | bool_of_val_true:   forall v ty, 
         is_true v ty -> 
         bool_of_val v ty Vtrue
  | bool_of_val_false:   forall v ty,
        is_false v ty ->
        bool_of_val v ty Vfalse.

(** The following [sem_] functions compute the result of an operator
  application.  Since operators are overloaded, the result depends
  both on the static types of the arguments and on their run-time values.
  Unlike in C, automatic conversions between integers and floats
  are not performed.  For instance, [e1 + e2] is undefined if [e1]
  is a float and [e2] an integer.  The Clight producer must have explicitly
  promoted [e2] to a float. *)

Function sem_neg (v: val) (ty: type) : option val :=
  match ty with
  | Tint _ _ =>
      match v with
      | Vint n => Some (Vint (Int.neg n))
      | _ => None
      end
  | Tfloat _ =>
      match v with
      | Vfloat f => Some (Vfloat (Float.neg f))
      | _ => None
      end
  | _ => None
  end.

Function sem_notint (v: val) : option val :=
  match v with
  | Vint n => Some (Vint (Int.xor n Int.mone))
  | _ => None
  end.

Function sem_notbool (v: val) (ty: type) : option val :=
  match ty with
  | Tint _ _ =>
      match v with
      | Vint n => Some (Val.of_bool (Int.eq n Int.zero))
      | Vptr _ _ => Some Vfalse
      | _ => None
      end
  | Tpointer _ =>
      match v with
      | Vint n => Some (Val.of_bool (Int.eq n Int.zero))
      | Vptr _ _ => Some Vfalse
      | _ => None
      end
  | Tfloat _ =>
      match v with
      | Vfloat f => Some (Val.of_bool (Float.cmp Ceq f Float.zero))
      | _ => None
      end
  | _ => None
  end.

Function sem_add (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_add t1 t2 with 
  | add_case_ii =>  
      match v1, v2 with
      | Vint n1, Vint n2 => Some (Vint (Int.add n1 n2))
      | _,  _ => None
      end
  | add_case_ff =>
      match v1, v2 with
      | Vfloat n1, Vfloat n2 => Some (Vfloat (Float.add n1 n2))
      | _,  _ => None
      end
  | add_case_pi ty=>
      match v1,v2 with
      | Vptr b1 ofs1, Vint n2 => 
	Some (Vptr b1 (Int.add ofs1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | _,  _ => None
      end   
  | add_default => None
end.

Function sem_sub (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_sub t1 t2 with
  | sub_case_ii =>               (**r integer subtraction *)
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Vint (Int.sub n1 n2))
      | _,  _ => None
      end 
  | sub_case_ff =>               (**r float subtraction *)
      match v1,v2 with
      | Vfloat f1, Vfloat f2 => Some (Vfloat(Float.sub f1 f2))
      | _,  _ => None
      end
  | sub_case_pi ty =>            (**r pointer minus integer *)
      match v1,v2 with
      | Vptr b1 ofs1, Vint n2 => 
            Some (Vptr b1 (Int.sub ofs1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | _,  _ => None
      end
  | sub_case_pp ty =>          (**r pointer minus pointer *)
      match v1,v2 with
      | Vptr b1 ofs1, Vptr b2 ofs2 =>
          if zeq b1 b2 then
            if Int.eq (Int.repr (sizeof ty)) Int.zero then None
            else Some (Vint (Int.divu (Int.sub ofs1 ofs2) (Int.repr (sizeof ty))))
          else None
      | _, _ => None
      end
  | sub_default => None
  end.
 
Function sem_mul (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
 match classify_mul t1 t2 with
  | mul_case_ii =>
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Vint (Int.mul n1 n2))
      | _,  _ => None
      end
  | mul_case_ff =>
      match v1,v2 with
      | Vfloat f1, Vfloat f2 => Some (Vfloat (Float.mul f1 f2))
      | _,  _ => None
      end
  | mul_default =>
      None
end.

Function sem_div (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
   match classify_div t1 t2 with
  | div_case_I32unsi =>
      match v1,v2 with
      | Vint n1, Vint n2 =>
          if Int.eq n2 Int.zero then None else Some (Vint (Int.divu n1 n2))
      | _,_ => None
      end
  | div_case_ii =>
      match v1,v2 with
       | Vint n1, Vint n2 =>
          if Int.eq n2 Int.zero then None else Some (Vint(Int.divs n1 n2))
      | _,_ => None
      end
  | div_case_ff =>
      match v1,v2 with
      | Vfloat f1, Vfloat f2 => Some (Vfloat(Float.div f1 f2))
      | _,  _ => None
      end 
  | div_default =>
      None
end.

Function sem_mod (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_mod t1 t2 with
  | mod_case_I32unsi =>
      match v1, v2 with
      | Vint n1, Vint n2 =>
          if Int.eq n2 Int.zero then None else Some (Vint (Int.modu n1 n2))
      | _, _ => None
      end
  | mod_case_ii =>
      match v1,v2 with
      | Vint n1, Vint n2 =>
          if Int.eq n2 Int.zero then None else Some (Vint (Int.mods n1 n2))
      | _, _ => None
      end
  | mod_default =>
      None
  end.

Function sem_and (v1 v2: val) : option val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Some (Vint(Int.and n1 n2))
  | _, _ => None
  end .

Function sem_or (v1 v2: val) : option val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Some (Vint(Int.or n1 n2))
  | _, _ => None
  end. 

Function sem_xor (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Some (Vint(Int.xor n1 n2))
  | _, _ => None
  end.

Function sem_shl (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 (Int.repr 32) then Some (Vint(Int.shl n1 n2)) else None
  | _, _ => None
  end.

Function sem_shr (v1: val) (t1: type) (v2: val) (t2: type): option val :=
  match classify_shr t1 t2 with 
  | shr_case_I32unsi => 
      match v1,v2 with 
      | Vint n1, Vint n2 =>
          if Int.ltu n2 (Int.repr 32) then Some (Vint (Int.shru n1 n2)) else None
      | _,_ => None
      end
   | shr_case_ii => 
      match v1,v2 with
      | Vint n1,  Vint n2 =>
          if Int.ltu n2 (Int.repr 32) then Some (Vint (Int.shr n1 n2)) else None
      | _,  _ => None
      end
   | shr_default=>
      None
   end.

Function sem_cmp_mismatch (c: comparison): option val :=
  match c with
  | Ceq =>  Some Vfalse
  | Cne =>  Some Vtrue
  | _   => None
  end.

Function sem_cmp (c:comparison)
                  (v1: val) (t1: type) (v2: val) (t2: type)
                  (m: mem): option val :=
  match classify_cmp t1 t2 with
  | cmp_case_I32unsi =>
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Val.of_bool (Int.cmpu c n1 n2))
      | _,  _ => None
      end
  | cmp_case_ipip =>
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Val.of_bool (Int.cmp c n1 n2))
      | Vptr b1 ofs1,  Vptr b2 ofs2  =>
          if valid_pointer m b1 (Int.signed ofs1)
          && valid_pointer m b2 (Int.signed ofs2) then
            if zeq b1 b2
            then Some (Val.of_bool (Int.cmp c ofs1 ofs2))
            else sem_cmp_mismatch c
          else None
      | Vptr b ofs, Vint n =>
          if Int.eq n Int.zero then sem_cmp_mismatch c else None
      | Vint n, Vptr b ofs =>
          if Int.eq n Int.zero then sem_cmp_mismatch c else None
      | _,  _ => None
      end
  | cmp_case_ff =>
      match v1,v2 with
      | Vfloat f1, Vfloat f2 => Some (Val.of_bool (Float.cmp c f1 f2))  
      | _,  _ => None
      end
  | cmp_default => None
  end.

Definition sem_unary_operation
            (op: unary_operation) (v: val) (ty: type): option val :=
  match op with
  | Onotbool => sem_notbool v ty
  | Onotint => sem_notint v
  | Oneg => sem_neg v ty
  end.

Definition sem_binary_operation
    (op: binary_operation)
    (v1: val) (t1: type) (v2: val) (t2:type)
    (m: mem): option val :=
  match op with
  | Oadd => sem_add v1 t1 v2 t2
  | Osub => sem_sub v1 t1 v2 t2 
  | Omul => sem_mul v1 t1 v2 t2
  | Omod => sem_mod v1 t1 v2 t2
  | Odiv => sem_div v1 t1 v2 t2 
  | Oand => sem_and v1 v2  
  | Oor  => sem_or v1 v2 
  | Oxor  => sem_xor v1 v2 
  | Oshl => sem_shl v1 v2 
  | Oshr  => sem_shr v1 t1 v2 t2   
  | Oeq => sem_cmp Ceq v1 t1 v2 t2 m
  | One => sem_cmp Cne v1 t1 v2 t2 m
  | Olt => sem_cmp Clt v1 t1 v2 t2 m
  | Ogt => sem_cmp Cgt v1 t1 v2 t2 m
  | Ole => sem_cmp Cle v1 t1 v2 t2 m
  | Oge => sem_cmp Cge v1 t1 v2 t2 m
  end.

(** Semantic of casts.  [cast v1 t1 t2 v2] holds if value [v1],
  viewed with static type [t1], can be cast to type [t2],
  resulting in value [v2].  *)

Definition cast_int_int (sz: intsize) (sg: signedness) (i: int) : int :=
  match sz, sg with
  | I8, Signed => Int.cast8signed i
  | I8, Unsigned => Int.cast8unsigned i
  | I16, Signed => Int.cast16signed i
  | I16, Unsigned => Int.cast16unsigned i 
  | I32 , _ => i
  end.

Definition cast_int_float (si : signedness) (i: int) : float :=
  match si with
  | Signed => Float.floatofint i
  | Unsigned => Float.floatofintu i
  end.

Definition cast_float_float (sz: floatsize) (f: float) : float :=
  match sz with
  | F32 => Float.singleoffloat f
  | F64 => f
  end.

Inductive neutral_for_cast: type -> Prop :=
  | nfc_int: forall sg,
      neutral_for_cast (Tint I32 sg)
  | nfc_ptr: forall ty,
      neutral_for_cast (Tpointer ty)
  | nfc_array: forall ty sz,
      neutral_for_cast (Tarray ty sz)
  | nfc_fun: forall targs tres,
      neutral_for_cast (Tfunction targs tres).

Inductive cast : val -> type -> type -> val -> Prop :=
  | cast_ii:   forall i sz2 sz1 si1 si2,
      cast (Vint i) (Tint sz1 si1) (Tint sz2 si2)
           (Vint (cast_int_int sz2 si2 i))
  | cast_fi:   forall f sz1 sz2 si2,
      cast (Vfloat f) (Tfloat sz1) (Tint sz2 si2)
           (Vint (cast_int_int sz2 si2 (Float.intoffloat f)))
  | cast_if:   forall i sz1 sz2 si1,
      cast (Vint i) (Tint sz1 si1) (Tfloat sz2)
          (Vfloat (cast_float_float sz2 (cast_int_float si1 i)))
  | cast_ff:   forall f sz1 sz2,
      cast (Vfloat f) (Tfloat sz1) (Tfloat sz2)
           (Vfloat (cast_float_float sz2 f))
  | cast_nn_p: forall b ofs t1 t2,
      neutral_for_cast t1 -> neutral_for_cast t2 ->
      cast (Vptr b ofs) t1 t2 (Vptr b ofs)
  | cast_nn_i: forall n t1 t2,
      neutral_for_cast t1 -> neutral_for_cast t2 ->
      cast (Vint n) t1 t2 (Vint n).

(** * Operational semantics *)

(** The semantics uses two environments.  The global environment
  maps names of functions and global variables to memory block references,
  and function pointers to their definitions.  (See module [Globalenvs].) *)

Definition genv := Genv.t fundef.

(** The local environment maps local variables to block references.
  The current value of the variable is stored in the associated memory
  block. *)

Definition env := PTree.t block. (* map variable -> location *)

Definition empty_env: env := (PTree.empty block).

(** The execution of a statement produces an ``outcome'', indicating
  how the execution terminated: either normally or prematurely
  through the execution of a [break], [continue] or [return] statement. *)

Inductive outcome: Set :=
   | Out_break: outcome                 (**r terminated by [break] *)
   | Out_continue: outcome              (**r terminated by [continue] *)
   | Out_normal: outcome                (**r terminated normally *)
   | Out_return: option val -> outcome. (**r terminated by [return] *)

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
  | Out_return (Some v'), ty => ty <> Tvoid /\ v'=v
  | _, _ => False
  end. 

(** Selection of the appropriate case of a [switch], given the value [n]
  of the selector expression. *)

Fixpoint select_switch (n: int) (sl: labeled_statements)
                       {struct sl}: labeled_statements :=
  match sl with
  | LSdefault _ => sl
  | LScase c s sl' => if Int.eq c n then sl else select_switch n sl'
  end.

(** [load_value_of_type ty m b ofs] computes the value of a datum
  of type [ty] residing in memory [m] at block [b], offset [ofs].
  If the type [ty] indicates an access by value, the corresponding
  memory load is performed.  If the type [ty] indicates an access by
  reference, the pointer [Vptr b ofs] is returned. *)

Definition load_value_of_type (ty: type) (m: mem) (b: block) (ofs: int) : option val :=
  match access_mode ty with
  | By_value chunk => Mem.loadv chunk m (Vptr b ofs)
  | By_reference => Some (Vptr b ofs)
  | By_nothing => None
  end.

(** Symmetrically, [store_value_of_type ty m b ofs v] returns the
  memory state after storing the value [v] in the datum
  of type [ty] residing in memory [m] at block [b], offset [ofs].
  This is allowed only if [ty] indicates an access by value. *)

Definition store_value_of_type (ty_dest: type) (m: mem) (loc: block) (ofs: int) (v: val) : option mem :=
  match access_mode ty_dest with
  | By_value chunk => Mem.storev chunk m (Vptr loc ofs) v
  | By_reference => None
  | By_nothing => None
  end.

(** Allocation of function-local variables.
  [alloc_variables e1 m1 vars e2 m2 bl] allocates one memory block
  for each variable declared in [vars], and associates the variable
  name with this block.  [e1] and [m1] are the initial local environment
  and memory state.  [e2] and [m2] are the final local environment
  and memory state.  The list [bl] collects the references to all
  the blocks that were allocated. *)

Inductive alloc_variables: env -> mem ->
                           list (ident * type) ->
                           env -> mem -> list block -> Prop :=
  | alloc_variables_nil:
      forall e m,
      alloc_variables e m nil e m nil
  | alloc_variables_cons:
      forall e m id ty vars m1 b1 m2 e2 lb,
      Mem.alloc m 0 (sizeof ty) = (m1, b1) ->
      alloc_variables (PTree.set id b1 e) m1 vars e2 m2 lb ->
      alloc_variables e m ((id, ty) :: vars) e2 m2 (b1 :: lb).

(** Initialization of local variables that are parameters to a function.
  [bind_parameters e m1 params args m2] stores the values [args]
  in the memory blocks corresponding to the variables [params].
  [m1] is the initial memory state and [m2] the final memory state. *)

Inductive bind_parameters: env ->
                           mem -> list (ident * type) -> list val ->
                           mem -> Prop :=
  | bind_parameters_nil:
      forall e m,
      bind_parameters e m nil nil m
  | bind_parameters_cons:
      forall e m id ty params v1 vl b m1 m2,
      PTree.get id e = Some b ->
      store_value_of_type ty m b Int.zero v1 = Some m1 ->
      bind_parameters e m1 params vl m2 ->
      bind_parameters e m ((id, ty) :: params) (v1 :: vl) m2.

Section RELSEM.

Variable ge: genv.

Section EXPR.

Variable e: env.
Variable m: mem.

(** [eval_expr ge e m a v] defines the evaluation of expression [a]
  in r-value position.  [v] is the value of the expression.
  [e] is the current environment and [m] is the current memory state. *)

Inductive eval_expr: expr -> val -> Prop :=
  | eval_Econst_int:   forall i ty,
      eval_expr (Expr (Econst_int i) ty) (Vint i)
  | eval_Econst_float:   forall f ty,
      eval_expr (Expr (Econst_float f) ty) (Vfloat f)
  | eval_Elvalue: forall a ty loc ofs v,
      eval_lvalue (Expr a ty) loc ofs ->
      load_value_of_type ty m loc ofs = Some v ->
      eval_expr (Expr a ty) v
  | eval_Eaddrof: forall a ty loc ofs,
      eval_lvalue a loc ofs ->
      eval_expr (Expr (Eaddrof a) ty) (Vptr loc ofs)
  | eval_Esizeof: forall ty' ty,
      eval_expr (Expr (Esizeof ty') ty) (Vint (Int.repr (sizeof ty')))
  | eval_Eunop:  forall op a ty v1 v,
      eval_expr a v1 ->
      sem_unary_operation op v1 (typeof a) = Some v ->
      eval_expr (Expr (Eunop op a) ty) v
  | eval_Ebinop: forall op a1 a2 ty v1 v2 v,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      sem_binary_operation op v1 (typeof a1) v2 (typeof a2) m = Some v ->
      eval_expr (Expr (Ebinop op a1 a2) ty) v
  | eval_Eorbool_1: forall a1 a2 ty v1,
      eval_expr a1 v1 ->
      is_true v1 (typeof a1) ->
      eval_expr (Expr (Eorbool a1 a2) ty) Vtrue
  | eval_Eorbool_2: forall a1 a2 ty v1 v2 v,
      eval_expr a1 v1 ->
      is_false v1 (typeof a1) -> 
      eval_expr a2 v2 ->
      bool_of_val v2 (typeof a2) v ->
      eval_expr (Expr (Eorbool a1 a2) ty) v
  | eval_Eandbool_1: forall a1 a2 ty v1,
      eval_expr a1 v1 ->
      is_false v1 (typeof a1) ->
      eval_expr (Expr (Eandbool a1 a2) ty) Vfalse
  | eval_Eandbool_2: forall a1 a2 ty v1 v2 v,
      eval_expr a1 v1 ->
      is_true v1 (typeof a1) -> 
      eval_expr a2 v2 ->
      bool_of_val v2 (typeof a2) v ->
      eval_expr (Expr (Eandbool a1 a2) ty) v
  | eval_Ecast:   forall a ty ty' v1 v,
      eval_expr a v1 ->
      cast v1 (typeof a) ty v ->
      eval_expr (Expr (Ecast ty a) ty') v

(** [eval_lvalue ge e m a b ofs] defines the evaluation of expression [a]
  in l-value position.  The result is the memory location [b, ofs]
  that contains the value of the expression [a]. *)

with eval_lvalue: expr -> block -> int -> Prop :=
  | eval_Evar_local:   forall id l ty,
      e!id = Some l ->
      eval_lvalue (Expr (Evar id) ty) l Int.zero
  | eval_Evar_global: forall id l ty,
      e!id = None ->
      Genv.find_symbol ge id = Some l ->
      eval_lvalue (Expr (Evar id) ty) l Int.zero
  | eval_Ederef: forall a ty l ofs,
      eval_expr a (Vptr l ofs) ->
      eval_lvalue (Expr (Ederef a) ty) l ofs
  | eval_Eindex: forall a1 a2 ty v1 v2 l ofs,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      sem_add v1 (typeof a1) v2 (typeof a2) = Some (Vptr l ofs) ->
      eval_lvalue (Expr (Eindex a1 a2) ty) l ofs
 | eval_Efield_struct:   forall a i ty l ofs id fList delta,
      eval_lvalue a l ofs ->
      typeof a = Tstruct id fList ->
      field_offset i fList = OK delta ->
      eval_lvalue (Expr (Efield a i) ty) l (Int.add ofs (Int.repr delta))
 | eval_Efield_union:   forall a i ty l ofs id fList,
      eval_lvalue a l ofs ->
      typeof a = Tunion id fList ->
      eval_lvalue (Expr (Efield a i) ty) l ofs.

Scheme eval_expr_ind2 := Minimality for eval_expr Sort Prop
  with eval_lvalue_ind2 := Minimality for eval_lvalue Sort Prop.

(** [eval_exprlist ge e m al vl] evaluates a list of r-value
  expressions [al] to their values [vl]. *)

Inductive eval_exprlist: list expr -> list val -> Prop :=
  | eval_Enil:
      eval_exprlist nil nil
  | eval_Econs:   forall a bl v vl,
      eval_expr a v ->
      eval_exprlist bl vl ->
      eval_exprlist (a :: bl) (v :: vl).

End EXPR.

(** [exec_stmt ge e m1 s t m2 out] describes the execution of 
  the statement [s].  [out] is the outcome for this execution.
  [m1] is the initial memory state, [m2] the final memory state.
  [t] is the trace of input/output events performed during this
  evaluation. *)

Inductive exec_stmt: env -> mem -> statement -> trace -> mem -> outcome -> Prop :=
  | exec_Sskip:   forall e m,
      exec_stmt e m Sskip
               E0 m Out_normal
  | exec_Sassign:   forall e m a1 a2 loc ofs v2 m',
      eval_lvalue e m a1 loc ofs ->
      eval_expr e m a2 v2 ->
      store_value_of_type (typeof a1) m loc ofs v2 = Some m' ->
      exec_stmt e m (Sassign a1 a2)
               E0 m' Out_normal
  | exec_Scall_none:   forall e m a al vf vargs f t m' vres,
      eval_expr e m a vf ->
      eval_exprlist e m al vargs ->
      Genv.find_funct ge vf = Some f ->
      type_of_fundef f = typeof a ->
      eval_funcall m f vargs t m' vres ->
      exec_stmt e m (Scall None a al)
                t m' Out_normal
  | exec_Scall_some:   forall e m lhs a al loc ofs vf vargs f t m' vres m'',
      eval_lvalue e m lhs loc ofs ->
      eval_expr e m a vf ->
      eval_exprlist e m al vargs ->
      Genv.find_funct ge vf = Some f ->
      type_of_fundef f = typeof a ->
      eval_funcall m f vargs t m' vres ->
      store_value_of_type (typeof lhs) m' loc ofs vres = Some m'' ->
      exec_stmt e m (Scall (Some lhs) a al)
                t m'' Out_normal
  | exec_Sseq_1:   forall e m s1 s2 t1 m1 t2 m2 out,
      exec_stmt e m s1 t1 m1 Out_normal ->
      exec_stmt e m1 s2 t2 m2 out ->
      exec_stmt e m (Ssequence s1 s2)
                (t1 ** t2) m2 out
  | exec_Sseq_2:   forall e m s1 s2 t1 m1 out,
      exec_stmt e m s1 t1 m1 out ->
      out <> Out_normal ->
      exec_stmt e m (Ssequence s1 s2)
                t1 m1 out
  | exec_Sifthenelse_true: forall e m a s1 s2 v1 t m' out,
      eval_expr e m a v1 ->
      is_true v1 (typeof a) ->
      exec_stmt e m s1 t m' out ->
      exec_stmt e m (Sifthenelse a s1 s2)
                t m' out
  | exec_Sifthenelse_false: forall e m a s1 s2 v1 t m' out,
      eval_expr e m a v1 ->
      is_false v1 (typeof a) ->
      exec_stmt e m s2 t m' out ->
      exec_stmt e m (Sifthenelse a s1 s2)
                t m' out
  | exec_Sreturn_none:   forall e m,
      exec_stmt e m (Sreturn None)
               E0 m (Out_return None)
  | exec_Sreturn_some: forall e m a v,
      eval_expr e m a v ->
      exec_stmt e m (Sreturn (Some a))
               E0 m (Out_return (Some v))
  | exec_Sbreak:   forall e m,
      exec_stmt e m Sbreak
               E0 m Out_break
  | exec_Scontinue:   forall e m,
      exec_stmt e m Scontinue
               E0 m Out_continue
  | exec_Swhile_false: forall e m a s v,
      eval_expr e m a v ->
      is_false v (typeof a) ->
      exec_stmt e m (Swhile a s)
               E0 m Out_normal
  | exec_Swhile_stop: forall e m a v s t m' out' out,
      eval_expr e m a v ->
      is_true v (typeof a) ->
      exec_stmt e m s t m' out' ->
      out_break_or_return out' out ->
      exec_stmt e m (Swhile a s)
                t m' out
  | exec_Swhile_loop: forall e m a s v t1 m1 out1 t2 m2 out,
      eval_expr e m a v ->
      is_true v (typeof a) ->
      exec_stmt e m s t1 m1 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e m1 (Swhile a s) t2 m2 out ->
      exec_stmt e m (Swhile a s)
                (t1 ** t2) m2 out
  | exec_Sdowhile_false: forall e m s a t m1 out1 v,
      exec_stmt e m s t m1 out1 ->
      out_normal_or_continue out1 ->
      eval_expr e m1 a v ->
      is_false v (typeof a) ->
      exec_stmt e m (Sdowhile a s)
                t m1 Out_normal
  | exec_Sdowhile_stop: forall e m s a t m1 out1 out,
      exec_stmt e m s t m1 out1 ->
      out_break_or_return out1 out ->
      exec_stmt e m (Sdowhile a s)
                t m1 out
  | exec_Sdowhile_loop: forall e m s a m1 m2 t1 t2 out out1 v,
      exec_stmt e m s t1 m1 out1 ->
      out_normal_or_continue out1 ->
      eval_expr e m1 a v ->
      is_true v (typeof a) ->
      exec_stmt e m1 (Sdowhile a s) t2 m2 out ->
      exec_stmt e m (Sdowhile a s) 
                (t1 ** t2) m2 out
  | exec_Sfor_start: forall e m s a1 a2 a3 out m1 m2 t1 t2,
      a1 <> Sskip ->
      exec_stmt e m a1 t1 m1 Out_normal ->
      exec_stmt e m1 (Sfor Sskip a2 a3 s) t2 m2 out ->
      exec_stmt e m (Sfor a1 a2 a3 s) 
                (t1 ** t2) m2 out
  | exec_Sfor_false: forall e m s a2 a3 v,
      eval_expr e m a2 v ->
      is_false v (typeof a2) ->
      exec_stmt e m (Sfor Sskip a2 a3 s)
               E0 m Out_normal
  | exec_Sfor_stop: forall e m s a2 a3 v m1 t out1 out,
      eval_expr e m a2 v ->
      is_true v (typeof a2) ->
      exec_stmt e m s t m1 out1 ->
      out_break_or_return out1 out ->
      exec_stmt e m (Sfor Sskip a2 a3 s)
                t m1 out
  | exec_Sfor_loop: forall e m s a2 a3 v m1 m2 m3 t1 t2 t3 out1 out,
      eval_expr e m a2 v ->
      is_true v (typeof a2) ->
      exec_stmt e m s t1 m1 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e m1 a3 t2 m2 Out_normal ->
      exec_stmt e m2 (Sfor Sskip a2 a3 s) t3 m3 out ->
      exec_stmt e m (Sfor Sskip a2 a3 s)
                (t1 ** t2 ** t3) m3 out
  | exec_Sswitch:   forall e m a t n sl m1 out,
      eval_expr e m a (Vint n) ->
      exec_lblstmts e m (select_switch n sl) t m1 out ->
      exec_stmt e m (Sswitch a sl)
                t m1 (outcome_switch out)

(** [exec_lblstmts ge e m1 ls t m2 out] is a variant of [exec_stmt]
  that executes in sequence all statements in the list of labeled
  statements [ls]. *)

with exec_lblstmts: env -> mem -> labeled_statements -> trace -> mem -> outcome -> Prop :=
  | exec_LSdefault: forall e m s t m1 out,
     exec_stmt e m s t m1 out ->
     exec_lblstmts e m (LSdefault s) t m1 out
  | exec_LScase_fallthrough: forall e m n s ls t1 m1 t2 m2 out,
     exec_stmt e m s t1 m1 Out_normal ->
     exec_lblstmts e m1 ls t2 m2 out ->
     exec_lblstmts e m (LScase n s ls) (t1 ** t2) m2 out
  | exec_LScase_stop: forall e m n s ls t m1 out,
     exec_stmt e m s t m1 out -> out <> Out_normal ->
     exec_lblstmts e m (LScase n s ls) t m1 out

(** [eval_funcall m1 fd args t m2 res] describes the invocation of
  function [fd] with arguments [args].  [res] is the value returned
  by the call.  *)

with eval_funcall: mem -> fundef -> list val -> trace -> mem -> val -> Prop :=
  | eval_funcall_internal: forall m f vargs t e m1 lb m2 m3 out vres,
      alloc_variables empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 lb ->
      bind_parameters e m1 f.(fn_params) vargs m2 ->
      exec_stmt e m2 f.(fn_body) t m3 out ->
      outcome_result_value out f.(fn_return) vres ->
      eval_funcall m (Internal f) vargs t (Mem.free_list m3 lb) vres
  | eval_funcall_external: forall m id targs tres vargs t vres,
      event_match (external_function id targs tres) vargs t vres ->
      eval_funcall m (External id targs tres) vargs t m vres.

Scheme exec_stmt_ind3 := Minimality for exec_stmt Sort Prop
  with exec_lblstmts_ind3 := Minimality for exec_lblstmts Sort Prop
  with eval_funcall_ind3 := Minimality for eval_funcall Sort Prop.

(** Coinductive semantics for divergence.
  [execinf_stmt ge e m s t] holds if the execution of statement [s]
  diverges, i.e. loops infinitely.  [t] is the possibly infinite
  trace of observable events performed during the execution. *)

CoInductive execinf_stmt: env -> mem -> statement -> traceinf -> Prop :=
  | execinf_Scall:   forall e m lhs a al vf vargs f t,
      eval_expr e m a vf ->
      eval_exprlist e m al vargs ->
      Genv.find_funct ge vf = Some f ->
      type_of_fundef f = typeof a ->
      evalinf_funcall m f vargs t ->
      execinf_stmt e m (Scall lhs a al) t
  | execinf_Sseq_1:   forall e m s1 s2 t,
      execinf_stmt e m s1 t ->
      execinf_stmt e m (Ssequence s1 s2) t
  | execinf_Sseq_2:   forall e m s1 s2 t1 m1 t2,
      exec_stmt e m s1 t1 m1 Out_normal ->
      execinf_stmt e m1 s2 t2 ->
      execinf_stmt e m (Ssequence s1 s2) (t1 *** t2)
  | execinf_Sifthenelse_true: forall e m a s1 s2 v1 t,
      eval_expr e m a v1 ->
      is_true v1 (typeof a) ->
      execinf_stmt e m s1 t ->
      execinf_stmt e m (Sifthenelse a s1 s2) t
  | execinf_Sifthenelse_false: forall e m a s1 s2 v1 t,
      eval_expr e m a v1 ->
      is_false v1 (typeof a) ->
      execinf_stmt e m s2 t ->
      execinf_stmt e m (Sifthenelse a s1 s2) t
  | execinf_Swhile_body: forall e m a v s t,
      eval_expr e m a v ->
      is_true v (typeof a) ->
      execinf_stmt e m s t ->
      execinf_stmt e m (Swhile a s) t
  | execinf_Swhile_loop: forall e m a s v t1 m1 out1 t2,
      eval_expr e m a v ->
      is_true v (typeof a) ->
      exec_stmt e m s t1 m1 out1 ->
      out_normal_or_continue out1 ->
      execinf_stmt e m1 (Swhile a s) t2 ->
      execinf_stmt e m (Swhile a s) (t1 *** t2)
  | execinf_Sdowhile_body: forall e m s a t,
      execinf_stmt e m s t ->
      execinf_stmt e m (Sdowhile a s) t
  | execinf_Sdowhile_loop: forall e m s a m1 t1 t2 out1 v,
      exec_stmt e m s t1 m1 out1 ->
      out_normal_or_continue out1 ->
      eval_expr e m1 a v ->
      is_true v (typeof a) ->
      execinf_stmt e m1 (Sdowhile a s) t2 ->
      execinf_stmt e m (Sdowhile a s) (t1 *** t2)
  | execinf_Sfor_start_1: forall e m s a1 a2 a3 t,
      execinf_stmt e m a1 t ->
      execinf_stmt e m (Sfor a1 a2 a3 s) t
  | execinf_Sfor_start_2: forall e m s a1 a2 a3 m1 t1 t2,
      a1 <> Sskip ->
      exec_stmt e m a1 t1 m1 Out_normal ->
      execinf_stmt e m1 (Sfor Sskip a2 a3 s) t2 ->
      execinf_stmt e m (Sfor a1 a2 a3 s) (t1 *** t2)
  | execinf_Sfor_body: forall e m s a2 a3 v t,
      eval_expr e m a2 v ->
      is_true v (typeof a2) ->
      execinf_stmt e m s t ->
      execinf_stmt e m (Sfor Sskip a2 a3 s) t
  | execinf_Sfor_next: forall e m s a2 a3 v m1 t1 t2 out1,
      eval_expr e m a2 v ->
      is_true v (typeof a2) ->
      exec_stmt e m s t1 m1 out1 ->
      out_normal_or_continue out1 ->
      execinf_stmt e m1 a3 t2 ->
      execinf_stmt e m (Sfor Sskip a2 a3 s) (t1 *** t2)
  | execinf_Sfor_loop: forall e m s a2 a3 v m1 m2 t1 t2 t3 out1,
      eval_expr e m a2 v ->
      is_true v (typeof a2) ->
      exec_stmt e m s t1 m1 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e m1 a3 t2 m2 Out_normal ->
      execinf_stmt e m2 (Sfor Sskip a2 a3 s) t3 ->
      execinf_stmt e m (Sfor Sskip a2 a3 s) (t1 *** t2 *** t3)
  | execinf_Sswitch:   forall e m a t n sl,
      eval_expr e m a (Vint n) ->
      execinf_lblstmts e m (select_switch n sl) t ->
      execinf_stmt e m (Sswitch a sl) t

with execinf_lblstmts: env -> mem -> labeled_statements -> traceinf -> Prop :=
  | execinf_LSdefault: forall e m s t,
     execinf_stmt e m s t ->
     execinf_lblstmts e m (LSdefault s) t
  | execinf_LScase_body: forall e m n s ls t,
     execinf_stmt e m s t ->
     execinf_lblstmts e m (LScase n s ls) t
  | execinf_LScase_fallthrough: forall e m n s ls t1 m1 t2,
     exec_stmt e m s t1 m1 Out_normal ->
     execinf_lblstmts e m1 ls t2 ->
     execinf_lblstmts e m (LScase n s ls) (t1 *** t2)

(** [evalinf_funcall ge m fd args t] holds if the invocation of function
    [fd] on arguments [args] diverges, with observable trace [t]. *)

with evalinf_funcall: mem -> fundef -> list val -> traceinf -> Prop :=
  | evalinf_funcall_internal: forall m f vargs t e m1 lb m2,
      alloc_variables empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 lb ->
      bind_parameters e m1 f.(fn_params) vargs m2 ->
      execinf_stmt e m2 f.(fn_body) t ->
      evalinf_funcall m (Internal f) vargs t.

End RELSEM.

(** Execution of a whole program.  [exec_program p beh] holds
  if the application of [p]'s main function to no arguments
  in the initial memory state for [p] executes without errors and produces
  the observable behaviour [beh]. *)

Inductive exec_program (p: program): program_behavior -> Prop :=
  | program_terminates: forall b f m1 t r,
      let ge := Genv.globalenv p in 
      let m0 := Genv.init_mem p in
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      eval_funcall ge m0 f nil t m1 (Vint r) ->
      exec_program p (Terminates t r)
  | program_diverges: forall b f t,
      let ge := Genv.globalenv p in 
      let m0 := Genv.init_mem p in
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      evalinf_funcall ge m0 f nil t ->
      exec_program p (Diverges t).

