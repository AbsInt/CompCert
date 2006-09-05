(** * Dynamic semantics for the Clight language *)

Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Csyntax.

(** ** Semantics of type-dependent operations *)

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
  | sub_case_ii =>               (* integer subtraction *)
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Vint (Int.sub n1 n2))
      | _,  _ => None
      end 
  | sub_case_ff =>               (* float subtraction *)
      match v1,v2 with
      | Vfloat f1, Vfloat f2 => Some (Vfloat(Float.sub f1 f2))
      | _,  _ => None
      end
  | sub_case_pi ty =>            (*array| pointer - offset *)
      match v1,v2 with
      | Vptr b1 ofs1, Vint n2 => 
            Some (Vptr b1 (Int.sub ofs1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | _,  _ => None
      end
  | sub_case_pp ty =>          (* array|pointer - array|pointer *)
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
      | Vint n1, Vint n2 =>Some (Val.of_bool (Int.cmpu c n1 n2))
      | _,  _ => None
      end
  | cmp_case_ii =>
      match v1,v2 with
      | Vint n1, Vint n2 =>Some (Val.of_bool (Int.cmp c n1 n2))
      | _,  _ => None
      end
  | cmp_case_ff =>
      match v1,v2 with
      | Vfloat f1, Vfloat f2 =>Some (Val.of_bool (Float.cmp c f1 f2))  
      | _,  _ => None
      end
  | cmp_case_pi =>
      match v1,v2 with
      | Vptr b ofs, Vint n2 =>
          if Int.eq n2 Int.zero then sem_cmp_mismatch c else None
      | _,  _ => None
      end
  | cmp_case_pp =>
      match v1,v2 with
      | Vptr b1 ofs1,  Vptr b2 ofs2  =>
          if valid_pointer m b1 (Int.signed ofs1) && valid_pointer m b2 (Int.signed ofs2) then
            if zeq b1 b2
            then Some (Val.of_bool (Int.cmp c ofs1 ofs2))
            else None
          else None
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
  | cast_ip_p:   forall b ofs t1 si2,
      cast (Vptr b ofs) (Tint I32 si2) (Tpointer t1) (Vptr b ofs)
  | cast_pi_p:   forall b ofs t1 si2,
      cast (Vptr b ofs) (Tpointer t1) (Tint I32 si2) (Vptr b ofs)
  | cast_pp_p:    forall b ofs t1 t2,
      cast (Vptr b ofs) (Tpointer t1) (Tpointer t2) (Vptr b ofs)
  | cast_ip_i:   forall n t1 si2,
      cast (Vint n) (Tint I32 si2) (Tpointer t1) (Vint n)
  | cast_pi_i:   forall n t1 si2,
      cast (Vint n) (Tpointer t1) (Tint I32 si2) (Vint n)
  | cast_pp_i:    forall n t1 t2,
      cast (Vint n) (Tpointer t1) (Tpointer t2) (Vint n).

(** ** Operational semantics *)

(** Global environment *)

Definition genv := Genv.t fundef.

(** Local environment *)

Definition env := PTree.t block. (* map variable -> location *)

Definition empty_env: env := (PTree.empty block).

(** Outcomes for statements *)

Inductive outcome: Set :=
   | Out_break: outcome
   | Out_continue: outcome
   | Out_normal: outcome
   | Out_return: option val -> outcome.

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

(** Selection of the appropriate case of a [switch] *)

Fixpoint select_switch (n: int) (sl: labeled_statements)
                       {struct sl}: labeled_statements :=
  match sl with
  | LSdefault _ => sl
  | LScase c s sl' => if Int.eq c n then sl else select_switch n sl'
  end.

(** Loads and stores by type *)

Definition load_value_of_type (ty: type) (m: mem) (b: block) (ofs: int) : option val :=
  match access_mode ty with
  | By_value chunk => Mem.loadv chunk m (Vptr b ofs)
  | By_reference => Some (Vptr b ofs)
  | By_nothing => None
  end.

Definition store_value_of_type (ty_dest: type) (m: mem) (loc: block) (ofs: int) (v: val) : option mem :=
  match access_mode ty_dest with
  | By_value chunk => Mem.storev chunk m (Vptr loc ofs) v
  | By_reference => None
  | By_nothing => None
  end.

(** Allocation and initialization of function-local variables *)

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

(** Evaluation of an expression in r-value position *)

Inductive eval_expr: env -> mem -> expr -> trace -> mem -> val -> Prop :=
  | eval_Econst_int:   forall e m i ty,
      eval_expr e m (Expr (Econst_int i) ty)
               E0 m (Vint i)
  | eval_Econst_float:   forall e m f ty,
      eval_expr e m (Expr (Econst_float f) ty)
               E0 m (Vfloat f)
  | eval_Elvalue: forall e m a ty t m1 loc ofs v,
      eval_lvalue e m (Expr a ty) t m1 loc ofs ->
      load_value_of_type ty m1 loc ofs = Some v ->
      eval_expr e m (Expr a ty) 
                t m1 v
  | eval_Eaddrof: forall e m a t m1 loc ofs ty,
      eval_lvalue e m a t m1 loc ofs ->
      eval_expr e m (Expr (Eaddrof a) ty)
                t m1 (Vptr loc ofs)
  | eval_Esizeof: forall e m ty' ty,
      eval_expr e m (Expr (Esizeof ty') ty) 
               E0 m (Vint (Int.repr (sizeof ty')))
  | eval_Eunop:  forall e m op a ty t m1 v1 v,
      eval_expr e m a t m1 v1 ->
      sem_unary_operation op v1 (typeof a) = Some v ->
      eval_expr e m (Expr (Eunop op a) ty) 
                t m1 v
  | eval_Ebinop: forall e m op a1 a2 ty t1 m1 v1 t2 m2 v2 v,
      eval_expr e m a1 t1 m1 v1 ->
      eval_expr e m1 a2 t2 m2 v2 ->
      sem_binary_operation op v1 (typeof a1) v2 (typeof a2) m2 = Some v ->
      eval_expr e m (Expr (Ebinop op a1 a2) ty)
                (t1 ** t2) m2 v
  | eval_Eorbool_1: forall e m a1 a2 t m1 v1 ty,
      eval_expr e m a1 t m1 v1 ->
      is_true v1 (typeof a1) ->
      eval_expr e m (Expr (Eorbool a1 a2) ty)
                  t m1 Vtrue
  | eval_Eorbool_2: forall e m a1 a2 ty t1 m1 v1 t2 m2 v2 v,
      eval_expr e m a1 t1 m1 v1 ->
      is_false v1 (typeof a1) -> 
      eval_expr e m1 a2 t2 m2 v2 ->
      bool_of_val v2 (typeof a2) v ->
      eval_expr e m (Expr (Eorbool a1 a2) ty)
                (t1 ** t2) m2 v
  | eval_Eandbool_1: forall e m a1 a2 t m1 v1 ty,
      eval_expr e m a1 t m1 v1 ->
      is_false v1 (typeof a1) ->
      eval_expr e m (Expr (Eandbool a1 a2) ty)
                  t m1 Vfalse
  | eval_Eandbool_2: forall e m a1 a2 ty t1 m1 v1 t2 m2 v2 v,
      eval_expr e m a1 t1 m1 v1 ->
      is_true v1 (typeof a1) -> 
      eval_expr e m1 a2 t2 m2 v2 ->
      bool_of_val v2 (typeof a2) v ->
      eval_expr e m (Expr (Eandbool a1 a2) ty)
                (t1 ** t2) m2 v
  | eval_Ecast:   forall e m a ty t m1 v1 v,
      eval_expr e m a t m1 v1 ->
      cast v1 (typeof a) ty v ->
      eval_expr e m (Expr (Ecast ty a) ty)
                t m1 v
  | eval_Ecall: forall e m a bl ty m3 vres t1 m1 vf t2 m2 vargs f t3,
      eval_expr e m a t1 m1 vf ->
      eval_exprlist e m1 bl t2 m2 vargs ->
      Genv.find_funct ge vf = Some f ->
      type_of_fundef f = typeof a ->
      eval_funcall m2 f vargs t3 m3 vres ->
      eval_expr e m (Expr (Ecall a bl) ty)
                (t1 ** t2 ** t3) m3 vres 

(** Evaluation of an expression in l-value position *)

with eval_lvalue: env -> mem -> expr -> trace -> mem -> block -> int -> Prop :=
  | eval_Evar_local:   forall e m id l ty,
      e!id = Some l ->
      eval_lvalue e m (Expr (Evar id) ty) 
                 E0 m l Int.zero
  | eval_Evar_global: forall e m id l ty,
      e!id = None ->
      Genv.find_symbol ge id = Some l ->
      eval_lvalue e m (Expr (Evar id) ty)
                 E0 m l Int.zero
  | eval_Ederef: forall e m m1 a t ofs ty l,
      eval_expr e m a t m1 (Vptr l ofs) ->
      eval_lvalue e m (Expr (Ederef a) ty)
                  t m1 l ofs
  | eval_Eindex: forall e m a1 t1 m1 v1 a2 t2 m2 v2 l ofs ty,
      eval_expr e m a1 t1 m1 v1 ->
      eval_expr e m1 a2 t2 m2 v2 ->
      sem_add v1 (typeof a1) v2 (typeof a2) = Some (Vptr l ofs) ->
      eval_lvalue e m (Expr (Eindex a1 a2) ty)
                  (t1 ** t2) m2 l ofs
 | eval_Efield_struct:   forall e m a t m1 l ofs fList i ty delta,
      eval_lvalue e m a t m1 l ofs ->
      typeof a = Tstruct fList ->
      field_offset i fList = Some delta ->
      eval_lvalue e m (Expr (Efield a i) ty)
                  t m1 l (Int.add ofs (Int.repr delta))
 | eval_Efield_union:   forall e m a t m1 l ofs fList i ty,
      eval_lvalue e m a t m1 l ofs ->
      typeof a = Tunion fList ->
      eval_lvalue e m (Expr (Efield a i) ty) 
                  t m1 l ofs

(** Evaluation of a list of expressions *)

with eval_exprlist: env -> mem -> exprlist -> trace -> mem -> list val -> Prop :=
  | eval_Enil:   forall e m,
      eval_exprlist e m Enil E0 m nil
  | eval_Econs:   forall e m a bl t1 m1 v t2 m2 vl,
      eval_expr e m a t1 m1 v ->
      eval_exprlist e m1 bl t2 m2 vl ->
      eval_exprlist e m (Econs a bl)
                    (t1 ** t2) m2 (v :: vl)

(** Execution of a statement *)

with exec_stmt: env -> mem -> statement -> trace -> mem -> outcome -> Prop :=
  | exec_Sskip:   forall e m,
      exec_stmt e m Sskip
               E0 m Out_normal
  | exec_Sexpr: forall e m a t m1 v,
      eval_expr e m a t m1 v ->
      exec_stmt e m (Sexpr a)
                t m1 Out_normal 
  | exec_Sassign:   forall e m a1 a2 t1 m1 loc ofs t2 m2 v2 m3,
      eval_lvalue e m a1 t1 m1 loc ofs ->
      eval_expr e m1 a2 t2 m2 v2 ->
      store_value_of_type (typeof a1) m2 loc ofs v2 = Some m3 ->
      exec_stmt e m (Sassign a1 a2)
                (t1 ** t2) m3 Out_normal
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
  | exec_Sifthenelse_true: forall e m a s1 s2 t1 m1 v1 t2 m2 out,
      eval_expr e m a t1 m1 v1 ->
      is_true v1 (typeof a) ->
      exec_stmt e m1 s1 t2 m2 out ->
      exec_stmt e m (Sifthenelse a s1 s2)
                (t1 ** t2) m2 out
  | exec_Sifthenelse_false: forall e m a s1 s2 t1 m1 v1 t2 m2 out,
      eval_expr e m a t1 m1 v1 ->
      is_false v1 (typeof a) ->
      exec_stmt e m1 s2 t2 m2 out ->
      exec_stmt e m (Sifthenelse a s1 s2)
                (t1 ** t2) m2 out
  | exec_Sreturn_none:   forall e m,
      exec_stmt e m (Sreturn None)
               E0 m (Out_return None)
  | exec_Sreturn_some: forall e m a t m1 v,
      eval_expr e m a t m1 v ->
      exec_stmt e m (Sreturn (Some a))
                t m1 (Out_return (Some v))
  | exec_Sbreak:   forall e m,
      exec_stmt e m Sbreak
               E0 m Out_break
  | exec_Scontinue:   forall e m,
      exec_stmt e m Scontinue
               E0 m Out_continue
  | exec_Swhile_false: forall e m s a t v m1,
      eval_expr e m a t m1 v ->
      is_false v (typeof a) ->
      exec_stmt e m (Swhile a s)
                t m1 Out_normal
  | exec_Swhile_stop: forall e m a t1 m1 v s m2 t2 out2 out,
      eval_expr e m a t1 m1 v ->
      is_true v (typeof a) ->
      exec_stmt e m1 s t2 m2 out2 ->
      out_break_or_return out2 out ->
      exec_stmt e m (Swhile a s)
                (t1 ** t2) m2 out
  | exec_Swhile_loop: forall e m a t1 m1 v s out2 out t2 m2 t3 m3,
      eval_expr e m a t1 m1 v ->
      is_true v (typeof a) ->
      exec_stmt e m1 s t2 m2 out2 ->
      out_normal_or_continue out2 ->
      exec_stmt e m2 (Swhile a s) t3 m3 out ->
      exec_stmt e m (Swhile a s)
                (t1 ** t2 ** t3) m3 out
  | exec_Sdowhile_false: forall e m s a t1 m1 out1 v t2 m2,
      exec_stmt e m s t1 m1 out1 ->
      out_normal_or_continue out1 ->
      eval_expr e m1 a t2 m2 v ->
      is_false v (typeof a) ->
      exec_stmt e m (Sdowhile a s)
                (t1 ** t2) m2 Out_normal
  | exec_Sdowhile_stop: forall e m s a t m1 out1 out,
      exec_stmt e m s t m1 out1 ->
      out_break_or_return out1 out ->
      exec_stmt e m (Sdowhile a s)
                t m1 out
  | exec_Sdowhile_loop: forall e m s a m1 m2 m3 t1 t2 t3 out out1 v,
      exec_stmt e m s t1 m1 out1 ->
      out_normal_or_continue out1 ->
      eval_expr e m1 a t2 m2 v ->
      is_true v (typeof a) ->
      exec_stmt e m2 (Sdowhile a s) t3 m3 out ->
      exec_stmt e m (Sdowhile a s) 
                (t1 ** t2 ** t3) m3 out
  | exec_Sfor_start: forall e m s a1 a2 a3 out m1 m2 t1 t2,
      exec_stmt e m a1 t1 m1 Out_normal ->
      exec_stmt e m1 (Sfor Sskip a2 a3 s) t2 m2 out ->
      exec_stmt e m (Sfor a1 a2 a3 s) 
                (t1 ** t2) m2 out
  | exec_Sfor_false: forall e m s a2 a3 t v m1,
      eval_expr e m a2 t m1 v ->
      is_false v (typeof a2) ->
      exec_stmt e m (Sfor Sskip a2 a3 s)
                t m1 Out_normal
  | exec_Sfor_stop: forall e m s a2 a3 v m1 m2 t1 t2 out2 out,
      eval_expr e m a2 t1 m1 v ->
      is_true v (typeof a2) ->
      exec_stmt e m1 s t2 m2 out2 ->
      out_break_or_return out2 out ->
      exec_stmt e m (Sfor Sskip a2 a3 s)
                (t1 ** t2) m2 out
  | exec_Sfor_loop: forall e m s a2 a3 v m1 m2 m3 m4 t1 t2 t3 t4 out2 out,
      eval_expr e m a2 t1 m1 v ->
      is_true v (typeof a2) ->
      exec_stmt e m1 s t2 m2 out2 ->
      out_normal_or_continue out2 ->
      exec_stmt e m2 a3 t3 m3 Out_normal ->
      exec_stmt e m3 (Sfor Sskip a2 a3 s) t4 m4 out ->
      exec_stmt e m (Sfor Sskip a2 a3 s)
                (t1 ** t2 ** t3 ** t4) m4 out
  | exec_Sswitch:   forall e m a t1 m1 n sl t2 m2 out,
      eval_expr e m a t1 m1 (Vint n) ->
      exec_lblstmts e m1 (select_switch n sl) t2 m2 out ->
      exec_stmt e m (Sswitch a sl)
                (t1 ** t2) m2 (outcome_switch out)

(** Execution of a list of labeled statements *)

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

(** Evaluation of a function invocation *)

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

Scheme eval_expr_ind6 := Minimality for eval_expr Sort Prop
  with eval_lvalue_ind6 := Minimality for eval_lvalue Sort Prop
  with eval_exprlist_ind6 := Minimality for eval_exprlist Sort Prop
  with exec_stmt_ind6 := Minimality for exec_stmt Sort Prop
  with exec_lblstmts_ind6 := Minimality for exec_lblstmts Sort Prop
  with eval_funcall_ind6 := Minimality for eval_funcall Sort Prop.

End RELSEM.

(** Execution of a whole program *)

Definition exec_program (p: program) (t: trace) (r: val) : Prop :=
  let ge := Genv.globalenv p in 
  let m0 := Genv.init_mem p in
  exists b, exists f, exists m1,
  Genv.find_symbol ge p.(prog_main) = Some b /\
  Genv.find_funct_ptr ge b = Some f /\
  type_of_fundef f = Tfunction Tnil (Tint I32 Signed) /\
  eval_funcall ge m0 f nil t m1 r.
