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

(** Translation from Clight to Csharpminor. *)

(** The main transformations performed by this first part are:
- Resolution of all type-dependent behaviours: overloaded operators
   are resolved, address computations for array and struct accesses
   are made explicit, etc.
- Translation of Clight's loops and [switch] statements into
   Csharpminor's simpler control structures.
*)

Require Import Coqlib Maps Errors Integers Floats.
Require Import AST Linking.
Require Import Ctypes Cop Clight Cminor Csharpminor.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

(** * Csharpminor constructors *)

(** The following functions build Csharpminor expressions that compute
   the value of a C operation.  Most construction functions take
   as arguments
-  Csharpminor subexpressions that compute the values of the
     arguments of the operation;
-  The C types of the arguments of the operation.  These types
     are used to insert the necessary numeric conversions and to
     resolve operation overloading.
   Most of these functions return a [res expr], with [Error]
   denoting a case where the operation is not defined at the given types.
*)

Definition make_intconst (n: int) :=  Econst (Ointconst n).

Definition make_longconst (f: int64) :=  Econst (Olongconst f).

Definition make_floatconst (f: float) :=  Econst (Ofloatconst f).

Definition make_singleconst (f: float32) :=  Econst (Osingleconst f).

Definition make_ptrofsconst (n: Z) :=
  if Archi.ptr64 then make_longconst (Int64.repr n) else make_intconst (Int.repr n).

Definition make_singleoffloat (e: expr) := Eunop Osingleoffloat e.
Definition make_floatofsingle (e: expr) := Eunop Ofloatofsingle e.

Definition make_floatofint (e: expr) (sg: signedness) :=
  match sg with
  | Signed => Eunop Ofloatofint e
  | Unsigned => Eunop Ofloatofintu e
  end.

Definition make_singleofint (e: expr) (sg: signedness) :=
  match sg with
  | Signed => Eunop Osingleofint e
  | Unsigned => Eunop Osingleofintu e
  end.

Definition make_intoffloat (e: expr) (sg: signedness) :=
  match sg with
  | Signed => Eunop Ointoffloat e
  | Unsigned => Eunop Ointuoffloat e
  end.

Definition make_intofsingle (e: expr) (sg: signedness) :=
  match sg with
  | Signed => Eunop Ointofsingle e
  | Unsigned => Eunop Ointuofsingle e
  end.

Definition make_longofint (e: expr) (sg: signedness) :=
  match sg with
  | Signed => Eunop Olongofint e
  | Unsigned => Eunop Olongofintu e
  end.

Definition make_floatoflong (e: expr) (sg: signedness) :=
  match sg with
  | Signed => Eunop Ofloatoflong e
  | Unsigned => Eunop Ofloatoflongu e
  end.

Definition make_singleoflong (e: expr) (sg: signedness) :=
  match sg with
  | Signed => Eunop Osingleoflong e
  | Unsigned => Eunop Osingleoflongu e
  end.

Definition make_longoffloat (e: expr) (sg: signedness) :=
  match sg with
  | Signed => Eunop Olongoffloat e
  | Unsigned => Eunop Olonguoffloat e
  end.

Definition make_longofsingle (e: expr) (sg: signedness) :=
  match sg with
  | Signed => Eunop Olongofsingle e
  | Unsigned => Eunop Olonguofsingle e
  end.

Definition make_cmpu_ne_zero (e: expr) :=
  match e with
  | Ebinop (Ocmp c) e1 e2 => e
  | Ebinop (Ocmpu c) e1 e2 => e
  | Ebinop (Ocmpf c) e1 e2 => e
  | Ebinop (Ocmpfs c) e1 e2 => e
  | Ebinop (Ocmpl c) e1 e2 => e
  | Ebinop (Ocmplu c) e1 e2 => e
  | _ => Ebinop (Ocmpu Cne) e (make_intconst Int.zero)
  end.

(** Variants of [sizeof] and [alignof] that check that the given type is complete. *)

Definition sizeof (ce: composite_env) (t: type) : res Z :=
  if complete_type ce t
  then OK (Ctypes.sizeof ce t)
  else Error (msg "incomplete type").

Definition alignof (ce: composite_env) (t: type) : res Z :=
  if complete_type ce t
  then OK (Ctypes.alignof ce t)
  else Error (msg "incomplete type").

(** [make_cast from to e] applies to [e] the numeric conversions needed
   to transform a result of type [from] to a result of type [to]. *)

Definition make_cast_int (e: expr) (sz: intsize) (si: signedness) :=
  match sz, si with
  | I8, Signed => Eunop Ocast8signed e
  | I8, Unsigned => Eunop Ocast8unsigned e
  | I16, Signed => Eunop Ocast16signed e
  | I16, Unsigned => Eunop Ocast16unsigned e
  | I32, _ => e
  | IBool, _ => make_cmpu_ne_zero e
  end.

Definition make_cast (from to: type) (e: expr) :=
  match classify_cast from to with
  | cast_case_pointer => OK e
  | cast_case_i2i sz2 si2 => OK (make_cast_int e sz2 si2)
  | cast_case_f2f => OK e
  | cast_case_s2s => OK e
  | cast_case_f2s => OK (make_singleoffloat e)
  | cast_case_s2f => OK (make_floatofsingle e)
  | cast_case_i2f si1 => OK (make_floatofint e si1)
  | cast_case_i2s si1 => OK (make_singleofint e si1)
  | cast_case_f2i sz2 si2 => OK (make_cast_int (make_intoffloat e si2) sz2 si2)
  | cast_case_s2i sz2 si2 => OK (make_cast_int (make_intofsingle e si2) sz2 si2)
  | cast_case_l2l => OK e
  | cast_case_i2l si1 => OK (make_longofint e si1)
  | cast_case_l2i sz2 si2 => OK (make_cast_int (Eunop Ointoflong e) sz2 si2)
  | cast_case_l2f si1 => OK (make_floatoflong e si1)
  | cast_case_l2s si1 => OK (make_singleoflong e si1)
  | cast_case_f2l si2 => OK (make_longoffloat e si2)
  | cast_case_s2l si2 => OK (make_longofsingle e si2)
  | cast_case_i2bool => OK (make_cmpu_ne_zero e)
  | cast_case_f2bool => OK (Ebinop (Ocmpf Cne) e (make_floatconst Float.zero))
  | cast_case_s2bool => OK (Ebinop (Ocmpfs Cne) e (make_singleconst Float32.zero))
  | cast_case_l2bool => OK (Ebinop (Ocmplu Cne) e (make_longconst Int64.zero))
  | cast_case_struct id1 id2 => OK e
  | cast_case_union id1 id2 => OK e
  | cast_case_void => OK e
  | cast_case_default => Error (msg "Cshmgen.make_cast")
  end.

(** [make_boolean e ty] returns a Csharpminor expression that evaluates
   to the boolean value of [e].  *)

Definition make_boolean (e: expr) (ty: type) :=
  match classify_bool ty with
  | bool_case_i => make_cmpu_ne_zero e
  | bool_case_f => Ebinop (Ocmpf Cne) e (make_floatconst Float.zero)
  | bool_case_s => Ebinop (Ocmpfs Cne) e (make_singleconst Float32.zero)
  | bool_case_l => Ebinop (Ocmplu Cne) e (make_longconst Int64.zero)
  | bool_default => e   (**r should not happen *)
  end.

(** Unary operators *)

Definition make_notbool (e: expr) (ty: type) :=
  match classify_bool ty with
  | bool_case_i => OK (Ebinop (Ocmpu Ceq) e (make_intconst Int.zero))
  | bool_case_f => OK (Ebinop (Ocmpf Ceq) e (make_floatconst Float.zero))
  | bool_case_s => OK (Ebinop (Ocmpfs Ceq) e (make_singleconst Float32.zero))
  | bool_case_l => OK (Ebinop (Ocmplu Ceq) e (make_longconst Int64.zero))
  | bool_default => Error (msg "Cshmgen.make_notbool")
  end.

Definition make_neg (e: expr) (ty: type) :=
  match classify_neg ty with
  | neg_case_i _ => OK (Eunop Onegint e)
  | neg_case_f => OK (Eunop Onegf e)
  | neg_case_s => OK (Eunop Onegfs e)
  | neg_case_l _ => OK (Eunop Onegl e)
  | neg_default => Error (msg "Cshmgen.make_neg")
  end.

Definition make_absfloat (e: expr) (ty: type) :=
  match classify_neg ty with
  | neg_case_i sg => OK (Eunop Oabsf (make_floatofint e sg))
  | neg_case_f => OK (Eunop Oabsf e)
  | neg_case_s => OK (Eunop Oabsf (make_floatofsingle e))
  | neg_case_l sg => OK (Eunop Oabsf (make_floatoflong e sg))
  | neg_default => Error (msg "Cshmgen.make_absfloat")
  end.

Definition make_notint (e: expr) (ty: type) :=
  match classify_notint ty with
  | notint_case_i _ => OK (Eunop Onotint e)
  | notint_case_l _ => OK (Eunop Onotl e)
  | notint_default => Error (msg "Cshmgen.make_notint")
  end.

(** Binary operators *)

Definition make_binarith (iop iopu fop sop lop lopu: binary_operation)
                         (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  let c := classify_binarith ty1 ty2 in
  let ty := binarith_type c in
  do e1' <- make_cast ty1 ty e1;
  do e2' <- make_cast ty2 ty e2;
  match c with
  | bin_case_i Signed => OK (Ebinop iop e1' e2')
  | bin_case_i Unsigned => OK (Ebinop iopu e1' e2')
  | bin_case_f => OK (Ebinop fop e1' e2')
  | bin_case_s => OK (Ebinop sop e1' e2')
  | bin_case_l Signed => OK (Ebinop lop e1' e2')
  | bin_case_l Unsigned => OK (Ebinop lopu e1' e2')
  | bin_default => Error (msg "Cshmgen.make_binarith")
  end.

Definition make_add_ptr_int (ce: composite_env) (ty: type) (si: signedness) (e1 e2: expr) :=
  do sz <- sizeof ce ty;
  if Archi.ptr64 then
    let n := make_longconst (Int64.repr sz) in
    OK (Ebinop Oaddl e1 (Ebinop Omull n (make_longofint e2 si)))
  else
    let n := make_intconst (Int.repr sz) in
    OK (Ebinop Oadd e1 (Ebinop Omul n e2)).

Definition make_add_ptr_long (ce: composite_env) (ty: type) (e1 e2: expr) :=
  do sz <- sizeof ce ty;
  if Archi.ptr64 then
    let n := make_longconst (Int64.repr sz) in
    OK (Ebinop Oaddl e1 (Ebinop Omull n e2))
  else
    let n := make_intconst (Int.repr sz) in
    OK (Ebinop Oadd e1 (Ebinop Omul n (Eunop Ointoflong e2))).

Definition make_add (ce: composite_env) (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_add ty1 ty2 with
  | add_case_pi ty si => make_add_ptr_int ce ty si e1 e2
  | add_case_pl ty => make_add_ptr_long ce ty e1 e2
  | add_case_ip si ty => make_add_ptr_int ce ty si e2 e1
  | add_case_lp ty => make_add_ptr_long ce ty e2 e1
  | add_default => make_binarith Oadd Oadd Oaddf Oaddfs Oaddl Oaddl e1 ty1 e2 ty2
  end.

Definition make_sub (ce: composite_env) (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_sub ty1 ty2 with
  | sub_case_pi ty si =>
      do sz <- sizeof ce ty;
      if Archi.ptr64 then
        let n := make_longconst (Int64.repr sz) in
        OK (Ebinop Osubl e1 (Ebinop Omull n (make_longofint e2 si)))
      else
        let n := make_intconst (Int.repr sz) in
        OK (Ebinop Osub e1 (Ebinop Omul n e2))
  | sub_case_pp ty =>
      do sz <- sizeof ce ty;
      if Archi.ptr64 then
        let n := make_longconst (Int64.repr sz) in
        OK (Ebinop Odivl (Ebinop Osubl e1 e2) n)
      else
        let n := make_intconst (Int.repr sz) in
        OK (Ebinop Odiv (Ebinop Osub e1 e2) n)
  | sub_case_pl ty =>
      do sz <- sizeof ce ty;
      if Archi.ptr64 then
        let n := make_longconst (Int64.repr sz) in
        OK (Ebinop Osubl e1 (Ebinop Omull n e2))
      else
        let n := make_intconst (Int.repr sz) in
        OK (Ebinop Osub e1 (Ebinop Omul n (Eunop Ointoflong e2)))
  | sub_default =>
      make_binarith Osub Osub Osubf Osubfs Osubl Osubl e1 ty1 e2 ty2
  end.

Definition make_mul (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  make_binarith Omul Omul Omulf Omulfs Omull Omull e1 ty1 e2 ty2.

Definition make_div (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  make_binarith Odiv Odivu Odivf Odivfs Odivl Odivlu e1 ty1 e2 ty2.

Definition make_binarith_int (iop iopu lop lopu: binary_operation)
                             (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  let c := classify_binarith ty1 ty2 in
  let ty := binarith_type c in
  do e1' <- make_cast ty1 ty e1;
  do e2' <- make_cast ty2 ty e2;
  match c with
  | bin_case_i Signed => OK (Ebinop iop e1' e2')
  | bin_case_i Unsigned => OK (Ebinop iopu e1' e2')
  | bin_case_l Signed => OK (Ebinop lop e1' e2')
  | bin_case_l Unsigned => OK (Ebinop lopu e1' e2')
  | bin_case_f | bin_case_s | bin_default => Error (msg "Cshmgen.make_binarith_int")
  end.

Definition make_mod (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  make_binarith_int Omod Omodu Omodl Omodlu e1 ty1 e2 ty2.

Definition make_and (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  make_binarith_int Oand Oand Oandl Oandl e1 ty1 e2 ty2.

Definition make_or (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  make_binarith_int Oor Oor Oorl Oorl e1 ty1 e2 ty2.

Definition make_xor (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  make_binarith_int Oxor Oxor Oxorl Oxorl e1 ty1 e2 ty2.

Definition make_shl (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_shift ty1 ty2 with
  | shift_case_ii _ => OK (Ebinop Oshl e1 e2)
  | shift_case_li _ => OK (Ebinop Oshll e1 e2)
  | shift_case_il _ => OK (Ebinop Oshl e1 (Eunop Ointoflong e2))
  | shift_case_ll _ => OK (Ebinop Oshll e1 (Eunop Ointoflong e2))
  | shift_default => Error (msg "Cshmgen.make_shl")
  end.

Definition make_shr (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_shift ty1 ty2 with
  | shift_case_ii Signed => OK (Ebinop Oshr e1 e2)
  | shift_case_ii Unsigned => OK (Ebinop Oshru e1 e2)
  | shift_case_li Signed => OK (Ebinop Oshrl e1 e2)
  | shift_case_li Unsigned => OK (Ebinop Oshrlu e1 e2)
  | shift_case_il Signed => OK (Ebinop Oshr e1 (Eunop Ointoflong e2))
  | shift_case_il Unsigned => OK (Ebinop Oshru e1 (Eunop Ointoflong e2))
  | shift_case_ll Signed => OK (Ebinop Oshrl e1 (Eunop Ointoflong e2))
  | shift_case_ll Unsigned => OK (Ebinop Oshrlu e1 (Eunop Ointoflong e2))
  | shift_default => Error (msg "Cshmgen.make_shr")
  end.

Definition make_cmp_ptr (c: comparison) (e1 e2: expr) :=
  Ebinop (if Archi.ptr64 then Ocmplu c else Ocmpu c) e1 e2.

Definition make_cmp (c: comparison) (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_cmp ty1 ty2 with
  | cmp_case_pp => OK (make_cmp_ptr c e1 e2)
  | cmp_case_pi si =>
      OK (make_cmp_ptr c e1 (if Archi.ptr64 then make_longofint e2 si else e2))
  | cmp_case_ip si =>
      OK (make_cmp_ptr c (if Archi.ptr64 then make_longofint e1 si else e1) e2)
  | cmp_case_pl =>
      OK (make_cmp_ptr c e1 (if Archi.ptr64 then e2 else Eunop Ointoflong e2))
  | cmp_case_lp =>
      OK (make_cmp_ptr c (if Archi.ptr64 then e1 else Eunop Ointoflong e1) e2)
  | cmp_default =>
      make_binarith
        (Ocmp c) (Ocmpu c) (Ocmpf c) (Ocmpfs c) (Ocmpl c) (Ocmplu c)
        e1 ty1 e2 ty2
  end.

(** [make_load addr ty_res] loads a value of type [ty_res] from
   the memory location denoted by the Csharpminor expression [addr].
   If [ty_res] is an array or function type, returns [addr] instead,
   as consistent with C semantics.
*)

Definition make_load (addr: expr) (ty_res: type) :=
  match (access_mode ty_res) with
  | By_value chunk => OK (Eload chunk addr)
  | By_reference => OK addr
  | By_copy => OK addr
  | By_nothing => Error (msg "Cshmgen.make_load")
  end.

(** [make_memcpy dst src ty] returns a [memcpy] builtin appropriate for
  by-copy assignment of a value of Clight type [ty]. *)

Definition make_memcpy (ce: composite_env) (dst src: expr) (ty: type) :=
  do sz <- sizeof ce ty;
  OK (Sbuiltin None (EF_memcpy sz (Ctypes.alignof_blockcopy ce ty))
                    (dst :: src :: nil)).

(** [make_store addr ty rhs] stores the value of the
   Csharpminor expression [rhs] into the memory location denoted by the
   Csharpminor expression [addr].
   [ty] is the type of the memory location. *)

Definition make_store (ce: composite_env) (addr: expr) (ty: type) (rhs: expr) :=
  match access_mode ty with
  | By_value chunk => OK (Sstore chunk addr rhs)
  | By_copy => make_memcpy ce addr rhs ty
  | _ => Error (msg "Cshmgen.make_store")
  end.

(** ** Translation of operators *)

Definition transl_unop (op: Cop.unary_operation) (a: expr) (ta: type) : res expr :=
  match op with
  | Cop.Onotbool => make_notbool a ta
  | Cop.Onotint => make_notint a ta
  | Cop.Oneg => make_neg a ta
  | Cop.Oabsfloat => make_absfloat a ta
  end.

Definition transl_binop (ce: composite_env)
                        (op: Cop.binary_operation)
                        (a: expr) (ta: type)
                        (b: expr) (tb: type) : res expr :=
  match op with
  | Cop.Oadd => make_add ce a ta b tb
  | Cop.Osub => make_sub ce a ta b tb
  | Cop.Omul => make_mul a ta b tb
  | Cop.Odiv => make_div a ta b tb
  | Cop.Omod => make_mod a ta b tb
  | Cop.Oand => make_and a ta b tb
  | Cop.Oor  => make_or a ta b tb
  | Cop.Oxor => make_xor a ta b tb
  | Cop.Oshl => make_shl a ta b tb
  | Cop.Oshr => make_shr a ta b tb
  | Cop.Oeq => make_cmp Ceq a ta b tb
  | Cop.One => make_cmp Cne a ta b tb
  | Cop.Olt => make_cmp Clt a ta b tb
  | Cop.Ogt => make_cmp Cgt a ta b tb
  | Cop.Ole => make_cmp Cle a ta b tb
  | Cop.Oge => make_cmp Cge a ta b tb
  end.

(** ** Translation of field accesses *)

Definition make_field_access (ce: composite_env) (ty: type) (f: ident) (a: expr) : res expr :=
  match ty with
  | Tstruct id _ =>
      match ce!id with
      | None =>
          Error (MSG "Undefined struct " :: CTX id :: nil)
      | Some co =>
          do ofs <- field_offset ce f (co_members co);
          OK (if Archi.ptr64
              then Ebinop Oaddl a (make_longconst (Int64.repr ofs))
              else Ebinop Oadd a (make_intconst (Int.repr ofs)))
      end
  | Tunion id _ =>
      OK a
  | _ =>
      Error(msg "Cshmgen.make_field_access")
  end.

(** * Translation of expressions *)

(** [transl_expr a] returns the Csharpminor code that computes the value
   of expression [a]. The computation is performed in the error monad
   (see module [Errors]) to enable error reporting. *)

Fixpoint transl_expr (ce: composite_env) (a: Clight.expr) {struct a} : res expr :=
  match a with
  | Clight.Econst_int n _ =>
      OK(make_intconst n)
  | Clight.Econst_float n _ =>
      OK(make_floatconst n)
  | Clight.Econst_single n _ =>
      OK(make_singleconst n)
  | Clight.Econst_long n _ =>
      OK(make_longconst n)
  | Clight.Evar id ty =>
      make_load (Eaddrof id) ty
  | Clight.Etempvar id ty =>
      OK(Evar id)
  | Clight.Ederef b ty =>
      do tb <- transl_expr ce b;
      make_load tb ty
  | Clight.Eaddrof b _ =>
      transl_lvalue ce b
  | Clight.Eunop op b _ =>
      do tb <- transl_expr ce b;
      transl_unop op tb (typeof b)
  | Clight.Ebinop op b c _ =>
      do tb <- transl_expr ce b;
      do tc <- transl_expr ce c;
      transl_binop ce op tb (typeof b) tc (typeof c)
  | Clight.Ecast b ty =>
      do tb <- transl_expr ce b;
      make_cast (typeof b) ty tb
  | Clight.Efield b i ty =>
      do tb <- transl_expr ce b;
      do addr <- make_field_access ce (typeof b) i tb;
      make_load addr ty
  | Clight.Esizeof ty' ty =>
      do sz <- sizeof ce ty'; OK(make_ptrofsconst sz)
  | Clight.Ealignof ty' ty =>
      do al <- alignof ce ty'; OK(make_ptrofsconst al)
  end

(** [transl_lvalue a] returns the Csharpminor code that evaluates
   [a] as a lvalue, that is, code that returns the memory address
   where the value of [a] is stored.
*)

with transl_lvalue (ce: composite_env) (a: Clight.expr) {struct a} : res expr :=
  match a with
  | Clight.Evar id _ =>
      OK (Eaddrof id)
  | Clight.Ederef b _ =>
      transl_expr ce b
  | Clight.Efield b i ty =>
      do tb <- transl_expr ce b;
      make_field_access ce (typeof b) i tb
  | _ =>
      Error(msg "Cshmgen.transl_lvalue")
  end.

(** [transl_arglist al tyl] returns a list of Csharpminor expressions
   that compute the values of the list [al] of Clight expressions,
   casted to the corresponding types in [tyl].
   Used for function applications. *)

Fixpoint transl_arglist (ce: composite_env) (al: list Clight.expr) (tyl: typelist)
                         {struct al}: res (list expr) :=
  match al, tyl with
  | nil, Tnil => OK nil
  | a1 :: a2, Tcons ty1 ty2 =>
      do ta1 <- transl_expr ce a1;
      do ta1' <- make_cast (typeof a1) ty1 ta1;
      do ta2 <- transl_arglist ce a2 ty2;
      OK (ta1' :: ta2)
  | a1 :: a2, Tnil =>
      (* Tolerance for calls to K&R or variadic functions *)
      do ta1 <- transl_expr ce a1;
      do ta1' <- make_cast (typeof a1) (default_argument_conversion (typeof a1)) ta1;
      do ta2 <- transl_arglist ce a2 Tnil;
      OK (ta1' :: ta2)
  | _, _ =>
      Error(msg "Cshmgen.transl_arglist: arity mismatch")
  end.

(** Compute the argument signature that corresponds to a function application. *)

Fixpoint typlist_of_arglist (al: list Clight.expr) (tyl: typelist)
                            {struct al}: list AST.typ :=
  match al, tyl with
  | nil, _ => nil
  | a1 :: a2, Tcons ty1 ty2 =>
      typ_of_type ty1 :: typlist_of_arglist a2 ty2
  | a1 :: a2, Tnil =>
      (* Tolerance for calls to K&R or variadic functions *)
      typ_of_type (default_argument_conversion (typeof a1)) :: typlist_of_arglist a2 Tnil
  end.

(** * Translation of statements *)

(** [transl_statement nbrk ncnt s] returns a Csharpminor statement
   that performs the same computations as the CabsCoq statement [s].

   If the statement [s] terminates prematurely on a [break] construct,
   the generated Csharpminor statement terminates prematurely on an
   [exit nbrk] construct.

   If the statement [s] terminates prematurely on a [continue]
   construct, the generated Csharpminor statement terminates
   prematurely on an [exit ncnt] construct.

   The general translation for loops is as follows:
<<
loop s1 s2          --->     block {
                               loop {
                                 block { s1 };
                                 // continue in s1 branches here
                                 s2;
                               }
                             }
                             // break in s1 and s2 branches here
*)

Fixpoint transl_statement (ce: composite_env) (tyret: type) (nbrk ncnt: nat)
                          (s: Clight.statement) {struct s} : res stmt :=
  match s with
  | Clight.Sskip =>
      OK Sskip
  | Clight.Sassign b c =>
      do tb <- transl_lvalue ce b;
      do tc <- transl_expr ce c;
      do tc' <- make_cast (typeof c) (typeof b) tc;
      make_store ce tb (typeof b) tc'
  | Clight.Sset x b =>
      do tb <- transl_expr ce b;
      OK(Sset x tb)
  | Clight.Scall x b cl =>
      match classify_fun (typeof b) with
      | fun_case_f args res cconv =>
          do tb <- transl_expr ce b;
          do tcl <- transl_arglist ce cl args;
          OK(Scall x {| sig_args := typlist_of_arglist cl args;
                        sig_res  := opttyp_of_type res;
                        sig_cc   := cconv |}
                   tb tcl)
      | _ => Error(msg "Cshmgen.transl_stmt(call)")
      end
  | Clight.Sbuiltin x ef tyargs bl =>
      do tbl <- transl_arglist ce bl tyargs;
      OK(Sbuiltin x ef tbl)
  | Clight.Ssequence s1 s2 =>
      do ts1 <- transl_statement ce tyret nbrk ncnt s1;
      do ts2 <- transl_statement ce tyret nbrk ncnt s2;
      OK (Sseq ts1 ts2)
  | Clight.Sifthenelse e s1 s2 =>
      do te <- transl_expr ce e;
      do ts1 <- transl_statement ce tyret nbrk ncnt s1;
      do ts2 <- transl_statement ce tyret nbrk ncnt s2;
      OK (Sifthenelse (make_boolean te (typeof e)) ts1 ts2)
  | Clight.Sloop s1 s2 =>
      do ts1 <- transl_statement ce tyret 1%nat 0%nat s1;
      do ts2 <- transl_statement ce tyret 0%nat (S ncnt) s2;
      OK (Sblock (Sloop (Sseq (Sblock ts1) ts2)))
  | Clight.Sbreak =>
      OK (Sexit nbrk)
  | Clight.Scontinue =>
      OK (Sexit ncnt)
  | Clight.Sreturn (Some e) =>
      do te <- transl_expr ce e;
      do te' <- make_cast (typeof e) tyret te;
      OK (Sreturn (Some te'))
  | Clight.Sreturn None =>
      OK (Sreturn None)
  | Clight.Sswitch a sl =>
      do ta <- transl_expr ce a;
      do tsl <- transl_lbl_stmt ce tyret 0%nat (S ncnt) sl;
      match classify_switch (typeof a) with
      | switch_case_i => OK (Sblock (Sswitch false ta tsl))
      | switch_case_l => OK (Sblock (Sswitch true ta tsl))
      | switch_default => Error(msg "Cshmgen.transl_stmt(switch)")
      end
  | Clight.Slabel lbl s =>
      do ts <- transl_statement ce tyret nbrk ncnt s;
      OK (Slabel lbl ts)
  | Clight.Sgoto lbl =>
      OK (Sgoto lbl)
  end

with transl_lbl_stmt (ce: composite_env) (tyret: type) (nbrk ncnt: nat)
                     (sl: Clight.labeled_statements)
                     {struct sl}: res lbl_stmt :=
  match sl with
  | Clight.LSnil =>
      OK LSnil
  | Clight.LScons n s sl' =>
      do ts <- transl_statement ce tyret nbrk ncnt s;
      do tsl' <- transl_lbl_stmt ce tyret nbrk ncnt sl';
      OK (LScons n ts tsl')
  end.

(*** Translation of functions *)

Definition transl_var (ce: composite_env) (v: ident * type) :=
  do sz <- sizeof ce (snd v); OK (fst v, sz).

Definition signature_of_function (f: Clight.function) :=
  {| sig_args := map typ_of_type (map snd (Clight.fn_params f));
     sig_res  := opttyp_of_type (Clight.fn_return f);
     sig_cc   := Clight.fn_callconv f |}.

Definition transl_function (ce: composite_env) (f: Clight.function) : res function :=
  do tbody <- transl_statement ce f.(Clight.fn_return) 1%nat 0%nat (Clight.fn_body f);
  do tvars <- mmap (transl_var ce) (Clight.fn_vars f);
  OK (mkfunction
       (signature_of_function f)
       (map fst (Clight.fn_params f))
       tvars
       (map fst (Clight.fn_temps f))
       tbody).

Definition transl_fundef (ce: composite_env) (id: ident) (f: Clight.fundef) : res fundef :=
  match f with
  | Internal g =>
      do tg <- transl_function ce g; OK(AST.Internal tg)
  | External ef args res cconv =>
      if signature_eq (ef_sig ef) (signature_of_type args res cconv)
      then OK(AST.External ef)
      else Error(msg "Cshmgen.transl_fundef: wrong external signature")
  end.

(** ** Translation of programs *)

Definition transl_globvar (id: ident) (ty: type) := OK tt.

Definition transl_program (p: Clight.program) : res program :=
  transform_partial_program2 (transl_fundef p.(prog_comp_env)) transl_globvar p.

