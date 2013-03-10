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

Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import AST.
Require Import Ctypes.
Require Import Cop.
Require Import Clight.
Require Import Cminor.
Require Import Csharpminor.

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

(** * Csharpminor constructors *)

(** The following functions build Csharpminor expressions that compute
   the value of a C operation.  Most construction functions take
   as arguments
-  Csharpminor subexpressions that compute the values of the
     arguments of the operation;
-  The C types of the arguments of the operation.  These types
     are used to insert the necessary numeric conversions and to
     resolve operation overloading.
   Most of these functions return an [option expr], with [None] 
   denoting a case where the operation is not defined at the given types.
*)

Definition make_intconst (n: int) :=  Econst (Ointconst n).

Definition make_floatconst (f: float) :=  Econst (Ofloatconst f).

Definition make_floatofint (e: expr) (sg: signedness) :=
  match sg with
  | Signed => Eunop Ofloatofint e
  | Unsigned => Eunop Ofloatofintu e
  end.

Definition make_intoffloat (e: expr) (sg: signedness) :=
  match sg with
  | Signed => Eunop Ointoffloat e
  | Unsigned => Eunop Ointuoffloat e
  end.

(** [make_boolean e ty] returns a Csharpminor expression that evaluates
   to the boolean value of [e].  *)

Definition make_cmp_ne_zero (e: expr) :=
  match e with
  | Ebinop (Ocmp c) e1 e2 => e
  | Ebinop (Ocmpu c) e1 e2 => e
  | Ebinop (Ocmpf c) e1 e2 => e
  | _ => Ebinop (Ocmp Cne) e (make_intconst Int.zero)
  end.

Definition make_boolean (e: expr) (ty: type) :=
  match classify_bool ty with
  | bool_case_i => make_cmp_ne_zero e
  | bool_case_f => Ebinop (Ocmpf Cne) e (make_floatconst Float.zero)
  | bool_case_p => Ebinop (Ocmpu Cne) e (make_intconst Int.zero)
  | bool_default => e   (**r should not happen *)
  end.

Definition make_notbool (e: expr) (ty: type) :=
  match classify_bool ty with
  | bool_case_i => OK (Ebinop (Ocmp Ceq) e (make_intconst Int.zero))
  | bool_case_f => OK (Ebinop (Ocmpf Ceq) e (make_floatconst Float.zero))
  | bool_case_p => OK (Ebinop (Ocmpu Ceq) e (make_intconst Int.zero))
  | _ => Error (msg "Cshmgen.make_notbool")
  end.

Definition make_neg (e: expr) (ty: type) :=
  match classify_neg ty with
  | neg_case_i _ => OK (Eunop Onegint e)
  | neg_case_f => OK (Eunop Onegf e)
  | _ => Error (msg "Cshmgen.make_neg")
  end.

Definition make_notint (e: expr) (ty: type) :=
  Eunop Onotint e.

Definition make_add (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_add ty1 ty2 with
  | add_case_ii _ => OK (Ebinop Oadd e1 e2)
  | add_case_ff => OK (Ebinop Oaddf e1 e2)
  | add_case_if sg => OK (Ebinop Oaddf (make_floatofint e1 sg) e2)
  | add_case_fi sg => OK (Ebinop Oaddf e1 (make_floatofint e2 sg))
  | add_case_pi ty _ =>
      let n := make_intconst (Int.repr (Ctypes.sizeof ty)) in
      OK (Ebinop Oadd e1 (Ebinop Omul n e2))
  | add_case_ip ty _ =>
      let n := make_intconst (Int.repr (Ctypes.sizeof ty)) in
      OK (Ebinop Oadd e2 (Ebinop Omul n e1))
  | add_default => Error (msg "Cshmgen.make_add")
  end.

Definition make_sub (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_sub ty1 ty2 with
  | sub_case_ii _ => OK (Ebinop Osub e1 e2)
  | sub_case_ff => OK (Ebinop Osubf e1 e2)
  | sub_case_if sg => OK (Ebinop Osubf (make_floatofint e1 sg) e2)
  | sub_case_fi sg => OK (Ebinop Osubf e1 (make_floatofint e2 sg))
  | sub_case_pi ty =>
      let n := make_intconst (Int.repr (Ctypes.sizeof ty)) in
      OK (Ebinop Osub e1 (Ebinop Omul n e2))
  | sub_case_pp ty =>
      let n := make_intconst (Int.repr (Ctypes.sizeof ty)) in
      OK (Ebinop Odivu (Ebinop Osub e1 e2) n)
  | sub_default => Error (msg "Cshmgen.make_sub")
  end.

Definition make_mul (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_mul ty1 ty2 with
  | mul_case_ii _ => OK (Ebinop Omul e1 e2)
  | mul_case_ff => OK (Ebinop Omulf e1 e2)
  | mul_case_if sg => OK (Ebinop Omulf (make_floatofint e1 sg) e2)
  | mul_case_fi sg => OK (Ebinop Omulf e1 (make_floatofint e2 sg))
  | mul_default => Error (msg "Cshmgen.make_mul")
  end.

Definition make_div (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_div ty1 ty2 with
  | div_case_ii Unsigned => OK (Ebinop Odivu e1 e2)
  | div_case_ii Signed => OK (Ebinop Odiv e1 e2)
  | div_case_ff => OK (Ebinop Odivf e1 e2)
  | div_case_if sg => OK (Ebinop Odivf (make_floatofint e1 sg) e2)
  | div_case_fi sg => OK (Ebinop Odivf e1 (make_floatofint e2 sg))
  | div_default => Error (msg "Cshmgen.make_div")
  end.

Definition make_mod (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_binint ty1 ty2 with
  | binint_case_ii Unsigned => OK (Ebinop Omodu e1 e2)
  | binint_case_ii Signed => OK (Ebinop Omod e1 e2)
  | mod_default => Error (msg "Cshmgen.make_mod")
  end.

Definition make_and (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  OK(Ebinop Oand e1 e2).

Definition make_or (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  OK(Ebinop Oor e1 e2).

Definition make_xor (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  OK(Ebinop Oxor e1 e2).

Definition make_shl (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  OK(Ebinop Oshl e1 e2).

Definition make_shr (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_shift ty1 ty2 with
  | shift_case_ii Unsigned => OK (Ebinop Oshru e1 e2)
  | shift_case_ii Signed => OK (Ebinop Oshr e1 e2)
  | shr_default => Error (msg "Cshmgen.make_shr")
  end.

Definition make_cmp (c: comparison) (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_cmp ty1 ty2 with
  | cmp_case_ii Signed => OK (Ebinop (Ocmp c) e1 e2)
  | cmp_case_ii Unsigned => OK (Ebinop (Ocmpu c) e1 e2)
  | cmp_case_pp => OK (Ebinop (Ocmpu c) e1 e2)
  | cmp_case_ff => OK (Ebinop (Ocmpf c) e1 e2)
  | cmp_case_if sg => OK (Ebinop (Ocmpf c) (make_floatofint e1 sg) e2)
  | cmp_case_fi sg => OK (Ebinop (Ocmpf c) e1 (make_floatofint e2 sg))
  | cmp_default => Error (msg "Cshmgen.make_cmp")
  end.

(** [make_cast from to e] applies to [e] the numeric conversions needed
   to transform a result of type [from] to a result of type [to]. *)

Definition make_cast_int (e: expr) (sz: intsize) (si: signedness) :=
  match sz, si with
  | I8, Signed => Eunop Ocast8signed e  
  | I8, Unsigned => Eunop Ocast8unsigned e  
  | I16, Signed => Eunop Ocast16signed e  
  | I16, Unsigned => Eunop Ocast16unsigned e  
  | I32, _ => e
  | IBool, _ => make_cmp_ne_zero e
  end.

Definition make_cast_float (e: expr) (sz: floatsize) :=
  match sz with
  | F32 => Eunop Osingleoffloat e
  | F64 => e
  end.

Definition make_cast (from to: type) (e: expr) :=
  match classify_cast from to with
  | cast_case_neutral => e
  | cast_case_i2i sz2 si2 => make_cast_int e sz2 si2
  | cast_case_f2f sz2 => make_cast_float e sz2
  | cast_case_i2f si1 sz2 => make_cast_float (make_floatofint e si1) sz2
  | cast_case_f2i sz2 si2 => make_cast_int (make_intoffloat e si2) sz2 si2
  | cast_case_f2bool => Ebinop (Ocmpf Cne) e (make_floatconst Float.zero)
  | cast_case_p2bool => Ebinop (Ocmpu Cne) e (make_intconst Int.zero)
  | cast_case_struct id1 fld1 id2 fld2 => e
  | cast_case_union id1 fld1 id2 fld2 => e
  | cast_case_void => e
  | cast_case_default => e
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

Definition make_memcpy (dst src: expr) (ty: type) :=
  Sbuiltin None (EF_memcpy (Ctypes.sizeof ty) (Ctypes.alignof ty))
                (dst :: src :: nil).

(** [make_store addr ty rhs] stores the value of the
   Csharpminor expression [rhs] into the memory location denoted by the
   Csharpminor expression [addr].  
   [ty] is the type of the memory location. *)

Definition make_store (addr: expr) (ty: type) (rhs: expr) :=
  match access_mode ty with
  | By_value chunk => OK (Sstore chunk addr rhs)
  | By_copy => OK (make_memcpy addr rhs ty)
  | _ => Error (msg "Cshmgen.make_store")
  end.

(** ** Translation of operators *)

Definition transl_unop (op: Cop.unary_operation) (a: expr) (ta: type) : res expr :=
  match op with
  | Cop.Onotbool => make_notbool a ta
  | Cop.Onotint => OK(make_notint a ta)
  | Cop.Oneg => make_neg a ta
  end.

Definition transl_binop (op: Cop.binary_operation)
                        (a: expr) (ta: type)
                        (b: expr) (tb: type) : res expr :=
  match op with
  | Cop.Oadd => make_add a ta b tb
  | Cop.Osub => make_sub a ta b tb
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

(** * Translation of expressions *)

(** [transl_expr a] returns the Csharpminor code that computes the value
   of expression [a]. The computation is performed in the error monad
   (see module [Errors]) to enable error reporting. *)

Fixpoint transl_expr (a: Clight.expr) {struct a} : res expr :=
  match a with
  | Clight.Econst_int n _ =>
      OK(make_intconst n)
  | Clight.Econst_float n _ =>
      OK(make_floatconst n)
  | Clight.Evar id ty =>
      make_load (Eaddrof id) ty
  | Clight.Etempvar id ty =>
      OK(Evar id)
  | Clight.Ederef b ty =>
      do tb <- transl_expr b;
      make_load tb ty
  | Clight.Eaddrof b _ =>
      transl_lvalue b
  | Clight.Eunop op b _ =>
      do tb <- transl_expr b;
      transl_unop op tb (typeof b)
  | Clight.Ebinop op b c _ =>
      do tb <- transl_expr b;
      do tc <- transl_expr c;
      transl_binop op tb (typeof b) tc (typeof c)
  | Clight.Ecast b ty =>
      do tb <- transl_expr b;
      OK (make_cast (typeof b) ty tb)
  | Clight.Efield b i ty => 
      match typeof b with
      | Tstruct _ fld _ =>
          do tb <- transl_expr b;
          do ofs <- field_offset i fld;
          make_load
            (Ebinop Oadd tb (make_intconst (Int.repr ofs)))
            ty
      | Tunion _ fld _ =>
          do tb <- transl_expr b;
          make_load tb ty
      | _ =>
          Error(msg "Cshmgen.transl_expr(field)")
      end
  end

(** [transl_lvalue a] returns the Csharpminor code that evaluates
   [a] as a lvalue, that is, code that returns the memory address
   where the value of [a] is stored.
*)

with transl_lvalue (a: Clight.expr) {struct a} : res expr :=
  match a with
  | Clight.Evar id _ =>
      OK (Eaddrof id)
  | Clight.Ederef b _ =>
      transl_expr b
  | Clight.Efield b i ty => 
      match typeof b with
      | Tstruct _ fld _ =>
          do tb <- transl_expr b;
          do ofs <- field_offset i fld;
          OK (Ebinop Oadd tb (make_intconst (Int.repr ofs)))
      | Tunion _ fld _ =>
          transl_expr b
      | _ =>
          Error(msg "Cshmgen.transl_lvalue(field)")
      end
  | _ => 
      Error(msg "Cshmgen.transl_lvalue")
  end.

(** [transl_arglist al tyl] returns a list of Csharpminor expressions
   that compute the values of the list [al] of Clight expressions,
   casted to the corresponding types in [tyl].
   Used for function applications. *)

Fixpoint transl_arglist (al: list Clight.expr) (tyl: typelist)
                         {struct al}: res (list expr) :=
  match al, tyl with
  | nil, Tnil => OK nil
  | a1 :: a2, Tcons ty1 ty2 =>
      do ta1 <- transl_expr a1;
      do ta2 <- transl_arglist a2 ty2;
      OK (make_cast (typeof a1) ty1 ta1 :: ta2)
  | _, _ =>
      Error(msg "Cshmgen.transl_arglist: arity mismatch")
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

Fixpoint transl_statement (tyret: type) (nbrk ncnt: nat)
                          (s: Clight.statement) {struct s} : res stmt :=
  match s with
  | Clight.Sskip =>
      OK Sskip
  | Clight.Sassign b c =>
      do tb <- transl_lvalue b;
      do tc <- transl_expr c;
      make_store tb (typeof b) (make_cast (typeof c) (typeof b) tc)
  | Clight.Sset x b =>
      do tb <- transl_expr b;
      OK(Sset x tb)
  | Clight.Scall x b cl =>
      match classify_fun (typeof b) with
      | fun_case_f args res =>
          do tb <- transl_expr b;
          do tcl <- transl_arglist cl args;
          OK(Scall x (signature_of_type args res) tb tcl)
      | _ => Error(msg "Cshmgen.transl_stmt(call)")
      end
  | Clight.Sbuiltin x ef tyargs bl =>
      do tbl <- transl_arglist bl tyargs;
      OK(Sbuiltin x ef tbl)
  | Clight.Ssequence s1 s2 =>
      do ts1 <- transl_statement tyret nbrk ncnt s1;
      do ts2 <- transl_statement tyret nbrk ncnt s2;
      OK (Sseq ts1 ts2)
  | Clight.Sifthenelse e s1 s2 =>
      do te <- transl_expr e;
      do ts1 <- transl_statement tyret nbrk ncnt s1;
      do ts2 <- transl_statement tyret nbrk ncnt s2;
      OK (Sifthenelse (make_boolean te (typeof e)) ts1 ts2)
  | Clight.Sloop s1 s2 =>
      do ts1 <- transl_statement tyret 1%nat 0%nat s1;
      do ts2 <- transl_statement tyret 0%nat (S ncnt) s2;
      OK (Sblock (Sloop (Sseq (Sblock ts1) ts2)))
  | Clight.Sbreak =>
      OK (Sexit nbrk)
  | Clight.Scontinue =>
      OK (Sexit ncnt)
  | Clight.Sreturn (Some e) =>
      do te <- transl_expr e;
      OK (Sreturn (Some (make_cast (typeof e) tyret te)))
  | Clight.Sreturn None =>
      OK (Sreturn None)
  | Clight.Sswitch a sl =>
      do ta <- transl_expr a;
      do tsl <- transl_lbl_stmt tyret 0%nat (S ncnt) sl;
      OK (Sblock (Sswitch ta tsl))
  | Clight.Slabel lbl s =>
      do ts <- transl_statement tyret nbrk ncnt s;
      OK (Slabel lbl ts)
  | Clight.Sgoto lbl =>
      OK (Sgoto lbl)
  end

with transl_lbl_stmt (tyret: type) (nbrk ncnt: nat)
                     (sl: Clight.labeled_statements)
                     {struct sl}: res lbl_stmt :=
  match sl with
  | Clight.LSdefault s =>
      do ts <- transl_statement tyret nbrk ncnt s;
      OK (LSdefault ts)
  | Clight.LScase n s sl' =>
      do ts <- transl_statement tyret nbrk ncnt s;
      do tsl' <- transl_lbl_stmt tyret nbrk ncnt sl';
      OK (LScase n ts tsl')
  end.

(*** Translation of functions *)

Definition transl_var (v: ident * type) := (fst v, sizeof (snd v)).

Definition signature_of_function (f: Clight.function) :=
  mksignature (map typ_of_type (map snd (Clight.fn_params f)))
              (opttyp_of_type (Clight.fn_return f)).

Definition transl_function (f: Clight.function) : res function :=
  do tbody <- transl_statement f.(Clight.fn_return) 1%nat 0%nat (Clight.fn_body f);
  OK (mkfunction 
       (signature_of_function f)
       (map fst (Clight.fn_params f))
       (map transl_var (Clight.fn_vars f))
       (map fst (Clight.fn_temps f))
       tbody).

Definition list_typ_eq: forall (l1 l2: list typ), {l1=l2} + {l1<>l2}
                     := list_eq_dec typ_eq.

Definition transl_fundef (f: Clight.fundef) : res fundef :=
  match f with
  | Clight.Internal g => 
      do tg <- transl_function g; OK(AST.Internal tg)
  | Clight.External ef args res =>
      if list_typ_eq (sig_args (ef_sig ef)) (typlist_of_typelist args)
      && opt_typ_eq (sig_res (ef_sig ef)) (opttyp_of_type res)
      then OK(AST.External ef)
      else Error(msg "Cshmgen.transl_fundef: wrong external signature")
  end.

(** ** Translation of programs *)

Definition transl_globvar (ty: type) := OK tt.

Definition transl_program (p: Clight.program) : res program :=
  transform_partial_program2 transl_fundef transl_globvar p.
