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

(** Compile-time evaluation of initializers for global C variables. *)

Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Csyntax.
Require Import Csem.

Open Scope error_monad_scope.

(** * Evaluation of compile-time constant expressions *)

(** Computing the predicates [cast], [is_true], and [is_false]. *)

Definition bool_val (v: val) (t: type) : res bool :=
  match v, t with
  | Vint n, Tint sz sg => OK (negb (Int.eq n Int.zero))
  | Vint n, Tpointer t' => OK (negb (Int.eq n Int.zero))
  | Vptr b ofs, Tint sz sg => OK true
  | Vptr b ofs, Tpointer t' => OK true
  | Vfloat f, Tfloat sz => OK (negb(Float.cmp Ceq f Float.zero))
  | _, _ => Error(msg "undefined conditional")
  end.

Definition is_neutral_for_cast (t: type) : bool :=
  match t with
  | Tint I32 sg => true
  | Tpointer ty => true
  | Tarray ty sz => true
  | Tfunction targs tres => true
  | _ => false
  end.

Definition do_cast (v: val) (t1 t2: type) : res val :=
  match v, t1, t2 with
  | Vint i, Tint sz1 si1, Tint sz2 si2 =>
      OK (Vint (cast_int_int sz2 si2 i))
  | Vfloat f, Tfloat sz1, Tint sz2 si2 =>
      match cast_float_int si2 f with
      | Some i => OK (Vint (cast_int_int sz2 si2 i))
      | None => Error(msg "overflow in float-to-int cast")
      end
  | Vint i, Tint sz1 si1, Tfloat sz2 =>
      OK (Vfloat (cast_float_float sz2 (cast_int_float si1 i)))
  | Vfloat f, Tfloat sz1, Tfloat sz2 =>
      OK (Vfloat (cast_float_float sz2 f))
  | Vptr b ofs, _, _ =>
      if is_neutral_for_cast t1 && is_neutral_for_cast t2
      then OK(Vptr b ofs) else Error(msg "undefined cast")
  | Vint n, _, _ =>
      if is_neutral_for_cast t1 && is_neutral_for_cast t2
      then OK(Vint n) else Error(msg "undefined cast")
  | _, _, _ =>
      Error(msg "undefined cast")
  end.

(** To evaluate constant expressions at compile-time, we use the same [value]
  type and the same [sem_*] functions that are used in CompCert C's semantics
  (module [Csem]).  However, we interpret pointer values symbolically:
  [Vptr (Zpos id) ofs] represents the address of global variable [id]
  plus byte offset [ofs]. *)

(** [constval a] evaluates the constant expression [a].

If [a] is a r-value, the returned value denotes:
- [Vint n], [Vfloat f]: the corresponding number
- [Vptr id ofs]: address of global variable [id] plus byte offset [ofs]
- [Vundef]: erroneous expression

If [a] is a l-value, the returned value denotes:
- [Vptr id ofs]: global variable [id] plus byte offset [ofs]
*)

Fixpoint constval (a: expr) : res val :=
  match a with
  | Eval v ty =>
      match v with
      | Vint _ | Vfloat _ => OK v
      | Vptr _ _ | Vundef => Error(msg "illegal constant")
      end
  | Evalof l ty =>
      match access_mode ty with
      | By_reference => constval l
      | _ => Error(msg "dereference operation")
      end
  | Eaddrof l ty =>
      constval l
  | Eunop op r1 ty =>
      do v1 <- constval r1;
      match sem_unary_operation op v1 (typeof r1) with
      | Some v => OK v
      | None => Error(msg "undefined unary operation")
      end
  | Ebinop op r1 r2 ty =>
      do v1 <- constval r1;
      do v2 <- constval r2;
      match sem_binary_operation op v1 (typeof r1) v2 (typeof r2) Mem.empty with
      | Some v => OK v
      | None => Error(msg "undefined binary operation")
      end
  | Ecast r ty =>
      do v <- constval r; do_cast v (typeof r) ty
  | Esizeof ty1 ty =>
      OK (Vint (Int.repr (sizeof ty1)))
  | Econdition r1 r2 r3 ty =>
      do v1 <- constval r1;
      do b1 <- bool_val v1 (typeof r1);
      do v2 <- constval r2;
      do v3 <- constval r3;
      OK (if b1 then v2 else v3)
  | Ecomma r1 r2 ty =>
      do v1 <- constval r1; constval r2
  | Evar x ty =>
      OK(Vptr (Zpos x) Int.zero)
  | Ederef r ty =>
      constval r
  | Efield l f ty =>
      match typeof l with
      | Tstruct id fList =>
          do delta <- field_offset f fList;
          do v <- constval l;
          OK (Val.add v (Vint (Int.repr delta)))
      | Tunion id fList =>
          constval l
      | _ =>
          Error(msg "ill-typed field access")
      end
  | Eparen r ty =>
      constval r
  | _ =>
    Error(msg "not a compile-time constant")
  end.

(** * Translation of initializers *)

(** Translate an initializing expression [a] for a scalar variable
  of type [ty].  Return the corresponding [init_data]. *)

Definition transl_init_single (ty: type) (a: expr) : res init_data :=
  do v1 <- constval a;
  do v2 <- do_cast v1 (typeof a) ty;
  match v2, ty with
  | Vint n, Tint I8 sg => OK(Init_int8 n)
  | Vint n, Tint I16 sg => OK(Init_int16 n)
  | Vint n, Tint I32 sg => OK(Init_int32 n)
  | Vint n, Tpointer _ => OK(Init_int32 n)
  | Vfloat f, Tfloat F32 => OK(Init_float32 f)
  | Vfloat f, Tfloat F64 => OK(Init_float64 f)
  | Vptr (Zpos id) ofs, Tint I32 sg => OK(Init_addrof id ofs)
  | Vptr (Zpos id) ofs, Tpointer _ => OK(Init_addrof id ofs)
  | Vundef, _ => Error(msg "undefined operation in initializer")
  | _, _ => Error (msg "type mismatch in initializer")
  end.

(** To come later: translation of compound initializers, currently
  still done in Caml (module [C2C]). *)

