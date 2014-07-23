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
Require Import Globalenvs.
Require Import Ctypes.
Require Import Cop.
Require Import Csyntax.

Open Scope error_monad_scope.

(** * Evaluation of compile-time constant expressions *)

(** To evaluate constant expressions at compile-time, we use the same [value]
  type and the same [sem_*] functions that are used in CompCert C's semantics
  (module [Csem]).  However, we interpret pointer values symbolically:
  [Vptr id ofs] represents the address of global variable [id]
  plus byte offset [ofs]. *)

(** [constval a] evaluates the constant expression [a].

If [a] is a r-value, the returned value denotes:
- [Vint n], [Vfloat f]: the corresponding number
- [Vptr id ofs]: address of global variable [id] plus byte offset [ofs]
- [Vundef]: erroneous expression

If [a] is a l-value, the returned value denotes:
- [Vptr id ofs]: global variable [id] plus byte offset [ofs]
*)

Definition do_cast (v: val) (t1 t2: type) : res val :=
  match sem_cast v t1 t2 with
  | Some v' => OK v'
  | None => Error(msg "undefined cast")
  end.

Fixpoint constval (a: expr) : res val :=
  match a with
  | Eval v ty =>
      match v with
      | Vint _ | Vfloat _ | Vsingle _ | Vlong _ => OK v
      | Vptr _ _ | Vundef => Error(msg "illegal constant")
      end
  | Evalof l ty =>
      match access_mode ty with
      | By_reference | By_copy => constval l
      | _ => Error(msg "dereferencing of an l-value")
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
      do v1 <- constval r; do_cast v1 (typeof r) ty
  | Esizeof ty1 ty =>
      OK (Vint (Int.repr (sizeof ty1)))
  | Ealignof ty1 ty =>
      OK (Vint (Int.repr (alignof ty1)))
  | Eseqand r1 r2 ty =>
      do v1 <- constval r1;
      do v2 <- constval r2;
      match bool_val v1 (typeof r1) with
      | Some true => do v3 <- do_cast v2 (typeof r2) type_bool; do_cast v3 type_bool ty
      | Some false => OK (Vint Int.zero)
      | None => Error(msg "undefined && operation")
      end
  | Eseqor r1 r2 ty =>
      do v1 <- constval r1;
      do v2 <- constval r2;
      match bool_val v1 (typeof r1) with
      | Some false => do v3 <- do_cast v2 (typeof r2) type_bool; do_cast v3 type_bool ty
      | Some true => OK (Vint Int.one)
      | None => Error(msg "undefined || operation")
      end
  | Econdition r1 r2 r3 ty =>
      do v1 <- constval r1;
      do v2 <- constval r2;
      do v3 <- constval r3;
      match bool_val v1 (typeof r1) with
      | Some true => do_cast v2 (typeof r2) ty
      | Some false => do_cast v3 (typeof r3) ty
      | None => Error(msg "condition is undefined")
      end
  | Ecomma r1 r2 ty =>
      do v1 <- constval r1; constval r2
  | Evar x ty =>
      OK(Vptr x Int.zero)
  | Ederef r ty =>
      constval r
  | Efield l f ty =>
      match typeof l with
      | Tstruct id fList _ =>
          do delta <- field_offset f fList;
          do v <- constval l;
          OK (Val.add v (Vint (Int.repr delta)))
      | Tunion id fList _ =>
          constval l
      | _ =>
          Error(msg "ill-typed field access")
      end
  | Eparen r ty =>
      do v <- constval r; do_cast v (typeof r) ty
  | _ =>
    Error(msg "not a compile-time constant")
  end.

(** * Translation of initializers *)

Inductive initializer :=
  | Init_single (a: expr)
  | Init_array (il: initializer_list)
  | Init_struct (il: initializer_list)
  | Init_union (f: ident) (i: initializer)
with initializer_list :=
  | Init_nil
  | Init_cons (i: initializer) (il: initializer_list).

(** Translate an initializing expression [a] for a scalar variable
  of type [ty].  Return the corresponding initialization datum. *)

Definition transl_init_single (ty: type) (a: expr) : res init_data :=
  do v1 <- constval a;
  do v2 <- do_cast v1 (typeof a) ty;
  match v2, ty with
  | Vint n, Tint (I8|IBool) sg _ => OK(Init_int8 n)
  | Vint n, Tint I16 sg _ => OK(Init_int16 n)
  | Vint n, Tint I32 sg _ => OK(Init_int32 n)
  | Vint n, Tpointer _ _ => OK(Init_int32 n)
  | Vint n, Tcomp_ptr _ _ => OK(Init_int32 n)
  | Vlong n, Tlong _ _ => OK(Init_int64 n)
  | Vsingle f, Tfloat F32 _ => OK(Init_float32 f)
  | Vfloat f, Tfloat F64 _ => OK(Init_float64 f)
  | Vptr id ofs, Tint I32 sg _ => OK(Init_addrof id ofs)
  | Vptr id ofs, Tpointer _ _ => OK(Init_addrof id ofs)
  | Vptr id ofs, Tcomp_ptr _ _ => OK(Init_addrof id ofs)
  | Vundef, _ => Error(msg "undefined operation in initializer")
  | _, _ => Error (msg "type mismatch in initializer")
  end.

(** Translate an initializer [i] for a variable of type [ty].
  Return the corresponding list of initialization data. *)

Definition padding (frm to: Z) : list init_data :=
  if zlt frm to then Init_space (to - frm) :: nil else nil.

Fixpoint transl_init (ty: type) (i: initializer)
                     {struct i} : res (list init_data) :=
  match i, ty with
  | Init_single a, _ =>
      do d <- transl_init_single ty a; OK (d :: nil)
  | Init_array il, Tarray tyelt nelt _ =>
      transl_init_array tyelt il (Zmax 0 nelt)
  | Init_struct il, Tstruct id fl _ =>
      transl_init_struct id ty fl il 0
  | Init_union f i1, Tunion id fl _ =>
      do ty1 <- field_type f fl;
      do d <- transl_init ty1 i1;
      OK (d ++ padding (sizeof ty1) (sizeof ty))
  | _, _ =>
      Error (msg "wrong type for compound initializer")
  end

with transl_init_array (ty: type) (il: initializer_list) (sz: Z)
                       {struct il} : res (list init_data) :=
  match il with
  | Init_nil =>
      if zeq sz 0 then OK nil
      else if zle 0 sz then OK (Init_space (sz * sizeof ty) :: nil)
      else Error (msg "wrong number of elements in array initializer")
  | Init_cons i1 il' =>
      do d1 <- transl_init ty i1;
      do d2 <- transl_init_array ty il' (sz - 1);
      OK (d1 ++ d2)
  end

with transl_init_struct (id: ident) (ty: type)
                        (fl: fieldlist) (il: initializer_list) (pos: Z)
                        {struct il} : res (list init_data) :=
  match il, fl with
  | Init_nil, Fnil =>
      OK (padding pos (sizeof ty))
  | Init_cons i1 il', Fcons _ ty1 fl' =>
      let pos1 := align pos (alignof ty1) in
      do d1 <- transl_init ty1 i1;
      do d2 <- transl_init_struct id ty fl' il' (pos1 + sizeof ty1);
      OK (padding pos pos1 ++ d1 ++ d2)
  | _, _ =>
      Error (msg "wrong number of elements in struct initializer")
  end.


