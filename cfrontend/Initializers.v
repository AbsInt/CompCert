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

Require Import Coqlib Maps Errors.
Require Import Integers Floats Values AST Memory Globalenvs.
Require Import Ctypes Cop Csyntax.

Open Scope error_monad_scope.

(** * Evaluation of compile-time constant expressions *)

(** To evaluate constant expressions at compile-time, we use the same [value]
  type and the same [sem_*] functions that are used in CompCert C's semantics
  (module [Csem]).  However, we interpret pointer values symbolically:
  [Vptr id ofs] represents the address of global variable [id]
  plus byte offset [ofs]. *)

(** [constval a] evaluates the constant expression [a].

If [a] is a r-value, the returned value denotes:
- [Vint n], [Vlong n], [Vfloat f], [Vsingle f]: the corresponding number
- [Vptr id ofs]: address of global variable [id] plus byte offset [ofs]
- [Vundef]: erroneous expression

If [a] is a l-value, the returned value denotes:
- [Vptr id ofs]: global variable [id] plus byte offset [ofs]
*)

Definition do_cast (v: val) (t1 t2: type) : res val :=
  match sem_cast v t1 t2 Mem.empty with
  | Some v' => OK v'
  | None => Error(msg "undefined cast")
  end.

Definition lookup_composite (ce: composite_env) (id: ident) : res composite :=
  match ce!id with
  | Some co => OK co
  | None => Error (MSG "Undefined struct or union " :: CTX id :: nil)
  end.

Fixpoint constval (ce: composite_env) (a: expr) : res val :=
  match a with
  | Eval v ty =>
      match v with
      | Vint _ | Vfloat _ | Vsingle _ | Vlong _ => OK v
      | Vptr _ _ | Vundef => Error(msg "illegal constant")
      end
  | Evalof l ty =>
      match access_mode ty with
      | By_reference | By_copy => constval ce l
      | _ => Error(msg "dereferencing of an l-value")
      end
  | Eaddrof l ty =>
      constval ce l
  | Eunop op r1 ty =>
      do v1 <- constval ce r1;
      match sem_unary_operation op v1 (typeof r1) Mem.empty with
      | Some v => OK v
      | None => Error(msg "undefined unary operation")
      end
  | Ebinop op r1 r2 ty =>
      do v1 <- constval ce r1;
      do v2 <- constval ce r2;
      match sem_binary_operation ce op v1 (typeof r1) v2 (typeof r2) Mem.empty with
      | Some v => OK v
      | None => Error(msg "undefined binary operation")
      end
  | Ecast r ty =>
      do v1 <- constval ce r; do_cast v1 (typeof r) ty
  | Esizeof ty1 ty =>
      OK (Vptrofs (Ptrofs.repr (sizeof ce ty1)))
  | Ealignof ty1 ty =>
      OK (Vptrofs (Ptrofs.repr (alignof ce ty1)))
  | Eseqand r1 r2 ty =>
      do v1 <- constval ce r1;
      do v2 <- constval ce r2;
      match bool_val v1 (typeof r1) Mem.empty with
      | Some true => do_cast v2 (typeof r2) type_bool
      | Some false => OK (Vint Int.zero)
      | None => Error(msg "undefined && operation")
      end
  | Eseqor r1 r2 ty =>
      do v1 <- constval ce r1;
      do v2 <- constval ce r2;
      match bool_val v1 (typeof r1) Mem.empty with
      | Some false => do_cast v2 (typeof r2) type_bool
      | Some true => OK (Vint Int.one)
      | None => Error(msg "undefined || operation")
      end
  | Econdition r1 r2 r3 ty =>
      do v1 <- constval ce r1;
      do v2 <- constval ce r2;
      do v3 <- constval ce r3;
      match bool_val v1 (typeof r1) Mem.empty with
      | Some true => do_cast v2 (typeof r2) ty
      | Some false => do_cast v3 (typeof r3) ty
      | None => Error(msg "condition is undefined")
      end
  | Ecomma r1 r2 ty =>
      do v1 <- constval ce r1; constval ce r2
  | Evar x ty =>
      OK(Vptr x Ptrofs.zero)
  | Ederef r ty =>
      constval ce r
  | Efield l f ty =>
      do (delta, bf) <-
        match typeof l with
        | Tstruct id _ =>
            do co <- lookup_composite ce id; field_offset ce f (co_members co)
        | Tunion id _ =>
            do co <- lookup_composite ce id; union_field_offset ce f (co_members co)
        | _ =>
            Error (msg "ill-typed field access")
        end;
      do v <- constval ce l;
      match bf with
      | Full =>
          OK (if Archi.ptr64
              then Val.addl v (Vlong (Int64.repr delta))
              else Val.add v (Vint (Int.repr delta)))
      | Bits _ _ _ _ =>
          Error(msg "taking the address of a bitfield")
      end
  | Eparen r tycast ty =>
      do v <- constval ce r; do_cast v (typeof r) tycast
  | _ =>
    Error(msg "not a compile-time constant")
  end.

(** [constval_cast ce a ty] evaluates [a] then converts its value to type [ty]. *)

Definition constval_cast (ce: composite_env) (a: expr) (ty: type): res val :=
  do v <- constval ce a; do_cast v (typeof a) ty.

(** * Building and recording initialization data *)

(** The following [state] type is the output of the translation of
    initializers.  It contains the list of initialization data
    generated so far, the corresponding position in bytes, and the
    total size expected for the final initialization data, in bytes. *)

Record state : Type := {
  init: list init_data;      (**r reversed *)
  curr: Z;                   (**r current position for head of [init] *)
  total_size: Z              (**r total expected size *)
}.

(** A state [s] can also be viewed as a memory block.  The size of
    the block is [s.(total_size)], it is initialized with zero bytes,
    then filled with the initialization data [rev s.(init)] like
    [Genv.store_init_data_list] does. *)

Definition initial_state (sz: Z) : state :=
  {| init := nil; curr := 0; total_size := sz |}.

(** We now define abstract "store" operations that operate
    directly on the state, but whose behavior mimic those of
    storing in the corresponding memory block.  To initialize
    bitfields, we also need an abstract "load" operation.
    The operations are optimized for stores that occur at increasing
    positions, like those that take place during initialization. *)

(** Initialization from bytes *)

Definition int_of_byte (b: byte) := Int.repr (Byte.unsigned b).

Definition Init_byte (b: byte) := Init_int8 (int_of_byte b).

(** Add a list of bytes to a reversed initialization data list. *)

Fixpoint add_rev_bytes (l: list byte) (il: list init_data) :=
  match l with
  | nil => il
  | b :: l => add_rev_bytes l (Init_byte b :: il)
  end.

(** Add [n] zero bytes to an initialization data list. *)

Definition add_zeros (n: Z) (il: list init_data) :=
  Z.iter n (fun l => Init_int8 Int.zero :: l) il.

(** Make sure the [depth] positions at the top of [il] are bytes,
    that is, [Init_int8] items.  Other numerical items are split
    into bytes.  [Init_addrof] items cannot be split and result in
    an error. *)

Fixpoint normalize (il: list init_data) (depth: Z) : res (list init_data) :=
  if zle depth 0 then OK il else
    match il with
    | nil =>
        Error (msg "normalize: empty list")
    | Init_int8 n :: il =>
        do il' <- normalize il (depth - 1);
        OK (Init_int8 n :: il')
    | Init_int16 n :: il =>
        do il' <- normalize il (depth - 2);
        OK (add_rev_bytes (encode_int 2%nat (Int.unsigned n)) il')
    | Init_int32 n :: il =>
        do il' <- normalize il (depth - 4);
        OK (add_rev_bytes (encode_int 4%nat (Int.unsigned n)) il')
    | Init_int64 n :: il =>
        do il' <- normalize il (depth - 8);
        OK (add_rev_bytes (encode_int 8%nat (Int64.unsigned n)) il')
    | Init_float32 f :: il =>
        do il' <- normalize il (depth - 4);
        OK (add_rev_bytes (encode_int 4%nat (Int.unsigned (Float32.to_bits f))) il')
    | Init_float64 f :: il =>
        do il' <- normalize il (depth - 8);
        OK (add_rev_bytes (encode_int 8%nat (Int64.unsigned (Float.to_bits f))) il')
    | Init_addrof _ _ :: il =>
        Error (msg "normalize: Init_addrof")
    | Init_space n :: il =>
        let n := Z.max 0 n in
        if zle n depth then
          do il' <- normalize il (depth - n);
          OK (add_zeros n il')
        else
          OK (add_zeros depth (Init_space (n - depth) :: il))
    end.

(** Split [il] into [depth] bytes and the initialization list that follows.
    The bytes are returned reversed. *)

Fixpoint decompose_rec (accu: list byte) (il: list init_data) (depth: Z) : res (list byte * list init_data) :=
  if zle depth 0 then OK (accu, il) else
    match il with
    | Init_int8 n :: il => decompose_rec (Byte.repr (Int.unsigned n) :: accu) il (depth - 1)
    | _ => Error (msg "decompose: wrong shape")
    end.

Definition decompose (il: list init_data) (depth: Z) : res (list byte * list init_data) :=
  decompose_rec nil il depth.

(** Decompose an initialization list in three parts:
    [depth] bytes (reversed), [sz] bytes (reversed),
    and the remainder of the initialization list. *)

Definition trisection (il: list init_data) (depth sz: Z) : res (list byte * list byte * list init_data) :=
  do il0 <- normalize il (depth + sz);
  do (bytes1, il1) <- decompose il0 depth;
  do (bytes2, il2) <- decompose il1 sz;
  OK (bytes1, bytes2, il2).

(** Graphically: [rev il] is equal to
<<
                 <---sz---><--depth-->
+----------------+---------+---------+
|                |         |         |
+----------------+---------+---------+
    rev il2         bytes2    bytes1
>>
*)

(** Add padding if necessary so that position [pos] is within the state. *)

Definition pad_to (s: state) (pos: Z) : state :=
  if zle pos s.(curr)
  then s
  else {| init := Init_space (pos - s.(curr)) :: s.(init);
          curr := pos;
          total_size := s.(total_size) |}.

(** Store the initialization data [i] at position [pos] in state [s]. *)

Definition store_data (s: state) (pos: Z) (i: init_data) : res state :=
  let sz := init_data_size i in
  assertion (zle 0 pos && zle (pos + sz) s.(total_size));
  if zle s.(curr) pos then
    OK {| init := i :: (if zlt s.(curr) pos
                        then Init_space (pos - s.(curr)) :: s.(init)
                        else s.(init));
          curr := pos + sz;
          total_size := s.(total_size) |}
  else
    let s' := pad_to s (pos + sz) in
    do x3 <- trisection s'.(init) (s'.(curr) - (pos + sz)) sz;
    let '(bytes1, _, il2) := x3 in
    OK {| init := add_rev_bytes bytes1 (i :: il2);
          curr := s'.(curr);
          total_size := s'.(total_size) |}.

(** Store the integer [n] of size [isz] at position [pos] in state [s]. *)

Definition init_data_for_carrier (isz: intsize) (n: int) :=
  match isz with
  | I8 | IBool => Init_int8 n
  | I16 => Init_int16 n
  | I32 => Init_int32 n
  end.

Definition store_int (s: state) (pos: Z) (isz: intsize) (n: int) : res state :=
  store_data s pos (init_data_for_carrier isz n).

(** Load the integer of size [isz] at position [pos] in state [s]. *)

Definition load_int (s: state) (pos: Z) (isz: intsize) : res int :=
  let chunk := chunk_for_carrier isz in
  let sz := size_chunk chunk in
  assertion (zle 0 pos && zle (pos + sz) s.(total_size));
  let s' := pad_to s (pos + sz) in
  do x3 <- trisection s'.(init) (s'.(curr) - (pos + sz)) sz;
  let '(_, bytes2, _) := x3 in
  OK (Int.repr (decode_int bytes2)).

(** Extract the final initialization data from a state. *)

Definition init_data_list_of_state (s: state) : res (list init_data) :=
  assertion (zle s.(curr) s.(total_size));
  let s' := pad_to s s.(total_size) in
  OK (List.rev' s'.(init)).

(** * Translation of initializers *)

Inductive initializer :=
  | Init_single (a: expr)
  | Init_array (il: initializer_list)
  | Init_struct (il: initializer_list)
  | Init_union (f: ident) (i: initializer)
with initializer_list :=
  | Init_nil
  | Init_cons (i: initializer) (il: initializer_list).

Definition length_initializer_list (il: initializer_list) :=
  let fix length (accu: Z) (il: initializer_list) : Z :=
    match il with Init_nil => accu | Init_cons _ il => length (Z.succ accu) il end
  in length 0 il.

(** Translate an initializing expression [a] for a scalar variable
  of type [ty].  Return the corresponding initialization datum. *)

Definition transl_init_single (ce: composite_env) (ty: type) (a: expr) : res init_data :=
  do v <- constval_cast ce a ty;
  match v, ty with
  | Vint n, Tint (I8|IBool) sg _ => OK(Init_int8 n)
  | Vint n, Tint I16 sg _ => OK(Init_int16 n)
  | Vint n, Tint I32 sg _ => OK(Init_int32 n)
  | Vint n, Tpointer _ _ => assertion (negb Archi.ptr64); OK(Init_int32 n)
  | Vlong n, Tlong _ _ => OK(Init_int64 n)
  | Vlong n, Tpointer _ _ => assertion (Archi.ptr64); OK(Init_int64 n)
  | Vsingle f, Tfloat F32 _ => OK(Init_float32 f)
  | Vfloat f, Tfloat F64 _ => OK(Init_float64 f)
  | Vptr id ofs, Tint I32 sg _ => assertion (negb Archi.ptr64); OK(Init_addrof id ofs)
  | Vptr id ofs, Tlong _ _ => assertion (Archi.ptr64); OK(Init_addrof id ofs)
  | Vptr id ofs, Tpointer _ _ => OK(Init_addrof id ofs)
  | Vundef, _ => Error(msg "undefined operation in initializer")
  | _, _ => Error (msg "type mismatch in initializer")
  end.

(** Initialize a bitfield [Bits sz sg p w] with expression [a]. *)

Definition transl_init_bitfield (ce: composite_env) (s: state)
                                (ty: type) (sz: intsize) (p w: Z)
                                (i: initializer) (pos: Z) : res state :=
  match i with
  | Init_single a =>
      do v <- constval_cast ce a ty;
      match v with
      | Vint n =>
          do c <- load_int s pos sz;
          let c' := Int.bitfield_insert (first_bit sz p w) w c n in
          store_int s pos sz c'
      | Vundef =>
          Error (msg "undefined operation in bitfield initializer")
      | _ =>
          Error (msg "type mismatch in bitfield initializer")
      end
  | _ =>
      Error (msg "bitfield initialized by composite initializer")
  end.

(** Padding bitfields and bitfields with zero width are not initialized. *)

Definition member_not_initialized (m: member) : bool :=
  match m with
  | Member_plain _ _ => false
  | Member_bitfield _ _ _ _ w p => p || zle w 0
  end.

(** Translate an initializer [i] for a variable of type [ty]
    and store the corresponding list of initialization data in state [s]
    at position [pos].  Return the updated state. *)

Fixpoint transl_init_rec (ce: composite_env) (s: state)
                         (ty: type) (i: initializer) (pos: Z)
                         {struct i} : res state :=
  match i, ty with
  | Init_single a, _ =>
      do d <- transl_init_single ce ty a; store_data s pos d
  | Init_array il, Tarray tyelt nelt _ =>
      assertion (zle (length_initializer_list il) (Z.max 0 nelt));
      transl_init_array ce s tyelt il pos
  | Init_struct il, Tstruct id _ =>
      do co <- lookup_composite ce id;
      match co_su co with
      | Struct => transl_init_struct ce s (co_members co) il pos 0
      | Union  => Error (MSG "struct/union mismatch on " :: CTX id :: nil)
      end
  | Init_union f i1, Tunion id _ =>
      do co <- lookup_composite ce id;
      match co_su co with
      | Struct => Error (MSG "union/struct mismatch on " :: CTX id :: nil)
      | Union =>  do ty1 <- field_type f (co_members co);
                  do (delta, layout) <- union_field_offset ce f (co_members co);
                  match layout with
                  | Full =>
                      transl_init_rec ce s ty1 i1 (pos + delta)
                  | Bits sz sg p w =>
                      transl_init_bitfield ce s ty1 sz p w i1 (pos + delta)
                  end
      end
  | _, _ =>
      Error (msg "wrong type for compound initializer")
  end

with transl_init_array (ce: composite_env) (s: state)
                       (tyelt: type) (il: initializer_list) (pos: Z)
                       {struct il} : res state :=
  match il with
  | Init_nil =>
      OK s
  | Init_cons i1 il' =>
      do s1 <- transl_init_rec ce s tyelt i1 pos;
      transl_init_array ce s1 tyelt il' (pos + sizeof ce tyelt)
  end

with transl_init_struct (ce: composite_env) (s: state)
                        (ms: members) (il: initializer_list)
                        (base: Z) (pos: Z)
                        {struct il} : res state :=
  match il with
  | Init_nil =>
      OK s
  | Init_cons i1 il' =>
      let fix init (ms: members) (pos: Z) {struct ms} : res state :=
        match ms with
        | nil =>
            Error (msg "too many elements in struct initializer")
        | m :: ms' =>
            if member_not_initialized m then
              init ms' (next_field ce pos m)
            else
              do (delta, layout) <- layout_field ce pos m;
              do s1 <-
                match layout with
                | Full =>
                    transl_init_rec ce s (type_member m) i1 (base + delta)
                | Bits sz sg p w =>
                    transl_init_bitfield ce s (type_member m) sz p w i1 (base + delta)
                end;
                transl_init_struct ce s1 ms' il' base (next_field ce pos m)
         end in
      init ms pos
  end.

(** The entry point. *)

Definition transl_init (ce: composite_env) (ty: type) (i: initializer)
                       : res (list init_data) :=
  let s0 := initial_state (sizeof ce ty) in
  do s1 <- transl_init_rec ce s0 ty i 0;
  init_data_list_of_state s1.
