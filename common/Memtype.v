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

(** This file defines the interface for the memory model that
  is used in the dynamic semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
*)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memdata.

(** Memory states are accessed by addresses [b, ofs]: pairs of a block
  identifier [b] and a byte offset [ofs] within that block.
  Each address is in one of the following five states:
- Freeable (exclusive access): all operations permitted
- Writable: load, store and pointer comparison operations are permitted,
  but freeing is not.
- Readable: only load and pointer comparison operations are permitted.
- Nonempty: valid, but only pointer comparisons are permitted.
- Empty: not yet allocated or previously freed; no operation permitted.

The first four cases are represented by the following type of permissions.
Being empty is represented by the absence of any permission.
*)

Inductive permission: Type :=
  | Freeable: permission
  | Writable: permission
  | Readable: permission
  | Nonempty: permission.

(** In the list, each permission implies the other permissions further down the
    list.  We reflect this fact by the following order over permissions. *)

Inductive perm_order: permission -> permission -> Prop :=
  | perm_refl:  forall p, perm_order p p
  | perm_F_any: forall p, perm_order Freeable p
  | perm_W_R:   perm_order Writable Readable
  | perm_any_N: forall p, perm_order p Nonempty.

Hint Constructors perm_order: mem.

Lemma perm_order_trans:
  forall p1 p2 p3, perm_order p1 p2 -> perm_order p2 p3 -> perm_order p1 p3.
Proof.
  intros. inv H; inv H0; constructor.
Qed.

Module Type MEM.

(** The abstract type of memory states. *)
Parameter mem: Type.

Definition nullptr: block := 0.

(** * Operations on memory states *)

(** [empty] is the initial memory state. *)
Parameter empty: mem.

(** [alloc m lo hi] allocates a fresh block of size [hi - lo] bytes.
  Valid offsets in this block are between [lo] included and [hi] excluded.
  These offsets are writable in the returned memory state.
  This block is not initialized: its contents are initially undefined.
  Returns a pair [(m', b)] of the updated memory state [m'] and
  the identifier [b] of the newly-allocated block.
  Note that [alloc] never fails: we are modeling an infinite memory. *)
Parameter alloc: forall (m: mem) (lo hi: Z), mem * block.

(** [free m b lo hi] frees (deallocates) the range of offsets from [lo]
  included to [hi] excluded in block [b].  Returns the updated memory
  state, or [None] if the freed addresses are not writable. *)
Parameter free: forall (m: mem) (b: block) (lo hi: Z), option mem.

(** [load chunk m b ofs] reads a memory quantity [chunk] from
  addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] in memory state
  [m].  Returns the value read, or [None] if the accessed addresses
  are not readable. *)
Parameter load: forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z), option val.

(** [store chunk m b ofs v] writes value [v] as memory quantity [chunk]
  from addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] in memory state
  [m].  Returns the updated memory state, or [None] if the accessed addresses
  are not writable. *)
Parameter store: forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val), option mem.

(** [loadv] and [storev] are variants of [load] and [store] where
  the address being accessed is passed as a value (of the [Vptr] kind). *)

Definition loadv (chunk: memory_chunk) (m: mem) (addr: val) : option val :=
  match addr with
  | Vptr b ofs => load chunk m b (Int.signed ofs)
  | _ => None
  end.

Definition storev (chunk: memory_chunk) (m: mem) (addr v: val) : option mem :=
  match addr with
  | Vptr b ofs => store chunk m b (Int.signed ofs) v
  | _ => None
  end.

(** [loadbytes m b ofs n] reads and returns the byte-level representation of
  the values contained at offsets [ofs] to [ofs + n - 1] within block [b]
  in memory state [m].
  [None] is returned if the accessed addresses are not readable. *)
Parameter loadbytes: forall (m: mem) (b: block) (ofs n: Z), option (list memval).

(** [free_list] frees all the given (block, lo, hi) triples. *)
Fixpoint free_list (m: mem) (l: list (block * Z * Z)) {struct l}: option mem :=
  match l with
  | nil => Some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi with
      | None => None
      | Some m' => free_list m' l'
      end
  end.

(** [drop_perm m b lo hi p] sets the permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have permissions
    at least [p] in the initial memory state [m].
    Returns updated memory state, or [None] if insufficient permissions. *)

Parameter drop_perm: forall (m: mem) (b: block) (lo hi: Z) (p: permission), option mem.

(** * Permissions, block validity, access validity, and bounds *)

(** The next block of a memory state is the block identifier for the
  next allocation.  It increases by one at each allocation.
  Block identifiers below [nextblock] are said to be valid, meaning
  that they have been allocated previously.  Block identifiers above
  [nextblock] are fresh or invalid, i.e. not yet allocated.  Note that
  a block identifier remains valid after a [free] operation over this
  block. *)

Parameter nextblock: mem -> block.
Axiom nextblock_pos:
  forall m, nextblock m > 0.

Definition valid_block (m: mem) (b: block) :=
  b < nextblock m.
Axiom valid_not_valid_diff:
  forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b'.

(** [perm m b ofs p] holds if the address [b, ofs] in memory state [m]
  has permission [p]: one of writable, readable, and nonempty.
  If the address is empty, [perm m b ofs p] is false for all values of [p]. *)
Parameter perm: forall (m: mem) (b: block) (ofs: Z) (p: permission), Prop.

(** Logical implications between permissions *)

Axiom perm_implies:
  forall m b ofs p1 p2, perm m b ofs p1 -> perm_order p1 p2 -> perm m b ofs p2.

(** Having a (nonempty) permission implies that the block is valid.
  In other words, invalid blocks, not yet allocated, are all empty. *)
Axiom perm_valid_block:
  forall m b ofs p, perm m b ofs p -> valid_block m b.

(* Unused?
(** The [Mem.perm] predicate is decidable. *)
Axiom perm_dec:
  forall m b ofs p, {perm m b ofs p} + {~ perm m b ofs p}.
*)

(** [range_perm m b lo hi p] holds iff the addresses [b, lo] to [b, hi-1]
  all have permission [p]. *)
Definition range_perm (m: mem) (b: block) (lo hi: Z) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm m b ofs p.

Axiom range_perm_implies:
  forall m b lo hi p1 p2,
  range_perm m b lo hi p1 -> perm_order p1 p2 -> range_perm m b lo hi p2.

(** An access to a memory quantity [chunk] at address [b, ofs] with
  permission [p] is valid in [m] if the accessed addresses all have
  permission [p] and moreover the offset is properly aligned. *)
Definition valid_access (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z) (p: permission): Prop :=
  range_perm m b ofs (ofs + size_chunk chunk) p
  /\ (align_chunk chunk | ofs).

Axiom valid_access_implies:
  forall m chunk b ofs p1 p2,
  valid_access m chunk b ofs p1 -> perm_order p1 p2 ->
  valid_access m chunk b ofs p2.

Axiom valid_access_valid_block:
  forall m chunk b ofs,
  valid_access m chunk b ofs Nonempty ->
  valid_block m b.

Axiom valid_access_perm:
  forall m chunk b ofs p,
  valid_access m chunk b ofs p ->
  perm m b ofs p.

(** [valid_pointer m b ofs] returns [true] if the address [b, ofs]
  is nonempty in [m] and [false] if it is empty. *)

Parameter valid_pointer: forall (m: mem) (b: block) (ofs: Z), bool.

Axiom valid_pointer_nonempty_perm:
  forall m b ofs,
  valid_pointer m b ofs = true <-> perm m b ofs Nonempty.
Axiom valid_pointer_valid_access:
  forall m b ofs,
  valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs Nonempty.

(** Each block has associated low and high bounds.  These are the bounds 
    that were given when the block was allocated.  *)

Parameter bounds: forall (m: mem) (b: block), Z*Z.

Notation low_bound m b := (fst(bounds m b)).
Notation high_bound m b := (snd(bounds m b)).

(** The crucial properties of bounds is that any offset below the low
    bound or above the high bound is empty. *)

Axiom perm_in_bounds:
  forall m b ofs p, perm m b ofs p -> low_bound m b <= ofs < high_bound m b.

Axiom range_perm_in_bounds:
  forall m b lo hi p, 
  range_perm m b lo hi p -> lo < hi ->
  low_bound m b <= lo /\ hi <= high_bound m b.

Axiom valid_access_in_bounds:
  forall m chunk b ofs p,
  valid_access m chunk b ofs p ->
  low_bound m b <= ofs /\ ofs + size_chunk chunk <= high_bound m b.

(** * Properties of the memory operations *)

(** ** Properties of the initial memory state. *)

Axiom nextblock_empty: nextblock empty = 1.
Axiom perm_empty: forall b ofs p, ~perm empty b ofs p.
Axiom valid_access_empty:
  forall chunk b ofs p, ~valid_access empty chunk b ofs p.

(** ** Properties of [load]. *)

(** A load succeeds if and only if the access is valid for reading *)
Axiom valid_access_load:
  forall m chunk b ofs,
  valid_access m chunk b ofs Readable ->
  exists v, load chunk m b ofs = Some v.
Axiom load_valid_access:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  valid_access m chunk b ofs Readable.

(** The value returned by [load] belongs to the type of the memory quantity
  accessed: [Vundef], [Vint] or [Vptr] for an integer quantity,
  [Vundef] or [Vfloat] for a float quantity. *)
Axiom load_type:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  Val.has_type v (type_of_chunk chunk).

(** For a small integer or float type, the value returned by [load]
  is invariant under the corresponding cast. *)
Axiom load_cast:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  match chunk with
  | Mint8signed => v = Val.sign_ext 8 v
  | Mint8unsigned => v = Val.zero_ext 8 v
  | Mint16signed => v = Val.sign_ext 16 v
  | Mint16unsigned => v = Val.zero_ext 16 v
  | Mfloat32 => v = Val.singleoffloat v
  | _ => True
  end.

Axiom load_int8_signed_unsigned:
  forall m b ofs,
  load Mint8signed m b ofs = option_map (Val.sign_ext 8) (load Mint8unsigned m b ofs).

Axiom load_int16_signed_unsigned:
  forall m b ofs,
  load Mint16signed m b ofs = option_map (Val.sign_ext 16) (load Mint16unsigned m b ofs).


(** ** Properties of [loadbytes]. *)

(** If [loadbytes] succeeds, the corresponding [load] succeeds and
  returns a value that is determined by the
  bytes read by [loadbytes]. *)
Axiom loadbytes_load:
  forall chunk m b ofs bytes,
  loadbytes m b ofs (size_chunk chunk) = Some bytes ->
  (align_chunk chunk | ofs) ->
  load chunk m b ofs = Some(decode_val chunk bytes).

(** Conversely, if [load] returns a value, the corresponding
  [loadbytes] succeeds and returns a list of bytes which decodes into the
  result of [load]. *)
Axiom load_loadbytes:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  exists bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes
             /\ v = decode_val chunk bytes.

(** [loadbytes] returns a list of length [n] (the number of bytes read). *)
Axiom loadbytes_length:
  forall m b ofs n bytes,
  loadbytes m b ofs n = Some bytes ->
  length bytes = nat_of_Z n.

(** Composing or decomposing [loadbytes] operations at adjacent addresses. *)
Axiom loadbytes_concat:
  forall m b ofs n1 n2 bytes1 bytes2,
  loadbytes m b ofs n1 = Some bytes1 ->
  loadbytes m b (ofs + n1) n2 = Some bytes2 ->
  n1 >= 0 -> n2 >= 0 ->
  loadbytes m b ofs (n1 + n2) = Some(bytes1 ++ bytes2).
Axiom loadbytes_split:
  forall m b ofs n1 n2 bytes,
  loadbytes m b ofs (n1 + n2) = Some bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2,
     loadbytes m b ofs n1 = Some bytes1 
  /\ loadbytes m b (ofs + n1) n2 = Some bytes2
  /\ bytes = bytes1 ++ bytes2.

(** ** Properties of [store]. *)

(** [store] preserves block validity, permissions, access validity, and bounds.
  Moreover, a [store] succeeds if and only if the corresponding access
  is valid for writing. *)

Axiom nextblock_store:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  nextblock m2 = nextblock m1.
Axiom store_valid_block_1:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b', valid_block m1 b' -> valid_block m2 b'.
Axiom store_valid_block_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b', valid_block m2 b' -> valid_block m1 b'.

Axiom perm_store_1:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b' ofs' p, perm m1 b' ofs' p -> perm m2 b' ofs' p.
Axiom perm_store_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b' ofs' p, perm m2 b' ofs' p -> perm m1 b' ofs' p.

Axiom valid_access_store:
  forall m1 chunk b ofs v,
  valid_access m1 chunk b ofs Writable ->
  { m2: mem | store chunk m1 b ofs v = Some m2 }.
Axiom store_valid_access_1:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
Axiom store_valid_access_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
Axiom store_valid_access_3:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  valid_access m1 chunk b ofs Writable.

Axiom bounds_store:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b', bounds m2 b' = bounds m1 b'.

(** Load-store properties. *)

Axiom load_store_similar:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  exists v', load chunk' m2 b ofs = Some v' /\ decode_encode_val v chunk chunk' v'.

Axiom load_store_same:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  Val.has_type v (type_of_chunk chunk) ->
  load chunk m2 b ofs = Some (Val.load_result chunk v).

Axiom load_store_other:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 b' ofs' = load chunk' m1 b' ofs'.

(** Integrity of pointer values. *)

Axiom load_store_pointer_overlap:
  forall chunk m1 b ofs v_b v_o m2 chunk' ofs' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs' = Some v ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v = Vundef.
Axiom load_store_pointer_mismatch:
  forall chunk m1 b ofs v_b v_o m2 chunk' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs = Some v ->
  chunk <> Mint32 \/ chunk' <> Mint32 ->
  v = Vundef.
Axiom load_pointer_store:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs' v_b v_o,
  load chunk' m2 b' ofs' = Some(Vptr v_b v_o) ->
  (chunk = Mint32 /\ v = Vptr v_b v_o /\ chunk' = Mint32 /\ b' = b /\ ofs' = ofs)
  \/ (b' <> b \/ ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs').

(** Load-store properties for [loadbytes]. *)

Axiom loadbytes_store_same:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  loadbytes m2 b ofs (size_chunk chunk) = Some(encode_val chunk v).
Axiom loadbytes_store_other:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b' ofs' n,
  b' <> b \/ n <= 0 \/ ofs' + n <= ofs \/ ofs + size_chunk chunk <= ofs' ->
  loadbytes m2 b' ofs' n = loadbytes m1 b' ofs' n.

(** [store] is insensitive to the signedness or the high bits of
  small integer quantities. *)

Axiom store_signed_unsigned_8:
  forall m b ofs v,
  store Mint8signed m b ofs v = store Mint8unsigned m b ofs v.
Axiom store_signed_unsigned_16:
  forall m b ofs v,
  store Mint16signed m b ofs v = store Mint16unsigned m b ofs v.
Axiom store_int8_zero_ext:
  forall m b ofs n,
  store Mint8unsigned m b ofs (Vint (Int.zero_ext 8 n)) =
  store Mint8unsigned m b ofs (Vint n).
Axiom store_int8_sign_ext:
  forall m b ofs n,
  store Mint8signed m b ofs (Vint (Int.sign_ext 8 n)) =
  store Mint8signed m b ofs (Vint n).
Axiom store_int16_zero_ext:
  forall m b ofs n,
  store Mint16unsigned m b ofs (Vint (Int.zero_ext 16 n)) =
  store Mint16unsigned m b ofs (Vint n).
Axiom store_int16_sign_ext:
  forall m b ofs n,
  store Mint16signed m b ofs (Vint (Int.sign_ext 16 n)) =
  store Mint16signed m b ofs (Vint n).
Axiom store_float32_truncate:
  forall m b ofs n,
  store Mfloat32 m b ofs (Vfloat (Float.singleoffloat n)) =
  store Mfloat32 m b ofs (Vfloat n).

(** ** Properties of [alloc]. *)

(** The identifier of the freshly allocated block is the next block
  of the initial memory state. *)

Axiom alloc_result:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  b = nextblock m1.

(** Effect of [alloc] on block validity. *)

Axiom nextblock_alloc:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  nextblock m2 = Zsucc (nextblock m1).

Axiom valid_block_alloc:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b', valid_block m1 b' -> valid_block m2 b'.
Axiom fresh_block_alloc:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  ~(valid_block m1 b).
Axiom valid_new_block:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  valid_block m2 b.
Axiom valid_block_alloc_inv:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b'.

(** Effect of [alloc] on permissions. *)

Axiom perm_alloc_1:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b' ofs p, perm m1 b' ofs p -> perm m2 b' ofs p.
Axiom perm_alloc_2:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall ofs, lo <= ofs < hi -> perm m2 b ofs Freeable.
Axiom perm_alloc_3:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall ofs p, ofs < lo \/ hi <= ofs -> ~perm m2 b ofs p.
Axiom perm_alloc_inv:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b' ofs p, 
  perm m2 b' ofs p ->
  if zeq b' b then lo <= ofs < hi else perm m1 b' ofs p.

(** Effect of [alloc] on access validity. *)

Axiom valid_access_alloc_other:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs p,
  valid_access m1 chunk b' ofs p ->
  valid_access m2 chunk b' ofs p.
Axiom valid_access_alloc_same:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk b ofs Freeable.
Axiom valid_access_alloc_inv:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs p,
  valid_access m2 chunk b' ofs p ->
  if eq_block b' b
  then lo <= ofs /\ ofs + size_chunk chunk <= hi /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk b' ofs p.

(** Effect of [alloc] on bounds. *)

Axiom bounds_alloc:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b', bounds m2 b' = if eq_block b' b then (lo, hi) else bounds m1 b'.

Axiom bounds_alloc_same:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  bounds m2 b = (lo, hi).

Axiom bounds_alloc_other:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b', b' <> b -> bounds m2 b' = bounds m1 b'.

(** Load-alloc properties. *)

Axiom load_alloc_unchanged:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs,
  valid_block m1 b' ->
  load chunk m2 b' ofs = load chunk m1 b' ofs.
Axiom load_alloc_other:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs v,
  load chunk m1 b' ofs = Some v ->
  load chunk m2 b' ofs = Some v.
Axiom load_alloc_same:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk ofs v,
  load chunk m2 b ofs = Some v ->
  v = Vundef.
Axiom load_alloc_same':
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  load chunk m2 b ofs = Some Vundef.

(** ** Properties of [free]. *)

(** [free] succeeds if and only if the correspond range of addresses
  has [Freeable] permission. *)

Axiom range_perm_free:
  forall m1 b lo hi,
  range_perm m1 b lo hi Freeable ->
  { m2: mem | free m1 b lo hi = Some m2 }.
Axiom free_range_perm:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  range_perm m1 bf lo hi Freeable.

(** Block validity is preserved by [free]. *)

Axiom nextblock_free:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  nextblock m2 = nextblock m1.
Axiom valid_block_free_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b, valid_block m1 b -> valid_block m2 b.
Axiom valid_block_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b, valid_block m2 b -> valid_block m1 b.

(** Effect of [free] on permissions. *)

Axiom perm_free_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b ofs p,
  b <> bf \/ ofs < lo \/ hi <= ofs ->
  perm m1 b ofs p ->
  perm m2 b ofs p.
Axiom perm_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall ofs p, lo <= ofs < hi -> ~ perm m2 bf ofs p.
Axiom perm_free_3:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b ofs p,
  perm m2 b ofs p -> perm m1 b ofs p.

(** Effect of [free] on access validity. *)

Axiom valid_access_free_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk b ofs p,
  valid_access m1 chunk b ofs p -> 
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  valid_access m2 chunk b ofs p.
Axiom valid_access_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk ofs p,
  lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
  ~(valid_access m2 chunk bf ofs p).
Axiom valid_access_free_inv_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk b ofs p,
  valid_access m2 chunk b ofs p ->
  valid_access m1 chunk b ofs p.
Axiom valid_access_free_inv_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk ofs p,
  valid_access m2 chunk bf ofs p ->
  lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs.

(** [free] preserves bounds. *)

Axiom bounds_free:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b, bounds m2 b = bounds m1 b.

(** Load-free properties *)

Axiom load_free:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk b ofs,
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  load chunk m2 b ofs = load chunk m1 b ofs.

(** ** Properties of [drop_perm]. *)

Axiom nextblock_drop:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  nextblock m' = nextblock m.

Axiom range_perm_drop_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  range_perm m b lo hi p.
Axiom range_perm_drop_2:
  forall m b lo hi p,
  range_perm m b lo hi p -> { m' | drop_perm m b lo hi p = Some m' }.

Axiom perm_drop_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall ofs, lo <= ofs < hi -> perm m' b ofs p.
Axiom perm_drop_2:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall ofs p', lo <= ofs < hi -> perm m' b ofs p' -> perm_order p p'.
Axiom perm_drop_3:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b' ofs p', b' <> b \/ ofs < lo \/ hi <= ofs -> perm m b' ofs p' -> perm m' b' ofs p'.
Axiom perm_drop_4:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b' ofs p', perm m' b' ofs p' -> perm m b' ofs p'.

Axiom bounds_drop:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b', bounds m' b' = bounds m b'.

Axiom load_drop:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall chunk b' ofs, 
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p Readable ->
  load chunk m' b' ofs = load chunk m b' ofs.

(** * Relating two memory states. *)

(** ** Memory extensions *)

(**  A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by relaxing the permissions of [m1] (for instance, allocating larger
  blocks) and replacing some of the [Vundef] values stored in [m1] by
  more defined values stored in [m2] at the same addresses. *)

Parameter extends: mem -> mem -> Prop.

Axiom extends_refl:
  forall m, extends m m.

Axiom load_extends:
  forall chunk m1 m2 b ofs v1,
  extends m1 m2 ->
  load chunk m1 b ofs = Some v1 ->
  exists v2, load chunk m2 b ofs = Some v2 /\ Val.lessdef v1 v2.

Axiom loadv_extends:
  forall chunk m1 m2 addr1 addr2 v1,
  extends m1 m2 ->
  loadv chunk m1 addr1 = Some v1 ->
  Val.lessdef addr1 addr2 ->
  exists v2, loadv chunk m2 addr2 = Some v2 /\ Val.lessdef v1 v2.

Axiom store_within_extends:
  forall chunk m1 m2 b ofs v1 m1' v2,
  extends m1 m2 ->
  store chunk m1 b ofs v1 = Some m1' ->
  Val.lessdef v1 v2 ->
  exists m2',
     store chunk m2 b ofs v2 = Some m2'
  /\ extends m1' m2'.

Axiom store_outside_extends:
  forall chunk m1 m2 b ofs v m2',
  extends m1 m2 ->
  store chunk m2 b ofs v = Some m2' ->
  ofs + size_chunk chunk <= low_bound m1 b \/ high_bound m1 b <= ofs ->
  extends m1 m2'.

Axiom storev_extends:
  forall chunk m1 m2 addr1 v1 m1' addr2 v2,
  extends m1 m2 ->
  storev chunk m1 addr1 v1 = Some m1' ->
  Val.lessdef addr1 addr2 ->
  Val.lessdef v1 v2 ->
  exists m2',
     storev chunk m2 addr2 v2 = Some m2'
  /\ extends m1' m2'.

Axiom alloc_extends:
  forall m1 m2 lo1 hi1 b m1' lo2 hi2,
  extends m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists m2',
     alloc m2 lo2 hi2 = (m2', b)
  /\ extends m1' m2'.

Axiom free_left_extends:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  extends m1' m2.

Axiom free_right_extends:
  forall m1 m2 b lo hi m2',
  extends m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall ofs p, lo <= ofs < hi -> ~perm m1 b ofs p) ->
  extends m1 m2'.

Axiom free_parallel_extends:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  exists m2',
     free m2 b lo hi = Some m2'
  /\ extends m1' m2'.

Axiom valid_block_extends:
  forall m1 m2 b,
  extends m1 m2 ->
  (valid_block m1 b <-> valid_block m2 b).
Axiom perm_extends:
  forall m1 m2 b ofs p,
  extends m1 m2 -> perm m1 b ofs p -> perm m2 b ofs p.
Axiom valid_access_extends:
  forall m1 m2 chunk b ofs p,
  extends m1 m2 -> valid_access m1 chunk b ofs p -> valid_access m2 chunk b ofs p.

(** * Memory injections *)

(** A memory injection [f] is a function from addresses to either [None]
  or [Some] of an address and an offset.  It defines a correspondence
  between the blocks of two memory states [m1] and [m2]:
- if [f b = None], the block [b] of [m1] has no equivalent in [m2];
- if [f b = Some(b', ofs)], the block [b] of [m2] corresponds to
  a sub-block at offset [ofs] of the block [b'] in [m2].

A memory injection [f] defines a relation [val_inject] between values
that is the identity for integer and float values, and relocates pointer 
values as prescribed by [f].  (See module [Values].)

Likewise, a memory injection [f] defines a relation between memory states 
that we now axiomatize. *)

Parameter inject: meminj -> mem -> mem -> Prop.

Axiom valid_block_inject_1:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m1 b1.

Axiom valid_block_inject_2:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m2 b2.

Axiom perm_inject:
  forall f m1 m2 b1 b2 delta ofs p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  perm m1 b1 ofs p -> perm m2 b2 (ofs + delta) p.

Axiom valid_access_inject:
  forall f m1 m2 chunk b1 ofs b2 delta p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_access m1 chunk b1 ofs p ->
  valid_access m2 chunk b2 (ofs + delta) p.

Axiom valid_pointer_inject:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_pointer m1 b1 ofs = true ->
  valid_pointer m2 b2 (ofs + delta) = true.

Axiom address_inject:
  forall f m1 m2 b1 ofs1 b2 delta,
  inject f m1 m2 ->
  perm m1 b1 (Int.signed ofs1) Nonempty ->
  f b1 = Some (b2, delta) ->
  Int.signed (Int.add ofs1 (Int.repr delta)) = Int.signed ofs1 + delta.

Axiom valid_pointer_inject_no_overflow:
  forall f m1 m2 b ofs b' x,
  inject f m1 m2 ->
  valid_pointer m1 b (Int.signed ofs) = true ->
  f b = Some(b', x) ->
  Int.min_signed <= Int.signed ofs + Int.signed (Int.repr x) <= Int.max_signed.

Axiom valid_pointer_inject_val:
  forall f m1 m2 b ofs b' ofs',
  inject f m1 m2 ->
  valid_pointer m1 b (Int.signed ofs) = true ->
  val_inject f (Vptr b ofs) (Vptr b' ofs') ->
  valid_pointer m2 b' (Int.signed ofs') = true.

Axiom inject_no_overlap:
  forall f m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2,
  inject f m1 m2 ->
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m1 b1 ofs1 Nonempty ->
  perm m1 b2 ofs2 Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.

Axiom different_pointers_inject:
  forall f m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  inject f m m' ->
  b1 <> b2 ->
  valid_pointer m b1 (Int.signed ofs1) = true ->
  valid_pointer m b2 (Int.signed ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Int.signed (Int.add ofs1 (Int.repr delta1)) <>
  Int.signed (Int.add ofs2 (Int.repr delta2)).

Axiom load_inject:
  forall f m1 m2 chunk b1 ofs b2 delta v1,
  inject f m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ val_inject f v1 v2.

Axiom loadv_inject:
  forall f m1 m2 chunk a1 a2 v1,
  inject f m1 m2 ->
  loadv chunk m1 a1 = Some v1 ->
  val_inject f a1 a2 ->
  exists v2, loadv chunk m2 a2 = Some v2 /\ val_inject f v1 v2.

Axiom store_mapped_inject:
  forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  val_inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ inject f n1 n2.

Axiom store_unmapped_inject:
  forall f chunk m1 b1 ofs v1 n1 m2,
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  inject f n1 m2.

Axiom store_outside_inject:
  forall f m1 m2 chunk b ofs v m2',
  inject f m1 m2 ->
  (forall b' delta,
    f b' = Some(b, delta) ->
    high_bound m1 b' + delta <= ofs
    \/ ofs + size_chunk chunk <= low_bound m1 b' + delta) ->
  store chunk m2 b ofs v = Some m2' ->
  inject f m1 m2'.

Axiom storev_mapped_inject:
  forall f chunk m1 a1 v1 n1 m2 a2 v2,
  inject f m1 m2 ->
  storev chunk m1 a1 v1 = Some n1 ->
  val_inject f a1 a2 ->
  val_inject f v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 = Some n2 /\ inject f n1 n2.

Axiom alloc_right_inject:
  forall f m1 m2 lo hi b2 m2',
  inject f m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  inject f m1 m2'.

Axiom alloc_left_unmapped_inject:
  forall f m1 m2 lo hi m1' b1,
  inject f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = None
  /\ (forall b, b <> b1 -> f' b = f b).

Definition inj_offset_aligned (delta: Z) (size: Z) : Prop :=
  forall chunk, size_chunk chunk <= size -> (align_chunk chunk | delta).

Axiom alloc_left_mapped_inject:
  forall f m1 m2 lo hi m1' b1 b2 delta,
  inject f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  Int.min_signed <= delta <= Int.max_signed ->
  delta = 0 \/ Int.min_signed <= low_bound m2 b2 /\ high_bound m2 b2 <= Int.max_signed ->
  (forall ofs p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) p) ->
  inj_offset_aligned delta (hi-lo) ->
  (forall b ofs, 
   f b = Some (b2, ofs) -> 
   high_bound m1 b + ofs <= lo + delta \/
   hi + delta <= low_bound m1 b + ofs) ->
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, delta)
  /\ (forall b, b <> b1 -> f' b = f b).

Axiom alloc_parallel_inject:
  forall f m1 m2 lo1 hi1 m1' b1 lo2 hi2,
  inject f m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b1) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists f', exists m2', exists b2,
  alloc m2 lo2 hi2 = (m2', b2)
  /\ inject f' m1' m2'
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, 0)
  /\ (forall b, b <> b1 -> f' b = f b).

Axiom free_inject:
  forall f m1 l m1' m2 b lo hi m2',
  inject f m1 m2 ->
  free_list m1 l = Some m1' ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs p -> lo <= ofs + delta < hi ->
    exists lo1, exists hi1, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
  inject f m1' m2'.

(** Memory states that inject into themselves. *)

Definition flat_inj (thr: block) : meminj :=
  fun (b: block) => if zlt b thr then Some(b, 0) else None.

Parameter inject_neutral: forall (thr: block) (m: mem), Prop.

Axiom neutral_inject:
  forall m, inject_neutral (nextblock m) m ->
  inject (flat_inj (nextblock m)) m m.

Axiom empty_inject_neutral:
  forall thr, inject_neutral thr empty.

Axiom alloc_inject_neutral:
  forall thr m lo hi b m',
  alloc m lo hi = (m', b) ->
  inject_neutral thr m ->
  nextblock m < thr ->
  inject_neutral thr m'.

Axiom store_inject_neutral:
  forall chunk m b ofs v m' thr,
  store chunk m b ofs v = Some m' ->
  inject_neutral thr m ->
  b < thr ->
  val_inject (flat_inj thr) v v ->
  inject_neutral thr m'.

Axiom drop_inject_neutral:
  forall m b lo hi p m' thr,
  drop_perm m b lo hi p = Some m' ->
  inject_neutral thr m ->
  b < thr ->
  inject_neutral thr m'.

End MEM.
