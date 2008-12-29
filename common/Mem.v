(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** This file develops the memory model that is used in the dynamic
  semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
*)
  
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.

Definition update (A: Set) (x: Z) (v: A) (f: Z -> A) : Z -> A :=
  fun y => if zeq y x then v else f y.

Implicit Arguments update [A].

Lemma update_s:
  forall (A: Set) (x: Z) (v: A) (f: Z -> A),
  update x v f x = v.
Proof.
  intros; unfold update. apply zeq_true.
Qed.

Lemma update_o:
  forall (A: Set) (x: Z) (v: A) (f: Z -> A) (y: Z),
  x <> y -> update x v f y = f y.
Proof.
  intros; unfold update. apply zeq_false; auto.
Qed.

(** * Structure of memory states *)

(** A memory state is organized in several disjoint blocks.  Each block
  has a low and a high bound that defines its size.  Each block map
  byte offsets to the contents of this byte. *)

(** The possible contents of a byte-sized memory cell.  To give intuitions,
  a 4-byte value [v] stored at offset [d] will be represented by
  the content [Datum(4, v)] at offset [d] and [Cont] at offsets [d+1],
  [d+2] and [d+3].  The [Cont] contents enable detecting future writes
  that would partially overlap the 4-byte value. *)

Inductive content : Set :=
  | Undef: content                 (**r undefined contents *)
  | Datum: nat -> val -> content   (**r first byte of a value *)
  | Cont: content.          (**r continuation bytes for a multi-byte value *)

Definition contentmap : Set := Z -> content.

(** A memory block comprises the dimensions of the block (low and high bounds)
  plus a mapping from byte offsets to contents.  *)

Record block_contents : Set := mkblock {
  low: Z;
  high: Z;
  contents: contentmap
}.

(** A memory state is a mapping from block addresses (represented by [Z]
  integers) to blocks.  We also maintain the address of the next 
  unallocated block, and a proof that this address is positive. *)

Record mem : Set := mkmem {
  blocks: Z -> block_contents;
  nextblock: block;
  nextblock_pos: nextblock > 0
}.

(** * Operations on memory stores *)

(** Memory reads and writes are performed by quantities called memory chunks,
  encoding the type, size and signedness of the chunk being addressed.
  The following functions extract the size information from a chunk. *)

Definition size_chunk (chunk: memory_chunk) : Z :=
  match chunk with
  | Mint8signed => 1
  | Mint8unsigned => 1
  | Mint16signed => 2
  | Mint16unsigned => 2
  | Mint32 => 4
  | Mfloat32 => 4
  | Mfloat64 => 8
  end.

Definition pred_size_chunk (chunk: memory_chunk) : nat :=
  match chunk with
  | Mint8signed => 0%nat
  | Mint8unsigned => 0%nat
  | Mint16signed => 1%nat
  | Mint16unsigned => 1%nat
  | Mint32 => 3%nat
  | Mfloat32 => 3%nat
  | Mfloat64 => 7%nat
  end.

Lemma size_chunk_pred:
  forall chunk, size_chunk chunk = 1 + Z_of_nat (pred_size_chunk chunk).
Proof.
  destruct chunk; auto.
Qed.

(** The initial store. *)

Remark one_pos: 1 > 0.
Proof. omega. Qed.

Definition empty_block (lo hi: Z) : block_contents :=
  mkblock lo hi (fun y => Undef).

Definition empty: mem :=
  mkmem (fun x => empty_block 0 0) 1 one_pos.

Definition nullptr: block := 0.

(** Allocation of a fresh block with the given bounds.  Return an updated
  memory state and the address of the fresh block, which initially contains
  undefined cells.  Note that allocation never fails: we model an
  infinite memory. *)

Remark succ_nextblock_pos:
  forall m, Zsucc m.(nextblock) > 0.
Proof. intro. generalize (nextblock_pos m). omega. Qed.

Definition alloc (m: mem) (lo hi: Z) :=
  (mkmem (update m.(nextblock) 
                 (empty_block lo hi)
                 m.(blocks))
         (Zsucc m.(nextblock))
         (succ_nextblock_pos m),
   m.(nextblock)).

(** Freeing a block.  Return the updated memory state where the given
  block address has been invalidated: future reads and writes to this
  address will fail.  Note that we make no attempt to return the block
  to an allocation pool: the given block address will never be allocated
  later. *)

Definition free (m: mem) (b: block) :=
  mkmem (update b 
                (empty_block 0 0)
                m.(blocks))
        m.(nextblock)
        m.(nextblock_pos).

(** Freeing of a list of blocks. *)

Definition free_list (m:mem) (l:list block) :=
  List.fold_right (fun b m => free m b) m l.

(** Return the low and high bounds for the given block address.
   Those bounds are 0 for freed or not yet allocated address. *)

Definition low_bound (m: mem) (b: block) :=
  low (m.(blocks) b).
Definition high_bound (m: mem) (b: block) :=
  high (m.(blocks) b).

(** A block address is valid if it was previously allocated. It remains valid
  even after being freed. *)

Definition valid_block (m: mem) (b: block) :=
  b < m.(nextblock).

(** Reading and writing [N] adjacent locations in a [contentmap].

  We define two functions and prove some of their properties:
  - [getN n ofs m] returns the datum at offset [ofs] in block contents [m]
    after checking that the contents of offsets [ofs+1] to [ofs+n+1]
    are [Cont].
  - [setN n ofs v m] updates the block contents [m], storing the content [v]
    at offset [ofs] and the content [Cont] at offsets [ofs+1] to [ofs+n+1].
 *)

Fixpoint check_cont (n: nat) (p: Z) (m: contentmap) {struct n} : bool :=
  match n with
  | O => true
  | S n1 =>
      match m p with
      | Cont => check_cont n1 (p + 1) m
      | _ => false
      end
  end.

Definition eq_nat: forall (p q: nat), {p=q} + {p<>q}.
Proof. decide equality. Defined.

Definition getN (n: nat) (p: Z) (m: contentmap) : val :=
  match m p with
  | Datum n' v =>
      if eq_nat n n' && check_cont n (p + 1) m then v else Vundef
  | _ =>
      Vundef
  end.

Fixpoint set_cont (n: nat) (p: Z) (m: contentmap) {struct n} : contentmap :=
  match n with
  | O => m
  | S n1 => update p Cont (set_cont n1 (p + 1) m)
  end.

Definition setN (n: nat) (p: Z) (v: val) (m: contentmap) : contentmap :=
  update p (Datum n v) (set_cont n (p + 1) m).

Lemma check_cont_spec:
  forall n m p,
  if check_cont n p m
  then (forall q, p <= q < p + Z_of_nat n -> m q = Cont)
  else (exists q, p <= q < p + Z_of_nat n /\ m q <> Cont).
Proof.
  induction n; intros.
  simpl. intros; omegaContradiction.
  simpl check_cont. repeat rewrite inj_S. caseEq (m p); intros.
  exists p; split. omega. congruence.
  exists p; split. omega. congruence.
  generalize (IHn m (p + 1)). case (check_cont n (p + 1) m).
  intros. assert (p = q \/ p + 1 <= q < p + Zsucc (Z_of_nat n)) by omega.
  elim H2; intro. congruence. apply H0; omega.
  intros [q [A B]]. exists q; split. omega. auto.
Qed.

Lemma check_cont_true:
  forall n m p,
  (forall q, p <= q < p + Z_of_nat n -> m q = Cont) ->
  check_cont n p m = true.
Proof.
  intros. generalize (check_cont_spec n m p). 
  destruct (check_cont n p m). auto. 
  intros [q [A B]]. elim B; auto.
Qed.

Lemma check_cont_false:
  forall n m p q,
  p <= q < p + Z_of_nat n -> m q <> Cont ->
  check_cont n p m = false.
Proof.
  intros. generalize (check_cont_spec n m p). 
  destruct (check_cont n p m).
  intros. elim H0; auto. 
  auto.
Qed.

Lemma set_cont_inside:
  forall n p m q,
  p <= q < p + Z_of_nat n ->
  (set_cont n p m) q = Cont.
Proof.
  induction n; intros.
  unfold Z_of_nat in H. omegaContradiction.
  simpl. 
  assert (p = q \/ p + 1 <= q < (p + 1) + Z_of_nat n).
    rewrite inj_S in H. omega. 
  elim H0; intro.
  subst q. apply update_s.
  rewrite update_o. apply IHn. auto. 
  red; intro; subst q. omega. 
Qed.

Lemma set_cont_outside:
  forall n p m q,
  q < p \/ p + Z_of_nat n <= q ->
  (set_cont n p m) q = m q.
Proof.
  induction n; intros.
  simpl. auto.
  simpl. rewrite inj_S in H. 
  rewrite update_o. apply IHn. omega. omega.
Qed.

Lemma getN_setN_same:
  forall n p v m,
  getN n p (setN n p v m) = v.
Proof.
  intros. unfold getN, setN. rewrite update_s.
  rewrite check_cont_true. unfold proj_sumbool.
  rewrite dec_eq_true. auto.
  intros. rewrite update_o. apply set_cont_inside. auto.
  omega. 
Qed.

Lemma getN_setN_other:
  forall n1 n2 p1 p2 v m,
  p1 + Z_of_nat n1 < p2 \/ p2 + Z_of_nat n2 < p1 ->
  getN n2 p2 (setN n1 p1 v m) = getN n2 p2 m.
Proof.
  intros. unfold getN, setN.
  generalize (check_cont_spec n2 m (p2 + 1));
  destruct (check_cont n2 (p2 + 1) m); intros.
  rewrite check_cont_true. 
  rewrite update_o. rewrite set_cont_outside. auto.
  omega. omega. 
  intros. rewrite update_o. rewrite set_cont_outside. auto.
  omega. omega.
  destruct H0 as [q [A B]].
  rewrite (check_cont_false n2 (update p1 (Datum n1 v) (set_cont n1 (p1 + 1) m)) (p2 + 1) q).
  rewrite update_o. rewrite set_cont_outside. auto.
  omega. omega. omega. 
  rewrite update_o. rewrite set_cont_outside. auto. 
  omega. omega.
Qed.

Lemma getN_setN_overlap:
  forall n1 n2 p1 p2 v m,
  p1 <> p2 ->
  p1 + Z_of_nat n1 >= p2 -> p2 + Z_of_nat n2 >= p1 ->
  getN n2 p2 (setN n1 p1 v m) = Vundef.
Proof.
  intros. unfold getN, setN.
  rewrite update_o; auto. 
  destruct (zlt p2 p1).
  (* [p1] belongs to [[p2, p2 + n2 - 1]], 
     therefore [check_cont n2 (p2 + 1) ...] is false. *)
  rewrite (check_cont_false n2 (update p1 (Datum n1 v) (set_cont n1 (p1 + 1) m)) (p2 + 1) p1).
  destruct (set_cont n1 (p1 + 1) m p2); auto.
  destruct (eq_nat n2 n); auto.
  omega.
  rewrite update_s. congruence.
  (* [p2] belongs to [[p1 + 1, p1 + n1 - 1]],
     therefore [set_cont n1 (p1 + 1) m p2] is [Cont]. *)
  rewrite set_cont_inside. auto. omega.
Qed.

Lemma getN_setN_mismatch:
  forall n1 n2 p v m,
  n1 <> n2 ->
  getN n2 p (setN n1 p v m) = Vundef.
Proof.
  intros. unfold getN, setN. rewrite update_s. 
  unfold proj_sumbool; rewrite dec_eq_false; simpl. auto. auto.
Qed.

Lemma getN_setN_characterization:
  forall m v n1 p1 n2 p2,
  getN n2 p2 (setN n1 p1 v m) = v
  \/ getN n2 p2 (setN n1 p1 v m) = getN n2 p2 m
  \/ getN n2 p2 (setN n1 p1 v m) = Vundef.
Proof.
  intros. destruct (zeq p1 p2). subst p2.
  destruct (eq_nat n1 n2). subst n2.
  left; apply getN_setN_same.
  right; right; apply getN_setN_mismatch; auto.
  destruct (zlt (p1 + Z_of_nat n1) p2).
  right; left; apply getN_setN_other; auto.
  destruct (zlt (p2 + Z_of_nat n2) p1).
  right; left; apply getN_setN_other; auto.
  right; right; apply getN_setN_overlap; omega.
Qed.

Lemma getN_init:
  forall n p,
  getN n p (fun y => Undef) = Vundef.
Proof.
  intros. auto.
Qed.

(** [valid_access m chunk b ofs] holds if a memory access (load or store)
    of the given chunk is possible in [m] at address [b, ofs]. *)

Inductive valid_access (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z) : Prop :=
  | valid_access_intro:
      valid_block m b ->
      low_bound m b <= ofs ->
      ofs + size_chunk chunk <= high_bound m b ->
      valid_access m chunk b ofs.

(** The following function checks whether accessing the given memory chunk
  at the given offset in the given block respects the bounds of the block. *)

Definition in_bounds (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z) :
           {valid_access m chunk b ofs} + {~valid_access m chunk b ofs}.
Proof.
  intros.
  destruct (zlt b m.(nextblock)).
  destruct (zle (low_bound m b) ofs).
  destruct (zle (ofs + size_chunk chunk) (high_bound m b)).
  left; constructor; auto.
  right; red; intro V; inv V; omega.
  right; red; intro V; inv V; omega.
  right; red; intro V; inv V; contradiction.
Defined.

Lemma in_bounds_true:
  forall m chunk b ofs (A: Set) (a1 a2: A),
  valid_access m chunk b ofs ->
  (if in_bounds m chunk b ofs then a1 else a2) = a1.
Proof.
  intros. destruct (in_bounds m chunk b ofs). auto. contradiction.
Qed.

(** [valid_pointer] holds if the given block address is valid and the
  given offset falls within the bounds of the corresponding block. *)

Definition valid_pointer (m: mem) (b: block) (ofs: Z) : bool :=
  zlt b m.(nextblock) &&
  zle (low_bound m b) ofs &&
  zlt ofs (high_bound m b).

(** [load chunk m b ofs] perform a read in memory state [m], at address
  [b] and offset [ofs].  [None] is returned if the address is invalid
  or the memory access is out of bounds. *)

Definition load (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z)
                : option val :=
  if in_bounds m chunk b ofs then
    Some (Val.load_result chunk
           (getN (pred_size_chunk chunk) ofs (contents (blocks m b))))
  else
    None.

Lemma load_inv:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  valid_access m chunk b ofs /\
  v = Val.load_result chunk
           (getN (pred_size_chunk chunk) ofs (contents (blocks m b))).
Proof.
  intros until v; unfold load.
  destruct (in_bounds m chunk b ofs); intros.
  split. auto. congruence.
  congruence.
Qed. 

(** [loadv chunk m addr] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

Definition loadv (chunk: memory_chunk) (m: mem) (addr: val) : option val :=
  match addr with
  | Vptr b ofs => load chunk m b (Int.signed ofs)
  | _ => None
  end.

(* The memory state [m] after a store of value [v] at offset [ofs]
   in block [b]. *)

Definition unchecked_store
     (chunk: memory_chunk) (m: mem) (b: block)
     (ofs: Z) (v: val) : mem :=
  let c := m.(blocks) b in
  mkmem
    (update b
        (mkblock c.(low) c.(high)
                 (setN (pred_size_chunk chunk) ofs v c.(contents)))
        m.(blocks))
    m.(nextblock)
    m.(nextblock_pos).

(** [store chunk m b ofs v] perform a write in memory state [m].
  Value [v] is stored at address [b] and offset [ofs].
  Return the updated memory store, or [None] if the address is invalid
  or the memory access is out of bounds. *)

Definition store (chunk: memory_chunk) (m: mem) (b: block)
                 (ofs: Z) (v: val) : option mem :=
  if in_bounds m chunk b ofs
  then Some(unchecked_store chunk m b ofs v)
  else None.

Lemma store_inv:
  forall chunk m b ofs v m',
  store chunk m b ofs v = Some m' ->
  valid_access m chunk b ofs /\
  m' = unchecked_store chunk m b ofs v.
Proof.
  intros until m'; unfold store.
  destruct (in_bounds m chunk b ofs); intros.
  split. auto. congruence.
  congruence.
Qed.

(** [storev chunk m addr v] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

Definition storev (chunk: memory_chunk) (m: mem) (addr v: val) : option mem :=
  match addr with
  | Vptr b ofs => store chunk m b (Int.signed ofs) v
  | _ => None
  end.

(** Build a block filled with the given initialization data. *)

Fixpoint contents_init_data (pos: Z) (id: list init_data) {struct id}: contentmap :=
  match id with
  | nil => (fun y => Undef)
  | Init_int8 n :: id' =>
      setN 0%nat pos (Vint n) (contents_init_data (pos + 1) id')
  | Init_int16 n :: id' =>
      setN 1%nat pos (Vint n) (contents_init_data (pos + 1) id')
  | Init_int32 n :: id' =>
      setN 3%nat pos (Vint n) (contents_init_data (pos + 1) id')
  | Init_float32 f :: id' =>
      setN 3%nat pos (Vfloat f) (contents_init_data (pos + 1) id')
  | Init_float64 f :: id' =>
      setN 7%nat pos (Vfloat f) (contents_init_data (pos + 1) id')
  | Init_space n :: id' =>
      contents_init_data (pos + Zmax n 0) id'
  | Init_pointer x :: id' =>
      (* Not handled properly yet *)
      contents_init_data (pos + 4) id'
  end.

Definition size_init_data (id: init_data) : Z :=
  match id with
  | Init_int8 _ => 1
  | Init_int16 _ => 2
  | Init_int32 _ => 4
  | Init_float32 _ => 4
  | Init_float64 _ => 8
  | Init_space n => Zmax n 0
  | Init_pointer _ => 4
  end.

Definition size_init_data_list (id: list init_data): Z :=
  List.fold_right (fun id sz => size_init_data id + sz) 0 id.

Remark size_init_data_list_pos:
  forall id, size_init_data_list id >= 0.
Proof.
  induction id; simpl.
  omega.
  assert (size_init_data a >= 0). destruct a; simpl; try omega. 
  generalize (Zmax2 z 0). omega. omega.
Qed.

Definition block_init_data (id: list init_data) : block_contents :=
  mkblock 0 (size_init_data_list id) (contents_init_data 0 id).

Definition alloc_init_data (m: mem) (id: list init_data) : mem * block :=
  (mkmem (update m.(nextblock)
                 (block_init_data id)
                 m.(blocks))
         (Zsucc m.(nextblock))
         (succ_nextblock_pos m),
   m.(nextblock)).

Remark block_init_data_empty:
  block_init_data nil = empty_block 0 0.
Proof.
  auto.
Qed.

(** * Properties of the memory operations *)

(** ** Properties related to block validity *)

Lemma valid_not_valid_diff:
  forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b'.
Proof.
  intros; red; intros. subst b'. contradiction.
Qed.

Lemma valid_access_valid_block:
  forall m chunk b ofs,
  valid_access m chunk b ofs -> valid_block m b.
Proof.
  intros. inv H; auto.
Qed.

Hint Resolve valid_not_valid_diff valid_access_valid_block: mem.

(** ** Properties related to [load] *)

Theorem valid_access_load:
  forall m chunk b ofs,
  valid_access m chunk b ofs ->
  exists v, load chunk m b ofs = Some v.
Proof.
  intros. econstructor. unfold load. rewrite in_bounds_true; auto.
Qed.

Theorem load_valid_access:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  valid_access m chunk b ofs.
Proof.
  intros. generalize (load_inv _ _ _ _ _ H). tauto.
Qed.

Hint Resolve load_valid_access valid_access_load.

(** ** Properties related to [store] *)

Lemma valid_access_store:
  forall m1 chunk b ofs v,
  valid_access m1 chunk b ofs ->
  exists m2, store chunk m1 b ofs v = Some m2.
Proof.
  intros. econstructor. unfold store. rewrite in_bounds_true; auto. 
Qed.

Hint Resolve valid_access_store: mem.

Section STORE.
Variable chunk: memory_chunk.
Variable m1: mem.
Variable b: block.
Variable ofs: Z.
Variable v: val.
Variable m2: mem.
Hypothesis STORE: store chunk m1 b ofs v = Some m2.

Lemma low_bound_store:
  forall b', low_bound m2 b' = low_bound m1 b'.
Proof.
  intro. elim (store_inv _ _ _ _ _ _ STORE); intros. 
  subst m2. unfold low_bound, unchecked_store; simpl.
  unfold update. destruct (zeq b' b); auto. subst b'; auto.
Qed.

Lemma high_bound_store:
  forall b', high_bound m2 b' = high_bound m1 b'.
Proof.
  intro. elim (store_inv _ _ _ _ _ _ STORE); intros. 
  subst m2. unfold high_bound, unchecked_store; simpl.
  unfold update. destruct (zeq b' b); auto. subst b'; auto.
Qed.

Lemma nextblock_store:
  nextblock m2 = nextblock m1.
Proof.
 intros. elim (store_inv _ _ _ _ _ _ STORE); intros. 
  subst m2; reflexivity.
Qed.

Lemma store_valid_block_1:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_store; auto.
Qed.

Lemma store_valid_block_2:
  forall b', valid_block m2 b' -> valid_block m1 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_store in H; auto.
Qed.

Hint Resolve store_valid_block_1 store_valid_block_2: mem.

Lemma store_valid_access_1:
  forall chunk' b' ofs',
  valid_access m1 chunk' b' ofs' -> valid_access m2 chunk' b' ofs'.
Proof.
  intros. inv H. constructor. auto with mem. 
  rewrite low_bound_store; auto.
  rewrite high_bound_store; auto.
Qed.

Lemma store_valid_access_2:
  forall chunk' b' ofs',
  valid_access m2 chunk' b' ofs' -> valid_access m1 chunk' b' ofs'.
Proof.
  intros. inv H. constructor. auto with mem. 
  rewrite low_bound_store in H1; auto.
  rewrite high_bound_store in H2; auto.
Qed.

Lemma store_valid_access_3:
  valid_access m1 chunk b ofs.
Proof.
  elim (store_inv _ _ _ _ _ _ STORE); intros. auto.
Qed.

Hint Resolve store_valid_access_1 store_valid_access_2
             store_valid_access_3: mem.

Theorem load_store_similar:
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  load chunk' m2 b ofs = Some (Val.load_result chunk' v).
Proof.
  intros. destruct (store_inv _ _ _ _ _ _ STORE).
  unfold load. rewrite in_bounds_true.
  decEq. decEq. rewrite H1. unfold unchecked_store; simpl.
  rewrite update_s. simpl.
  replace (pred_size_chunk chunk) with (pred_size_chunk chunk').
  apply getN_setN_same.
  repeat rewrite size_chunk_pred in H. omega.
  apply store_valid_access_1.
  inv H0. constructor; auto. congruence.
Qed.

Theorem load_store_same:
  load chunk m2 b ofs = Some (Val.load_result chunk v).
Proof.
  eapply load_store_similar; eauto.
Qed.
        
Theorem load_store_other:
  forall chunk' b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 b' ofs' = load chunk' m1 b' ofs'.
Proof.
  intros. destruct (store_inv _ _ _ _ _ _ STORE).
  unfold load. destruct (in_bounds m1 chunk' b' ofs').
  rewrite in_bounds_true. decEq. decEq. 
  rewrite H1; unfold unchecked_store; simpl.
  unfold update. destruct (zeq b' b). subst b'.
  simpl. repeat rewrite size_chunk_pred in H.
  apply getN_setN_other. elim H; intro. congruence. omega.
  auto.
  eauto with mem.
  destruct (in_bounds m2 chunk' b' ofs'); auto.
  elim n. eauto with mem.
Qed.

Theorem load_store_overlap:
  forall chunk' ofs' v',
  load chunk' m2 b ofs' = Some v' ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v' = Vundef.
Proof.
  intros. destruct (store_inv _ _ _ _ _ _ STORE).
  destruct (load_inv _ _ _ _ _ H). rewrite H6. 
  rewrite H4. unfold unchecked_store. simpl. rewrite update_s.
  simpl. rewrite getN_setN_overlap. 
  destruct chunk'; reflexivity.
  auto. rewrite size_chunk_pred in H2. omega.
  rewrite size_chunk_pred in H1. omega.
Qed.

Theorem load_store_overlap':
  forall chunk' ofs',
  valid_access m1 chunk' b ofs' ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  load chunk' m2 b ofs' = Some Vundef.
Proof.
  intros.
  assert (exists v', load chunk' m2 b ofs' = Some v').
    eauto with mem.
  destruct H3 as [v' LOAD]. rewrite LOAD. decEq.
  eapply load_store_overlap; eauto.
Qed.

Theorem load_store_mismatch:
  forall chunk' v',
  load chunk' m2 b ofs = Some v' ->
  size_chunk chunk' <> size_chunk chunk ->
  v' = Vundef.
Proof.
  intros. destruct (store_inv _ _ _ _ _ _ STORE).
  destruct (load_inv _ _ _ _ _ H). rewrite H4. 
  rewrite H2. unfold unchecked_store. simpl. rewrite update_s.
  simpl. rewrite getN_setN_mismatch.
  destruct chunk'; reflexivity.
  repeat rewrite size_chunk_pred in H0; omega.
Qed.

Theorem load_store_mismatch':
  forall chunk',
  valid_access m1 chunk' b ofs ->
  size_chunk chunk' <> size_chunk chunk ->
  load chunk' m2 b ofs = Some Vundef.
Proof.
  intros.
  assert (exists v', load chunk' m2 b ofs = Some v').
    eauto with mem.
  destruct H1 as [v' LOAD]. rewrite LOAD. decEq.
  eapply load_store_mismatch; eauto.
Qed.

Inductive load_store_cases 
      (chunk1: memory_chunk) (b1: block) (ofs1: Z)
      (chunk2: memory_chunk) (b2: block) (ofs2: Z) : Set :=
  | lsc_similar:
      b1 = b2 -> ofs1 = ofs2 -> size_chunk chunk1 = size_chunk chunk2 ->
      load_store_cases chunk1 b1 ofs1 chunk2 b2 ofs2
  | lsc_other:
      b1 <> b2 \/ ofs2 + size_chunk chunk2 <= ofs1 \/ ofs1 + size_chunk chunk1 <= ofs2 ->
      load_store_cases chunk1 b1 ofs1 chunk2 b2 ofs2
  | lsc_overlap:
      b1 = b2 -> ofs1 <> ofs2 -> ofs2 + size_chunk chunk2 > ofs1 -> ofs1 + size_chunk chunk1 > ofs2 ->
      load_store_cases chunk1 b1 ofs1 chunk2 b2 ofs2
  | lsc_mismatch:
      b1 = b2 -> ofs1 = ofs2 -> size_chunk chunk1 <> size_chunk chunk2 ->
      load_store_cases chunk1 b1 ofs1 chunk2 b2 ofs2.

Remark size_chunk_pos:
  forall chunk1, size_chunk chunk1 > 0.
Proof.
  destruct chunk1; simpl; omega.
Qed.

Definition load_store_classification:
  forall (chunk1: memory_chunk) (b1: block) (ofs1: Z)
         (chunk2: memory_chunk) (b2: block) (ofs2: Z),
  load_store_cases chunk1 b1 ofs1 chunk2 b2 ofs2.
Proof.
  intros. destruct (eq_block b1 b2).
  destruct (zeq ofs1 ofs2).
  destruct (zeq (size_chunk chunk1) (size_chunk chunk2)).
  apply lsc_similar; auto.
  apply lsc_mismatch; auto.
  destruct (zle (ofs2 + size_chunk chunk2) ofs1).
  apply lsc_other. tauto.
  destruct (zle (ofs1 + size_chunk chunk1) ofs2).
  apply lsc_other. tauto.
  apply lsc_overlap; auto.
  apply lsc_other; tauto.
Qed.

Theorem load_store_characterization:
  forall chunk' b' ofs',
  valid_access m1 chunk' b' ofs' ->
  load chunk' m2 b' ofs' =
    match load_store_classification chunk b ofs chunk' b' ofs' with
    | lsc_similar _ _ _ => Some (Val.load_result chunk' v)
    | lsc_other _ => load chunk' m1 b' ofs'
    | lsc_overlap _ _ _ _ => Some Vundef
    | lsc_mismatch _ _ _ => Some Vundef
    end.
Proof.
  intros. 
  assert (exists v', load chunk' m2 b' ofs' = Some v') by eauto with mem.
  destruct H0 as [v' LOAD].
  destruct (load_store_classification chunk b ofs chunk' b' ofs').
  subst b' ofs'. apply load_store_similar; auto.
  apply load_store_other; intuition.
  subst b'. rewrite LOAD. decEq.
  eapply load_store_overlap; eauto. 
  subst b' ofs'. rewrite LOAD. decEq.
  eapply load_store_mismatch; eauto.
Qed.

End STORE.

Hint Resolve store_valid_block_1 store_valid_block_2: mem.
Hint Resolve store_valid_access_1 store_valid_access_2
             store_valid_access_3: mem.

(** ** Properties related to [alloc]. *)

Section ALLOC.

Variable m1: mem.
Variables lo hi: Z.
Variable m2: mem.
Variable b: block.
Hypothesis ALLOC: alloc m1 lo hi = (m2, b).

Lemma nextblock_alloc:
  nextblock m2 = Zsucc (nextblock m1).
Proof.
  injection ALLOC; intros. rewrite <- H0; auto.
Qed.

Lemma alloc_result:
  b = nextblock m1.
Proof.
  injection ALLOC; auto.
Qed.

Lemma valid_block_alloc:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_alloc. omega.
Qed.

Lemma fresh_block_alloc:
  ~(valid_block m1 b).
Proof.
  unfold valid_block. rewrite alloc_result. omega.
Qed.

Lemma valid_new_block:
  valid_block m2 b.
Proof.
  unfold valid_block. rewrite alloc_result. rewrite nextblock_alloc. omega.
Qed.

Hint Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem.

Lemma valid_block_alloc_inv:
  forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b'.
Proof.
  unfold valid_block; intros. 
  rewrite nextblock_alloc in H. rewrite alloc_result. 
  unfold block; omega.
Qed.

Lemma low_bound_alloc:
  forall b', low_bound m2 b' = if zeq b' b then lo else low_bound m1 b'.
Proof.
  intros. injection ALLOC; intros. rewrite <- H0; unfold low_bound; simpl.
  unfold update. rewrite H. destruct (zeq b' b); auto.
Qed.

Lemma low_bound_alloc_same:
  low_bound m2 b = lo.
Proof.
  rewrite low_bound_alloc. apply zeq_true. 
Qed.

Lemma low_bound_alloc_other:
  forall b', valid_block m1 b' -> low_bound m2 b' = low_bound m1 b'.
Proof.
  intros; rewrite low_bound_alloc.
  apply zeq_false. eauto with mem. 
Qed.

Lemma high_bound_alloc:
  forall b', high_bound m2 b' = if zeq b' b then hi else high_bound m1 b'.
Proof.
  intros. injection ALLOC; intros. rewrite <- H0; unfold high_bound; simpl.
  unfold update. rewrite H. destruct (zeq b' b); auto.
Qed.

Lemma high_bound_alloc_same:
  high_bound m2 b = hi.
Proof.
  rewrite high_bound_alloc. apply zeq_true. 
Qed.

Lemma high_bound_alloc_other:
  forall b', valid_block m1 b' -> high_bound m2 b' = high_bound m1 b'.
Proof.
  intros; rewrite high_bound_alloc.
  apply zeq_false. eauto with mem. 
Qed.

Lemma valid_access_alloc_other:
  forall chunk b' ofs,
  valid_access m1 chunk b' ofs ->
  valid_access m2 chunk b' ofs.
Proof.
  intros. inv H. constructor. auto with mem. 
  rewrite low_bound_alloc_other; auto. 
  rewrite high_bound_alloc_other; auto.
Qed.

Lemma valid_access_alloc_same:
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi ->
  valid_access m2 chunk b ofs.
Proof.
  intros. constructor. auto with mem.
  rewrite low_bound_alloc_same; auto.
  rewrite high_bound_alloc_same; auto.
Qed.

Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.

Lemma valid_access_alloc_inv:
  forall chunk b' ofs,
  valid_access m2 chunk b' ofs ->
  valid_access m1 chunk b' ofs \/
  (b' = b /\ lo <= ofs /\ ofs + size_chunk chunk <= hi).
Proof.
  intros. inv H. 
  elim (valid_block_alloc_inv _ H0); intro.
  subst b'. rewrite low_bound_alloc_same in H1.
  rewrite high_bound_alloc_same in H2. 
  right. tauto.
  left. constructor. auto. 
  rewrite low_bound_alloc_other in H1; auto.
  rewrite high_bound_alloc_other in H2; auto.
Qed.

Theorem load_alloc_unchanged:
  forall chunk b' ofs,
  valid_block m1 b' ->
  load chunk m2 b' ofs = load chunk m1 b' ofs.
Proof.
  intros. unfold load.
  destruct (in_bounds m2 chunk b' ofs). 
  elim (valid_access_alloc_inv _ _ _ v). intro.
  rewrite in_bounds_true; auto. 
  injection ALLOC; intros. rewrite <- H2; simpl.
  rewrite update_o. auto. rewrite H1. apply sym_not_equal. eauto with mem.
  intros [A [B C]]. subst b'. elimtype False. eauto with mem. 
  destruct (in_bounds m1 chunk b' ofs).
  elim n; eauto with mem.
  auto.
Qed.

Theorem load_alloc_other:
  forall chunk b' ofs v,
  load chunk m1 b' ofs = Some v ->
  load chunk m2 b' ofs = Some v.
Proof.
  intros. rewrite <- H. apply load_alloc_unchanged. eauto with mem.
Qed.

Theorem load_alloc_same:
  forall chunk ofs v,
  load chunk m2 b ofs = Some v ->
  v = Vundef.
Proof.
  intros. destruct (load_inv _ _ _ _ _ H). rewrite H1.
  injection ALLOC; intros. rewrite <- H3; simpl. 
  rewrite <- H2. rewrite update_s. 
  simpl. rewrite getN_init. destruct chunk; auto.
Qed.

Theorem load_alloc_same':
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi ->
  load chunk m2 b ofs = Some Vundef.
Proof.
  intros. assert (exists v, load chunk m2 b ofs = Some v).
    apply valid_access_load. constructor; eauto with mem.
    rewrite low_bound_alloc_same. auto.
    rewrite high_bound_alloc_same. auto.
  destruct H1 as [v LOAD]. rewrite LOAD. decEq.
  eapply load_alloc_same; eauto.
Qed.

End ALLOC.

Hint Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem.
Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.
Hint Resolve load_alloc_unchanged: mem.

(** ** Properties related to [free]. *)

Section FREE.

Variable m: mem.
Variable bf: block.

Lemma valid_block_free_1:
  forall b, valid_block m b -> valid_block (free m bf) b.
Proof.
  unfold valid_block, free; intros; simpl; auto.
Qed.

Lemma valid_block_free_2:
  forall b, valid_block (free m bf) b -> valid_block m b.
Proof.
  unfold valid_block, free; intros; simpl in *; auto.
Qed.

Hint Resolve valid_block_free_1 valid_block_free_2: mem.

Lemma low_bound_free:
  forall b, b <> bf -> low_bound (free m bf) b = low_bound m b.
Proof.
  intros. unfold low_bound, free; simpl.
  rewrite update_o; auto.
Qed.

Lemma high_bound_free:
  forall b, b <> bf -> high_bound (free m bf) b = high_bound m b.
Proof.
  intros. unfold high_bound, free; simpl.
  rewrite update_o; auto.
Qed.

Lemma low_bound_free_same:
  forall m b, low_bound (free m b) b = 0.
Proof.
  intros. unfold low_bound; simpl. rewrite update_s. simpl; omega.
Qed.

Lemma high_bound_free_same:
  forall m b, high_bound (free m b) b = 0.
Proof.
  intros. unfold high_bound; simpl. rewrite update_s. simpl; omega.
Qed.

Lemma valid_access_free_1:
  forall chunk b ofs,
  valid_access m chunk b ofs -> b <> bf ->
  valid_access (free m bf) chunk b ofs.
Proof.
  intros. inv H. constructor. auto with mem. 
  rewrite low_bound_free; auto. rewrite high_bound_free; auto.
Qed.

Lemma valid_access_free_2:
  forall chunk ofs, ~(valid_access (free m bf) chunk bf ofs).
Proof.
  intros; red; intros. inv H. 
  unfold free, low_bound in H1; simpl in H1. rewrite update_s in H1. simpl in H1.
  unfold free, high_bound in H2; simpl in H2. rewrite update_s in H2. simpl in H2.
  generalize (size_chunk_pos chunk). omega.
Qed.

Hint Resolve valid_access_free_1 valid_access_free_2: mem.

Lemma valid_access_free_inv:
  forall chunk b ofs,
  valid_access (free m bf) chunk b ofs ->
  valid_access m chunk b ofs /\ b <> bf.
Proof.
  intros. destruct (eq_block b bf). subst b.
  elim (valid_access_free_2 _ _ H). 
  inv H. rewrite low_bound_free in H1; auto. 
  rewrite high_bound_free in H2; auto.
  split; auto. constructor; auto with mem.
Qed.

Theorem load_free:
  forall chunk b ofs,
  b <> bf ->
  load chunk (free m bf) b ofs = load chunk m b ofs.
Proof.
  intros. unfold load.
  destruct (in_bounds m chunk b ofs).
  rewrite in_bounds_true; auto with mem. 
  unfold free; simpl. rewrite update_o; auto. 
  destruct (in_bounds (free m bf) chunk b ofs); auto.
  elim n. elim (valid_access_free_inv _ _ _ v); auto.
Qed.

End FREE.

(** ** Properties related to [free_list] *)

Lemma valid_block_free_list_1:
  forall bl m b, valid_block m b -> valid_block (free_list m bl) b.
Proof.
  induction bl; simpl; intros. auto. 
  apply valid_block_free_1; auto. 
Qed.

Lemma valid_block_free_list_2:
  forall bl m b, valid_block (free_list m bl) b -> valid_block m b.
Proof.
  induction bl; simpl; intros. auto.
  apply IHbl. apply valid_block_free_2 with a; auto. 
Qed.

Lemma valid_access_free_list:
  forall chunk b ofs m bl,
  valid_access m chunk b ofs -> ~In b bl ->
  valid_access (free_list m bl) chunk b ofs.
Proof.
  induction bl; simpl; intros. auto. 
  apply valid_access_free_1. apply IHbl. auto. intuition. intuition congruence.
Qed.

Lemma valid_access_free_list_inv:
  forall chunk b ofs m bl,
  valid_access (free_list m bl) chunk b ofs ->
  ~In b bl /\ valid_access m chunk b ofs.
Proof.
  induction bl; simpl; intros.
  tauto.
  elim (valid_access_free_inv _ _ _ _ _ H); intros.
  elim (IHbl H0); intros.
  intuition congruence.
Qed.

(** ** Properties related to pointer validity *)

Lemma valid_pointer_valid_access:
  forall m b ofs,
  valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs.
Proof.
  unfold valid_pointer; intros; split; intros.
  destruct (andb_prop _ _ H). destruct (andb_prop _ _ H0).
  constructor. red. eapply proj_sumbool_true; eauto.
  eapply proj_sumbool_true; eauto.
  change (size_chunk Mint8unsigned) with 1. 
  generalize (proj_sumbool_true _ H1). omega.
  inv H. unfold proj_sumbool. 
  rewrite zlt_true; auto. rewrite zle_true; auto.
  change (size_chunk Mint8unsigned) with 1 in H2. 
  rewrite zlt_true. auto. omega.
Qed.

Theorem valid_pointer_alloc:
  forall (m1 m2: mem) (lo hi: Z) (b b': block) (ofs: Z), 
  alloc m1 lo hi = (m2, b') ->
  valid_pointer m1 b ofs = true ->
  valid_pointer m2 b ofs = true.
Proof.
  intros. rewrite valid_pointer_valid_access in H0.
  rewrite valid_pointer_valid_access.
  eauto with mem.
Qed.

Theorem valid_pointer_store:
  forall (chunk: memory_chunk) (m1 m2: mem) (b b': block) (ofs ofs': Z) (v: val),
  store chunk m1 b' ofs' v = Some m2 ->
  valid_pointer m1 b ofs = true -> valid_pointer m2 b ofs = true.
Proof.
  intros. rewrite valid_pointer_valid_access in H0.
  rewrite valid_pointer_valid_access.
  eauto with mem.
Qed.

(** * Generic injections between memory states. *)

Section GENERIC_INJECT.

Definition meminj : Set := block -> option (block * Z).

Variable val_inj: meminj -> val -> val -> Prop.

(*
Hypothesis val_inj_ptr:
  forall mi b1 ofs1 b2 ofs2,
  val_inj mi (Vptr b1 ofs1) (Vptr b2 ofs2) <->
  exists delta, mi b1 = Some(b2, delta) /\ ofs2 = Int.repr (Int.signed ofs1 + delta).
*)

Hypothesis val_inj_undef:
  forall mi, val_inj mi Vundef Vundef.

Definition mem_inj (mi: meminj) (m1 m2: mem) :=
  forall chunk b1 ofs v1 b2 delta,
  mi b1 = Some(b2, delta) ->
  load chunk m1 b1 ofs = Some v1 ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ val_inj mi v1 v2.

Lemma valid_access_inj:
  forall mi m1 m2 chunk b1 ofs b2 delta,
  mi b1 = Some(b2, delta) ->
  mem_inj mi m1 m2 ->
  valid_access m1 chunk b1 ofs ->
  valid_access m2 chunk b2 (ofs + delta).
Proof.
  intros. 
  assert (exists v1, load chunk m1 b1 ofs = Some v1) by eauto with mem.
  destruct H2 as [v1 LOAD1].
  destruct (H0 _ _ _ _ _ _ H LOAD1) as [v2 [LOAD2 VCP]].
  eauto with mem.
Qed.

Hint Resolve valid_access_inj: mem.

Lemma store_unmapped_inj:
  forall mi m1 m2 b ofs v chunk m1',
  mem_inj mi m1 m2 ->
  mi b = None ->
  store chunk m1 b ofs v = Some m1' ->
  mem_inj mi m1' m2.
Proof.
  intros; red; intros.
  assert (load chunk0 m1 b1 ofs0 = Some v1).
    rewrite <- H3; symmetry. eapply load_store_other; eauto.
    left. congruence.
  eapply H; eauto.
Qed.

Lemma store_outside_inj:
  forall mi m1 m2 chunk b ofs v m2',
  mem_inj mi m1 m2 ->
  (forall b' delta,
    mi b' = Some(b, delta) ->
    high_bound m1 b' + delta <= ofs
    \/ ofs + size_chunk chunk <= low_bound m1 b' + delta) ->
  store chunk m2 b ofs v = Some m2' ->
  mem_inj mi m1 m2'.
Proof.
  intros; red; intros.
  exploit H; eauto. intros [v2 [LOAD2 VINJ]].
  exists v2; split; auto.
  rewrite <- LOAD2. eapply load_store_other; eauto.
  destruct (eq_block b2 b). subst b2.
  right. generalize (H0 _ _ H2); intro.
  assert (valid_access m1 chunk0 b1 ofs0) by eauto with mem.
  inv H5. omega. auto.
Qed. 

Definition meminj_no_overlap (mi: meminj) (m: mem) : Prop :=
  forall b1 b1' delta1 b2 b2' delta2,
  b1 <> b2 ->
  mi b1 = Some (b1', delta1) ->
  mi b2 = Some (b2', delta2) ->
  b1' <> b2' 
  \/ low_bound m b1 >= high_bound m b1
  \/ low_bound m b2 >= high_bound m b2
  \/ high_bound m b1 + delta1 <= low_bound m b2 + delta2 
  \/ high_bound m b2 + delta2 <= low_bound m b1 + delta1.

Lemma store_mapped_inj:
  forall mi m1 m2 b1 ofs b2 delta v1 v2 chunk m1',
  mem_inj mi m1 m2 ->
  meminj_no_overlap mi m1 ->
  mi b1 = Some(b2, delta) ->
  store chunk m1 b1 ofs v1 = Some m1' ->
  (forall chunk', size_chunk chunk' = size_chunk chunk ->
    val_inj mi (Val.load_result chunk' v1) (Val.load_result chunk' v2)) ->
  exists m2',
  store chunk m2 b2 (ofs + delta) v2 = Some m2' /\ mem_inj mi m1' m2'.
Proof.
  intros. 
  assert (exists m2', store chunk m2 b2 (ofs + delta) v2 = Some m2') by eauto with mem.
  destruct H4 as [m2' STORE2].
  exists m2'; split. auto.
  red. intros chunk' b1' ofs' v b2' delta' CP LOAD1.
  assert (valid_access m1 chunk' b1' ofs') by eauto with mem.
  generalize (load_store_characterization _ _ _ _ _ _ H2 _ _ _ H4).
  destruct (load_store_classification chunk b1 ofs chunk' b1' ofs');
  intro.
  (* similar *)
  subst b1' ofs'.
  rewrite CP in H1. inv H1.
  rewrite LOAD1 in H5. inv H5.
  exists (Val.load_result chunk' v2). split. 
  eapply load_store_similar; eauto.
  auto.
  (* disjoint *)
  rewrite LOAD1 in H5. 
  destruct (H _ _ _ _ _ _ CP (sym_equal H5)) as [v2' [LOAD2 VCP]].
  exists v2'. split; auto.
  rewrite <- LOAD2. eapply load_store_other; eauto.
  destruct (eq_block b1 b1'). subst b1'.
  rewrite CP in H1; inv H1. 
  right. elim o; [congruence | omega].
  assert (valid_access m1 chunk b1 ofs) by eauto with mem.
  generalize (H0 _ _ _ _ _ _ n H1 CP). intros [A | [A | [A | A]]].
  auto.
  inv H6. generalize (size_chunk_pos chunk). intro. omegaContradiction.
  inv H4. generalize (size_chunk_pos chunk'). intro. omegaContradiction.
  right. inv H4. inv H6. omega. 
  (* overlapping *)
  subst b1'. rewrite CP in H1; inv H1. 
  assert (exists v2', load chunk' m2' b2 (ofs' + delta) = Some v2') by eauto with mem.
  destruct H1 as [v2' LOAD2'].
  assert (v2' = Vundef). eapply load_store_overlap; eauto. 
    omega. omega. omega.
  exists v2'; split. auto. 
  replace v with Vundef by congruence. subst v2'. apply val_inj_undef.
  (* mismatch *)
  subst b1' ofs'. rewrite CP in H1; inv H1. 
  assert (exists v2', load chunk' m2' b2 (ofs + delta) = Some v2') by eauto with mem.
  destruct H1 as [v2' LOAD2'].
  assert (v2' = Vundef). eapply load_store_mismatch; eauto. 
  exists v2'; split. auto. 
  replace v with Vundef by congruence. subst v2'. apply val_inj_undef.
Qed.

Lemma alloc_parallel_inj:
  forall mi m1 m2 lo1 hi1 m1' b1 lo2 hi2 m2' b2 delta,
  mem_inj mi m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b1) ->
  alloc m2 lo2 hi2 = (m2', b2) ->
  mi b1 = Some(b2, delta) ->
  lo2 <= lo1 + delta -> hi1 + delta <= hi2 ->
  mem_inj mi m1' m2'.
Proof.
  intros; red; intros.
  exploit (valid_access_alloc_inv m1); eauto with mem.
  intros [A | [A [B C]]].
  assert (load chunk m1 b0 ofs = Some v1).
    rewrite <- H6. symmetry. eapply load_alloc_unchanged; eauto with mem.
  exploit H; eauto. intros [v2 [LOAD2 VINJ]]. 
  exists v2; split.
    rewrite <- LOAD2. eapply load_alloc_unchanged; eauto with mem.
  auto.
  subst b0. rewrite H2 in H5. inversion H5. subst b3 delta0.
  assert (v1 = Vundef). eapply load_alloc_same with (m1 := m1); eauto.
  subst v1.
  assert (exists v2, load chunk m2' b2 (ofs + delta) = Some v2).
    apply valid_access_load.
    eapply valid_access_alloc_same; eauto. omega. omega. 
  destruct H7 as [v2 LOAD2]. 
  assert (v2 = Vundef). eapply load_alloc_same with (m1 := m2); eauto.
  subst v2.
  exists Vundef; split. auto. apply val_inj_undef.
Qed.

Lemma alloc_right_inj:
  forall mi m1 m2 lo hi b2 m2',
  mem_inj mi m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  mem_inj mi m1 m2'.
Proof.
  intros; red; intros.
  exploit H; eauto. intros [v2 [LOAD2 VINJ]].
  exists v2; split; auto.
  assert (valid_block m2 b0).
    apply valid_access_valid_block with chunk (ofs + delta). 
    eauto with mem. 
  rewrite <- LOAD2. eapply load_alloc_unchanged; eauto.
Qed.

Hypothesis val_inj_undef_any:
  forall mi v, val_inj mi Vundef v.

Lemma alloc_left_unmapped_inj:
  forall mi m1 m2 lo hi b1 m1',
  mem_inj mi m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  mi b1 = None ->
  mem_inj mi m1' m2.
Proof.
  intros; red; intros.
  exploit (valid_access_alloc_inv m1); eauto with mem.
  intros [A | [A [B C]]].
  eapply H; eauto. 
  rewrite <- H3. symmetry. eapply load_alloc_unchanged; eauto with mem.
  subst b0. congruence.
Qed.

Lemma alloc_left_mapped_inj:
  forall mi m1 m2 lo hi b1 m1' b2 delta,
  mem_inj mi m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  mi b1 = Some(b2, delta) ->
  valid_block m2 b2 ->
  low_bound m2 b2 <= lo + delta -> hi + delta <= high_bound m2 b2 ->
  mem_inj mi m1' m2.
Proof.
  intros; red; intros.
  exploit (valid_access_alloc_inv m1); eauto with mem.
  intros [A | [A [B C]]].
  eapply H; eauto. 
  rewrite <- H6. symmetry. eapply load_alloc_unchanged; eauto with mem.
  subst b0. rewrite H1 in H5. inversion H5. subst b3 delta0.
  assert (v1 = Vundef). eapply load_alloc_same with (m1 := m1); eauto.
  subst v1.
  assert (exists v2, load chunk m2 b2 (ofs + delta) = Some v2).
    apply valid_access_load. constructor. auto. omega. omega.
  destruct H7 as [v2 LOAD2]. exists v2; split. auto.
  apply val_inj_undef_any.
Qed.

Lemma free_parallel_inj:
  forall mi m1 m2 b1 b2 delta,
  mem_inj mi m1 m2 ->
  mi b1 = Some(b2, delta) ->
  (forall b delta', mi b = Some(b2, delta') -> b = b1) ->
  mem_inj mi (free m1 b1) (free m2 b2).
Proof.
  intros; red; intros.
  exploit valid_access_free_inv; eauto with mem. intros [A B].
  assert (load chunk m1 b0 ofs = Some v1).
    rewrite <- H3. symmetry. apply load_free. auto.
  exploit H; eauto. intros [v2 [LOAD2 INJ]].
  exists v2; split. 
    rewrite <- LOAD2. apply load_free.
    red; intro; subst b3. elim B. eauto. 
  auto.
Qed.

Lemma free_left_inj:
  forall mi m1 m2 b1,
  mem_inj mi m1 m2 ->
  mem_inj mi (free m1 b1) m2.
Proof.
  intros; red; intros.
  exploit valid_access_free_inv; eauto with mem. intros [A B].
  eapply H; eauto with mem. 
  rewrite <- H1; symmetry; eapply load_free; eauto.
Qed.

Lemma free_list_left_inj:
  forall mi bl m1 m2,
  mem_inj mi m1 m2 ->
  mem_inj mi (free_list m1 bl) m2.
Proof.
  induction bl; intros; simpl.
  auto.
  apply free_left_inj. auto.
Qed.

Lemma free_right_inj:
  forall mi m1 m2 b2,
  mem_inj mi m1 m2 ->
  (forall b1 delta chunk ofs, 
   mi b1 = Some(b2, delta) -> ~(valid_access m1 chunk b1 ofs)) ->
  mem_inj mi m1 (free m2 b2).
Proof.
  intros; red; intros.
  assert (b0 <> b2).
    red; intro; subst b0. elim (H0 b1 delta chunk ofs H1).
    eauto with mem.
  exploit H; eauto. intros [v2 [LOAD2 INJ]].
  exists v2; split; auto. 
  rewrite <- LOAD2. apply load_free. auto.
Qed.

Lemma valid_pointer_inj:
  forall mi m1 m2 b1 ofs b2 delta,
  mi b1 = Some(b2, delta) ->
  mem_inj mi m1 m2 ->
  valid_pointer m1 b1 ofs = true ->
  valid_pointer m2 b2 (ofs + delta) = true.
Proof.
  intros. rewrite valid_pointer_valid_access in H1.
  rewrite valid_pointer_valid_access. eauto with mem.
Qed.

End GENERIC_INJECT.

(** ** Store extensions *)

(** A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by increasing the sizes of the memory blocks of [m1] (decreasing
  the low bounds, increasing the high bounds), while still keeping the
  same contents for block offsets that are valid in [m1]. *)

Definition inject_id : meminj := fun b => Some(b, 0).

Definition val_inj_id (mi: meminj) (v1 v2: val) : Prop := v1 = v2.

Definition extends (m1 m2: mem) :=
  nextblock m1 = nextblock m2 /\ mem_inj val_inj_id inject_id m1 m2.

Theorem extends_refl:
  forall (m: mem), extends m m.
Proof.
  intros; split. auto. 
  red; unfold inject_id; intros. inv H.
  exists v1; split. replace (ofs + 0) with ofs by omega. auto.
  unfold val_inj_id; auto.
Qed.

Theorem alloc_extends:
  forall (m1 m2 m1' m2': mem) (lo1 hi1 lo2 hi2: Z) (b1 b2: block),
  extends m1 m2 ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  alloc m1 lo1 hi1 = (m1', b1) ->
  alloc m2 lo2 hi2 = (m2', b2) ->
  b1 = b2 /\ extends m1' m2'.
Proof.
  intros. destruct H.
  assert (b1 = b2).
    transitivity (nextblock m1). eapply alloc_result; eauto.
    symmetry. rewrite H. eapply alloc_result; eauto.
  subst b2. split. auto. split. 
  rewrite (nextblock_alloc _ _ _ _ _ H2). 
  rewrite (nextblock_alloc _ _ _ _ _ H3).
  congruence.
  eapply alloc_parallel_inj; eauto. 
    unfold val_inj_id; auto.
    unfold inject_id; eauto.
    omega. omega.
Qed.

Theorem free_extends:
  forall (m1 m2: mem) (b: block),
  extends m1 m2 ->
  extends (free m1 b) (free m2 b).
Proof.
  intros. destruct H. split. 
  simpl; auto.
  eapply free_parallel_inj; eauto. 
  unfold inject_id. eauto.
  unfold inject_id; intros. congruence.
Qed.

Theorem load_extends:
  forall (chunk: memory_chunk) (m1 m2: mem) (b: block) (ofs: Z) (v: val),
  extends m1 m2 ->
  load chunk m1 b ofs = Some v ->
  load chunk m2 b ofs = Some v.
Proof.
  intros. destruct H. 
  exploit H1; eauto. unfold inject_id. eauto. 
  unfold val_inj_id. intros [v2 [LOAD EQ]].
  replace (ofs + 0) with ofs in LOAD by omega. congruence.
Qed.

Theorem store_within_extends:
  forall (chunk: memory_chunk) (m1 m2 m1': mem) (b: block) (ofs: Z) (v: val),
  extends m1 m2 ->
  store chunk m1 b ofs v = Some m1' ->
  exists m2', store chunk m2 b ofs v = Some m2' /\ extends m1' m2'.
Proof.
  intros. destruct H. 
  exploit store_mapped_inj; eauto. 
  unfold val_inj_id; eauto.
  unfold meminj_no_overlap, inject_id; intros.
    inv H3. inv H4. auto.
  unfold inject_id; eauto.
  unfold val_inj_id; intros. eauto.
  intros [m2' [STORE MINJ]].
  exists m2'; split.
  replace (ofs + 0) with ofs in STORE by omega. auto.
  split. 
  rewrite (nextblock_store _ _ _ _ _ _ H0).
  rewrite (nextblock_store _ _ _ _ _ _ STORE).
  auto.
  auto.
Qed.

Theorem store_outside_extends:
  forall (chunk: memory_chunk) (m1 m2 m2': mem) (b: block) (ofs: Z) (v: val),
  extends m1 m2 ->
  ofs + size_chunk chunk <= low_bound m1 b \/ high_bound m1 b <= ofs ->
  store chunk m2 b ofs v = Some m2' ->
  extends m1 m2'.
Proof.
  intros. destruct H. split. 
  rewrite (nextblock_store _ _ _ _ _ _ H1). auto.
  eapply store_outside_inj; eauto. 
  unfold inject_id; intros. inv H3. omega.
Qed.

Theorem valid_pointer_extends:
  forall m1 m2 b ofs,
  extends m1 m2 -> valid_pointer m1 b ofs = true ->
  valid_pointer m2 b ofs = true.
Proof.
  intros. destruct H. 
  replace ofs with (ofs + 0) by omega.
  apply valid_pointer_inj with val_inj_id inject_id m1 b; auto.
Qed.

(** * The ``less defined than'' relation over memory states *)

(** A memory state [m1] is less defined than [m2] if, for all addresses,
  the value [v1] read in [m1] at this address is less defined than
  the value [v2] read in [m2], that is, either [v1 = v2] or [v1 = Vundef]. *)

Definition val_inj_lessdef (mi: meminj) (v1 v2: val) : Prop :=
  Val.lessdef v1 v2.

Definition lessdef (m1 m2: mem) : Prop :=
  nextblock m1 = nextblock m2 /\
  mem_inj val_inj_lessdef inject_id m1 m2.

Lemma lessdef_refl:
  forall m, lessdef m m.
Proof.
  intros; split. auto.
  red; intros. unfold inject_id in H. inv H. 
  exists v1; split. replace (ofs + 0) with ofs by omega. auto.
  red. constructor.
Qed.

Lemma load_lessdef:
  forall m1 m2 chunk b ofs v1,
  lessdef m1 m2 -> load chunk m1 b ofs = Some v1 ->
  exists v2, load chunk m2 b ofs = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. destruct H.
  exploit H1; eauto. unfold inject_id. eauto.
  intros [v2 [LOAD INJ]]. exists v2; split.
  replace ofs with (ofs + 0) by omega. auto.
  auto.
Qed.

Lemma loadv_lessdef:
  forall m1 m2 chunk addr1 addr2 v1,
  lessdef m1 m2 -> Val.lessdef addr1 addr2 ->
  loadv chunk m1 addr1 = Some v1 ->
  exists v2, loadv chunk m2 addr2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. inv H0.  
  destruct addr2; simpl in *; try discriminate.
  eapply load_lessdef; eauto.
  simpl in H1; discriminate.
Qed.

Lemma store_lessdef:
  forall m1 m2 chunk b ofs v1 v2 m1',
  lessdef m1 m2 -> Val.lessdef v1 v2 ->
  store chunk m1 b ofs v1 = Some m1' ->
  exists m2', store chunk m2 b ofs v2 = Some m2' /\ lessdef m1' m2'.
Proof.
  intros. destruct H. 
  exploit store_mapped_inj; eauto.
    unfold val_inj_lessdef; intros; constructor.
    red; unfold inject_id; intros. inv H4. inv H5. auto.
    unfold inject_id; eauto.
    unfold val_inj_lessdef; intros.
    apply Val.load_result_lessdef. eexact H0.
  intros [m2' [STORE MINJ]].
  exists m2'; split. replace ofs with (ofs + 0) by omega. auto.
  split. 
  rewrite (nextblock_store _ _ _ _ _ _ H1).
  rewrite (nextblock_store _ _ _ _ _ _ STORE).
  auto.
  auto.
Qed.

Lemma storev_lessdef:
  forall m1 m2 chunk addr1 v1 addr2 v2 m1',
  lessdef m1 m2 -> Val.lessdef addr1 addr2 -> Val.lessdef v1 v2 ->
  storev chunk m1 addr1 v1 = Some m1' ->
  exists m2', storev chunk m2 addr2 v2 = Some m2' /\ lessdef m1' m2'.
Proof.
  intros. inv H0.  
  destruct addr2; simpl in H2; try discriminate.
  simpl. eapply store_lessdef; eauto.
  discriminate.
Qed. 

Lemma alloc_lessdef:
  forall m1 m2 lo hi b1 m1' b2 m2',
  lessdef m1 m2 -> alloc m1 lo hi = (m1', b1) -> alloc m2 lo hi = (m2', b2) ->
  b1 = b2 /\ lessdef m1' m2'.
Proof.
  intros. destruct H.
  assert (b1 = b2).
    transitivity (nextblock m1). eapply alloc_result; eauto.
    symmetry. rewrite H. eapply alloc_result; eauto.
  subst b2. split. auto. split. 
  rewrite (nextblock_alloc _ _ _ _ _ H0). 
  rewrite (nextblock_alloc _ _ _ _ _ H1).
  congruence.
  eapply alloc_parallel_inj; eauto. 
    unfold val_inj_lessdef; auto.
    unfold inject_id; eauto.
    omega. omega.
Qed.

Lemma free_lessdef:
  forall m1 m2 b, lessdef m1 m2 -> lessdef (free m1 b) (free m2 b).
Proof.
  intros. destruct H. split.
  simpl; auto.
  eapply free_parallel_inj; eauto.
  unfold inject_id. eauto.
  unfold inject_id; intros. congruence.
Qed.

Lemma valid_block_lessdef:
  forall m1 m2 b, lessdef m1 m2 -> valid_block m1 b -> valid_block m2 b.
Proof.
  unfold valid_block. intros. destruct H. rewrite <- H; auto.
Qed.

Lemma valid_pointer_lessdef:
  forall m1 m2 b ofs,
  lessdef m1 m2 -> valid_pointer m1 b ofs = true -> valid_pointer m2 b ofs = true.
Proof.
  intros. destruct H.
  replace ofs with (ofs + 0) by omega.
  apply valid_pointer_inj with val_inj_lessdef inject_id m1 b; auto.
Qed.

(** ** Memory injections *)

(** A memory injection [f] is a function from addresses to either [None]
  or [Some] of an address and an offset.  It defines a correspondence
  between the blocks of two memory states [m1] and [m2]:
- if [f b = None], the block [b] of [m1] has no equivalent in [m2];
- if [f b = Some(b', ofs)], the block [b] of [m2] corresponds to
  a sub-block at offset [ofs] of the block [b'] in [m2].
*)

(** A memory injection defines a relation between values that is the
  identity relation, except for pointer values which are shifted
  as prescribed by the memory injection. *)

Inductive val_inject (mi: meminj): val -> val -> Prop :=
  | val_inject_int:
      forall i, val_inject mi (Vint i) (Vint i)
  | val_inject_float:
      forall f, val_inject mi (Vfloat f) (Vfloat f)
  | val_inject_ptr:
      forall b1 ofs1 b2 ofs2 x,
      mi b1 = Some (b2, x) ->
      ofs2 = Int.add ofs1 (Int.repr x) ->
      val_inject mi (Vptr b1 ofs1) (Vptr b2 ofs2)
  | val_inject_undef: forall v,
      val_inject mi Vundef v.

Hint Resolve val_inject_int val_inject_float val_inject_ptr 
             val_inject_undef.

Inductive val_list_inject (mi: meminj): list val -> list val-> Prop:= 
  | val_nil_inject :
      val_list_inject mi nil nil
  | val_cons_inject : forall v v' vl vl' , 
      val_inject mi v v' -> val_list_inject mi vl vl'->
      val_list_inject mi (v :: vl) (v' :: vl').  

Hint Resolve val_nil_inject val_cons_inject.

(** A memory state [m1] injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- loads in [m1] must have matching loads in [m2] in the sense
  of the [mem_inj] predicate;
- unallocated blocks in [m1] must be mapped to [None] by [f];
- if [f b = Some(b', delta)], [b'] must be valid in [m2];
- distinct blocks in [m1] are mapped to non-overlapping sub-blocks in [m2];
- the sizes of [m2]'s blocks are representable with signed machine integers;
- the offsets [delta] are representable with signed machine integers.
*)

Record mem_inject (f: meminj) (m1 m2: mem) : Prop :=
  mk_mem_inject {
    mi_inj:
      mem_inj val_inject f m1 m2;
    mi_freeblocks:
      forall b, ~(valid_block m1 b) -> f b = None;
    mi_mappedblocks:
      forall b b' delta, f b = Some(b', delta) -> valid_block m2 b';
    mi_no_overlap:
      meminj_no_overlap f m1;
    mi_range_1:
      forall b b' delta,
      f b = Some(b', delta) ->
      Int.min_signed <= delta <= Int.max_signed;
    mi_range_2:
      forall b b' delta,
      f b = Some(b', delta) ->
      delta = 0 \/ (Int.min_signed <= low_bound m2 b' /\ high_bound m2 b' <= Int.max_signed)
  }.


(** The following lemmas establish the absence of machine integer overflow
  during address computations. *)

Lemma address_inject:
  forall f m1 m2 chunk b1 ofs1 b2 delta,
  mem_inject f m1 m2 ->
  valid_access m1 chunk b1 (Int.signed ofs1) ->
  f b1 = Some (b2, delta) ->
  Int.signed (Int.add ofs1 (Int.repr delta)) = Int.signed ofs1 + delta.
Proof.
  intros. inversion H.
  elim (mi_range_4 _ _ _ H1); intro.
  (* delta = 0 *)
  subst delta. change (Int.repr 0) with Int.zero.
  rewrite Int.add_zero. omega.
  (* delta <> 0 *)
  rewrite Int.add_signed.
  repeat rewrite Int.signed_repr. auto.
  eauto.
  assert (valid_access m2 chunk b2 (Int.signed ofs1 + delta)).
    eapply valid_access_inj; eauto.
  inv H3. generalize (size_chunk_pos chunk); omega.
  eauto.
Qed.

Lemma valid_pointer_inject_no_overflow:
  forall f m1 m2 b ofs b' x,
  mem_inject f m1 m2 ->
  valid_pointer m1 b (Int.signed ofs) = true ->
  f b = Some(b', x) ->
  Int.min_signed <= Int.signed ofs + Int.signed (Int.repr x) <= Int.max_signed.
Proof.
  intros. inv H. rewrite valid_pointer_valid_access in H0.
  assert (valid_access m2 Mint8unsigned b' (Int.signed ofs + x)).
    eapply valid_access_inj; eauto.
  inv H. change (size_chunk Mint8unsigned) with 1 in H4.
  rewrite Int.signed_repr; eauto.
  exploit mi_range_4; eauto. intros [A | [A B]].
  subst x. rewrite Zplus_0_r. apply Int.signed_range.
  omega.
Qed.

Lemma valid_pointer_inject:
  forall f m1 m2 b ofs b' ofs',
  mem_inject f m1 m2 ->
  valid_pointer m1 b (Int.signed ofs) = true ->
  val_inject f (Vptr b ofs) (Vptr b' ofs') ->
  valid_pointer m2 b' (Int.signed ofs') = true.
Proof.
  intros. inv H1. 
  exploit valid_pointer_inject_no_overflow; eauto. intro NOOV.
  inv H. rewrite Int.add_signed. rewrite Int.signed_repr; auto.
  rewrite Int.signed_repr; eauto.
  eapply valid_pointer_inj; eauto.
Qed.

Lemma different_pointers_inject:
  forall f m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  mem_inject f m m' ->
  b1 <> b2 ->
  valid_pointer m b1 (Int.signed ofs1) = true ->
  valid_pointer m b2 (Int.signed ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Int.signed (Int.add ofs1 (Int.repr delta1)) <>
  Int.signed (Int.add ofs2 (Int.repr delta2)).
Proof.
  intros. 
  rewrite valid_pointer_valid_access in H1. 
  rewrite valid_pointer_valid_access in H2. 
  rewrite (address_inject _ _ _ _ _ _ _ _ H H1 H3). 
  rewrite (address_inject _ _ _ _ _ _ _ _ H H2 H4). 
  inv H1. simpl in H7. inv H2. simpl in H9.
  exploit (mi_no_overlap _ _ _ H); eauto.
  intros [A | [A | [A | [A | A]]]].
  auto. omegaContradiction. omegaContradiction. 
  right. omega. right. omega.
Qed.

(** Relation between injections and loads. *)

Lemma load_inject:
  forall f m1 m2 chunk b1 ofs b2 delta v1,
  mem_inject f m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ val_inject f v1 v2.
Proof.
  intros. inversion H.
  eapply mi_inj0; eauto. 
Qed.

Lemma loadv_inject:
  forall f m1 m2 chunk a1 a2 v1,
  mem_inject f m1 m2 ->
  loadv chunk m1 a1 = Some v1 ->
  val_inject f a1 a2 ->
  exists v2, loadv chunk m2 a2 = Some v2 /\ val_inject f v1 v2.
Proof.
  intros. inv H1; simpl in H0; try discriminate.
  exploit load_inject; eauto. intros [v2 [LOAD INJ]].
  exists v2; split; auto. simpl.
  replace (Int.signed (Int.add ofs1 (Int.repr x)))
     with (Int.signed ofs1 + x).
  auto. symmetry. eapply address_inject; eauto with mem.
Qed.

(** Relation between injections and stores. *)

Inductive val_content_inject (f: meminj): memory_chunk -> val -> val -> Prop :=
  | val_content_inject_base:
      forall chunk v1 v2,
      val_inject f v1 v2 ->
      val_content_inject f chunk v1 v2
  | val_content_inject_8:
      forall chunk n1 n2,
      chunk = Mint8unsigned \/ chunk = Mint8signed ->
      Int.zero_ext 8 n1 = Int.zero_ext 8 n2 ->
      val_content_inject f chunk (Vint n1) (Vint n2)
  | val_content_inject_16:
      forall chunk n1 n2,
      chunk = Mint16unsigned \/ chunk = Mint16signed ->
      Int.zero_ext 16 n1 = Int.zero_ext 16 n2 ->
      val_content_inject f chunk (Vint n1) (Vint n2)
  | val_content_inject_32:
      forall f1 f2,
      Float.singleoffloat f1 = Float.singleoffloat f2 ->
      val_content_inject f Mfloat32 (Vfloat f1) (Vfloat f2).

Hint Resolve val_content_inject_base.

Lemma load_result_inject:
  forall f chunk v1 v2 chunk',
  val_content_inject f chunk v1 v2 ->
  size_chunk chunk = size_chunk chunk' ->
  val_inject f (Val.load_result chunk' v1) (Val.load_result chunk' v2).
Proof.
  intros. inv H; simpl.
  inv H1; destruct chunk'; simpl; econstructor; eauto.

  elim H1; intro; subst chunk;
  destruct chunk'; simpl in H0; try discriminate; simpl.
  replace (Int.sign_ext 8 n1) with (Int.sign_ext 8 n2).
  constructor. apply Int.sign_ext_equal_if_zero_equal; auto. compute; auto.
  rewrite H2. constructor.
  replace (Int.sign_ext 8 n1) with (Int.sign_ext 8 n2).
  constructor. apply Int.sign_ext_equal_if_zero_equal; auto. compute; auto.
  rewrite H2. constructor.

  elim H1; intro; subst chunk;
  destruct chunk'; simpl in H0; try discriminate; simpl.
  replace (Int.sign_ext 16 n1) with (Int.sign_ext 16 n2).
  constructor. apply Int.sign_ext_equal_if_zero_equal; auto. compute; auto.
  rewrite H2. constructor.
  replace (Int.sign_ext 16 n1) with (Int.sign_ext 16 n2).
  constructor. apply Int.sign_ext_equal_if_zero_equal; auto. compute; auto.
  rewrite H2. constructor.

  destruct chunk'; simpl in H0; try discriminate; simpl.
  constructor. rewrite H1; constructor.
Qed.

Lemma store_mapped_inject_1 :
  forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  mem_inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  val_content_inject f chunk v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ mem_inject f n1 n2.
Proof.
  intros. inversion H. 
  exploit store_mapped_inj; eauto.
  intros; constructor.
  intros. apply load_result_inject with chunk; eauto.
  intros [n2 [STORE MINJ]].
  exists n2; split. auto. constructor.
  (* inj *)
  auto.
  (* freeblocks *)
  intros. apply mi_freeblocks0. red; intro. elim H3. eauto with mem.
  (* mappedblocks *)
  intros. eauto with mem.
  (* no_overlap *)
  red; intros.
  repeat rewrite (low_bound_store _ _ _ _ _ _ H0).
  repeat rewrite (high_bound_store _ _ _ _ _ _ H0).
  eapply mi_no_overlap0; eauto.
  (* range *)
  auto.
  intros. 
  repeat rewrite (low_bound_store _ _ _ _ _ _ STORE).
  repeat rewrite (high_bound_store _ _ _ _ _ _ STORE).
  eapply mi_range_4; eauto.
Qed.

Lemma store_mapped_inject:
  forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  mem_inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  val_inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ mem_inject f n1 n2.
Proof.
  intros. eapply store_mapped_inject_1; eauto.
Qed.

Lemma store_unmapped_inject:
  forall f chunk m1 b1 ofs v1 n1 m2,
  mem_inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  mem_inject f n1 m2.
Proof.
  intros. inversion H.
  constructor.
  (* inj *)
  eapply store_unmapped_inj; eauto.
  (* freeblocks *)
  intros. apply mi_freeblocks0. red; intros; elim H2; eauto with mem.
  (* mappedblocks *)
  intros. eapply mi_mappedblocks0; eauto with mem.
  (* no_overlap *)
  red; intros.
  repeat rewrite (low_bound_store _ _ _ _ _ _ H0).
  repeat rewrite (high_bound_store _ _ _ _ _ _ H0).
  eapply mi_no_overlap0; eauto.
  (* range *)
  auto. auto.
Qed.

Lemma storev_mapped_inject_1:
  forall f chunk m1 a1 v1 n1 m2 a2 v2,
  mem_inject f m1 m2 ->
  storev chunk m1 a1 v1 = Some n1 ->
  val_inject f a1 a2 ->
  val_content_inject f chunk v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 = Some n2 /\ mem_inject f n1 n2.
Proof.
  intros. inv H1; simpl in H0; try discriminate.
  simpl. replace (Int.signed (Int.add ofs1 (Int.repr x)))
            with (Int.signed ofs1 + x).
  eapply store_mapped_inject_1; eauto.
  symmetry. eapply address_inject; eauto with mem.
Qed.

Lemma storev_mapped_inject:
  forall f chunk m1 a1 v1 n1 m2 a2 v2,
  mem_inject f m1 m2 ->
  storev chunk m1 a1 v1 = Some n1 ->
  val_inject f a1 a2 ->
  val_inject f v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 = Some n2 /\ mem_inject f n1 n2.
Proof.
  intros. eapply storev_mapped_inject_1; eauto.
Qed.

(** Relation between injections and [free] *)

Lemma meminj_no_overlap_free:
  forall mi m b,
  meminj_no_overlap mi m ->
  meminj_no_overlap mi (free m b).
Proof.
  intros; red; intros.
  assert (low_bound (free m b) b >= high_bound (free m b) b).
    rewrite low_bound_free_same; rewrite high_bound_free_same; auto.
    omega.
  destruct (eq_block b1 b); destruct (eq_block b2 b); subst; auto.
  repeat (rewrite low_bound_free; auto). 
  repeat (rewrite high_bound_free; auto).
Qed.

Lemma meminj_no_overlap_free_list:
  forall mi m bl,
  meminj_no_overlap mi m ->
  meminj_no_overlap mi (free_list m bl).
Proof.
  induction bl; simpl; intros. auto.
  apply meminj_no_overlap_free. auto.
Qed.

Lemma free_inject:
  forall f m1 m2 l b,
  (forall b1 delta, f b1 = Some(b, delta) -> In b1 l) ->
  mem_inject f m1 m2 ->
  mem_inject f (free_list m1 l) (free m2 b).
Proof.
  intros. inversion H0. constructor.
  (* inj *)
  apply free_right_inj. apply free_list_left_inj. auto.
  intros; red; intros. 
  elim (valid_access_free_list_inv _ _ _ _ _ H2); intros.
  elim H3; eauto.
  (* freeblocks *)
  intros. apply mi_freeblocks0. red; intro; elim H1.
  apply valid_block_free_list_1; auto.
  (* mappedblocks *)
  intros. apply valid_block_free_1. eauto. 
  (* overlap *)
  apply meminj_no_overlap_free_list; auto.
  (* range *)
  auto.
  intros. destruct (eq_block b' b). subst b'.
  rewrite low_bound_free_same; rewrite high_bound_free_same. 
  right; compute; intuition congruence.
  rewrite low_bound_free; auto. rewrite high_bound_free; auto.
  eauto.
Qed.

(** Monotonicity properties of memory injections. *)

Definition inject_incr (f1 f2: meminj) : Prop :=
  forall b, f1 b = f2 b \/ f1 b = None.

Lemma inject_incr_refl :
   forall f , inject_incr f f .
Proof. unfold inject_incr . intros. left . auto . Qed.

Lemma inject_incr_trans :
  forall f1 f2 f3, 
  inject_incr f1 f2 -> inject_incr f2 f3 -> inject_incr f1 f3 .
Proof .
  unfold inject_incr; intros.
  generalize (H b); generalize (H0 b); intuition congruence.
Qed.

Lemma val_inject_incr:
  forall f1 f2 v v',
  inject_incr f1 f2 ->
  val_inject f1 v v' ->
  val_inject f2 v v'.
Proof.
  intros. inversion H0.
  constructor.
  constructor.
  elim (H b1); intro. 
    apply val_inject_ptr with x. congruence. auto. 
    congruence.
  constructor.
Qed.

Lemma val_list_inject_incr:
  forall f1 f2 vl vl' ,
  inject_incr f1 f2 -> val_list_inject f1 vl vl' ->
  val_list_inject f2 vl vl'.
Proof.
  induction vl; intros; inv H0. auto.
  constructor. eapply val_inject_incr; eauto. auto.
Qed.

Hint Resolve inject_incr_refl val_inject_incr val_list_inject_incr.

(** Properties of injections and allocations. *)

Definition extend_inject
       (b: block) (x: option (block * Z)) (f: meminj) : meminj :=
  fun (b': block) => if zeq b' b then x else f b'.

Lemma extend_inject_incr:
  forall f b x,
  f b = None ->
  inject_incr f (extend_inject b x f).
Proof.
  intros; red; intros. unfold extend_inject. 
  destruct (zeq b0 b). subst b0; auto. auto.
Qed.

Lemma alloc_right_inject:
  forall f m1 m2 lo hi m2' b,
  mem_inject f m1 m2 ->
  alloc m2 lo hi = (m2', b) ->
  mem_inject f m1 m2'.
Proof.
  intros. inversion H. constructor.
  eapply alloc_right_inj; eauto.
  auto.
  intros. eauto with mem. 
  auto.
  auto.
  intros. replace (low_bound m2' b') with (low_bound m2 b').
  replace (high_bound m2' b') with (high_bound m2 b').
  eauto. 
  symmetry. eapply high_bound_alloc_other; eauto. 
  symmetry. eapply low_bound_alloc_other; eauto.
Qed.

Lemma alloc_unmapped_inject:
  forall f m1 m2 lo hi m1' b,
  mem_inject f m1 m2 ->
  alloc m1 lo hi = (m1', b) ->
  mem_inject (extend_inject b None f) m1' m2 /\
  inject_incr f (extend_inject b None f).
Proof.
  intros. inversion H.
  assert (inject_incr f (extend_inject b None f)).
  apply extend_inject_incr. apply mi_freeblocks0. eauto with mem.
  split; auto. constructor.
  (* inj *)
  eapply alloc_left_unmapped_inj; eauto.
  red; intros. unfold extend_inject in H2.
  destruct (zeq b1 b). congruence.
  exploit mi_inj0; eauto. intros [v2 [LOAD VINJ]].
  exists v2; split. auto. 
  apply val_inject_incr with f; auto.
  unfold extend_inject. apply zeq_true.
  (* freeblocks *)
  intros. unfold extend_inject. destruct (zeq b0 b). auto.
  apply mi_freeblocks0; red; intro. elim H2. eauto with mem.
  (* mappedblocks *)
  intros. unfold extend_inject in H2. destruct (zeq b0 b).
  discriminate. eauto.
  (* overlap *)
  red; unfold extend_inject, update; intros.
  repeat rewrite (low_bound_alloc _ _ _ _ _ H0).
  repeat rewrite (high_bound_alloc _ _ _ _ _ H0).
  destruct (zeq b1 b); try discriminate.
  destruct (zeq b2 b); try discriminate.
  eauto.
  (* range *)
  unfold extend_inject; intros.
  destruct (zeq b0 b). discriminate. eauto.
  unfold extend_inject; intros.
  destruct (zeq b0 b). discriminate. eauto.
Qed.

Lemma alloc_mapped_inject:
  forall f m1 m2 lo hi m1' b b' ofs,
  mem_inject f m1 m2 ->
  alloc m1 lo hi = (m1', b) ->
  valid_block m2 b' ->
  Int.min_signed <= ofs <= Int.max_signed ->
  Int.min_signed <= low_bound m2 b' ->
  high_bound m2 b' <= Int.max_signed ->
  low_bound m2 b' <= lo + ofs ->
  hi + ofs <= high_bound m2 b' ->
  (forall b0 ofs0, 
   f b0 = Some (b', ofs0) -> 
   high_bound m1 b0 + ofs0 <= lo + ofs \/
   hi + ofs <= low_bound m1 b0 + ofs0) ->
  mem_inject (extend_inject b (Some (b', ofs)) f) m1' m2 /\
  inject_incr f (extend_inject b (Some (b', ofs)) f).
Proof.
  intros. inversion H.
  assert (inject_incr f (extend_inject b (Some (b', ofs)) f)).
  apply extend_inject_incr. apply mi_freeblocks0. eauto with mem.
  split; auto.
  constructor. 
  (* inj *)
  eapply alloc_left_mapped_inj; eauto.
  red; intros. unfold extend_inject in H9.
  rewrite zeq_false in H9.
  exploit mi_inj0; eauto. intros [v2 [LOAD VINJ]].
  exists v2; split. auto. eapply val_inject_incr; eauto.
  eauto with mem. 
  unfold extend_inject. apply zeq_true.
  (* freeblocks *)
  intros. unfold extend_inject. rewrite zeq_false.
  apply mi_freeblocks0. red; intro. elim H9; eauto with mem.
  apply sym_not_equal; eauto with mem.
  (* mappedblocks *)
  unfold extend_inject; intros.
  destruct (zeq b0 b). inv H9. auto. eauto.
  (* overlap *)
  red; unfold extend_inject, update; intros.
  repeat rewrite (low_bound_alloc _ _ _ _ _ H0).
  repeat rewrite (high_bound_alloc _ _ _ _ _ H0).
  destruct (zeq b1 b); [inv H10|idtac];
  (destruct (zeq b2 b); [inv H11|idtac]).
  congruence. 
  destruct (zeq b1' b2'). subst b2'. generalize (H7 _ _ H11). tauto. auto.
  destruct (zeq b1' b2'). subst b2'. generalize (H7 _ _ H10). tauto. auto.
  eauto.
  (* range *)
  unfold extend_inject; intros. 
  destruct (zeq b0 b). inv H9. auto. eauto.
  unfold extend_inject; intros. 
  destruct (zeq b0 b). inv H9. auto. eauto.
Qed.

Lemma alloc_parallel_inject:
  forall f m1 m2 lo hi m1' m2' b1 b2,
  mem_inject f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  alloc m2 lo hi = (m2', b2) ->
  Int.min_signed <= lo -> hi <= Int.max_signed ->
  mem_inject (extend_inject b1 (Some(b2, 0)) f) m1' m2' /\
  inject_incr f (extend_inject b1 (Some(b2, 0)) f).
Proof.
  intros. 
  eapply alloc_mapped_inject; eauto.
  eapply alloc_right_inject; eauto.
  eauto with mem.
  compute; intuition congruence.
  rewrite (low_bound_alloc_same _ _ _ _ _ H1). auto.
  rewrite (high_bound_alloc_same _ _ _ _ _ H1). auto.
  rewrite (low_bound_alloc_same _ _ _ _ _ H1). omega.
  rewrite (high_bound_alloc_same _ _ _ _ _ H1). omega.
  intros. elimtype False. inv H. 
  exploit mi_mappedblocks0; eauto.
  change (~ valid_block m2 b2). eauto with mem.
Qed.

Definition meminj_init (m: mem) : meminj :=
  fun (b: block) => if zlt b m.(nextblock) then Some(b, 0) else None.

Definition mem_inject_neutral (m: mem) : Prop :=
  forall f chunk b ofs v,
  load chunk m b ofs = Some v -> val_inject f v v.

Lemma init_inject:
  forall m,
  mem_inject_neutral m ->
  mem_inject (meminj_init m) m m.
Proof.
  intros; constructor.
  (* inj *)
  red; intros. unfold meminj_init in H0. 
  destruct (zlt b1 (nextblock m)); inversion H0.
  subst b2 delta. exists v1; split.
  rewrite Zplus_0_r. auto. eapply H; eauto.
  (* free blocks *)
  unfold valid_block, meminj_init; intros.
  apply zlt_false. omega.
  (* mapped blocks *)
  unfold valid_block, meminj_init; intros.
  destruct (zlt b (nextblock m)); inversion H0. subst b'; auto.
  (* overlap *)
  red; unfold meminj_init; intros.
  destruct (zlt b1 (nextblock m)); inversion H1.
  destruct (zlt b2 (nextblock m)); inversion H2.
  left; congruence.
  (* range *)
  unfold meminj_init; intros.
  destruct (zlt b (nextblock m)); inversion H0. subst delta.
  compute; intuition congruence.
  unfold meminj_init; intros.
  destruct (zlt b (nextblock m)); inversion H0. subst delta.
  auto.
Qed.

Remark getN_setN_inject:
  forall f m v n1 p1 n2 p2,
  val_inject f (getN n2 p2 m) (getN n2 p2 m) ->
  val_inject f v v ->
  val_inject f (getN n2 p2 (setN n1 p1 v m))
               (getN n2 p2 (setN n1 p1 v m)).
Proof.
  intros. 
  destruct (getN_setN_characterization m v n1 p1 n2 p2)
  as [A | [A | A]]; rewrite A; auto.
Qed.
             
Remark getN_contents_init_data_inject:
  forall f n ofs id pos,
  val_inject f (getN n ofs (contents_init_data pos id))
               (getN n ofs (contents_init_data pos id)).
Proof.
  induction id; simpl; intros.
  repeat rewrite getN_init. constructor.
  destruct a; auto; apply getN_setN_inject; auto.
Qed.

Lemma alloc_init_data_neutral:
  forall m id m' b,
  mem_inject_neutral m ->
  alloc_init_data m id = (m', b) ->
  mem_inject_neutral m'.
Proof.
  intros. injection H0; intros A B.
  red; intros. 
  exploit load_inv; eauto. intros [C D].
  rewrite <- B in D; simpl in D. rewrite A in D. 
  unfold update in D. destruct (zeq b0 b).
  subst b0. rewrite D. simpl. 
  apply load_result_inject with chunk. constructor.
  apply getN_contents_init_data_inject. auto.
  apply H with chunk b0 ofs. unfold load.
  rewrite in_bounds_true. congruence. 
  inversion C. constructor.
  generalize H2. unfold valid_block. rewrite <- B; simpl.
  rewrite A. unfold block in n; intros. omega.
  replace (low_bound m b0) with (low_bound m' b0). auto.
  unfold low_bound; rewrite <- B; simpl; rewrite A. rewrite update_o; auto.
  replace (high_bound m b0) with (high_bound m' b0). auto.
  unfold high_bound; rewrite <- B; simpl; rewrite A. rewrite update_o; auto.
Qed.

(** ** Memory shifting *)

(** A special case of memory injection where blocks are not coalesced:
  each source block injects in a distinct target block. *)

Definition memshift := block -> option Z.

(*
Inductive val_shift (mi: memshift): val -> val -> Prop :=
  | val_shift_int:
      forall i, val_shift mi (Vint i) (Vint i)
  | val_shift_float:
      forall f, val_shift mi (Vfloat f) (Vfloat f)
  | val_shift_ptr:
      forall b ofs1 ofs2 x,
      mi b = Some x ->
      ofs2 = Int.add ofs1 (Int.repr x) ->
      val_shift mi (Vptr b ofs1) (Vptr b ofs2)
  | val_shift_undef: 
      val_shift mi Vundef Vundef.
*)

Definition meminj_of_shift (mi: memshift) : meminj :=
  fun b => match mi b with None => None | Some x => Some (b, x) end.

Definition val_shift (mi: memshift) (v1 v2: val): Prop :=
  val_inject (meminj_of_shift mi) v1 v2.

Record mem_shift (f: memshift) (m1 m2: mem) : Prop :=
  mk_mem_shift {
    ms_inj:
      mem_inj val_inject (meminj_of_shift f) m1 m2;
    ms_samedomain:
      nextblock m1 = nextblock m2;
    ms_domain:
      forall b, match f b with Some _ => b < nextblock m1 | None => b >= nextblock m1 end;
    ms_range_1:
      forall b delta,
      f b = Some delta ->
      Int.min_signed <= delta <= Int.max_signed;
    ms_range_2:
      forall b delta,
      f b = Some delta ->
      Int.min_signed <= low_bound m2 b /\ high_bound m2 b <= Int.max_signed
  }.

(** The following lemmas establish the absence of machine integer overflow
  during address computations. *)

Lemma address_shift:
  forall f m1 m2 chunk b ofs1 delta,
  mem_shift f m1 m2 ->
  valid_access m1 chunk b (Int.signed ofs1) ->
  f b = Some delta ->
  Int.signed (Int.add ofs1 (Int.repr delta)) = Int.signed ofs1 + delta.
Proof.
  intros. inversion H.
  elim (ms_range_4 _ _ H1); intros.
  rewrite Int.add_signed.
  repeat rewrite Int.signed_repr. auto.
  eauto.
  assert (valid_access m2 chunk b (Int.signed ofs1 + delta)).
    eapply valid_access_inj with (mi := meminj_of_shift f); eauto.
    unfold meminj_of_shift. rewrite H1; auto. 
  inv H4. generalize (size_chunk_pos chunk); omega.
  eauto.
Qed.

Lemma valid_pointer_shift_no_overflow:
  forall f m1 m2 b ofs x,
  mem_shift f m1 m2 ->
  valid_pointer m1 b (Int.signed ofs) = true ->
  f b = Some x ->
  Int.min_signed <= Int.signed ofs + Int.signed (Int.repr x) <= Int.max_signed.
Proof.
  intros. inv H. rewrite valid_pointer_valid_access in H0.
  assert (valid_access m2 Mint8unsigned b (Int.signed ofs + x)).
    eapply valid_access_inj with (mi := meminj_of_shift f); eauto.
    unfold meminj_of_shift. rewrite H1; auto. 
  inv H. change (size_chunk Mint8unsigned) with 1 in H4.
  rewrite Int.signed_repr; eauto.
  exploit ms_range_4; eauto. intros [A B]. omega.
Qed.

Lemma valid_pointer_shift:
  forall f m1 m2 b ofs b' ofs',
  mem_shift f m1 m2 ->
  valid_pointer m1 b (Int.signed ofs) = true ->
  val_shift f (Vptr b ofs) (Vptr b' ofs') ->
  valid_pointer m2 b' (Int.signed ofs') = true.
Proof.
  intros. unfold val_shift in H1. inv H1.
  assert (f b = Some x). 
    unfold meminj_of_shift in H5. destruct (f b); congruence. 
  exploit valid_pointer_shift_no_overflow; eauto. intro NOOV.
  inv H. rewrite Int.add_signed. rewrite Int.signed_repr; auto.
  rewrite Int.signed_repr; eauto.
  eapply valid_pointer_inj; eauto.
Qed.

(** Relation between shifts and loads. *)

Lemma load_shift:
  forall f m1 m2 chunk b ofs delta v1,
  mem_shift f m1 m2 ->
  load chunk m1 b ofs = Some v1 ->
  f b = Some delta ->
  exists v2, load chunk m2 b (ofs + delta) = Some v2 /\ val_shift f v1 v2.
Proof.
  intros. inversion H.
  unfold val_shift. eapply ms_inj0; eauto.
  unfold meminj_of_shift; rewrite H1; auto.
Qed.

Lemma loadv_shift:
  forall f m1 m2 chunk a1 a2 v1,
  mem_shift f m1 m2 ->
  loadv chunk m1 a1 = Some v1 ->
  val_shift f a1 a2 ->
  exists v2, loadv chunk m2 a2 = Some v2 /\ val_shift f v1 v2.
Proof.
  intros. unfold val_shift in H1. inv H1; simpl in H0; try discriminate.
  generalize H2. unfold meminj_of_shift. caseEq (f b1); intros; inv H3.
  exploit load_shift; eauto. intros [v2 [LOAD INJ]].
  exists v2; split; auto. simpl.
  replace (Int.signed (Int.add ofs1 (Int.repr x)))
     with (Int.signed ofs1 + x).
  auto. symmetry. eapply address_shift; eauto with mem.
Qed.

(** Relation between shifts and stores. *)

Lemma store_within_shift:
  forall f chunk m1 b ofs v1 n1 m2 delta v2,
  mem_shift f m1 m2 ->
  store chunk m1 b ofs v1 = Some n1 ->
  f b = Some delta ->
  val_shift f v1 v2 ->
  exists n2,
    store chunk m2 b (ofs + delta) v2 = Some n2
    /\ mem_shift f n1 n2.
Proof.
  intros. inversion H. 
  exploit store_mapped_inj; eauto.
  intros; constructor.
  red. intros until delta2. unfold meminj_of_shift. 
  destruct (f b1). destruct (f b2). intros. inv H4. inv H5. auto. 
  congruence. congruence. 
  unfold meminj_of_shift. rewrite H1. auto.
  intros. apply load_result_inject with chunk; eauto.
  unfold val_shift in H2. eauto. 
  intros [n2 [STORE MINJ]].
  exists n2; split. auto. constructor.
  (* inj *)
  auto.
  (* samedomain *)
  rewrite (nextblock_store _ _ _ _ _ _ H0).
  rewrite (nextblock_store _ _ _ _ _ _ STORE).
  auto.
  (* domain *)
  rewrite (nextblock_store _ _ _ _ _ _ H0). auto.
  (* range *)
  auto.
  intros. 
  repeat rewrite (low_bound_store _ _ _ _ _ _ STORE).
  repeat rewrite (high_bound_store _ _ _ _ _ _ STORE).
  eapply ms_range_4; eauto.
Qed.

Lemma store_outside_shift:
  forall f chunk m1 b ofs m2 v m2' delta,
  mem_shift f m1 m2 ->
  f b = Some delta ->
  high_bound m1 b + delta <= ofs
  \/ ofs + size_chunk chunk <= low_bound m1 b + delta ->
  store chunk m2 b ofs v = Some m2' ->
  mem_shift f m1 m2'.
Proof.
  intros. inversion H. constructor.
  (* inj *)
  eapply store_outside_inj; eauto. 
  unfold meminj_of_shift. intros b' d'. caseEq (f b'); intros; inv H4.
  congruence.
  (* samedomain *)
  rewrite (nextblock_store _ _ _ _ _ _ H2).
  auto.
  (* domain *)
  auto.
  (* range *)
  auto.
  intros. 
  repeat rewrite (low_bound_store _ _ _ _ _ _ H2).
  repeat rewrite (high_bound_store _ _ _ _ _ _ H2).
  eapply ms_range_4; eauto.
Qed.

Lemma storev_shift:
  forall f chunk m1 a1 v1 n1 m2 a2 v2,
  mem_shift f m1 m2 ->
  storev chunk m1 a1 v1 = Some n1 ->
  val_shift f a1 a2 ->
  val_shift f v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 = Some n2 /\ mem_shift f n1 n2.
Proof.
  intros. unfold val_shift in H1. inv H1; simpl in H0; try discriminate.
  generalize H3. unfold meminj_of_shift. caseEq (f b1); intros; inv H4.
  exploit store_within_shift; eauto. intros [n2 [A B]].
  exists n2; split; auto.
  unfold storev. 
  replace (Int.signed (Int.add ofs1 (Int.repr x)))
     with (Int.signed ofs1 + x).
  auto. symmetry. eapply address_shift; eauto with mem.
Qed.

(** Relation between shifts and [free]. *)

Lemma free_shift:
  forall f m1 m2 b,
  mem_shift f m1 m2 ->
  mem_shift f (free m1 b) (free m2 b).
Proof.
  intros. inv H. constructor.
  (* inj *)
  apply free_right_inj. apply free_left_inj; auto.
  intros until ofs. unfold meminj_of_shift. caseEq (f b1); intros; inv H0.
  apply valid_access_free_2.
  (* samedomain *)
  simpl. auto.
  (* domain *)
  simpl. auto.
  (* range *)
  auto.
  intros. destruct (eq_block b0 b). 
  subst b0. rewrite low_bound_free_same. rewrite high_bound_free_same.
  vm_compute; intuition congruence.
  rewrite low_bound_free; auto. rewrite high_bound_free; auto. eauto.
Qed.

(** Relation between shifts and allocation. *)

Definition shift_incr (f1 f2: memshift) : Prop :=
  forall b, f1 b = f2 b \/ f1 b = None.

Remark shift_incr_inject_incr:
  forall f1 f2,
  shift_incr f1 f2 -> inject_incr (meminj_of_shift f1) (meminj_of_shift f2).
Proof.
  intros. unfold meminj_of_shift. red. intros. 
  elim (H b); intro. rewrite H0. auto. rewrite H0. auto.
Qed.

Lemma val_shift_incr:
  forall f1 f2 v1 v2,
  shift_incr f1 f2 -> val_shift f1 v1 v2 -> val_shift f2 v1 v2.
Proof.
  unfold val_shift; intros. 
  apply val_inject_incr with (meminj_of_shift f1).
  apply shift_incr_inject_incr. auto. auto.
Qed.

(***
Remark mem_inj_incr:
  forall f1 f2 m1 m2,
  inject_incr f1 f2 -> mem_inj val_inject f1 m1 m2 -> mem_inj val_inject f2 m1 m2.
Proof.
  intros; red; intros. 
  destruct (H b1). rewrite <- H3 in H1.
  exploit H0; eauto. intros [v2 [A B]]. 
  exists v2; split. auto. apply val_inject_incr with f1; auto.
  congruence.
***)

Lemma alloc_shift:
  forall f m1 m2 lo1 hi1 m1' b delta lo2 hi2,
  mem_shift f m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b) ->
  lo2 <= lo1 + delta -> hi1 + delta <= hi2 ->
  Int.min_signed <= delta <= Int.max_signed ->
  Int.min_signed <= lo2 -> hi2 <= Int.max_signed ->
  exists f', exists m2',
     alloc m2 lo2 hi2 = (m2', b)
  /\ mem_shift f' m1' m2'
  /\ shift_incr f f'
  /\ f' b = Some delta.
Proof.
  intros. inv H. caseEq (alloc m2 lo2 hi2). intros m2' b' ALLOC2.
  assert (b' = b).
    rewrite (alloc_result _ _ _ _ _ H0).
    rewrite (alloc_result _ _ _ _ _ ALLOC2).
    auto.
  subst b'.
  assert (f b = None).
    generalize (ms_domain0 b). 
    rewrite (alloc_result _ _ _ _ _ H0).
    destruct (f (nextblock m1)). 
    intros. omegaContradiction.
    auto.
  set (f' := fun (b': block) => if zeq b' b then Some delta else f b').
  assert (shift_incr f f').
    red; unfold f'; intros.
    destruct (zeq b0 b); auto.
    subst b0. auto.
  exists f'; exists m2'.
  split. auto.
  (* mem_shift *)
  split. constructor.
  (* inj *)
  assert (mem_inj val_inject (meminj_of_shift f') m1 m2).
    red; intros.
    assert (meminj_of_shift f b1 = Some (b2, delta0)).
      rewrite <- H7. unfold meminj_of_shift, f'.
      destruct (zeq b1 b); auto.
      subst b1.
      assert (valid_block m1 b) by eauto with mem. 
      assert (~valid_block m1 b) by eauto with mem.
      contradiction.
    exploit ms_inj0; eauto. intros [v2 [A B]].
    exists v2; split; auto. 
    apply val_inject_incr with (meminj_of_shift f).
    apply shift_incr_inject_incr. auto. auto.
  eapply alloc_parallel_inj; eauto.
  unfold meminj_of_shift, f'. rewrite zeq_true. auto.
  (* samedomain *)
  rewrite (nextblock_alloc _ _ _ _ _ H0).
  rewrite (nextblock_alloc _ _ _ _ _ ALLOC2).
  congruence.
  (* domain *)
  intros. unfold f'. 
  rewrite (nextblock_alloc _ _ _ _ _ H0).
  rewrite (alloc_result _ _ _ _ _ H0).
  destruct (zeq b0 (nextblock m1)). omega.
  generalize (ms_domain0 b0). destruct (f b0); omega.
  (* range *)
  unfold f'; intros. destruct (zeq b0 b). congruence. eauto. 
  unfold f'; intros.
  rewrite (low_bound_alloc _ _ _ _ _ ALLOC2). 
  rewrite (high_bound_alloc _ _ _ _ _ ALLOC2). 
  destruct (zeq b0 b). auto. eauto.
  (* shift_incr *)
  split. auto.
  (* f' b = delta *)
  unfold f'. apply zeq_true. 
Qed.

