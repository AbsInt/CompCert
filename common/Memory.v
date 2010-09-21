(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt        *)
(*          with contributions from Andrew Appel, Rob Dockins,         *)
(*          and Gordon Stewart (Princeton University)                  *)
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
  
Require Import Axioms.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Export Memdata.
Require Export Memtype.

Definition update (A: Type) (x: Z) (v: A) (f: Z -> A) : Z -> A :=
  fun y => if zeq y x then v else f y.

Implicit Arguments update [A].

Lemma update_s:
  forall (A: Type) (x: Z) (v: A) (f: Z -> A),
  update x v f x = v.
Proof.
  intros; unfold update. apply zeq_true.
Qed.

Lemma update_o:
  forall (A: Type) (x: Z) (v: A) (f: Z -> A) (y: Z),
  x <> y -> update x v f y = f y.
Proof.
  intros; unfold update. apply zeq_false; auto.
Qed.

Module Mem <: MEM.

Definition perm_order' (po: option permission) (p: permission) := 
  match po with
  | Some p' => perm_order p' p
  | None => False
 end.

Record mem_ : Type := mkmem {
  mem_contents: block -> Z -> memval;
  mem_access: block -> Z -> option permission;
  bounds: block -> Z * Z;
  nextblock: block;
  nextblock_pos: nextblock > 0;
  nextblock_noaccess: forall b, 0 < b < nextblock \/ bounds b = (0,0) ;
  bounds_noaccess: forall b ofs, ofs < fst(bounds b) \/ ofs >= snd(bounds b) -> mem_access b ofs = None;
  noread_undef: forall b ofs,  perm_order' (mem_access b ofs) Readable \/ mem_contents b ofs = Undef
}.

Definition mem := mem_.

Lemma mkmem_ext:
 forall cont1 cont2 acc1 acc2 bound1 bound2 next1 next2 
          a1 a2 b1 b2 c1 c2 d1 d2,
  cont1=cont2 -> acc1=acc2 -> bound1=bound2 -> next1=next2 ->
  mkmem cont1 acc1 bound1 next1 a1 b1 c1 d1 =
  mkmem cont2 acc2 bound2 next2 a2 b2 c2 d2.
Proof.
  intros. subst. f_equal; apply proof_irr.
Qed.

(** * Validity of blocks and accesses *)

(** A block address is valid if it was previously allocated. It remains valid
  even after being freed. *)

Definition valid_block (m: mem) (b: block) :=
  b < nextblock m.

Theorem valid_not_valid_diff:
  forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b'.
Proof.
  intros; red; intros. subst b'. contradiction.
Qed.

Hint Local Resolve valid_not_valid_diff: mem.

(** Permissions *)

Definition perm (m: mem) (b: block) (ofs: Z) (p: permission) : Prop :=
   perm_order' (mem_access m b ofs) p.

Theorem perm_implies:
  forall m b ofs p1 p2, perm m b ofs p1 -> perm_order p1 p2 -> perm m b ofs p2.
Proof.
  unfold perm, perm_order'; intros.
  destruct (mem_access m b ofs); auto.
  eapply perm_order_trans; eauto.
Qed.

Hint Local Resolve perm_implies: mem.

Theorem perm_valid_block:
  forall m b ofs p, perm m b ofs p -> valid_block m b.
Proof.
  unfold perm; intros. 
  destruct (zlt b m.(nextblock)).
  auto.
  assert (mem_access m b ofs = None). 
  destruct (nextblock_noaccess m b).
  elimtype False; omega.
  apply bounds_noaccess. rewrite H0; simpl; omega.
  rewrite H0 in H.
  contradiction.
Qed.

Hint Local Resolve perm_valid_block: mem.

Remark perm_order_dec:
  forall p1 p2, {perm_order p1 p2} + {~perm_order p1 p2}.
Proof.
  intros. destruct p1; destruct p2; (left; constructor) || (right; intro PO; inversion PO).
Qed.

Remark perm_order'_dec:
  forall op p, {perm_order' op p} + {~perm_order' op p}.
Proof.
  intros. destruct op; unfold perm_order'.
  apply perm_order_dec.
  right; tauto.
Qed.

Theorem perm_dec:
  forall m b ofs p, {perm m b ofs p} + {~ perm m b ofs p}.
Proof.
  unfold perm; intros.
  apply perm_order'_dec.
Qed.
 
Definition range_perm (m: mem) (b: block) (lo hi: Z) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm m b ofs p.

Theorem range_perm_implies:
  forall m b lo hi p1 p2,
  range_perm m b lo hi p1 -> perm_order p1 p2 -> range_perm m b lo hi p2.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Hint Local Resolve range_perm_implies: mem.

Lemma range_perm_dec:
  forall m b lo hi p, {range_perm m b lo hi p} + {~ range_perm m b lo hi p}.
Proof.
  intros. 
  assert (forall n, 0 <= n ->
          {range_perm m b lo (lo + n) p} + {~ range_perm m b lo (lo + n) p}).
    apply natlike_rec2.
    left. red; intros. omegaContradiction.
    intros. destruct H0. 
    destruct (perm_dec m b (lo + z) p). 
    left. red; intros. destruct (zeq ofs (lo + z)). congruence. apply r. omega. 
    right; red; intro. elim n. apply H0. omega. 
    right; red; intro. elim n. red; intros. apply H0. omega. 
  destruct (zlt lo hi).
  replace hi with (lo + (hi - lo)) by omega. apply H. omega.
  left; red; intros. omegaContradiction. 
Qed.

(** [valid_access m chunk b ofs p] holds if a memory access
    of the given chunk is possible in [m] at address [b, ofs]
    with permissions [p].
    This means:
- The range of bytes accessed all have permission [p].
- The offset [ofs] is aligned.
*)

Definition valid_access (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z) (p: permission): Prop :=
  range_perm m b ofs (ofs + size_chunk chunk) p
  /\ (align_chunk chunk | ofs).

Theorem valid_access_implies:
  forall m chunk b ofs p1 p2,
  valid_access m chunk b ofs p1 -> perm_order p1 p2 ->
  valid_access m chunk b ofs p2.
Proof.
  intros. inv H. constructor; eauto with mem.
Qed.

Theorem valid_access_freeable_any:
  forall m chunk b ofs p,
  valid_access m chunk b ofs Freeable ->
  valid_access m chunk b ofs p.
Proof.
  intros.
  eapply valid_access_implies; eauto. constructor.
Qed.

Hint Local Resolve valid_access_implies: mem.

Theorem valid_access_valid_block:
  forall m chunk b ofs,
  valid_access m chunk b ofs Nonempty ->
  valid_block m b.
Proof.
  intros. destruct H.
  assert (perm m b ofs Nonempty).
    apply H. generalize (size_chunk_pos chunk). omega.
  eauto with mem.
Qed.

Hint Local Resolve valid_access_valid_block: mem.

Lemma valid_access_perm:
  forall m chunk b ofs p,
  valid_access m chunk b ofs p ->
  perm m b ofs p.
Proof.
  intros. destruct H. apply H. generalize (size_chunk_pos chunk). omega.
Qed.

Lemma valid_access_compat:
  forall m chunk1 chunk2 b ofs p,
  size_chunk chunk1 = size_chunk chunk2 ->
  valid_access m chunk1 b ofs p->
  valid_access m chunk2 b ofs p.
Proof.
  intros. inv H0. rewrite H in H1. constructor; auto.
  rewrite <- (align_chunk_compat _ _ H). auto.
Qed.

Lemma valid_access_dec:
  forall m chunk b ofs p,
  {valid_access m chunk b ofs p} + {~ valid_access m chunk b ofs p}.
Proof.
  intros. 
  destruct (range_perm_dec m b ofs (ofs + size_chunk chunk) p).
  destruct (Zdivide_dec (align_chunk chunk) ofs (align_chunk_pos chunk)).
  left; constructor; auto.
  right; red; intro V; inv V; contradiction.
  right; red; intro V; inv V; contradiction.
Qed.

(** [valid_pointer] is a boolean-valued function that says whether
    the byte at the given location is nonempty. *)

Definition valid_pointer (m: mem) (b: block) (ofs: Z): bool :=
  perm_dec m b ofs Nonempty.

Theorem valid_pointer_nonempty_perm:
  forall m b ofs,
  valid_pointer m b ofs = true <-> perm m b ofs Nonempty.
Proof.
  intros. unfold valid_pointer. 
  destruct (perm_dec m b ofs Nonempty); simpl;
  intuition congruence.
Qed.

Theorem valid_pointer_valid_access:
  forall m b ofs,
  valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs Nonempty.
Proof.
  intros. rewrite valid_pointer_nonempty_perm. 
  split; intros.
  split. simpl; red; intros. replace ofs0 with ofs by omega. auto.
  simpl. apply Zone_divide. 
  destruct H. apply H. simpl. omega.
Qed.

(** Bounds *)

(** Each block has a low bound and a high bound, determined at allocation time
    and invariant afterward.  The crucial properties of bounds is
    that any offset below the low bound or above the high bound is
    empty. *)

Notation low_bound m b := (fst(bounds m b)).
Notation high_bound m b := (snd(bounds m b)).

Theorem perm_in_bounds:
  forall m b ofs p, perm m b ofs p -> low_bound m b <= ofs < high_bound m b.
Proof.
  unfold perm. intros.
  destruct (zlt ofs (fst (bounds m b))).
  exploit bounds_noaccess. left; eauto.
  intros.
  rewrite H0 in H. contradiction.
  destruct (zlt ofs (snd (bounds m b))).
  omega. 
  exploit bounds_noaccess. right; eauto.
  intro; rewrite H0 in H. contradiction.
Qed.

Theorem range_perm_in_bounds:
  forall m b lo hi p, 
  range_perm m b lo hi p -> lo < hi -> low_bound m b <= lo /\ hi <= high_bound m b.
Proof.
  intros. split. 
  exploit (perm_in_bounds m b lo p). apply H. omega. omega.
  exploit (perm_in_bounds m b (hi-1) p). apply H. omega. omega.
Qed.

Theorem valid_access_in_bounds:
  forall m chunk b ofs p,
  valid_access m chunk b ofs p ->
  low_bound m b <= ofs /\ ofs + size_chunk chunk <= high_bound m b.
Proof.
  intros. inv H. apply range_perm_in_bounds with p; auto.
  generalize (size_chunk_pos chunk). omega.
Qed.

Hint Local Resolve perm_in_bounds range_perm_in_bounds valid_access_in_bounds.

(** * Store operations *)

(** The initial store *)

Program Definition empty: mem :=
  mkmem (fun b ofs => Undef)
        (fun b ofs => None)
        (fun b => (0,0))
        1 _ _ _ _.
Next Obligation.
  omega.
Qed.

Definition nullptr: block := 0.

(** Allocation of a fresh block with the given bounds.  Return an updated
  memory state and the address of the fresh block, which initially contains
  undefined cells.  Note that allocation never fails: we model an
  infinite memory. *)

Program Definition alloc (m: mem) (lo hi: Z) :=
  (mkmem (update m.(nextblock) 
                 (fun ofs => Undef)
                 m.(mem_contents))
         (update m.(nextblock)
                 (fun ofs => if zle lo ofs && zlt ofs hi then Some Freeable else None)
                 m.(mem_access))
         (update m.(nextblock) (lo, hi) m.(bounds))
         (Zsucc m.(nextblock))
         _ _ _ _,
   m.(nextblock)).
Next Obligation.
  generalize (nextblock_pos m). omega. 
Qed.
Next Obligation.
  assert (0 < b < Zsucc (nextblock m) \/ b <= 0 \/ b > nextblock m) by omega.
  destruct H as [?|[?|?]]. left; omega.
  right.
  rewrite update_o.
  destruct (nextblock_noaccess m b); auto. elimtype False; omega.
  generalize (nextblock_pos m); omega.
(*  generalize (bounds_noaccess m b 0).*)
  destruct (nextblock_noaccess m b); auto. left; omega.
  rewrite update_o. right; auto. omega.
Qed.
Next Obligation.
  unfold update in *. destruct (zeq b (nextblock m)). 
  simpl in H. destruct H. 
  unfold proj_sumbool. rewrite zle_false. auto. omega.
  unfold proj_sumbool. rewrite zlt_false; auto. rewrite andb_false_r. auto.
  apply bounds_noaccess. auto.
Qed.
Next Obligation.
unfold update.
destruct (zeq b (nextblock m)); auto.
apply noread_undef.
Qed.


(** Freeing a block between the given bounds.
  Return the updated memory state where the given range of the given block
  has been invalidated: future reads and writes to this
  range will fail.  Requires write permission on the given range. *)

Definition clearN (m: block -> Z -> memval) (b: block) (lo hi: Z) : 
    block -> Z -> memval :=
   fun b' ofs => if zeq b' b 
                         then if zle lo ofs && zlt ofs hi then Undef else m b' ofs
                         else m b' ofs.

Lemma clearN_in:
   forall m b lo hi ofs, lo <= ofs < hi -> clearN m b lo hi b ofs = Undef.
Proof.
intros. unfold clearN. rewrite zeq_true.
destruct H; unfold andb, proj_sumbool.
rewrite zle_true; auto. rewrite zlt_true; auto.
Qed.

Lemma clearN_out:
  forall m b lo hi b' ofs, (b<>b' \/ ofs < lo \/ hi <= ofs) -> clearN m b lo hi b' ofs = m b' ofs.
Proof.
intros. unfold clearN. destruct (zeq b' b); auto.
subst b'.
destruct H. contradiction H; auto.
destruct (zle lo ofs); auto.
destruct (zlt ofs hi); auto.
elimtype False; omega.
Qed.


Program Definition unchecked_free (m: mem) (b: block) (lo hi: Z): mem :=
  mkmem (clearN m.(mem_contents) b lo hi)
        (update b 
                (fun ofs => if zle lo ofs && zlt ofs hi then None else m.(mem_access) b ofs)
                m.(mem_access))
        m.(bounds)
        m.(nextblock) _ _ _ _.
Next Obligation.
  apply nextblock_pos. 
Qed.
Next Obligation.
apply (nextblock_noaccess m b0).
Qed.
Next Obligation.
  unfold update. destruct (zeq b0 b). subst b0. 
  destruct (zle lo ofs); simpl; auto.
  destruct (zlt ofs hi); simpl; auto.
  apply bounds_noaccess; auto.
  apply bounds_noaccess; auto.
  apply bounds_noaccess; auto.
Qed.
Next Obligation.
  unfold clearN, update.
  destruct (zeq b0 b). subst b0. 
  destruct (zle lo ofs); simpl; auto.
  destruct (zlt ofs hi); simpl; auto.
  apply noread_undef.
  apply noread_undef.
  apply noread_undef.
Qed.

Definition free (m: mem) (b: block) (lo hi: Z): option mem :=
  if range_perm_dec m b lo hi Freeable 
  then Some(unchecked_free m b lo hi)
  else None.

Fixpoint free_list (m: mem) (l: list (block * Z * Z)) {struct l}: option mem :=
  match l with
  | nil => Some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi with
      | None => None
      | Some m' => free_list m' l'
      end
  end.

(** Memory reads. *)

(** Reading N adjacent bytes in a block content. *)

Fixpoint getN (n: nat) (p: Z) (c: Z -> memval) {struct n}: list memval :=
  match n with
  | O => nil
  | S n' => c p :: getN n' (p + 1) c
  end.

(** [load chunk m b ofs] perform a read in memory state [m], at address
  [b] and offset [ofs].  It returns the value of the memory chunk
  at that address.  [None] is returned if the accessed bytes
  are not readable. *)

Definition load (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z): option val :=
  if valid_access_dec m chunk b ofs Readable
  then Some(decode_val chunk (getN (size_chunk_nat chunk) ofs (m.(mem_contents) b)))
  else None.

(** [loadv chunk m addr] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

Definition loadv (chunk: memory_chunk) (m: mem) (addr: val) : option val :=
  match addr with
  | Vptr b ofs => load chunk m b (Int.signed ofs)
  | _ => None
  end.

(** [loadbytes m b ofs n] reads [n] consecutive bytes starting at
  location [(b, ofs)].  Returns [None] if the accessed locations are
  not readable. *)

Definition loadbytes (m: mem) (b: block) (ofs n: Z): option (list memval) :=
  if range_perm_dec m b ofs (ofs + n) Readable
  then Some (getN (nat_of_Z n) ofs (m.(mem_contents) b))
  else None.

(** Memory stores. *)

(** Writing N adjacent bytes in a block content. *)

Fixpoint setN (vl: list memval) (p: Z) (c: Z -> memval) {struct vl}: Z -> memval :=
  match vl with
  | nil => c
  | v :: vl' => setN vl' (p + 1) (update p v c)
  end.


Remark setN_other:
  forall vl c p q,
  (forall r, p <= r < p + Z_of_nat (length vl) -> r <> q) ->
  setN vl p c q = c q.
Proof.
  induction vl; intros; simpl.
  auto. 
  simpl length in H. rewrite inj_S in H.
  transitivity (update p a c q).
  apply IHvl. intros. apply H. omega. 
  apply update_o. apply H. omega. 
Qed.

Remark setN_outside:
  forall vl c p q,
  q < p \/ q >= p + Z_of_nat (length vl) ->
  setN vl p c q = c q.
Proof.
  intros. apply setN_other. 
  intros. omega. 
Qed.

Remark getN_setN_same:
  forall vl p c,
  getN (length vl) p (setN vl p c) = vl.
Proof.
  induction vl; intros; simpl.
  auto.
  decEq. 
  rewrite setN_outside. apply update_s. omega. 
  apply IHvl. 
Qed.

Remark getN_exten:
  forall c1 c2 n p,
  (forall i, p <= i < p + Z_of_nat n -> c1 i = c2 i) ->
  getN n p c1 = getN n p c2.
Proof.
  induction n; intros. auto. rewrite inj_S in H. simpl. decEq. 
  apply H. omega. apply IHn. intros. apply H. omega.
Qed.

Remark getN_setN_outside:
  forall vl q c n p,
  p + Z_of_nat n <= q \/ q + Z_of_nat (length vl) <= p ->
  getN n p (setN vl q c) = getN n p c.
Proof.
  intros. apply getN_exten. intros. apply setN_outside. omega. 
Qed.

Lemma store_noread_undef:
  forall m ch b ofs (VA: valid_access m ch b ofs Writable) v,
       forall b' ofs', 
       perm m b' ofs' Readable \/ 
        update b (setN (encode_val ch v) ofs (mem_contents m b)) (mem_contents m) b' ofs' = Undef.
Proof.
  intros.
  destruct VA as [? _].
  unfold update.
  destruct (zeq b' b).
  subst b'.
  assert (ofs <= ofs' < ofs + size_chunk ch \/ (ofs' < ofs \/ ofs' >= ofs + size_chunk ch)) by omega.
  destruct H0.
  exploit (H ofs'); auto; intro.
  eauto with mem.
  rewrite setN_outside.
  destruct (noread_undef m b ofs'); auto.
  rewrite encode_val_length. rewrite <- size_chunk_conv; auto.
  destruct (noread_undef m b' ofs'); auto.
Qed.

(** [store chunk m b ofs v] perform a write in memory state [m].
  Value [v] is stored at address [b] and offset [ofs].
  Return the updated memory store, or [None] if the accessed bytes
  are not writable. *)

Definition store (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val): option mem :=
 match valid_access_dec m chunk b ofs Writable with
 | left VA => Some (mkmem (update b 
                                  (setN (encode_val chunk v) ofs (m.(mem_contents) b))
                                  m.(mem_contents))
                    m.(mem_access)
                    m.(bounds)
                    m.(nextblock)
                    m.(nextblock_pos)
                    m.(nextblock_noaccess)
                    m.(bounds_noaccess)
                    (store_noread_undef m chunk b ofs VA v))
 | right _ => None
 end.

(** [storev chunk m addr v] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

Definition storev (chunk: memory_chunk) (m: mem) (addr v: val) : option mem :=
  match addr with
  | Vptr b ofs => store chunk m b (Int.signed ofs) v
  | _ => None
  end.

(** [drop_perm m b lo hi p] sets the permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have permissions
    at least [p] in the initial memory state [m].
    Returns updated memory state, or [None] if insufficient permissions. *)

Program Definition drop_perm (m: mem) (b: block) (lo hi: Z) (p: permission): option mem :=
  if range_perm_dec m b lo hi p then
    Some (mkmem (update b 
                        (fun ofs => if zle lo ofs && zlt ofs hi && negb (perm_order_dec p Readable)
                                    then Undef else m.(mem_contents) b ofs)
                        m.(mem_contents))
                (update b
                        (fun ofs => if zle lo ofs && zlt ofs hi then Some p else m.(mem_access) b ofs)
                        m.(mem_access))
                m.(bounds) m.(nextblock) _ _ _ _)
  else None.
Next Obligation.
  destruct m; auto.
Qed.
Next Obligation.
  destruct m; auto.
Qed.
Next Obligation.
  unfold update. destruct (zeq b0 b). subst b0.
  destruct (zle lo ofs). destruct (zlt ofs hi).
  exploit range_perm_in_bounds; eauto. omega. intros. omegaContradiction. 
  simpl. eapply bounds_noaccess; eauto. 
  simpl. eapply bounds_noaccess; eauto.
  eapply bounds_noaccess; eauto. 
Qed.
Next Obligation.
  unfold update. destruct (zeq b0 b). subst b0. 
  destruct (zle lo ofs && zlt ofs hi). 
  destruct (perm_order_dec p Readable); simpl; auto.
  eapply noread_undef; eauto.
  eapply noread_undef; eauto.
Qed.

(** * Properties of the memory operations *)

(** Properties of the empty store. *)

Theorem nextblock_empty: nextblock empty = 1.
Proof. reflexivity. Qed.

Theorem perm_empty: forall b ofs p, ~perm empty b ofs p.
Proof. 
  intros. unfold perm, empty; simpl. congruence.
Qed.

Theorem valid_access_empty: forall chunk b ofs p, ~valid_access empty chunk b ofs p.
Proof.
  intros. red; intros. elim (perm_empty b ofs p). apply H. 
  generalize (size_chunk_pos chunk); omega.
Qed.

(** ** Properties related to [load] *)

Theorem valid_access_load:
  forall m chunk b ofs,
  valid_access m chunk b ofs Readable ->
  exists v, load chunk m b ofs = Some v.
Proof.
  intros. econstructor. unfold load. rewrite pred_dec_true; eauto.  
Qed.

Theorem load_valid_access:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  valid_access m chunk b ofs Readable.
Proof.
  intros until v. unfold load. 
  destruct (valid_access_dec m chunk b ofs Readable); intros.
  auto. 
  congruence.
Qed.

Lemma load_result:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  v = decode_val chunk (getN (size_chunk_nat chunk) ofs (m.(mem_contents) b)).
Proof.
  intros until v. unfold load. 
  destruct (valid_access_dec m chunk b ofs Readable); intros.
  congruence.
  congruence.
Qed.

Hint Local Resolve load_valid_access valid_access_load: mem.

Theorem load_type:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  Val.has_type v (type_of_chunk chunk).
Proof.
  intros. exploit load_result; eauto; intros. rewrite H0. 
  apply decode_val_type. 
Qed.

Theorem load_cast:
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
Proof.
  intros. exploit load_result; eauto.
  set (l := getN (size_chunk_nat chunk) ofs (mem_contents m b)).
  intros. subst v. apply decode_val_cast. 
Qed.

Theorem load_int8_signed_unsigned:
  forall m b ofs,
  load Mint8signed m b ofs = option_map (Val.sign_ext 8) (load Mint8unsigned m b ofs).
Proof.
  intros. unfold load.
  change (size_chunk_nat Mint8signed) with (size_chunk_nat Mint8unsigned).
  set (cl := getN (size_chunk_nat Mint8unsigned) ofs (mem_contents m b)).
  destruct (valid_access_dec m Mint8signed b ofs Readable).
  rewrite pred_dec_true; auto. unfold decode_val. 
  destruct (proj_bytes cl); auto. rewrite decode_int8_signed_unsigned. auto.
  rewrite pred_dec_false; auto.
Qed.

Theorem load_int16_signed_unsigned:
  forall m b ofs,
  load Mint16signed m b ofs = option_map (Val.sign_ext 16) (load Mint16unsigned m b ofs).
Proof.
  intros. unfold load.
  change (size_chunk_nat Mint16signed) with (size_chunk_nat Mint16unsigned).
  set (cl := getN (size_chunk_nat Mint16unsigned) ofs (mem_contents m b)).
  destruct (valid_access_dec m Mint16signed b ofs Readable).
  rewrite pred_dec_true; auto. unfold decode_val. 
  destruct (proj_bytes cl); auto. rewrite decode_int16_signed_unsigned. auto.
  rewrite pred_dec_false; auto.
Qed.

Theorem loadbytes_load:
  forall chunk m b ofs bytes,
  loadbytes m b ofs (size_chunk chunk) = Some bytes ->
  (align_chunk chunk | ofs) ->
  load chunk m b ofs = Some(decode_val chunk bytes).
Proof.
  unfold loadbytes, load; intros. 
  destruct (range_perm_dec m b ofs (ofs + size_chunk chunk) Readable);
  try congruence.
  inv H. rewrite pred_dec_true. auto. 
  split; auto.
Qed.

Theorem load_loadbytes:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  exists bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes
             /\ v = decode_val chunk bytes.
Proof.
  intros. exploit load_valid_access; eauto. intros [A B].
  exploit load_result; eauto. intros. 
  exists (getN (size_chunk_nat chunk) ofs (mem_contents m b)); split.
  unfold loadbytes. rewrite pred_dec_true; auto. 
  auto.
Qed.

Lemma getN_length:
  forall c n p, length (getN n p c) = n.
Proof.
  induction n; simpl; intros. auto. decEq; auto.
Qed.

Theorem loadbytes_length:
  forall m b ofs n bytes,
  loadbytes m b ofs n = Some bytes ->
  length bytes = nat_of_Z n.
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + n) Readable); try congruence.
  inv H. apply getN_length.
Qed.

Lemma getN_concat:
  forall c n1 n2 p,
  getN (n1 + n2)%nat p c = getN n1 p c ++ getN n2 (p + Z_of_nat n1) c.
Proof.
  induction n1; intros.
  simpl. decEq. omega.
  rewrite inj_S. simpl. decEq.
  replace (p + Zsucc (Z_of_nat n1)) with ((p + 1) + Z_of_nat n1) by omega.
  auto. 
Qed.

Theorem loadbytes_concat:
  forall m b ofs n1 n2 bytes1 bytes2,
  loadbytes m b ofs n1 = Some bytes1 ->
  loadbytes m b (ofs + n1) n2 = Some bytes2 ->
  n1 >= 0 -> n2 >= 0 ->
  loadbytes m b ofs (n1 + n2) = Some(bytes1 ++ bytes2).
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + n1) Readable); try congruence.
  destruct (range_perm_dec m b (ofs + n1) (ofs + n1 + n2) Readable); try congruence.
  rewrite pred_dec_true. rewrite nat_of_Z_plus; auto.
  rewrite getN_concat. rewrite nat_of_Z_eq; auto.
  congruence.
  red; intros. 
  assert (ofs0 < ofs + n1 \/ ofs0 >= ofs + n1) by omega.
  destruct H4. apply r; omega. apply r0; omega.
Qed.

Theorem loadbytes_split:
  forall m b ofs n1 n2 bytes,
  loadbytes m b ofs (n1 + n2) = Some bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2,
     loadbytes m b ofs n1 = Some bytes1 
  /\ loadbytes m b (ofs + n1) n2 = Some bytes2
  /\ bytes = bytes1 ++ bytes2.
Proof.
  unfold loadbytes; intros. 
  destruct (range_perm_dec m b ofs (ofs + (n1 + n2)) Readable);
  try congruence.
  rewrite nat_of_Z_plus in H; auto. rewrite getN_concat in H.
  rewrite nat_of_Z_eq in H; auto. 
  repeat rewrite pred_dec_true.
  econstructor; econstructor.
  split. reflexivity. split. reflexivity. congruence.
  red; intros; apply r; omega.
  red; intros; apply r; omega.
Qed.

Theorem load_rep:
 forall ch m1 m2 b ofs v1 v2, 
  (forall z, 0 <= z < size_chunk ch -> mem_contents m1 b (ofs+z) = mem_contents m2 b (ofs+z)) ->
  load ch m1 b ofs = Some v1 ->
  load ch m2 b ofs = Some v2 ->
  v1 = v2.
Proof.
intros.
apply load_result in H0.
apply load_result in H1.
subst.
f_equal.
rewrite size_chunk_conv in H.
remember (size_chunk_nat ch) as n; clear Heqn.
revert ofs H; induction n; intros; simpl; auto.
f_equal.
rewrite inj_S in H.
replace ofs with (ofs+0) by omega.
apply H; omega.
apply IHn.
intros.
rewrite <- Zplus_assoc.
apply H.
rewrite inj_S. omega.
Qed.

(** ** Properties related to [store] *)

Theorem valid_access_store:
  forall m1 chunk b ofs v,
  valid_access m1 chunk b ofs Writable ->
  { m2: mem | store chunk m1 b ofs v = Some m2 }.
Proof.
  intros.
  unfold store. 
  destruct (valid_access_dec m1 chunk b ofs Writable).
  eauto.
  contradiction.
Qed.

Hint Local Resolve valid_access_store: mem.

Section STORE.
Variable chunk: memory_chunk.
Variable m1: mem.
Variable b: block.
Variable ofs: Z.
Variable v: val.
Variable m2: mem.
Hypothesis STORE: store chunk m1 b ofs v = Some m2.
(*
Lemma store_result:
  m2 = unchecked_store chunk m1 b ofs v.
Proof.
  unfold store in STORE.
  destruct (valid_access_dec m1 chunk b ofs Writable).
  congruence. 
  congruence.
Qed.
*)

Lemma store_access: mem_access m2 = mem_access m1.
Proof.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Lemma store_mem_contents: mem_contents m2 = 
                                       update b (setN (encode_val chunk v) ofs (m1.(mem_contents) b)) m1.(mem_contents).
Proof.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Theorem perm_store_1:
  forall b' ofs' p, perm m1 b' ofs' p -> perm m2 b' ofs' p.
Proof.
  intros. 
 unfold perm in *. rewrite store_access; auto.
Qed.

Theorem perm_store_2:
  forall b' ofs' p, perm m2 b' ofs' p -> perm m1 b' ofs' p.
Proof.
  intros. unfold perm in *.  rewrite store_access in H; auto.
Qed.

Hint Local Resolve perm_store_1 perm_store_2: mem.

Theorem nextblock_store:
  nextblock m2 = nextblock m1.
Proof.
  intros.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Theorem store_valid_block_1:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_store; auto.
Qed.

Theorem store_valid_block_2:
  forall b', valid_block m2 b' -> valid_block m1 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_store in H; auto.
Qed.

Hint Local Resolve store_valid_block_1 store_valid_block_2: mem.

Theorem store_valid_access_1:
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Theorem store_valid_access_2:
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Theorem store_valid_access_3:
  valid_access m1 chunk b ofs Writable.
Proof.
  unfold store in STORE. destruct (valid_access_dec m1 chunk b ofs Writable).
  auto. 
  congruence.
Qed.

Hint Local Resolve store_valid_access_1 store_valid_access_2
             store_valid_access_3: mem.

Theorem bounds_store:
  forall b', bounds m2 b' = bounds m1 b'.
Proof.
  intros.
  unfold store in STORE.
  destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE. simpl. auto.
Qed.

Theorem load_store_similar:
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  exists v', load chunk' m2 b ofs = Some v' /\ decode_encode_val v chunk chunk' v'.
Proof.
  intros.
  exploit (valid_access_load m2 chunk').
    eapply valid_access_compat. symmetry; eauto. eauto with mem. 
  intros [v' LOAD].
  exists v'; split; auto.
  exploit load_result; eauto. intros B. 
  rewrite B. rewrite store_mem_contents; simpl. 
  rewrite update_s.
  replace (size_chunk_nat chunk') with (length (encode_val chunk v)).
  rewrite getN_setN_same. apply decode_encode_val_general. 
  rewrite encode_val_length. repeat rewrite size_chunk_conv in H. 
  apply inj_eq_rev; auto.
Qed.

Theorem load_store_same:
  Val.has_type v (type_of_chunk chunk) ->
  load chunk m2 b ofs = Some (Val.load_result chunk v).
Proof.
  intros.
  destruct (load_store_similar chunk) as [v' [A B]]. auto.
  rewrite A. decEq. eapply decode_encode_val_similar; eauto. 
Qed.

Theorem load_store_other:
  forall chunk' b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 b' ofs' = load chunk' m1 b' ofs'.
Proof.
  intros. unfold load. 
  destruct (valid_access_dec m1 chunk' b' ofs' Readable).
  rewrite pred_dec_true. 
  decEq. decEq. rewrite store_mem_contents; simpl.
  unfold update. destruct (zeq b' b). subst b'.
  apply getN_setN_outside. rewrite encode_val_length. repeat rewrite <- size_chunk_conv.
  intuition.
  auto.
  eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem. 
Qed.

Theorem loadbytes_store_same:
  loadbytes m2 b ofs (size_chunk chunk) = Some(encode_val chunk v).
Proof.
  intros.
  assert (valid_access m2 chunk b ofs Readable) by eauto with mem.
  unfold loadbytes. rewrite pred_dec_true. rewrite store_mem_contents; simpl. 
  rewrite update_s. 
  replace (nat_of_Z (size_chunk chunk))
     with (length (encode_val chunk v)).
  rewrite getN_setN_same. auto.
  rewrite encode_val_length. auto.
  apply H. 
Qed.

Theorem loadbytes_store_other:
  forall b' ofs' n,
  b' <> b
  \/ n <= 0
  \/ ofs' + n <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  loadbytes m2 b' ofs' n = loadbytes m1 b' ofs' n.
Proof.
  intros. unfold loadbytes. 
  destruct (range_perm_dec m1 b' ofs' (ofs' + n) Readable).
  rewrite pred_dec_true. 
  decEq. rewrite store_mem_contents; simpl.
  unfold update. destruct (zeq b' b). subst b'.
  destruct H. congruence.
  destruct (zle n 0). 
  rewrite (nat_of_Z_neg _ z). auto.
  destruct H. omegaContradiction.
  apply getN_setN_outside. rewrite encode_val_length. rewrite <- size_chunk_conv.
  rewrite nat_of_Z_eq. auto. omega. 
  auto.
  red; intros. eauto with mem.
  rewrite pred_dec_false. auto.
  red; intro; elim n0; red; intros; eauto with mem.
Qed.

Lemma setN_property:
  forall (P: memval -> Prop) vl p q c,
  (forall v, In v vl -> P v) ->
  p <= q < p + Z_of_nat (length vl) ->
  P(setN vl p c q).
Proof.
  induction vl; intros.
  simpl in H0. omegaContradiction.
  simpl length in H0. rewrite inj_S in H0. simpl. 
  destruct (zeq p q). subst q. rewrite setN_outside. rewrite update_s. 
  auto with coqlib. omega.
  apply IHvl. auto with coqlib. omega.
Qed.

Lemma getN_in:
  forall c q n p,
  p <= q < p + Z_of_nat n ->
  In (c q) (getN n p c).
Proof.
  induction n; intros.
  simpl in H; omegaContradiction.
  rewrite inj_S in H. simpl. destruct (zeq p q).
  subst q. auto.
  right. apply IHn. omega. 
Qed.

Theorem load_pointer_store:
  forall chunk' b' ofs' v_b v_o,
  load chunk' m2 b' ofs' = Some(Vptr v_b v_o) ->
  (chunk = Mint32 /\ v = Vptr v_b v_o /\ chunk' = Mint32 /\ b' = b /\ ofs' = ofs)
  \/ (b' <> b \/ ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs').
Proof.
  intros. exploit load_result; eauto. rewrite store_mem_contents; simpl. 
  unfold update. destruct (zeq b' b); auto. subst b'. intro DEC.
  destruct (zle (ofs' + size_chunk chunk') ofs); auto.
  destruct (zle (ofs + size_chunk chunk) ofs'); auto.
  destruct (size_chunk_nat_pos chunk) as [sz SZ].
  destruct (size_chunk_nat_pos chunk') as [sz' SZ'].
  exploit decode_pointer_shape; eauto. intros [CHUNK' PSHAPE]. clear CHUNK'.
  generalize (encode_val_shape chunk v). intro VSHAPE.  
  set (c := mem_contents m1 b) in *.
  set (c' := setN (encode_val chunk v) ofs c) in *.
  destruct (zeq ofs ofs').

(* 1.  ofs = ofs':  must be same chunks and same value *)
  subst ofs'. inv VSHAPE. 
  exploit decode_val_pointer_inv; eauto. intros [A B].
  subst chunk'. simpl in B. inv B.
  generalize H4. unfold c'. rewrite <- H0. simpl. 
  rewrite setN_outside; try omega. rewrite update_s. intros.
  exploit (encode_val_pointer_inv chunk v v_b v_o). 
  rewrite <- H0. subst mv1. eauto. intros [C [D E]].
  left; auto.

  destruct (zlt ofs ofs').

(* 2. ofs < ofs':

      ofs   ofs'   ofs+|chunk|
       [-------------------]       write
            [-------------------]  read

   The byte at ofs' satisfies memval_valid_cont (consequence of write).
   For the read to return a pointer, it must satisfy ~memval_valid_cont. 
*)
  elimtype False.
  assert (~memval_valid_cont (c' ofs')).
    rewrite SZ' in PSHAPE. simpl in PSHAPE. inv PSHAPE. auto.
  assert (memval_valid_cont (c' ofs')).
    inv VSHAPE. unfold c'. rewrite <- H1. simpl. 
    apply setN_property. auto.
    assert (length mvl = sz). 
      generalize (encode_val_length chunk v). rewrite <- H1. rewrite SZ. 
      simpl; congruence.
    rewrite H4. rewrite size_chunk_conv in z0. omega. 
  contradiction.

(* 3. ofs > ofs':

      ofs'   ofs   ofs'+|chunk'|
              [-------------------]  write
        [----------------]           read

   The byte at ofs satisfies memval_valid_first (consequence of write).
   For the read to return a pointer, it must satisfy ~memval_valid_first.
*)
  elimtype False.
  assert (memval_valid_first (c' ofs)).
    inv VSHAPE. unfold c'. rewrite <- H0. simpl. 
    rewrite setN_outside. rewrite update_s. auto. omega.
  assert (~memval_valid_first (c' ofs)).
    rewrite SZ' in PSHAPE. simpl in PSHAPE. inv PSHAPE. 
    apply H4. apply getN_in. rewrite size_chunk_conv in z. 
    rewrite SZ' in z. rewrite inj_S in z. omega. 
  contradiction.
Qed.

End STORE.

Hint Local Resolve perm_store_1 perm_store_2: mem.
Hint Local Resolve store_valid_block_1 store_valid_block_2: mem.
Hint Local Resolve store_valid_access_1 store_valid_access_2
             store_valid_access_3: mem.

Theorem load_store_pointer_overlap:
  forall chunk m1 b ofs v_b v_o m2 chunk' ofs' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs' = Some v ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v = Vundef.
Proof.
  intros.
  exploit store_mem_contents; eauto. intro ST.
  exploit load_result; eauto. intro LD.
  rewrite LD; clear LD.
Opaque encode_val.
  rewrite ST; simpl.
  rewrite update_s.
  set (c := mem_contents m1 b).
  set (c' := setN (encode_val chunk (Vptr v_b v_o)) ofs c).
  destruct (decode_val_shape chunk' (getN (size_chunk_nat chunk') ofs' c'))
  as [OK | VSHAPE].
  apply getN_length. 
  exact OK.
  elimtype False.
  destruct (size_chunk_nat_pos chunk) as [sz SZ]. 
  destruct (size_chunk_nat_pos chunk') as [sz' SZ']. 
  assert (ENC: encode_val chunk (Vptr v_b v_o) = list_repeat (size_chunk_nat chunk) Undef
               \/ pointer_encoding_shape (encode_val chunk (Vptr v_b v_o))).
  destruct chunk; try (left; reflexivity). 
  right. apply encode_pointer_shape. 
  assert (GET: getN (size_chunk_nat chunk) ofs c' = encode_val chunk (Vptr v_b v_o)).
  unfold c'. rewrite <- (encode_val_length chunk (Vptr v_b v_o)). 
  apply getN_setN_same.
  destruct (zlt ofs ofs').

(* ofs < ofs':

      ofs   ofs'   ofs+|chunk|
       [-------------------]       write
            [-------------------]  read

   The byte at ofs' is Undef or not memval_valid_first (because write of pointer).
   The byte at ofs' must be memval_valid_first and not Undef (otherwise load returns Vundef).
*)
  assert (memval_valid_first (c' ofs') /\ c' ofs' <> Undef).
    rewrite SZ' in VSHAPE. simpl in VSHAPE. inv VSHAPE. auto.
  assert (~memval_valid_first (c' ofs') \/ c' ofs' = Undef).
    unfold c'. destruct ENC.
    right. apply setN_property. rewrite H5. intros. eapply in_list_repeat; eauto.
    rewrite encode_val_length. rewrite <- size_chunk_conv. omega.
    left. revert H5. rewrite <- GET. rewrite SZ. simpl. intros. inv H5.
    apply setN_property. apply H9. rewrite getN_length.
    rewrite size_chunk_conv in H3. rewrite SZ in H3. rewrite inj_S in H3. omega. 
  intuition. 

(* ofs > ofs':

      ofs'   ofs   ofs'+|chunk'|
              [-------------------]  write
        [----------------]           read

   The byte at ofs is Undef or not memval_valid_cont (because write of pointer).
   The byte at ofs must be memval_valid_cont and not Undef (otherwise load returns Vundef).
*)
  assert (memval_valid_cont (c' ofs) /\ c' ofs <> Undef).
    rewrite SZ' in VSHAPE. simpl in VSHAPE. inv VSHAPE. 
    apply H8. apply getN_in. rewrite size_chunk_conv in H2. 
    rewrite SZ' in H2. rewrite inj_S in H2. omega. 
  assert (~memval_valid_cont (c' ofs) \/ c' ofs = Undef).
    elim ENC. 
    rewrite <- GET. rewrite SZ. simpl. intros. right; congruence.
    rewrite <- GET. rewrite SZ. simpl. intros. inv H5. auto.
  intuition.
Qed.

Theorem load_store_pointer_mismatch:
  forall chunk m1 b ofs v_b v_o m2 chunk' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs = Some v ->
  chunk <> Mint32 \/ chunk' <> Mint32 ->
  v = Vundef.
Proof.
  intros.
  exploit store_mem_contents; eauto. intro ST.
  exploit load_result; eauto. intro LD.
  rewrite LD; clear LD.
Opaque encode_val.
  rewrite ST; simpl.
  rewrite update_s.
  set (c1 := mem_contents m1 b).
  set (e := encode_val chunk (Vptr v_b v_o)).
  destruct (size_chunk_nat_pos chunk) as [sz SZ].
  destruct (size_chunk_nat_pos chunk') as [sz' SZ'].
  assert (match e with
          | Undef :: _ => True
          | Pointer _ _ _ :: _ => chunk = Mint32
          | _ => False
          end).
Transparent encode_val.
  unfold e, encode_val. rewrite SZ. destruct chunk; simpl; auto.
  destruct e as [ | e1 el]. contradiction.
  rewrite SZ'. simpl. rewrite setN_outside. rewrite update_s. 
  destruct e1; try contradiction. 
  destruct chunk'; auto. 
  destruct chunk'; auto. intuition.
  omega.
Qed.

Lemma store_similar_chunks:
  forall chunk1 chunk2 v1 v2 m b ofs,
  encode_val chunk1 v1 = encode_val chunk2 v2 ->
  store chunk1 m b ofs v1 = store chunk2 m b ofs v2.
Proof.
  intros. unfold store. 
  assert (size_chunk chunk1 = size_chunk chunk2).
    repeat rewrite size_chunk_conv.
    rewrite <- (encode_val_length chunk1 v1).
    rewrite <- (encode_val_length chunk2 v2).
    congruence.
  unfold store.
  destruct (valid_access_dec m chunk1 b ofs Writable);
  destruct (valid_access_dec m chunk2 b ofs Writable); auto.
  f_equal. apply mkmem_ext; auto. congruence.
  elimtype False.
  destruct chunk1; destruct chunk2;  inv H0; unfold valid_access, align_chunk in *; try contradiction.
  elimtype False.
  destruct chunk1; destruct chunk2;  inv H0; unfold valid_access, align_chunk in *; try contradiction.
Qed.


Theorem store_signed_unsigned_8:
  forall m b ofs v,
  store Mint8signed m b ofs v = store Mint8unsigned m b ofs v.
Proof. intros. apply store_similar_chunks. apply encode_val_int8_signed_unsigned. Qed.

Theorem store_signed_unsigned_16:
  forall m b ofs v,
  store Mint16signed m b ofs v = store Mint16unsigned m b ofs v.
Proof. intros. apply store_similar_chunks. apply encode_val_int16_signed_unsigned. Qed.

Theorem store_int8_zero_ext:
  forall m b ofs n,
  store Mint8unsigned m b ofs (Vint (Int.zero_ext 8 n)) =
  store Mint8unsigned m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int8_zero_ext. Qed.

Theorem store_int8_sign_ext:
  forall m b ofs n,
  store Mint8signed m b ofs (Vint (Int.sign_ext 8 n)) =
  store Mint8signed m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int8_sign_ext. Qed.

Theorem store_int16_zero_ext:
  forall m b ofs n,
  store Mint16unsigned m b ofs (Vint (Int.zero_ext 16 n)) =
  store Mint16unsigned m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int16_zero_ext. Qed.

Theorem store_int16_sign_ext:
  forall m b ofs n,
  store Mint16signed m b ofs (Vint (Int.sign_ext 16 n)) =
  store Mint16signed m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int16_sign_ext. Qed.

Theorem store_float32_truncate:
  forall m b ofs n,
  store Mfloat32 m b ofs (Vfloat (Float.singleoffloat n)) =
  store Mfloat32 m b ofs (Vfloat n).
Proof. intros. apply store_similar_chunks. simpl. decEq. apply encode_float32_cast. Qed.

(** ** Properties related to [alloc]. *)

Section ALLOC.

Variable m1: mem.
Variables lo hi: Z.
Variable m2: mem.
Variable b: block.
Hypothesis ALLOC: alloc m1 lo hi = (m2, b).

Theorem nextblock_alloc:
  nextblock m2 = Zsucc (nextblock m1).
Proof.
  injection ALLOC; intros. rewrite <- H0; auto.
Qed.

Theorem alloc_result:
  b = nextblock m1.
Proof.
  injection ALLOC; auto.
Qed.

Theorem valid_block_alloc:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_alloc. omega.
Qed.

Theorem fresh_block_alloc:
  ~(valid_block m1 b).
Proof.
  unfold valid_block. rewrite alloc_result. omega.
Qed.

Theorem valid_new_block:
  valid_block m2 b.
Proof.
  unfold valid_block. rewrite alloc_result. rewrite nextblock_alloc. omega.
Qed.

Hint Local Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem.

Theorem valid_block_alloc_inv:
  forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b'.
Proof.
  unfold valid_block; intros. 
  rewrite nextblock_alloc in H. rewrite alloc_result. 
  unfold block; omega.
Qed.

Theorem perm_alloc_1:
  forall b' ofs p, perm m1 b' ofs p -> perm m2 b' ofs p.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. unfold update. destruct (zeq b' (nextblock m1)); auto.
  elimtype False.
  destruct (nextblock_noaccess m1 b').
  omega.
  rewrite bounds_noaccess in H. contradiction. rewrite H0.  simpl; omega.
Qed.

Theorem perm_alloc_2:
  forall ofs, lo <= ofs < hi -> perm m2 b ofs Freeable.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. rewrite update_s. unfold proj_sumbool. rewrite zle_true.
  rewrite zlt_true. simpl. auto with mem. omega. omega.
Qed.

Theorem perm_alloc_3:
  forall ofs p, ofs < lo \/ hi <= ofs -> ~perm m2 b ofs p.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. rewrite update_s. unfold proj_sumbool.
  destruct H. rewrite zle_false. simpl. congruence. omega.
  rewrite zlt_false. rewrite andb_false_r.
  intro; contradiction.
  omega.
Qed.

Hint Local Resolve perm_alloc_1 perm_alloc_2 perm_alloc_3: mem.

Theorem perm_alloc_inv:
  forall b' ofs p, 
  perm m2 b' ofs p ->
  if zeq b' b then lo <= ofs < hi else perm m1 b' ofs p.
Proof.
  intros until p; unfold perm. inv ALLOC. simpl. 
  unfold update. destruct (zeq b' (nextblock m1)); intros.
  destruct (zle lo ofs); try contradiction. destruct (zlt ofs hi); try contradiction.
  split; auto. 
  auto.
Qed.

Theorem valid_access_alloc_other:
  forall chunk b' ofs p,
  valid_access m1 chunk b' ofs p ->
  valid_access m2 chunk b' ofs p.
Proof.
  intros. inv H. constructor; auto with mem.
  red; auto with mem.
Qed.

Theorem valid_access_alloc_same:
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk b ofs Freeable.
Proof.
  intros. constructor; auto with mem.
  red; intros. apply perm_alloc_2. omega. 
Qed.

Hint Local Resolve valid_access_alloc_other valid_access_alloc_same: mem.

Theorem valid_access_alloc_inv:
  forall chunk b' ofs p,
  valid_access m2 chunk b' ofs p ->
  if eq_block b' b
  then lo <= ofs /\ ofs + size_chunk chunk <= hi /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk b' ofs p.
Proof.
  intros. inv H.
  generalize (size_chunk_pos chunk); intro.
  unfold eq_block. destruct (zeq b' b). subst b'.
  assert (perm m2 b ofs p). apply H0. omega. 
  assert (perm m2 b (ofs + size_chunk chunk - 1) p). apply H0. omega. 
  exploit perm_alloc_inv. eexact H2. rewrite zeq_true. intro.
  exploit perm_alloc_inv. eexact H3. rewrite zeq_true. intro. 
  intuition omega. 
  split; auto. red; intros. 
  exploit perm_alloc_inv. apply H0. eauto. rewrite zeq_false; auto. 
Qed.

Theorem bounds_alloc:
  forall b', bounds m2 b' = if eq_block b' b then (lo, hi) else bounds m1 b'.
Proof.
  injection ALLOC; intros. rewrite <- H; rewrite <- H0; simpl. 
  unfold update. auto. 
Qed.

Theorem bounds_alloc_same:
  bounds m2 b = (lo, hi).
Proof.
  rewrite bounds_alloc. apply dec_eq_true. 
Qed. 

Theorem bounds_alloc_other:
  forall b', b' <> b -> bounds m2 b' = bounds m1 b'.
Proof.
  intros. rewrite bounds_alloc. apply dec_eq_false. auto.
Qed.

Theorem load_alloc_unchanged:
  forall chunk b' ofs,
  valid_block m1 b' ->
  load chunk m2 b' ofs = load chunk m1 b' ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk b' ofs Readable).
  exploit valid_access_alloc_inv; eauto. destruct (eq_block b' b); intros.
  subst b'. elimtype False. eauto with mem.
  rewrite pred_dec_true; auto.
  injection ALLOC; intros. rewrite <- H2; simpl.
  rewrite update_o. auto. rewrite H1. apply sym_not_equal; eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem.
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
  intros. exploit load_result; eauto. intro. rewrite H0. 
  injection ALLOC; intros. rewrite <- H2; simpl. rewrite <- H1.
  rewrite update_s. destruct chunk; reflexivity. 
Qed.

Theorem load_alloc_same':
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  load chunk m2 b ofs = Some Vundef.
Proof.
  intros. assert (exists v, load chunk m2 b ofs = Some v).
    apply valid_access_load. constructor; auto.
    red; intros. eapply perm_implies. apply perm_alloc_2. omega. auto with mem.
  destruct H2 as [v LOAD]. rewrite LOAD. decEq.
  eapply load_alloc_same; eauto.
Qed.

End ALLOC.

Hint Local Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem.
Hint Local Resolve valid_access_alloc_other valid_access_alloc_same: mem.

(** ** Properties related to [free]. *)

Theorem range_perm_free:
  forall m1 b lo hi,
  range_perm m1 b lo hi Freeable ->
  { m2: mem | free m1 b lo hi = Some m2 }.
Proof.
  intros; unfold free. rewrite pred_dec_true; auto. econstructor; eauto.
Qed.

Section FREE.

Variable m1: mem.
Variable bf: block.
Variables lo hi: Z.
Variable m2: mem.
Hypothesis FREE: free m1 bf lo hi = Some m2.

Theorem free_range_perm:
  range_perm m1 bf lo hi Freeable.
Proof.
  unfold free in FREE. destruct (range_perm_dec m1 bf lo hi Freeable); auto.
  congruence.
Qed.

Lemma free_result:
  m2 = unchecked_free m1 bf lo hi.
Proof.
  unfold free in FREE. destruct (range_perm_dec m1 bf lo hi Freeable).
  congruence. congruence.
Qed.

Theorem nextblock_free:
  nextblock m2 = nextblock m1.
Proof.
  rewrite free_result; reflexivity.
Qed.

Theorem valid_block_free_1:
  forall b, valid_block m1 b -> valid_block m2 b.
Proof.
  intros. rewrite free_result. assumption.
Qed.

Theorem valid_block_free_2:
  forall b, valid_block m2 b -> valid_block m1 b.
Proof.
  intros. rewrite free_result in H. assumption.
Qed.

Hint Local Resolve valid_block_free_1 valid_block_free_2: mem.

Theorem perm_free_1:
  forall b ofs p,
  b <> bf \/ ofs < lo \/ hi <= ofs ->
  perm m1 b ofs p ->
  perm m2 b ofs p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  unfold update. destruct (zeq b bf). subst b.
  destruct (zle lo ofs); simpl. 
  destruct (zlt ofs hi); simpl.
  elimtype False; intuition.
  auto. auto.
  auto.
Qed.

Theorem perm_free_2:
  forall ofs p, lo <= ofs < hi -> ~ perm m2 bf ofs p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite update_s. unfold proj_sumbool. rewrite zle_true. rewrite zlt_true. 
  simpl. congruence. omega. omega.
Qed.

Theorem perm_free_3:
  forall b ofs p,
  perm m2 b ofs p -> perm m1 b ofs p.
Proof.
  intros until p. rewrite free_result. unfold perm, unchecked_free; simpl.
  unfold update. destruct (zeq b bf). subst b. 
  destruct (zle lo ofs); simpl. 
  destruct (zlt ofs hi); simpl. intro; contradiction.
  congruence. auto. auto.
Qed.

Theorem valid_access_free_1:
  forall chunk b ofs p,
  valid_access m1 chunk b ofs p -> 
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  valid_access m2 chunk b ofs p.
Proof.
  intros. inv H. constructor; auto with mem.
  red; intros. eapply perm_free_1; eauto.
  destruct (zlt lo hi). intuition. right. omega. 
Qed.

Theorem valid_access_free_2:
  forall chunk ofs p,
  lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
  ~(valid_access m2 chunk bf ofs p).
Proof.
  intros; red; intros. inv H2. 
  generalize (size_chunk_pos chunk); intros.
  destruct (zlt ofs lo).
  elim (perm_free_2 lo p).
  omega. apply H3. omega. 
  elim (perm_free_2 ofs p).
  omega. apply H3. omega. 
Qed.

Theorem valid_access_free_inv_1:
  forall chunk b ofs p,
  valid_access m2 chunk b ofs p ->
  valid_access m1 chunk b ofs p.
Proof.
  intros. destruct H. split; auto. 
  red; intros. generalize (H ofs0 H1). 
  rewrite free_result. unfold perm, unchecked_free; simpl. 
  unfold update. destruct (zeq b bf). subst b. 
  destruct (zle lo ofs0); simpl.
  destruct (zlt ofs0 hi); simpl. 
  intro; contradiction. congruence. auto. auto.
Qed.

Theorem valid_access_free_inv_2:
  forall chunk ofs p,
  valid_access m2 chunk bf ofs p ->
  lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs.
Proof.
  intros.
  destruct (zlt lo hi); auto. 
  destruct (zle (ofs + size_chunk chunk) lo); auto.
  destruct (zle hi ofs); auto.
  elim (valid_access_free_2 chunk ofs p); auto. omega.
Qed.

Theorem bounds_free:
  forall b, bounds m2 b = bounds m1 b.
Proof.
  intros. rewrite free_result; simpl. auto.
Qed.

Theorem load_free:
  forall chunk b ofs,
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  load chunk m2 b ofs = load chunk m1 b ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk b ofs Readable).
  rewrite pred_dec_true. 
  rewrite free_result; auto.
  simpl. f_equal. f_equal.
  unfold clearN.
  rewrite size_chunk_conv in H.
  remember (size_chunk_nat chunk) as n; clear Heqn.
  clear v FREE.
  revert lo hi ofs H; induction n; intros; simpl; auto.
  f_equal.
  destruct (zeq b bf); auto. subst bf.
  destruct (zle lo ofs); auto. destruct (zlt ofs hi); auto.
  elimtype False.
  destruct H as [? | [? | [? | ?]]]; try omega.
  contradict H; auto.
  rewrite inj_S in H; omega.
  apply IHn.
  rewrite inj_S in H.
  destruct H as [? | [? | [? | ?]]]; auto.
  unfold block in *; omega.
  unfold block in *; omega.

  apply valid_access_free_inv_1; auto. 
  rewrite pred_dec_false; auto.
  red; intro; elim n. eapply valid_access_free_1; eauto. 
Qed.

End FREE.

Hint Local Resolve valid_block_free_1 valid_block_free_2
             perm_free_1 perm_free_2 perm_free_3 
             valid_access_free_1 valid_access_free_inv_1: mem.

(** ** Properties related to [drop_perm] *)

Theorem range_perm_drop_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' -> range_perm m b lo hi p.
Proof.
  unfold drop_perm; intros. 
  destruct (range_perm_dec m b lo hi p). auto. discriminate.
Qed.

Theorem range_perm_drop_2:
  forall m b lo hi p,
  range_perm m b lo hi p -> {m' | drop_perm m b lo hi p = Some m' }.
Proof.
  unfold drop_perm; intros. 
  destruct (range_perm_dec m b lo hi p). econstructor. eauto. contradiction.
Qed.

Section DROP.

Variable m: mem.
Variable b: block.
Variable lo hi: Z.
Variable p: permission.
Variable m': mem.
Hypothesis DROP: drop_perm m b lo hi p = Some m'.

Theorem nextblock_drop:
  nextblock m' = nextblock m.
Proof.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi p); inv DROP; auto.
Qed.

Theorem perm_drop_1:
  forall ofs, lo <= ofs < hi -> perm m' b ofs p.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi p); inv DROP.
  unfold perm. simpl. rewrite update_s. unfold proj_sumbool. 
  rewrite zle_true. rewrite zlt_true. simpl. constructor.
  omega. omega. 
Qed.
  
Theorem perm_drop_2:
  forall ofs p', lo <= ofs < hi -> perm m' b ofs p' -> perm_order p p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi p); inv DROP.
  revert H0. unfold perm; simpl. rewrite update_s. unfold proj_sumbool. 
  rewrite zle_true. rewrite zlt_true. simpl. auto. 
  omega. omega. 
Qed.

Theorem perm_drop_3:
  forall b' ofs p', b' <> b \/ ofs < lo \/ hi <= ofs -> perm m b' ofs p' -> perm m' b' ofs p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi p); inv DROP.
  unfold perm; simpl. unfold update. destruct (zeq b' b). subst b'. 
  unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi). 
  byContradiction. intuition omega.
  auto. auto. auto.
Qed.

Theorem perm_drop_4:
  forall b' ofs p', perm m' b' ofs p' -> perm m b' ofs p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi p); inv DROP.
  revert H. unfold perm; simpl. unfold update. destruct (zeq b' b). 
  subst b'. unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi).
  simpl. intros. apply perm_implies with p. apply r. tauto. auto.
  auto. auto. auto.
Qed.

Theorem bounds_drop:
  forall b', bounds m' b' = bounds m b'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi p); inv DROP.
  unfold bounds; simpl. auto.
Qed.

Lemma valid_access_drop_1:
  forall chunk b' ofs p', 
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p p' ->
  valid_access m chunk b' ofs p' -> valid_access m' chunk b' ofs p'.
Proof.
  intros. destruct H0. split; auto. 
  red; intros.
  destruct (zeq b' b). subst b'.
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto. 
  destruct (zle hi ofs0). eapply perm_drop_3; eauto.
  apply perm_implies with p. eapply perm_drop_1; eauto. omega. 
  generalize (size_chunk_pos chunk); intros. intuition. omegaContradiction. omegaContradiction.
  eapply perm_drop_3; eauto.
Qed.

Lemma valid_access_drop_2:
  forall chunk b' ofs p', 
  valid_access m' chunk b' ofs p' -> valid_access m chunk b' ofs p'.
Proof.
  intros. destruct H; split; auto. 
  red; intros. eapply perm_drop_4; eauto. 
Qed.

(*
Lemma valid_access_drop_3:
  forall chunk b' ofs p',
  valid_access m' chunk b' ofs p' ->
  b' <> b \/ Intv.disjoint (lo, hi) (ofs, ofs + size_chunk chunk) \/ perm_order p p'.
Proof.
  intros. destruct H. 
  destruct (zeq b' b); auto. subst b'.
  destruct (Intv.disjoint_dec (lo, hi) (ofs, ofs + size_chunk chunk)); auto. 
  exploit intv_not_disjoint; eauto. intros [x [A B]]. 
  right; right. apply perm_drop_2 with x. auto. apply H. auto. 
Qed.
*)

Theorem load_drop:
  forall chunk b' ofs, 
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p Readable ->
  load chunk m' b' ofs = load chunk m b' ofs.
Proof.
  intros.
  unfold load.
  destruct (valid_access_dec m chunk b' ofs Readable).
  rewrite pred_dec_true.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi p); inv DROP. simpl.
  unfold update. destruct (zeq b' b). subst b'. decEq. decEq. 
  apply getN_exten. rewrite <- size_chunk_conv. intros.
  unfold proj_sumbool. destruct (zle lo i). destruct (zlt i hi). destruct (perm_order_dec p Readable).
  auto.
  elimtype False. intuition.
  auto. auto. auto.
  eapply valid_access_drop_1; eauto. 
  rewrite pred_dec_false. auto.
  red; intros; elim n. eapply valid_access_drop_2; eauto.
Qed.

End DROP.

(** * Extensionality properties *)

Lemma mem_access_ext:
  forall m1 m2, perm m1 = perm m2 -> mem_access m1 = mem_access m2.
Proof.
  intros.
  apply extensionality; intro b.
  apply extensionality; intro ofs.
  case_eq (mem_access m1 b ofs); case_eq (mem_access m2 b ofs); intros; auto.
  assert (perm m1 b ofs p <-> perm m2 b ofs p) by (rewrite H; intuition).
  assert (perm m1 b ofs p0 <-> perm m2 b ofs p0) by (rewrite H; intuition).
  unfold perm, perm_order' in H2,H3.
  rewrite H0 in H2,H3; rewrite H1 in H2,H3.
  f_equal.
  assert (perm_order p p0 -> perm_order p0 p -> p0=p) by
    (clear; intros; inv H; inv H0; auto).
  intuition.
  assert (perm m1 b ofs p <-> perm m2 b ofs p) by (rewrite H; intuition).
  unfold perm, perm_order' in H2; rewrite H0 in H2; rewrite H1 in H2.
  assert (perm_order p p) by auto with mem.
  intuition.
  assert (perm m1 b ofs p <-> perm m2 b ofs p) by (rewrite H; intuition).
  unfold perm, perm_order'  in H2; rewrite H0 in H2; rewrite H1 in H2.
  assert (perm_order p p) by auto with mem.
  intuition.
Qed.

Lemma mem_ext': 
  forall m1 m2, 
  mem_access m1 = mem_access m2 ->
  nextblock m1 = nextblock m2 ->
  (forall b, 0 < b < nextblock m1 -> bounds m1 b = bounds m2 b) ->
  (forall b ofs, perm_order' (mem_access m1 b ofs) Readable -> 
                          mem_contents m1 b ofs = mem_contents m2 b ofs) ->
  m1 = m2.
Proof.
  intros.
  destruct m1; destruct m2; simpl in *.
  destruct H; subst.
  apply mkmem_ext; auto.
  apply extensionality; intro b.
  apply extensionality; intro ofs.
  destruct (perm_order'_dec (mem_access0 b ofs) Readable).
  auto.
  destruct (noread_undef0 b ofs); try contradiction.
  destruct (noread_undef1 b ofs); try contradiction.
  congruence.
  apply extensionality; intro b.
  destruct (nextblock_noaccess0 b); auto.
  destruct (nextblock_noaccess1 b); auto.
  congruence.
Qed.

Theorem mem_ext:
  forall m1 m2, 
  perm m1 = perm m2 ->
  nextblock m1 = nextblock m2 ->
  (forall b, 0 < b < nextblock m1 -> bounds m1 b = bounds m2 b) ->
  (forall b ofs, loadbytes m1 b ofs 1 = loadbytes m2 b ofs 1) ->
  m1 = m2.
Proof.
  intros.
  generalize (mem_access_ext _ _ H); clear H; intro.
  apply mem_ext'; auto.
  intros.
  specialize (H2 b ofs).
  unfold loadbytes in H2; simpl in H2.
  destruct (range_perm_dec m1 b ofs (ofs+1)).
  destruct (range_perm_dec m2 b ofs (ofs+1)).
  inv H2; auto.
  contradict n.
  intros ofs' ?; assert (ofs'=ofs) by omega; subst ofs'.
  unfold perm, perm_order'.
    rewrite <- H; destruct (mem_access m1 b ofs); try destruct p; intuition.
  contradict n.
  intros ofs' ?; assert (ofs'=ofs) by omega; subst ofs'.
  unfold perm. destruct (mem_access m1 b ofs); try destruct p; intuition.
Qed.

(** * Generic injections *)

(** A memory state [m1] generically injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address.
*)

Record mem_inj (f: meminj) (m1 m2: mem) : Prop :=
  mk_mem_inj {
    mi_access:
      forall b1 b2 delta chunk ofs p,
      f b1 = Some(b2, delta) ->
      valid_access m1 chunk b1 ofs p ->
      valid_access m2 chunk b2 (ofs + delta) p;
    mi_memval:
      forall b1 ofs b2 delta,
      f b1 = Some(b2, delta) ->
      perm m1 b1 ofs Nonempty ->
      memval_inject f (m1.(mem_contents) b1 ofs) (m2.(mem_contents) b2 (ofs + delta))
  }.

(** Preservation of permissions *)

Lemma perm_inj:
  forall f m1 m2 b1 ofs p b2 delta,
  mem_inj f m1 m2 ->
  perm m1 b1 ofs p ->
  f b1 = Some(b2, delta) ->
  perm m2 b2 (ofs + delta) p.
Proof.
  intros. 
  assert (valid_access m1 Mint8unsigned b1 ofs p).
    split. red; intros. simpl in H2. replace ofs0 with ofs by omega. auto.
    simpl. apply Zone_divide.
  exploit mi_access; eauto. intros [A B].
  apply A. simpl; omega. 
Qed.

(** Preservation of loads. *)

Lemma getN_inj:
  forall f m1 m2 b1 b2 delta,
  mem_inj f m1 m2 ->
  f b1 = Some(b2, delta) ->
  forall n ofs,
  range_perm m1 b1 ofs (ofs + Z_of_nat n) Readable ->
  list_forall2 (memval_inject f) 
               (getN n ofs (m1.(mem_contents) b1))
               (getN n (ofs + delta) (m2.(mem_contents) b2)).
Proof.
  induction n; intros; simpl.
  constructor.
  rewrite inj_S in H1. 
  constructor. 
  eapply mi_memval; eauto.
  apply perm_implies with Readable.
  apply H1. omega. constructor. 
  replace (ofs + delta + 1) with ((ofs + 1) + delta) by omega.
  apply IHn. red; intros; apply H1; omega. 
Qed.

Lemma load_inj:
  forall f m1 m2 chunk b1 ofs b2 delta v1,
  mem_inj f m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ val_inject f v1 v2.
Proof.
  intros.
  exists (decode_val chunk (getN (size_chunk_nat chunk) (ofs + delta) (m2.(mem_contents) b2))).
  split. unfold load. apply pred_dec_true.  
  eapply mi_access; eauto with mem. 
  exploit load_result; eauto. intro. rewrite H2. 
  apply decode_val_inject. apply getN_inj; auto. 
  rewrite <- size_chunk_conv. exploit load_valid_access; eauto. intros [A B]. auto.
Qed.

(** Preservation of stores. *)

Lemma setN_inj:
  forall (access: Z -> Prop) delta f vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  forall p c1 c2,
  (forall q, access q -> memval_inject f (c1 q) (c2 (q + delta))) ->
  (forall q, access q -> memval_inject f ((setN vl1 p c1) q) 
                                         ((setN vl2 (p + delta) c2) (q + delta))).
Proof.
  induction 1; intros; simpl. 
  auto.
  replace (p + delta + 1) with ((p + 1) + delta) by omega.
  apply IHlist_forall2; auto. 
  intros. unfold update at 1. destruct (zeq q0 p). subst q0.
  rewrite update_s. auto.
  rewrite update_o. auto. omega.
Qed.

Definition meminj_no_overlap (f: meminj) (m: mem) : Prop :=
  forall b1 b1' delta1 b2 b2' delta2,
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' 
(*
  \/ low_bound m b1 >= high_bound m b1
  \/ low_bound m b2 >= high_bound m b2 *)
  \/ high_bound m b1 + delta1 <= low_bound m b2 + delta2 
  \/ high_bound m b2 + delta2 <= low_bound m b1 + delta1.

Lemma meminj_no_overlap_perm:
  forall f m b1 b1' delta1 b2 b2' delta2 ofs1 ofs2,
  meminj_no_overlap f m ->
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m b1 ofs1 Nonempty ->
  perm m b2 ofs2 Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.
Proof.
  intros. exploit H; eauto. intro. 
  exploit perm_in_bounds. eexact H3. intro. 
  exploit perm_in_bounds. eexact H4. intro.
  destruct H5. auto. right. omega. 
Qed.

Lemma store_mapped_inj:
  forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  mem_inj f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  meminj_no_overlap f m1 ->
  f b1 = Some (b2, delta) ->
  val_inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ mem_inj f n1 n2.
Proof.
  intros. inversion H. 
  assert (valid_access m2 chunk b2 (ofs + delta) Writable).
    eapply mi_access0; eauto with mem.
  destruct (valid_access_store _ _ _ _ v2 H4) as [n2 STORE]. 
  exists n2; split. eauto.
  constructor.
(* access *)
  intros.
  eapply store_valid_access_1; [apply STORE |].
  eapply mi_access0; eauto.
  eapply store_valid_access_2; [apply H0 |]. auto.
(* mem_contents *)
  intros.
  assert (perm m1 b0 ofs0 Nonempty). eapply perm_store_2; eauto. 
  rewrite (store_mem_contents _ _ _ _ _ _ H0).
  rewrite (store_mem_contents _ _ _ _ _ _ STORE).
  unfold update. 
  destruct (zeq b0 b1). subst b0.
  (* block = b1, block = b2 *)
  assert (b3 = b2) by congruence. subst b3.
  assert (delta0 = delta) by congruence. subst delta0.
  rewrite zeq_true.
  apply setN_inj with (access := fun ofs => perm m1 b1 ofs Nonempty).
  apply encode_val_inject; auto. auto. auto. 
  destruct (zeq b3 b2). subst b3.
  (* block <> b1, block = b2 *)
  rewrite setN_other. auto.
  rewrite encode_val_length. rewrite <- size_chunk_conv. intros. 
  assert (b2 <> b2 \/ ofs0 + delta0 <> (r - delta) + delta).
    eapply meminj_no_overlap_perm; eauto. 
    exploit store_valid_access_3. eexact H0. intros [A B].
    eapply perm_implies. apply A. omega. auto with mem.
  destruct H9. congruence. omega.
  (* block <> b1, block <> b2 *)
  eauto.
Qed.

Lemma store_unmapped_inj:
  forall f chunk m1 b1 ofs v1 n1 m2,
  mem_inj f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  mem_inj f n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* access *)
  eauto with mem.
(* mem_contents *)
  intros. 
  rewrite (store_mem_contents _ _ _ _ _ _ H0).
  rewrite update_o. eauto with mem. 
  congruence.
Qed.

Lemma store_outside_inj:
  forall f m1 m2 chunk b ofs v m2',
  mem_inj f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Nonempty ->
    ofs' + delta < ofs \/ ofs' + delta >= ofs + size_chunk chunk) ->
  store chunk m2 b ofs v = Some m2' ->
  mem_inj f m1 m2'.
Proof.
  intros. inversion H. constructor.
(* access *)
  eauto with mem.
(* mem_contents *)
  intros. 
  rewrite (store_mem_contents _ _ _ _ _ _ H1).
  unfold update. destruct (zeq b2 b). subst b2.
  rewrite setN_outside. auto. 
  rewrite encode_val_length. rewrite <- size_chunk_conv. 
  eapply H0; eauto. 
  eauto with mem.
Qed.

(** Preservation of allocations *)

Lemma alloc_right_inj:
  forall f m1 m2 lo hi b2 m2',
  mem_inj f m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  mem_inj f m1 m2'.
Proof.
  intros. injection H0. intros NEXT MEM.
  inversion H. constructor.
(* access *)
  intros. eauto with mem. 
(* mem_contents *)
  intros.
  assert (valid_access m2 Mint8unsigned b0 (ofs + delta) Nonempty).
    eapply mi_access0; eauto.
    split. simpl. red; intros. assert (ofs0 = ofs) by omega. congruence.
    simpl. apply Zone_divide. 
  assert (valid_block m2 b0) by eauto with mem.
  rewrite <- MEM; simpl. rewrite update_o. eauto with mem.
  rewrite NEXT. apply sym_not_equal. eauto with mem. 
Qed.

Lemma alloc_left_unmapped_inj:
  forall f m1 m2 lo hi m1' b1,
  mem_inj f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  f b1 = None ->
  mem_inj f m1' m2.
Proof.
  intros. inversion H. constructor.
(* access *)
  unfold update; intros.
  exploit valid_access_alloc_inv; eauto. unfold eq_block. intros. 
  destruct (zeq b0 b1). congruence. eauto.
(* mem_contents *)
  injection H0; intros NEXT MEM. intros. 
  rewrite <- MEM; simpl. rewrite NEXT. unfold update.
  exploit perm_alloc_inv; eauto. intros. 
  destruct (zeq b0 b1). constructor. eauto.
Qed.

Definition inj_offset_aligned (delta: Z) (size: Z) : Prop :=
  forall chunk, size_chunk chunk <= size -> (align_chunk chunk | delta).

Lemma alloc_left_mapped_inj:
  forall f m1 m2 lo hi m1' b1 b2 delta,
  mem_inj f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  inj_offset_aligned delta (hi-lo) ->
  (forall ofs p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) p) ->
  f b1 = Some(b2, delta) ->
  mem_inj f m1' m2.
Proof.
  intros. inversion H. constructor.
(* access *)
  intros. 
  exploit valid_access_alloc_inv; eauto. unfold eq_block. intros.
  destruct (zeq b0 b1). subst b0. rewrite H4 in H5. inversion H5; clear H5; subst b3 delta0.
  split. red; intros. 
  replace ofs0 with ((ofs0 - delta) + delta) by omega. 
  apply H3. omega. 
  destruct H6. apply Zdivide_plus_r. auto. apply H2. omega.
  eauto.
(* mem_contents *)
  injection H0; intros NEXT MEM. 
  intros. rewrite <- MEM; simpl. rewrite NEXT. unfold update.
  exploit perm_alloc_inv; eauto. intros. 
  destruct (zeq b0 b1). constructor. eauto.
Qed.

Lemma free_left_inj:
  forall f m1 m2 b lo hi m1',
  mem_inj f m1 m2 ->
  free m1 b lo hi = Some m1' ->
  mem_inj f m1' m2.
Proof.
  intros. exploit free_result; eauto. intro FREE. inversion H. constructor.
(* access *)
  intros. eauto with mem. 
(* mem_contents *)
  intros. rewrite FREE; simpl.
  assert (b=b1 /\ lo <= ofs < hi \/ (b<>b1 \/ ofs<lo \/ hi <= ofs)) by (unfold block; omega).
  destruct H3.
  destruct H3. subst b1.
  rewrite (clearN_in _ _ _ _ _ H4); auto.
  constructor.
  rewrite (clearN_out _ _ _ _ _ _ H3).
  apply mi_memval0; auto.
  eapply perm_free_3; eauto.
Qed.


Lemma free_right_inj:
  forall f m1 m2 b lo hi m2',
  mem_inj f m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs p ->
    lo <= ofs + delta < hi -> False) ->
  mem_inj f m1 m2'.
Proof.
  intros. exploit free_result; eauto. intro FREE. inversion H. constructor.
(* access *)
  intros. exploit mi_access0; eauto. intros [RG AL]. split; auto.
  red; intros. eapply perm_free_1; eauto. 
  destruct (zeq b2 b); auto. subst b. right.
  destruct (zlt ofs0 lo); auto. destruct (zle hi ofs0); auto.
  elimtype False. eapply H1 with (ofs := ofs0 - delta). eauto. 
  apply H3. omega. omega.
(* mem_contents *)
  intros. rewrite FREE; simpl.
  specialize (mi_memval0 _ _ _ _ H2 H3).
  assert (b=b2 /\ lo <= ofs+delta < hi \/ (b<>b2 \/ ofs+delta<lo \/ hi <= ofs+delta)) by (unfold block; omega).
  destruct H4. destruct H4. subst b2.
  specialize (H1 _ _ _ _ H2 H3). elimtype False; auto.
  rewrite (clearN_out _ _ _ _ _ _ H4); auto.
Qed.

(** Preservation of [drop_perm] operations. *)

Lemma drop_unmapped_inj:
  forall f m1 m2 b lo hi p m1',
  mem_inj f m1 m2 ->
  drop_perm m1 b lo hi p = Some m1' ->
  f b = None ->
  mem_inj f m1' m2.
Proof.
  intros. inv H. constructor. 
  intros. eapply mi_access0. eauto.
  eapply valid_access_drop_2; eauto. 
  intros. replace (mem_contents m1' b1 ofs) with (mem_contents m1 b1 ofs). 
  apply mi_memval0; auto. 
  eapply perm_drop_4; eauto. 
  unfold drop_perm in H0. destruct (range_perm_dec m1 b lo hi p); inv H0. 
  simpl. rewrite update_o; auto. congruence.
Qed.

Lemma drop_mapped_inj:
  forall f m1 m2 b1 b2 delta lo hi p m1',
  mem_inj f m1 m2 ->
  drop_perm m1 b1 lo hi p = Some m1' ->
  meminj_no_overlap f m1 ->
  f b1 = Some(b2, delta) ->
  exists m2',
      drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2'
   /\ mem_inj f m1' m2'.
Proof.
  intros. 
  assert ({ m2' | drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2' }).
  apply range_perm_drop_2. red; intros. 
  replace ofs with ((ofs - delta) + delta) by omega.
  eapply perm_inj; eauto. eapply range_perm_drop_1; eauto. omega. 
  destruct X as [m2' DROP]. exists m2'; split; auto.
  inv H. constructor; intros.
(* access *)
  exploit mi_access0; eauto. eapply valid_access_drop_2; eauto.
  intros [A B]. split; auto. red; intros.
  destruct (eq_block b1 b0). subst b0. rewrite H2 in H; inv H.
  (* b1 = b0 *)
  destruct (zlt ofs0 (lo + delta0)). eapply perm_drop_3; eauto. 
  destruct (zle (hi + delta0) ofs0). eapply perm_drop_3; eauto.
  destruct H3 as [C D].
  assert (perm_order p p0).
    eapply perm_drop_2. eexact H0. instantiate (1 := ofs0 - delta0). omega. 
    apply C. omega. 
  apply perm_implies with p; auto.
  eapply perm_drop_1. eauto. omega.
  (* b1 <> b0 *)
  eapply perm_drop_3; eauto.
  exploit H1; eauto. intros [P | P]. auto. right. 
  destruct (zlt lo hi). 
  exploit range_perm_in_bounds. eapply range_perm_drop_1. eexact H0. auto. 
  intros [U V].
  exploit valid_access_drop_2. eexact H0. eauto.
  intros [C D].
  exploit range_perm_in_bounds. eexact C. generalize (size_chunk_pos chunk); omega. 
  intros [X Y].
  generalize (size_chunk_pos chunk). omega.
  omega.
(* memval *)
  assert (A: perm m1 b0 ofs Nonempty). eapply perm_drop_4; eauto.
  exploit mi_memval0; eauto. intros B.
  unfold drop_perm in *. 
  destruct (range_perm_dec m1 b1 lo hi p); inversion H0; clear H0. clear H5.
  destruct (range_perm_dec m2 b2 (lo + delta) (hi + delta) p); inversion DROP; clear DROP. clear H4.
  simpl. unfold update. destruct (zeq b0 b1). 
  (* b1 = b0 *)
  subst b0. rewrite H2 in H; inv H. rewrite zeq_true. unfold proj_sumbool. 
  destruct (zle lo ofs).
  rewrite zle_true. 
  destruct (zlt ofs hi).
  rewrite zlt_true.
  destruct (perm_order_dec p Readable).
  simpl. auto.
  simpl. constructor.
  omega.
  rewrite zlt_false. simpl. auto. omega. 
  omega.
  rewrite zle_false. simpl. auto. omega.
  (* b1 <> b0 *)
  destruct (zeq b3 b2).
  (* b2 = b3 *)
  subst b3. exploit H1. eauto. eauto. eauto. intros [P | P]. congruence.
  exploit perm_in_bounds; eauto. intros X.
  destruct (zle (lo + delta) (ofs + delta0)).
  destruct (zlt (ofs + delta0) (hi + delta)).
  destruct (zlt lo hi). 
  exploit range_perm_in_bounds. eexact r. auto. intros [Y Z].
  omegaContradiction.
  omegaContradiction.
  simpl. auto.
  simpl. auto.
  auto.
Qed.

(** * Memory extensions *)

(**  A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by increasing the sizes of the memory blocks of [m1] (decreasing
  the low bounds, increasing the high bounds), and replacing some of
  the [Vundef] values stored in [m1] by more defined values stored
  in [m2] at the same locations. *)

Record extends_ (m1 m2: mem) : Prop :=
  mk_extends {
    mext_next: nextblock m1 = nextblock m2;
    mext_inj:  mem_inj inject_id m1 m2
(*
    mext_bounds: forall b, low_bound m2 b <= low_bound m1 b /\ high_bound m1 b <= high_bound m2 b
*)
  }.

Definition extends := extends_.

Theorem extends_refl:
  forall m, extends m m.
Proof.
  intros. constructor. auto. constructor.
  intros. unfold inject_id in H; inv H. replace (ofs + 0) with ofs by omega. auto.
  intros. unfold inject_id in H; inv H. replace (ofs + 0) with ofs by omega. 
  apply memval_inject_id.
(*  intros. omega. *)
Qed.

Theorem load_extends:
  forall chunk m1 m2 b ofs v1,
  extends m1 m2 ->
  load chunk m1 b ofs = Some v1 ->
  exists v2, load chunk m2 b ofs = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. inv H. exploit load_inj; eauto. unfold inject_id; reflexivity. 
  intros [v2 [A B]]. exists v2; split.
  replace (ofs + 0) with ofs in A by omega. auto.
  rewrite val_inject_id in B. auto.
Qed.

Theorem loadv_extends:
  forall chunk m1 m2 addr1 addr2 v1,
  extends m1 m2 ->
  loadv chunk m1 addr1 = Some v1 ->
  Val.lessdef addr1 addr2 ->
  exists v2, loadv chunk m2 addr2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  unfold loadv; intros. inv H1. 
  destruct addr2; try congruence. eapply load_extends; eauto. 
  congruence.
Qed.

Theorem store_within_extends:
  forall chunk m1 m2 b ofs v1 m1' v2,
  extends m1 m2 ->
  store chunk m1 b ofs v1 = Some m1' ->
  Val.lessdef v1 v2 ->
  exists m2',
     store chunk m2 b ofs v2 = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  exploit store_mapped_inj; eauto. 
    unfold inject_id; red; intros. inv H3; inv H4. auto.
    unfold inject_id; reflexivity.
    rewrite val_inject_id. eauto.
  intros [m2' [A B]].
  exists m2'; split.
  replace (ofs + 0) with ofs in A by omega. auto.
  split; auto.
  rewrite (nextblock_store _ _ _ _ _ _ H0).
  rewrite (nextblock_store _ _ _ _ _ _ A).
  auto.
(*
  intros.
  rewrite (bounds_store _ _ _ _ _ _ H0).
  rewrite (bounds_store _ _ _ _ _ _ A).
  auto.
*)
Qed.

Theorem store_outside_extends:
  forall chunk m1 m2 b ofs v m2',
  extends m1 m2 ->
  store chunk m2 b ofs v = Some m2' ->
  ofs + size_chunk chunk <= low_bound m1 b \/ high_bound m1 b <= ofs ->
  extends m1 m2'.
Proof.
  intros. inversion H. constructor.
  rewrite (nextblock_store _ _ _ _ _ _ H0). auto.
  eapply store_outside_inj; eauto.
  unfold inject_id; intros. inv H2.
  exploit perm_in_bounds; eauto. omega.
(* 
  intros.
  rewrite (bounds_store _ _ _ _ _ _ H0). auto.
*)
Qed.

Theorem storev_extends:
  forall chunk m1 m2 addr1 v1 m1' addr2 v2,
  extends m1 m2 ->
  storev chunk m1 addr1 v1 = Some m1' ->
  Val.lessdef addr1 addr2 ->
  Val.lessdef v1 v2 ->
  exists m2',
     storev chunk m2 addr2 v2 = Some m2'
  /\ extends m1' m2'.
Proof.
  unfold storev; intros. inv H1. 
  destruct addr2; try congruence. eapply store_within_extends; eauto. 
  congruence.
Qed.

Theorem alloc_extends:
  forall m1 m2 lo1 hi1 b m1' lo2 hi2,
  extends m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists m2',
     alloc m2 lo2 hi2 = (m2', b)
  /\ extends m1' m2'.
Proof.
  intros. inv H. 
  case_eq (alloc m2 lo2 hi2); intros m2' b' ALLOC. 
  assert (b' = b).
    rewrite (alloc_result _ _ _ _ _ H0). 
    rewrite (alloc_result _ _ _ _ _ ALLOC).
    auto.
  subst b'.
  exists m2'; split; auto.
  constructor. 
  rewrite (nextblock_alloc _ _ _ _ _ H0).
  rewrite (nextblock_alloc _ _ _ _ _ ALLOC). 
  congruence.
  eapply alloc_left_mapped_inj with (m1 := m1) (m2 := m2') (b2 := b) (delta := 0); eauto.
  eapply alloc_right_inj; eauto.
  eauto with mem.
  red. intros. apply Zdivide_0.
  intros.
  eapply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto.
  omega.
Qed.

Theorem free_left_extends:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  extends m1' m2.
Proof.
  intros. inv H. constructor.
  rewrite (nextblock_free _ _ _ _ _ H0). auto.
  eapply free_left_inj; eauto.
(*
  intros. rewrite (bounds_free _ _ _ _ _ H0). auto.
*)
Qed.

Theorem free_right_extends:
  forall m1 m2 b lo hi m2',
  extends m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall ofs p, lo <= ofs < hi -> ~perm m1 b ofs p) ->
  extends m1 m2'.
Proof.
  intros. inv H. constructor.
  rewrite (nextblock_free _ _ _ _ _ H0). auto.
  eapply free_right_inj; eauto.
  unfold inject_id; intros. inv H.
  elim (H1 ofs p); auto. omega.
(* 
  intros. rewrite (bounds_free _ _ _ _ _ H0). auto.
*)
Qed. 

Theorem free_parallel_extends:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  exists m2',
     free m2 b lo hi = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H. 
  assert ({ m2': mem | free m2 b lo hi = Some m2' }).
    apply range_perm_free. red; intros. 
    replace ofs with (ofs + 0) by omega.
    eapply perm_inj with (b1 := b); eauto.
    eapply free_range_perm; eauto.
  destruct X as [m2' FREE]. exists m2'; split; auto.
  inv H. constructor.
  rewrite (nextblock_free _ _ _ _ _ H0).
  rewrite (nextblock_free _ _ _ _ _ FREE). auto.
  eapply free_right_inj with (m1 := m1'); eauto. 
  eapply free_left_inj; eauto. 
  unfold inject_id; intros. inv H. 
  assert (~perm m1' b ofs p). eapply perm_free_2; eauto. omega. 
  contradiction.
(*
  intros.
  rewrite (bounds_free _ _ _ _ _ H0).
  rewrite (bounds_free _ _ _ _ _ FREE).
  auto.
*)
Qed.

Theorem valid_block_extends:
  forall m1 m2 b,
  extends m1 m2 ->
  (valid_block m1 b <-> valid_block m2 b).
Proof.
  intros. inv H. unfold valid_block. rewrite mext_next0. omega. 
Qed.

Theorem perm_extends:
  forall m1 m2 b ofs p,
  extends m1 m2 -> perm m1 b ofs p -> perm m2 b ofs p.
Proof.
  intros. inv H. replace ofs with (ofs + 0) by omega. 
  eapply perm_inj; eauto. 
Qed.

Theorem valid_access_extends:
  forall m1 m2 chunk b ofs p,
  extends m1 m2 -> valid_access m1 chunk b ofs p -> valid_access m2 chunk b ofs p.
Proof.
  intros. inv H. replace ofs with (ofs + 0) by omega. 
  eapply mi_access; eauto. auto. 
Qed.

(*
Theorem bounds_extends:
  forall m1 m2 b,
  extends m1 m2 -> low_bound m2 b <= low_bound m1 b /\ high_bound m1 b <= high_bound m2 b.
Proof.
  intros. inv H. auto.
Qed.
*)

(** * Memory injections *)

(** A memory state [m1] injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address;
- unallocated blocks in [m1] must be mapped to [None] by [f];
- if [f b = Some(b', delta)], [b'] must be valid in [m2];
- distinct blocks in [m1] are mapped to non-overlapping sub-blocks in [m2];
- the sizes of [m2]'s blocks are representable with signed machine integers;
- the offsets [delta] are representable with signed machine integers.
*)

Record inject_ (f: meminj) (m1 m2: mem) : Prop :=
  mk_inject {
    mi_inj:
      mem_inj f m1 m2;
    mi_freeblocks:
      forall b, ~(valid_block m1 b) -> f b = None;
    mi_mappedblocks:
      forall b b' delta, f b = Some(b', delta) -> valid_block m2 b';
    mi_no_overlap:
      meminj_no_overlap f m1;
    mi_range_offset:
      forall b b' delta,
      f b = Some(b', delta) ->
      Int.min_signed <= delta <= Int.max_signed;
    mi_range_block:
      forall b b' delta,
      f b = Some(b', delta) ->
      delta = 0 \/ 
      (Int.min_signed <= low_bound m2 b' /\ high_bound m2 b' <= Int.max_signed)
  }.

Definition inject := inject_.

Hint Local Resolve mi_mappedblocks mi_range_offset: mem.

(** Preservation of access validity and pointer validity *)

Theorem valid_block_inject_1:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m1 b1.
Proof.
  intros. inv H. destruct (zlt b1 (nextblock m1)). auto. 
  assert (f b1 = None). eapply mi_freeblocks; eauto. congruence.
Qed.

Theorem valid_block_inject_2:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m2 b2.
Proof.
  intros. eapply mi_mappedblocks; eauto. 
Qed.

Hint Local Resolve valid_block_inject_1 valid_block_inject_2: mem.

Theorem perm_inject:
  forall f m1 m2 b1 b2 delta ofs p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  perm m1 b1 ofs p -> perm m2 b2 (ofs + delta) p.
Proof.
  intros. inv H0. eapply perm_inj; eauto. 
Qed.

Theorem valid_access_inject:
  forall f m1 m2 chunk b1 ofs b2 delta p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_access m1 chunk b1 ofs p ->
  valid_access m2 chunk b2 (ofs + delta) p.
Proof.
  intros. eapply mi_access; eauto. apply mi_inj; auto. 
Qed.

Theorem valid_pointer_inject:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_pointer m1 b1 ofs = true ->
  valid_pointer m2 b2 (ofs + delta) = true.
Proof.
  intros. 
  rewrite valid_pointer_valid_access in H1.
  rewrite valid_pointer_valid_access.
  eapply valid_access_inject; eauto.
Qed.

(** The following lemmas establish the absence of machine integer overflow
  during address computations. *)

Lemma address_inject:
  forall f m1 m2 b1 ofs1 b2 delta,
  inject f m1 m2 ->
  perm m1 b1 (Int.signed ofs1) Nonempty ->
  f b1 = Some (b2, delta) ->
  Int.signed (Int.add ofs1 (Int.repr delta)) = Int.signed ofs1 + delta.
Proof.
  intros.
  exploit perm_inject; eauto. intro A.
  exploit perm_in_bounds. eexact A. intros [B C]. 
  exploit mi_range_block; eauto. intros [D | [E F]].
  subst delta. rewrite Int.add_zero. omega.
  rewrite Int.add_signed.
  repeat rewrite Int.signed_repr. auto.
  eapply mi_range_offset; eauto.
  omega. 
  eapply mi_range_offset; eauto.
Qed.

Lemma address_inject':
  forall f m1 m2 chunk b1 ofs1 b2 delta,
  inject f m1 m2 ->
  valid_access m1 chunk b1 (Int.signed ofs1) Nonempty ->
  f b1 = Some (b2, delta) ->
  Int.signed (Int.add ofs1 (Int.repr delta)) = Int.signed ofs1 + delta.
Proof.
  intros. destruct H0. eapply address_inject; eauto. 
  apply H0. generalize (size_chunk_pos chunk). omega. 
Qed.

Theorem valid_pointer_inject_no_overflow:
  forall f m1 m2 b ofs b' x,
  inject f m1 m2 ->
  valid_pointer m1 b (Int.signed ofs) = true ->
  f b = Some(b', x) ->
  Int.min_signed <= Int.signed ofs + Int.signed (Int.repr x) <= Int.max_signed.
Proof.
  intros. rewrite valid_pointer_valid_access in H0.
  exploit address_inject'; eauto. intros.
  rewrite Int.signed_repr; eauto.
  rewrite <- H2. apply Int.signed_range. 
  eapply mi_range_offset; eauto.
Qed.

Theorem valid_pointer_inject_val:
  forall f m1 m2 b ofs b' ofs',
  inject f m1 m2 ->
  valid_pointer m1 b (Int.signed ofs) = true ->
  val_inject f (Vptr b ofs) (Vptr b' ofs') ->
  valid_pointer m2 b' (Int.signed ofs') = true.
Proof.
  intros. inv H1.
  exploit valid_pointer_inject_no_overflow; eauto. intro NOOV.
  rewrite Int.add_signed. rewrite Int.signed_repr; auto.
  rewrite Int.signed_repr.
  eapply valid_pointer_inject; eauto.
  eapply mi_range_offset; eauto.
Qed.

Theorem inject_no_overlap:
  forall f m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2,
  inject f m1 m2 ->
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m1 b1 ofs1 Nonempty ->
  perm m1 b2 ofs2 Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.
Proof.
  intros. inv H. eapply meminj_no_overlap_perm; eauto.
Qed.

Theorem different_pointers_inject:
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
Proof.
  intros. 
  rewrite valid_pointer_valid_access in H1. 
  rewrite valid_pointer_valid_access in H2. 
  rewrite (address_inject' _ _ _ _ _ _ _ _ H H1 H3). 
  rewrite (address_inject' _ _ _ _ _ _ _ _ H H2 H4). 
  inv H1. simpl in H5. inv H2. simpl in H1.
  eapply meminj_no_overlap_perm. 
  eapply mi_no_overlap; eauto. eauto. eauto. eauto. 
  apply (H5 (Int.signed ofs1)). omega.
  apply (H1 (Int.signed ofs2)). omega.
Qed.

(** Preservation of loads *)

Theorem load_inject:
  forall f m1 m2 chunk b1 ofs b2 delta v1,
  inject f m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ val_inject f v1 v2.
Proof.
  intros. inv H. eapply load_inj; eauto. 
Qed.

Theorem loadv_inject:
  forall f m1 m2 chunk a1 a2 v1,
  inject f m1 m2 ->
  loadv chunk m1 a1 = Some v1 ->
  val_inject f a1 a2 ->
  exists v2, loadv chunk m2 a2 = Some v2 /\ val_inject f v1 v2.
Proof.
  intros. inv H1; simpl in H0; try discriminate.
  exploit load_inject; eauto. intros [v2 [LOAD INJ]].
  exists v2; split; auto. simpl.
  replace (Int.signed (Int.add ofs1 (Int.repr delta)))
     with (Int.signed ofs1 + delta).
  auto. symmetry. eapply address_inject'; eauto with mem.
Qed.

(** Preservation of stores *)

Theorem store_mapped_inject:
  forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  val_inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ inject f n1 n2.
Proof.
  intros. inversion H.
  exploit store_mapped_inj; eauto. intros [n2 [STORE MI]].
  exists n2; split. eauto. constructor.
(* inj *)
  auto.
(* freeblocks *)
  eauto with mem. 
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros.
  repeat rewrite (bounds_store _ _ _ _ _ _ H0).
  eauto. 
(* range offset *)
  eauto.
(* range blocks *)
  intros. rewrite (bounds_store _ _ _ _ _ _ STORE). eauto.
Qed.

Theorem store_unmapped_inject:
  forall f chunk m1 b1 ofs v1 n1 m2,
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  inject f n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* inj *)
  eapply store_unmapped_inj; eauto.
(* freeblocks *)
  eauto with mem. 
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. 
  repeat rewrite (bounds_store _ _ _ _ _ _ H0).
  eauto. 
(* range offset *)
  eauto.
(* range blocks *)
  auto.
Qed.

Theorem store_outside_inject:
  forall f m1 m2 chunk b ofs v m2',
  inject f m1 m2 ->
  (forall b' delta,
    f b' = Some(b, delta) ->
    high_bound m1 b' + delta <= ofs
    \/ ofs + size_chunk chunk <= low_bound m1 b' + delta) ->
  store chunk m2 b ofs v = Some m2' ->
  inject f m1 m2'.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply store_outside_inj; eauto.
  intros. exploit perm_in_bounds; eauto. intro. 
  exploit H0; eauto. intro. omega. 
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* range offset *)
  auto.
(* rang blocks *)
  intros. rewrite (bounds_store _ _ _ _ _ _ H1). eauto.
Qed.

Theorem storev_mapped_inject:
  forall f chunk m1 a1 v1 n1 m2 a2 v2,
  inject f m1 m2 ->
  storev chunk m1 a1 v1 = Some n1 ->
  val_inject f a1 a2 ->
  val_inject f v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 = Some n2 /\ inject f n1 n2.
Proof.
  intros. inv H1; simpl in H0; try discriminate.
  simpl. replace (Int.signed (Int.add ofs1 (Int.repr delta)))
            with (Int.signed ofs1 + delta).
  eapply store_mapped_inject; eauto.
  symmetry. eapply address_inject'; eauto with mem.
Qed.

(* Preservation of allocations *)

Theorem alloc_right_inject:
  forall f m1 m2 lo hi b2 m2',
  inject f m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  inject f m1 m2'.
Proof.
  intros. injection H0. intros NEXT MEM.
  inversion H. constructor.
(* inj *)
  eapply alloc_right_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* range offset *)
  auto.
(* range block *)
  intros. rewrite (bounds_alloc_other _ _ _ _ _ H0). eauto. 
  eapply valid_not_valid_diff; eauto with mem.
Qed.

Theorem alloc_left_unmapped_inject:
  forall f m1 m2 lo hi m1' b1,
  inject f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = None
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros. inversion H.
  assert (inject_incr f (update b1 None f)).
    red; unfold update; intros. destruct (zeq b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
  assert (mem_inj (update b1 None f) m1 m2).
    inversion mi_inj0; constructor; eauto with mem.
    unfold update; intros. destruct (zeq b0 b1). congruence. eauto. 
    unfold update; intros. destruct (zeq b0 b1). congruence. 
    apply memval_inject_incr with f; auto. 
  exists (update b1 None f); split. constructor.
(* inj *)
  eapply alloc_left_unmapped_inj; eauto. apply update_s. 
(* freeblocks *)
  intros. unfold update. destruct (zeq b b1). auto. 
  apply mi_freeblocks0. red; intro; elim H3. eauto with mem. 
(* mappedblocks *)
  unfold update; intros. destruct (zeq b b1). congruence. eauto. 
(* no overlap *)
  unfold update; red; intros.
  destruct (zeq b0 b1); destruct (zeq b2 b1); try congruence.
  repeat rewrite (bounds_alloc_other _ _ _ _ _ H0); eauto.
(* range offset *)
  unfold update; intros.
  destruct (zeq b b1). congruence. eauto.
(* range block *)
  unfold update; intros.
  destruct (zeq b b1). congruence. eauto.
(* incr *)
  split. auto. 
(* image *)
  split. apply update_s.
(* incr *)
  intros; apply update_o; auto.
Qed.

Theorem alloc_left_mapped_inject:
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
Proof.
  intros. inversion H.
  assert (inject_incr f (update b1 (Some(b2, delta)) f)).
    red; unfold update; intros. destruct (zeq b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
  assert (mem_inj (update b1 (Some(b2, delta)) f) m1 m2).
    inversion mi_inj0; constructor; eauto with mem.
    unfold update; intros. destruct (zeq b0 b1).
      inv H8. elim (fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
      eauto.
    unfold update; intros. destruct (zeq b0 b1).
      inv H8. elim (fresh_block_alloc _ _ _ _ _ H0). eauto with mem. 
      apply memval_inject_incr with f; auto. 
  exists (update b1 (Some(b2, delta)) f). split. constructor.
(* inj *)
  eapply alloc_left_mapped_inj; eauto. apply update_s.
(* freeblocks *)
  unfold update; intros. destruct (zeq b b1). subst b. 
  elim H9. eauto with mem.
  eauto with mem.
(* mappedblocks *)
  unfold update; intros. destruct (zeq b b1). inv H9. auto.
  eauto.
(* overlap *)
  unfold update; red; intros.
  repeat rewrite (bounds_alloc _ _ _ _ _ H0). unfold eq_block. 
  destruct (zeq b0 b1); destruct (zeq b3 b1); simpl.
  inv H10; inv H11. congruence.
  inv H10. destruct (zeq b1' b2'); auto. subst b2'. 
  right. generalize (H6 _ _ H11). tauto. 
  inv H11. destruct (zeq b1' b2'); auto. subst b2'. 
  right. eapply H6; eauto. 
  eauto.
(* range offset *)
  unfold update; intros. destruct (zeq b b1). inv H9. auto. eauto.
(* range block *)
  unfold update; intros. destruct (zeq b b1). inv H9. auto. eauto.
(* incr *)
  split. auto.
(* image of b1 *)
  split. apply update_s.
(* image of others *)
  intros. apply update_o; auto.
Qed.

Theorem alloc_parallel_inject:
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
Proof.
  intros.
  case_eq (alloc m2 lo2 hi2). intros m2' b2 ALLOC.
  exploit alloc_left_mapped_inject. 
  eapply alloc_right_inject; eauto.
  eauto.
  instantiate (1 := b2). eauto with mem.
  instantiate (1 := 0). generalize Int.min_signed_neg Int.max_signed_pos; omega.
  auto.
  intros.
  apply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto. omega.
  red; intros. apply Zdivide_0.
  intros. elimtype False. apply (valid_not_valid_diff m2 b2 b2); eauto with mem.
  intros [f' [A [B [C D]]]].
  exists f'; exists m2'; exists b2; auto.
Qed.

(** Preservation of [free] operations *)

Lemma free_left_inject:
  forall f m1 m2 b lo hi m1',
  inject f m1 m2 ->
  free m1 b lo hi = Some m1' ->
  inject f m1' m2.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply free_left_inj; eauto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  auto.
(* no overlap *)
  red; intros. repeat rewrite (bounds_free _ _ _ _ _ H0). eauto. 
(* range offset *)
  auto.
(* range block *)
  auto.
Qed.

Lemma free_list_left_inject:
  forall f m2 l m1 m1',
  inject f m1 m2 ->
  free_list m1 l = Some m1' ->
  inject f m1' m2.
Proof.
  induction l; simpl; intros. 
  inv H0. auto.
  destruct a as [[b lo] hi]. generalize H0. case_eq (free m1 b lo hi); intros.
  apply IHl with m; auto. eapply free_left_inject; eauto.
  congruence.
Qed.

Lemma free_right_inject:
  forall f m1 m2 b lo hi m2',
  inject f m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs p ->
    lo <= ofs + delta < hi -> False) ->
  inject f m1 m2'.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply free_right_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* range offset *)
  auto.
(* range blocks *)
  intros. rewrite (bounds_free _ _ _ _ _ H0). eauto.
Qed.

Lemma perm_free_list:
  forall l m m' b ofs p,
  free_list m l = Some m' ->
  perm m' b ofs p ->
  perm m b ofs p /\ 
  (forall lo hi, In (b, lo, hi) l -> lo <= ofs < hi -> False).
Proof.
  induction l; intros until p; simpl.
  intros. inv H. split; auto. 
  destruct a as [[b1 lo1] hi1].
  case_eq (free m b1 lo1 hi1); intros; try congruence.
  exploit IHl; eauto. intros [A B].
  split. eauto with mem.
  intros. destruct H2. inv H2.
  elim (perm_free_2 _ _ _ _ _ H ofs p). auto. auto.
  eauto.
Qed.

Theorem free_inject:
  forall f m1 l m1' m2 b lo hi m2',
  inject f m1 m2 ->
  free_list m1 l = Some m1' ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs p,
    f b1 = Some(b, delta) -> 
    perm m1 b1 ofs p -> lo <= ofs + delta < hi ->
    exists lo1, exists hi1, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
  inject f m1' m2'.
Proof.
  intros. 
  eapply free_right_inject; eauto. 
  eapply free_list_left_inject; eauto.
  intros. exploit perm_free_list; eauto. intros [A B].
  exploit H2; eauto. intros [lo1 [hi1 [C D]]]. eauto.
Qed.

(*
Theorem free_inject':
  forall f m1 l m1' m2 b lo hi m2',
  inject f m1 m2 ->
  free_list m1 l = Some m1' ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta,
    f b1 = Some(b, delta) -> In (b1, low_bound m1 b1, high_bound m1 b1) l) ->
  inject f m1' m2'.
Proof.
  intros. eapply free_inject; eauto.
  intros. exists (low_bound m1 b1); exists (high_bound m1 b1).
  split. eauto. apply perm_in_bounds with p. auto.
Qed.
*)

(** Injecting a memory into itself. *)

Definition flat_inj (thr: block) : meminj :=
  fun (b: block) => if zlt b thr then Some(b, 0) else None.

Definition inject_neutral (thr: block) (m: mem) :=
  mem_inj (flat_inj thr) m m.

Remark flat_inj_no_overlap:
  forall thr m, meminj_no_overlap (flat_inj thr) m.
Proof.
  unfold flat_inj; intros; red; intros.
  destruct (zlt b1 thr); inversion H0; subst.
  destruct (zlt b2 thr); inversion H1; subst.
  auto.
Qed.

Theorem neutral_inject:
  forall m, inject_neutral (nextblock m) m -> inject (flat_inj (nextblock m)) m m.
Proof.
  intros. constructor.
(* meminj *)
  auto.
(* freeblocks *)
  unfold flat_inj, valid_block; intros.
  apply zlt_false. omega.
(* mappedblocks *)
  unfold flat_inj, valid_block; intros. 
  destruct (zlt b (nextblock m)); inversion H0; subst. auto.
(* no overlap *)
  apply flat_inj_no_overlap.
(* range *)
  unfold flat_inj; intros.
  destruct (zlt b (nextblock m)); inv H0.
  generalize Int.min_signed_neg Int.max_signed_pos; omega.
(* range *)
  unfold flat_inj; intros.
  destruct (zlt b (nextblock m)); inv H0. auto.
Qed.

Theorem empty_inject_neutral:
  forall thr, inject_neutral thr empty.
Proof.
  intros; red; constructor.
(* access *)
  unfold flat_inj; intros. destruct (zlt b1 thr); inv H.
  replace (ofs + 0) with ofs by omega; auto.
(* mem_contents *)
  intros; simpl; constructor.
Qed.

Theorem alloc_inject_neutral:
  forall thr m lo hi b m',
  alloc m lo hi = (m', b) ->
  inject_neutral thr m ->
  nextblock m < thr ->
  inject_neutral thr m'.
Proof.
  intros; red. 
  eapply alloc_left_mapped_inj with (m1 := m) (b2 := b) (delta := 0). 
  eapply alloc_right_inj; eauto. eauto. eauto with mem. 
  red. intros. apply Zdivide_0. 
  intros.
  apply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto. omega. 
  unfold flat_inj. apply zlt_true. 
  rewrite (alloc_result _ _ _ _ _ H). auto.
Qed.

Theorem store_inject_neutral:
  forall chunk m b ofs v m' thr,
  store chunk m b ofs v = Some m' ->
  inject_neutral thr m ->
  b < thr ->
  val_inject (flat_inj thr) v v ->
  inject_neutral thr m'.
Proof.
  intros; red.
  exploit store_mapped_inj. eauto. eauto. apply flat_inj_no_overlap. 
  unfold flat_inj. apply zlt_true; auto. eauto.
  replace (ofs + 0) with ofs by omega.  
  intros [m'' [A B]]. congruence.
Qed. 

Theorem drop_inject_neutral:
  forall m b lo hi p m' thr,
  drop_perm m b lo hi p = Some m' ->
  inject_neutral thr m ->
  b < thr ->
  inject_neutral thr m'.
Proof.
  unfold inject_neutral; intros.
  exploit drop_mapped_inj; eauto. apply flat_inj_no_overlap. 
  unfold flat_inj. apply zlt_true; eauto. 
  repeat rewrite Zplus_0_r. intros [m'' [A B]]. congruence.
Qed.

End Mem.

Notation mem := Mem.mem.

Global Opaque Mem.alloc Mem.free Mem.store Mem.load.

Hint Resolve
  Mem.valid_not_valid_diff
  Mem.perm_implies
  Mem.perm_valid_block
  Mem.range_perm_implies
  Mem.valid_access_implies
  Mem.valid_access_valid_block
  Mem.valid_access_perm
  Mem.valid_access_load
  Mem.load_valid_access
  Mem.valid_access_store
  Mem.perm_store_1
  Mem.perm_store_2
  Mem.nextblock_store
  Mem.store_valid_block_1
  Mem.store_valid_block_2
  Mem.store_valid_access_1
  Mem.store_valid_access_2
  Mem.store_valid_access_3
  Mem.nextblock_alloc
  Mem.alloc_result
  Mem.valid_block_alloc
  Mem.fresh_block_alloc
  Mem.valid_new_block
  Mem.perm_alloc_1
  Mem.perm_alloc_2
  Mem.perm_alloc_3
  Mem.perm_alloc_inv
  Mem.valid_access_alloc_other
  Mem.valid_access_alloc_same
  Mem.valid_access_alloc_inv
  Mem.range_perm_free
  Mem.free_range_perm
  Mem.nextblock_free
  Mem.valid_block_free_1
  Mem.valid_block_free_2
  Mem.perm_free_1
  Mem.perm_free_2
  Mem.perm_free_3
  Mem.valid_access_free_1
  Mem.valid_access_free_2
  Mem.valid_access_free_inv_1
  Mem.valid_access_free_inv_2
: mem.
