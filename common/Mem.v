(** This file develops the memory model that is used in the dynamic
  semantics of all the languages of the compiler back-end.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block;
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address.
*)
  
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.

(** * Structure of memory states *)

(** A memory state is organized in several disjoint blocks.  Each block
  has a low and a high bound that defines its size.  Each block map
  byte offsets to the contents of this byte. *)

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

(** The possible contents of a byte-sized memory cell.  To give intuitions,
  a 4-byte value [v] stored at offset [d] will be represented by
  the content [Datum32 v] at offset [d] and [Cont] at offsets [d+1],
  [d+2] and [d+3].  The [Cont] contents enable detecting future writes
  that would overlap partially the 4-byte value. *)

Inductive content : Set :=
  | Undef: content              (**r undefined contents *)
  | Datum8: val -> content      (**r a value that fits in 1 byte *)
  | Datum16: val -> content     (**r first byte of a 2-byte value *)
  | Datum32: val -> content     (**r first byte of a 4-byte value *)
  | Datum64: val -> content     (**r first byte of a 8-byte value *)
  | Cont: content.            (**r continuation bytes for a multi-byte value *)

Definition contentmap : Set := Z -> content.

(** A memory block comprises the dimensions of the block (low and high bounds)
  plus a mapping from byte offsets to contents.  For technical reasons,
  we also carry around a proof that the mapping is equal to [Undef]
  outside the range of allowed byte offsets. *)

Record block_contents : Set := mkblock {
  low: Z;
  high: Z;
  contents: contentmap;
  undef_outside: forall ofs, ofs < low \/ ofs >= high -> contents ofs = Undef
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
  It is useful to extract only the size information as given by the
  following [memory_size] type. *)

Inductive memory_size : Set :=
  | Size8: memory_size
  | Size16: memory_size
  | Size32: memory_size
  | Size64: memory_size.

Definition size_mem (sz: memory_size) :=
  match sz with
  | Size8 => 1
  | Size16 => 2
  | Size32 => 4
  | Size64 => 8
  end.

Definition mem_chunk (chunk: memory_chunk) :=
  match chunk with
  | Mint8signed => Size8
  | Mint8unsigned => Size8
  | Mint16signed => Size16
  | Mint16unsigned => Size16
  | Mint32 => Size32
  | Mfloat32 => Size32
  | Mfloat64 => Size64
  end.

Definition size_chunk (chunk: memory_chunk) := size_mem (mem_chunk chunk).

(** The initial store. *)

Remark one_pos: 1 > 0.
Proof. omega. Qed.

Remark undef_undef_outside:
  forall lo hi ofs, ofs < lo \/ ofs >= hi -> (fun y => Undef) ofs = Undef.
Proof.
  auto.
Qed.

Definition empty_block (lo hi: Z) : block_contents :=
  mkblock lo hi (fun y => Undef) (undef_undef_outside lo hi).

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

Definition getN (n: nat) (p: Z) (m: contentmap) : content :=
  if check_cont n (p + 1) m then m p else Undef.

Fixpoint set_cont (n: nat) (p: Z) (m: contentmap) {struct n} : contentmap :=
  match n with
  | O => m
  | S n1 => update p Cont (set_cont n1 (p + 1) m)
  end.

Definition setN (n: nat) (p: Z) (v: content) (m: contentmap) : contentmap :=
  update p v (set_cont n (p + 1) m).

Lemma check_cont_true:
  forall n p m,
  (forall q, p <= q < p + Z_of_nat n -> m q = Cont) ->
  check_cont n p m = true.
Proof.
  induction n; intros.
  reflexivity.
  simpl. rewrite H. apply IHn. 
  intros. apply H. rewrite inj_S. omega.
  rewrite inj_S. omega. 
Qed.

Hint Resolve check_cont_true.

Lemma check_cont_inv:
  forall n p m,
  check_cont n p m = true ->
  (forall q, p <= q < p + Z_of_nat n -> m q = Cont).
Proof.
  induction n; intros until m.
  unfold Z_of_nat. intros. omegaContradiction.
  unfold check_cont; fold check_cont. 
  caseEq (m p); intros; try discriminate.
  assert (p = q \/ p + 1 <= q < (p + 1) + Z_of_nat n).
    rewrite inj_S in H1. omega. 
  elim H2; intro.
  subst q. auto.
  apply IHn with (p + 1); auto.
Qed.

Hint Resolve check_cont_inv.

Lemma check_cont_false:
  forall n p q m,
  p <= q < p + Z_of_nat n ->
  m q <> Cont ->
  check_cont n p m = false.
Proof.
  intros. caseEq (check_cont n p m); intro.
  generalize (check_cont_inv _ _ _ H1 q H). intro. contradiction.
  auto.
Qed.

Hint Resolve check_cont_false.

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

Hint Resolve set_cont_inside.

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

Hint Resolve set_cont_outside.

Lemma getN_setN_same:
  forall n p v m,
  getN n p (setN n p v m) = v.
Proof.
  intros. unfold getN, setN.
  rewrite check_cont_true. apply update_s.
  intros. rewrite update_o. apply set_cont_inside. auto.
  omega. 
Qed.

Hint Resolve getN_setN_same.

Lemma getN_setN_other:
  forall n1 n2 p1 p2 v m,
  p1 + Z_of_nat n1 < p2 \/ p2 + Z_of_nat n2 < p1 ->
  getN n2 p2 (setN n1 p1 v m) = getN n2 p2 m.
Proof.
  intros. unfold getN, setN.
  caseEq (check_cont n2 (p2 + 1) m); intro.
  rewrite check_cont_true. rewrite update_o.
  apply set_cont_outside. omega. omega.
  intros. rewrite update_o. rewrite set_cont_outside.
  eapply check_cont_inv. eauto. auto.
  omega. omega. 
  caseEq (check_cont n2 (p2 + 1) (update p1 v (set_cont n1 (p1 + 1) m))); intros.
  assert (check_cont n2 (p2 + 1) m = true).
  apply check_cont_true. intros. 
  generalize (check_cont_inv _ _ _ H1 q H2).
  rewrite update_o. rewrite set_cont_outside. auto. omega. omega.
  rewrite H0 in H2; discriminate.
  auto.
Qed. 

Hint Resolve getN_setN_other.

Lemma getN_setN_overlap:
  forall n1 n2 p1 p2 v m,
  p1 <> p2 ->
  p1 + Z_of_nat n1 >= p2 -> p2 + Z_of_nat n2 >= p1 ->
  v <> Cont ->
  getN n2 p2 (setN n1 p1 v m) = Cont \/
  getN n2 p2 (setN n1 p1 v m) = Undef.
Proof.
  intros. unfold getN.
  caseEq (check_cont n2 (p2 + 1) (setN n1 p1 v m)); intro.
  case (zlt p2 p1); intro.
  assert (p2 + 1 <= p1 < p2 + 1 + Z_of_nat n2). omega.
  generalize (check_cont_inv _ _ _ H3 p1 H4). 
  unfold setN. rewrite update_s. intro. contradiction.
  left. unfold setN. rewrite update_o.
  apply set_cont_inside. omega. auto.
  right; auto.
Qed. 

Hint Resolve getN_setN_overlap.

Lemma getN_setN_mismatch:
  forall n1 n2 p v m,
  getN n2 p (setN n1 p v m) = v \/ getN n2 p (setN n1 p v m) = Undef.
Proof.
  intros. unfold getN. 
  caseEq (check_cont n2 (p + 1) (setN n1 p v m)); intro.
  left. unfold setN. apply update_s.
  right. auto.
Qed.

Hint Resolve getN_setN_mismatch.

Lemma getN_init:
  forall n p,
  getN n p (fun y => Undef) = Undef.
Proof.
  intros. unfold getN.
  case (check_cont n (p + 1) (fun y => Undef)); auto.
Qed.

Hint Resolve getN_init.

(** The following function checks whether accessing the given memory chunk
  at the given offset in the given block respects the bounds of the block. *)

Definition in_bounds (chunk: memory_chunk) (ofs: Z) (c: block_contents) : 
        {c.(low) <= ofs /\ ofs + size_chunk chunk <= c.(high)}
      + {c.(low) > ofs \/ ofs + size_chunk chunk > c.(high)} :=
  match zle c.(low) ofs, zle (ofs + size_chunk chunk) c.(high) with
  | left P1, left P2 => left _ (conj P1 P2)
  | left P1, right P2 => right _ (or_intror _ P2)
  | right P1, _ => right _ (or_introl _ P1)
  end.

Lemma in_bounds_holds:
  forall (chunk: memory_chunk) (ofs: Z) (c: block_contents)
         (A: Set) (a b: A),
  c.(low) <= ofs -> ofs + size_chunk chunk <= c.(high) ->
  (if in_bounds chunk ofs c then a else b) = a.
Proof.
  intros. case (in_bounds chunk ofs c); intro.
  auto.
  omegaContradiction.
Qed.

Lemma in_bounds_exten:
  forall (chunk: memory_chunk) (ofs: Z) (c: block_contents) (x: contentmap) P,
  in_bounds chunk ofs (mkblock (low c) (high c) x P) =
  in_bounds chunk ofs c.
Proof.
  intros; reflexivity.
Qed.

Hint Resolve in_bounds_holds in_bounds_exten.

(** [valid_pointer] holds if the given block address is valid and the
  given offset falls within the bounds of the corresponding block. *)

Definition valid_pointer (m: mem) (b: block) (ofs: Z) : bool :=
  if zlt b m.(nextblock) then
    (let c := m.(blocks) b in
     if zle c.(low) ofs then if zlt ofs c.(high) then true else false
                        else false)
  else false.

(** Read a quantity of size [sz] at offset [ofs] in block contents [c].
  Return [Vundef] if the requested size does not match that of the
  current contents, or if the following offsets do not contain [Cont].
  The first check captures a size mismatch between the read and the
  latest write at this offset.  The second check captures partial overwriting
  of the latest write at this offset by a more recent write at a nearby
  offset. *)

Definition load_contents (sz: memory_size) (c: contentmap) (ofs: Z) : val :=
  match sz with
  | Size8 =>
      match getN 0%nat ofs c with
      | Datum8 n => n
      | _ => Vundef
      end
  | Size16 =>
      match getN 1%nat ofs c with
      | Datum16 n => n
      | _ => Vundef
      end
  | Size32 =>
      match getN 3%nat ofs c with
      | Datum32 n => n
      | _ => Vundef
      end
  | Size64 =>
      match getN 7%nat ofs c with
      | Datum64 n => n
      | _ => Vundef
      end
  end.

(** [load chunk m b ofs] perform a read in memory state [m], at address
  [b] and offset [ofs].  [None] is returned if the address is invalid
  or the memory access is out of bounds. *)

Definition load (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z)
                : option val :=
  if zlt b m.(nextblock) then
    (let c := m.(blocks) b in
     if in_bounds chunk ofs c
     then Some (Val.load_result chunk
                    (load_contents (mem_chunk chunk) c.(contents) ofs))
     else None)
  else
    None.

(** [loadv chunk m addr] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

Definition loadv (chunk: memory_chunk) (m: mem) (addr: val) : option val :=
  match addr with
  | Vptr b ofs => load chunk m b (Int.signed ofs)
  | _ => None
  end.

Theorem load_in_bounds:
  forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z),
  valid_block m b ->
  low_bound m b <= ofs ->
  ofs + size_chunk chunk <= high_bound m b ->
  exists v, load chunk m b ofs = Some v.
Proof.
  intros. unfold load. rewrite zlt_true; auto.
  rewrite in_bounds_holds. 
  exists (Val.load_result chunk
            (load_contents (mem_chunk chunk)
                           (contents (m.(blocks) b))
                           ofs)).
  auto.
  exact H0. exact H1.
Qed.

Lemma load_inv:
  forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val),
  load chunk m b ofs = Some v ->
  let c := m.(blocks) b in
  b < m.(nextblock) /\
  c.(low) <= ofs /\
  ofs + size_chunk chunk <= c.(high) /\
  Val.load_result chunk (load_contents (mem_chunk chunk)  c.(contents) ofs) = v.
Proof.
  intros until v; unfold load.
  case (zlt b (nextblock m)); intro.
  set (c := m.(blocks) b).
  case (in_bounds chunk ofs c).
  intuition congruence.
  intros; discriminate.
  intros; discriminate.
Qed.
Hint Resolve load_in_bounds load_inv.

(* Write the value [v] with size [sz] at offset [ofs] in block contents [c].
   Return updated block contents.  [Cont] contents are stored at the following
   offsets. *)

Definition store_contents (sz: memory_size) (c: contentmap)
                          (ofs: Z) (v: val) : contentmap :=
  match sz with
  | Size8 =>
      setN 0%nat ofs (Datum8 v) c
  | Size16 =>
      setN 1%nat ofs (Datum16 v) c
  | Size32 =>
      setN 3%nat ofs (Datum32 v) c
  | Size64 =>
      setN 7%nat ofs (Datum64 v) c
  end.

Remark store_contents_undef_outside:
  forall sz c ofs v lo hi,
  lo <= ofs /\ ofs + size_mem sz <= hi ->
  (forall x, x < lo \/ x >= hi -> c x = Undef) ->
  (forall x, x < lo \/ x >= hi ->
     store_contents sz c ofs v x = Undef).
Proof.
  intros until hi; intros [LO HI] UO.
  assert (forall n d x, 
            ofs + (1 + Z_of_nat n) <= hi ->
            x < lo \/ x >= hi ->
            setN n ofs d c x = Undef).
    intros. unfold setN. rewrite update_o.
    transitivity (c x). apply set_cont_outside. omega. 
    apply UO. omega. omega.
  unfold store_contents; destruct sz; unfold size_mem in HI;
  intros; apply H; auto; simpl Z_of_nat; auto.
Qed.

Definition unchecked_store
     (chunk: memory_chunk) (m: mem) (b: block)
     (ofs: Z) (v: val)
     (P: (m.(blocks) b).(low) <= ofs /\
         ofs + size_chunk chunk <= (m.(blocks) b).(high)) : mem :=
  let c := m.(blocks) b in
  mkmem
    (update b
        (mkblock c.(low) c.(high)
                 (store_contents (mem_chunk chunk) c.(contents) ofs v)
                 (store_contents_undef_outside (mem_chunk chunk) c.(contents)
                      ofs v _ _ P c.(undef_outside)))
        m.(blocks))
    m.(nextblock)
    m.(nextblock_pos).

(** [store chunk m b ofs v] perform a write in memory state [m].
  Value [v] is stored at address [b] and offset [ofs].
  Return the updated memory store, or [None] if the address is invalid
  or the memory access is out of bounds. *)

Definition store (chunk: memory_chunk) (m: mem) (b: block)
                 (ofs: Z) (v: val) : option mem :=
  if zlt b m.(nextblock) then
    match in_bounds chunk ofs (m.(blocks) b) with
    | left P => Some(unchecked_store chunk m b ofs v P)
    | right _ => None
    end
  else
    None.

(** [storev chunk m addr v] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

Definition storev (chunk: memory_chunk) (m: mem) (addr v: val) : option mem :=
  match addr with
  | Vptr b ofs => store chunk m b (Int.signed ofs) v
  | _ => None
  end.

Theorem store_in_bounds:
  forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val),
  valid_block m b ->
  low_bound m b <= ofs ->
  ofs + size_chunk chunk <= high_bound m b ->
  exists m', store chunk m b ofs v = Some m'.
Proof.
  intros. unfold store.
  rewrite zlt_true; auto. 
  case (in_bounds chunk ofs (blocks m b)); intro P.
  exists (unchecked_store chunk m b ofs v P). reflexivity.
  unfold low_bound in H0. unfold high_bound in H1. omegaContradiction.
Qed.

Lemma store_inv:
  forall (chunk: memory_chunk) (m m': mem) (b: block) (ofs: Z) (v: val),
  store chunk m b ofs v = Some m' ->
  let c := m.(blocks) b in
  b < m.(nextblock) /\
  c.(low) <= ofs /\
  ofs + size_chunk chunk <= c.(high) /\
  m'.(nextblock) = m.(nextblock) /\
  exists P, m'.(blocks) =
    update b (mkblock c.(low) c.(high)
                        (store_contents (mem_chunk chunk) c.(contents) ofs v) P)
                        m.(blocks).
Proof.
  intros until v; unfold store.
  case (zlt b (nextblock m)); intro.
  set (c := m.(blocks) b).
  case (in_bounds chunk ofs c).
  intros; injection H; intro; subst m'. simpl.
  intuition. fold c. 
  exists (store_contents_undef_outside (mem_chunk chunk) 
            (contents c) ofs v (low c) (high c) a (undef_outside c)).
  auto.
  intros; discriminate.
  intros; discriminate.
Qed.

Hint Resolve store_in_bounds store_inv.

(** Build a block filled with the given initialization data. *)

Fixpoint contents_init_data (pos: Z) (id: list init_data) {struct id}: contentmap :=
  match id with
  | nil => (fun y => Undef)
  | Init_int8 n :: id' =>
      store_contents Size8 (contents_init_data (pos + 1) id') pos (Vint n)
  | Init_int16 n :: id' =>
      store_contents Size16 (contents_init_data (pos + 2) id') pos (Vint n)
  | Init_int32 n :: id' =>
      store_contents Size32 (contents_init_data (pos + 4) id') pos (Vint n)
  | Init_float32 f :: id' =>
      store_contents Size32 (contents_init_data (pos + 4) id') pos (Vfloat f)
  | Init_float64 f :: id' =>
      store_contents Size64 (contents_init_data (pos + 8) id') pos (Vfloat f)
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

Remark contents_init_data_undef_outside:
  forall id pos x,
  x < pos \/ x >= pos + size_init_data_list id ->
  contents_init_data pos id x = Undef.
Proof.
  induction id; simpl; intros.
  auto.
  generalize (size_init_data_list_pos id); intro.
  assert (forall n delta dt,
    delta = 1 + Z_of_nat n ->
    x < pos \/ x >= pos + (delta + size_init_data_list id) ->
    setN n pos dt (contents_init_data (pos + delta) id) x = Undef).
  intros. unfold setN. rewrite update_o. 
  transitivity (contents_init_data (pos + delta) id x).
  apply set_cont_outside.  omega. 
  apply IHid. omega. omega.
  unfold size_init_data in H; destruct a;
  try (apply H1; [reflexivity|assumption]).
  apply IHid. generalize (Zmax2 z 0). omega. 
  apply IHid. omega. 
Qed.

Definition block_init_data (id: list init_data) : block_contents :=
  mkblock 0 (size_init_data_list id) 
          (contents_init_data 0 id)
          (contents_init_data_undef_outside id 0).

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
  unfold block_init_data, empty_block. simpl. 
  decEq. apply proof_irrelevance. 
Qed.

(** * Properties of the memory operations *)

(** ** Properties related to block validity *)

Lemma valid_not_valid_diff:
  forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b'.
Proof.
  intros; red; intros. subst b'. contradiction.
Qed.

Theorem fresh_block_alloc:
  forall (m1 m2: mem) (lo hi: Z) (b: block), 
  alloc m1 lo hi = (m2, b) -> ~(valid_block m1 b).
Proof.
  intros. injection H; intros; subst b. 
  unfold valid_block. omega.
Qed.

Theorem valid_new_block:
  forall (m1 m2: mem) (lo hi: Z) (b: block), 
  alloc m1 lo hi = (m2, b) -> valid_block m2 b.
Proof.
  unfold alloc, valid_block; intros.
  injection H; intros. subst b; subst m2; simpl. omega.
Qed.

Theorem valid_block_alloc:
  forall (m1 m2: mem) (lo hi: Z) (b b': block), 
  alloc m1 lo hi = (m2, b') ->
  valid_block m1 b -> valid_block m2 b.
Proof.
  unfold alloc, valid_block; intros.
  injection H; intros. subst m2; simpl. omega.
Qed.

Theorem valid_block_store:
  forall (chunk: memory_chunk) (m1 m2: mem) (b b': block) (ofs: Z) (v: val),
  store chunk m1 b' ofs v = Some m2 ->
  valid_block m1 b -> valid_block m2 b.
Proof.
  intros. generalize (store_inv _ _ _ _ _ _ H). 
  intros [A [B [C [D [P E]]]]].
  red. rewrite D. exact H0.
Qed.

Theorem valid_block_free:
  forall (m: mem) (b b': block), 
  valid_block m b -> valid_block (free m b') b.
Proof.
  unfold valid_block, free; intros.
  simpl. auto.
Qed.

(** ** Properties related to [alloc] *)

Theorem load_alloc_other:
  forall (chunk: memory_chunk) (m1 m2: mem)
         (b b': block) (ofs lo hi: Z) (v: val),
  alloc m1 lo hi = (m2, b') ->
  load chunk m1 b ofs = Some v ->
  load chunk m2 b ofs = Some v.
Proof.
  unfold alloc; intros.
  injection H; intros; subst m2; clear H.
  generalize (load_inv _ _ _ _ _ H0).
  intros (A, (B, (C, D))).
  unfold load; simpl.
  rewrite zlt_true.
  repeat (rewrite update_o).
  rewrite in_bounds_holds. congruence. auto. auto.
  omega. omega.
Qed.

Lemma load_contents_init:
  forall (sz: memory_size) (ofs: Z),
  load_contents sz (fun y => Undef) ofs = Vundef.
Proof.
  intros. destruct sz; reflexivity.
Qed.

Theorem load_alloc_same:
  forall (chunk: memory_chunk) (m1 m2: mem)
         (b b': block) (ofs lo hi: Z) (v: val),
  alloc m1 lo hi = (m2, b') ->
  load chunk m2 b' ofs = Some v ->
  v = Vundef.
Proof.
  unfold alloc; intros.
  injection H; intros; subst m2; clear H.
  generalize (load_inv _ _ _ _ _ H0).
  simpl. rewrite H1. rewrite update_s. simpl. intros (A, (B, (C, D))).
  rewrite <- D. rewrite load_contents_init. 
  destruct chunk; reflexivity.
Qed.  

Theorem low_bound_alloc:
  forall (m1 m2: mem) (b b': block) (lo hi: Z),
  alloc m1 lo hi = (m2, b') ->
  low_bound m2 b = if zeq b b' then lo else low_bound m1 b.
Proof.
  unfold alloc; intros. 
  injection H; intros; subst m2; clear H.
  unfold low_bound; simpl. 
  unfold update.
  subst b'.
  case (zeq b (nextblock m1)); reflexivity.
Qed.

Theorem high_bound_alloc:
  forall (m1 m2: mem) (b b': block) (lo hi: Z),
  alloc m1 lo hi = (m2, b') ->
  high_bound m2 b = if zeq b b' then hi else high_bound m1 b.
Proof.
  unfold alloc; intros. 
  injection H; intros; subst m2; clear H.
  unfold high_bound; simpl. 
  unfold update.
  subst b'.
  case (zeq b (nextblock m1)); reflexivity.
Qed.

Theorem store_alloc:
  forall (chunk: memory_chunk) (m1 m2: mem) (b: block) (ofs lo hi: Z) (v: val),
  alloc m1 lo hi = (m2, b) ->
  lo <= ofs -> ofs + size_chunk chunk <= hi ->
  exists m2', store chunk m2 b ofs v = Some m2'.
Proof.
  unfold alloc; intros.
  injection H; intros.
  assert (A: b < m2.(nextblock)).
  subst m2; subst b; simpl; omega.
  assert (B: low_bound m2 b <= ofs).
  subst m2; subst b. unfold low_bound; simpl. rewrite update_s.
  simpl. assumption.
  assert (C: ofs + size_chunk chunk <= high_bound m2 b).
  subst m2; subst b. unfold high_bound; simpl. rewrite update_s.
  simpl. assumption.
  exact (store_in_bounds chunk m2 b ofs v A B C).
Qed.

Hint Resolve store_alloc high_bound_alloc low_bound_alloc load_alloc_same
load_contents_init load_alloc_other.

(** ** Properties related to [free] *)

Theorem load_free:
  forall (chunk: memory_chunk) (m: mem) (b bf: block) (ofs: Z),
  b <> bf ->
  load chunk (free m bf) b ofs = load chunk m b ofs.
Proof.
  intros. unfold free, load; simpl.
  case (zlt b (nextblock m)).
  repeat (rewrite update_o; auto).
  reflexivity.
Qed.

Theorem low_bound_free:
  forall (m: mem) (b bf: block),
  b <> bf ->
  low_bound (free m bf) b = low_bound m b.
Proof.
  intros. unfold free, low_bound; simpl.
  rewrite update_o; auto.
Qed.

Theorem high_bound_free:
  forall (m: mem) (b bf: block),
  b <> bf ->
  high_bound (free m bf) b = high_bound m b.
Proof.
  intros. unfold free, high_bound; simpl.
  rewrite update_o; auto.
Qed.
Hint Resolve load_free low_bound_free high_bound_free.

(** ** Properties related to [store] *)

Lemma store_is_in_bounds:
  forall chunk m1 b ofs v m2,
  store chunk m1 b ofs v = Some m2 ->
  low_bound m1 b <= ofs /\ ofs + size_chunk chunk <= high_bound m1 b.
Proof.
  intros. generalize (store_inv _ _ _ _ _ _ H).
  intros [A [B [C [P D]]]].
  unfold low_bound, high_bound. tauto.
Qed.

Lemma load_store_contents_same:
  forall (sz: memory_size) (c: contentmap) (ofs: Z) (v: val),
  load_contents sz (store_contents sz c ofs v) ofs = v.
Proof.
  intros until v.
  unfold load_contents, store_contents in |- *; case sz;
    rewrite getN_setN_same; reflexivity.
Qed.
  
Theorem load_store_same:
  forall (chunk: memory_chunk) (m1 m2: mem) (b: block) (ofs: Z) (v: val),
  store chunk m1 b ofs v = Some m2 ->
  load chunk m2 b ofs = Some (Val.load_result chunk v).
Proof.
  intros.
  generalize (store_inv _ _ _ _ _ _ H).
  intros (A, (B, (C, (D, (P, E))))).
  unfold load. rewrite D. 
  rewrite zlt_true; auto. rewrite E. 
  repeat (rewrite update_s). simpl.
  rewrite in_bounds_exten. rewrite in_bounds_holds; auto.
  rewrite load_store_contents_same; auto.
Qed.
           
Lemma load_store_contents_other:
  forall (sz1 sz2: memory_size) (c: contentmap) 
         (ofs1 ofs2: Z) (v: val),
  ofs2 + size_mem sz2 <= ofs1 \/ ofs1 + size_mem sz1 <= ofs2 ->
  load_contents sz2 (store_contents sz1 c ofs1 v) ofs2 =
  load_contents sz2 c ofs2.
Proof.
  intros until v.
  unfold size_mem, store_contents, load_contents;
  case sz1; case sz2; intros;
  (rewrite getN_setN_other; 
   [reflexivity | simpl Z_of_nat; omega]).
Qed.

Theorem load_store_other:
  forall (chunk1 chunk2: memory_chunk) (m1 m2: mem)
         (b1 b2: block) (ofs1 ofs2: Z) (v: val),
  store chunk1 m1 b1 ofs1 v = Some m2 ->
  b1 <> b2
  \/ ofs2 + size_chunk chunk2 <= ofs1
  \/ ofs1 + size_chunk chunk1 <= ofs2 ->
  load chunk2 m2 b2 ofs2 = load chunk2 m1 b2 ofs2.
Proof.
  intros.
  generalize (store_inv _ _ _ _ _ _ H).
  intros (A, (B, (C, (D, (P, E))))).
  unfold load. rewrite D.
  case (zlt b2 (nextblock m1)); intro.
  rewrite E; unfold update; case (zeq b2 b1); intro; simpl.
  subst b2. rewrite in_bounds_exten. 
  rewrite load_store_contents_other. auto.
  tauto.
  reflexivity. 
  reflexivity.
Qed.

Ltac LSCO :=
  match goal with
  | |- (match getN ?sz2 ?ofs2 (setN ?sz1 ?ofs1 ?v ?c) with
        | Undef => _
        | Datum8 _ => _
        | Datum16 _ => _
        | Datum32 _ => _
        | Datum64 _ => _
        | Cont => _ 
        end = _) =>
    elim (getN_setN_overlap sz1 sz2 ofs1 ofs2 v c);
    [ let H := fresh in (intro H; rewrite H; reflexivity)
    | let H := fresh in (intro H; rewrite H; reflexivity)
    | assumption
    | simpl Z_of_nat; omega
    | simpl Z_of_nat; omega
    | discriminate ]
  end.

Lemma load_store_contents_overlap:
  forall (sz1 sz2: memory_size) (c: contentmap) 
         (ofs1 ofs2: Z) (v: val),
  ofs1 <> ofs2 ->
  ofs2 + size_mem sz2 > ofs1 -> ofs1 + size_mem sz1 > ofs2 ->
  load_contents sz2 (store_contents sz1 c ofs1 v) ofs2 = Vundef.
Proof.
  intros.
  destruct sz1; destruct sz2; simpl in H0; simpl in H1; simpl; LSCO.
Qed.

Ltac LSCM :=
  match goal with
  | H:(?x <> ?x) |- _ =>
    elim H; reflexivity
  | |- (match getN ?sz2 ?ofs (setN ?sz1 ?ofs ?v ?c) with
        | Undef => _
        | Datum8 _ => _
        | Datum16 _ => _
        | Datum32 _ => _
        | Datum64 _ => _
        | Cont => _ 
        end = _) =>
    elim (getN_setN_mismatch sz1 sz2 ofs v c);
    [ let H := fresh in (intro H; rewrite H; reflexivity)
    | let H := fresh in (intro H; rewrite H; reflexivity) ]
  end.

Lemma load_store_contents_mismatch:
  forall (sz1 sz2: memory_size) (c: contentmap) 
         (ofs: Z) (v: val),
  sz1 <> sz2 ->
  load_contents sz2 (store_contents sz1 c ofs v) ofs = Vundef.
Proof.
  intros.
  destruct sz1; destruct sz2; simpl; LSCM.
Qed.  

Theorem low_bound_store:
  forall (chunk: memory_chunk) (m1 m2: mem) (b b': block) (ofs: Z) (v: val),
  store chunk m1 b ofs v = Some m2 ->
  low_bound m2 b' = low_bound m1 b'.
Proof.
  intros.
  generalize (store_inv _ _ _ _ _ _ H).
  intros (A, (B, (C, (D, (P, E))))).
  unfold low_bound. rewrite E; unfold update.
  case (zeq b' b); intro.
  subst b'. reflexivity.
  reflexivity.
Qed.

Theorem high_bound_store:
  forall (chunk: memory_chunk) (m1 m2: mem) (b b': block) (ofs: Z) (v: val),
  store chunk m1 b ofs v = Some m2 ->
  high_bound m2 b' = high_bound m1 b'.
Proof.
  intros.
  generalize (store_inv _ _ _ _ _ _ H).
  intros (A, (B, (C, (D, (P, E))))).
  unfold high_bound. rewrite E; unfold update.
  case (zeq b' b); intro.
  subst b'. reflexivity.
  reflexivity. 
Qed.

Hint Resolve high_bound_store low_bound_store load_store_contents_mismatch
  load_store_contents_overlap load_store_other store_is_in_bounds  
  load_store_contents_same  load_store_same load_store_contents_other.

(** * Agreement between memory blocks. *)

(** Two memory blocks [c1] and [c2] agree on a range [lo] to [hi]
  if they associate the same contents to byte offsets in the range
  [lo] (included) to [hi] (excluded). *)

Definition contentmap_agree (lo hi: Z) (c1 c2: contentmap) :=
  forall (ofs: Z),
    lo <= ofs < hi -> c1 ofs = c2 ofs.

Definition block_contents_agree (lo hi: Z) (c1 c2: block_contents) :=
  contentmap_agree lo hi c1.(contents) c2.(contents).

Definition block_agree (b: block) (lo hi: Z) (m1 m2: mem) :=
  block_contents_agree lo hi
     (m1.(blocks) b) (m2.(blocks) b).

Theorem block_agree_refl:
  forall (m: mem) (b: block) (lo hi: Z),
  block_agree b lo hi m m.
Proof.
  intros. hnf. auto.
Qed.

Theorem block_agree_sym:
  forall (m1 m2: mem) (b: block) (lo hi: Z),
  block_agree b lo hi m1 m2 ->
  block_agree b lo hi m2 m1.
Proof.
  intros. hnf. intros. symmetry. apply H. auto.
Qed.

Theorem block_agree_trans:
  forall (m1 m2 m3: mem) (b: block) (lo hi: Z),
  block_agree b lo hi m1 m2 ->
  block_agree b lo hi m2 m3 ->
  block_agree b lo hi m1 m3.
Proof.
  intros. hnf. intros. 
  transitivity (contents (blocks m2 b) ofs).
  apply H; auto. apply H0; auto.
Qed.

Lemma check_cont_agree:
  forall (c1 c2: contentmap) (lo hi: Z),
  contentmap_agree lo hi c1 c2 ->
  forall (n: nat) (ofs: Z),
  lo <= ofs -> ofs + Z_of_nat n <= hi ->
  check_cont n ofs c2 = check_cont n ofs c1.
Proof.
  induction n; intros; simpl.
  auto.
  rewrite inj_S in H1.
  rewrite H. case (c2 ofs); intros; auto. 
  apply IHn; omega.
  omega.
Qed.

Lemma getN_agree:
  forall (c1 c2: contentmap) (lo hi: Z),
  contentmap_agree lo hi c1 c2 ->
  forall (n: nat) (ofs: Z),
  lo <= ofs -> ofs + Z_of_nat n < hi ->
  getN n ofs c2 = getN n ofs c1.
Proof.
  intros. unfold getN. 
  rewrite (check_cont_agree c1 c2 lo hi H n (ofs + 1)).
  case (check_cont n (ofs + 1) c1).
  symmetry. apply H. omega. auto.
  omega. omega.
Qed.

Lemma load_contentmap_agree:
  forall (sz: memory_size) (c1 c2: contentmap) (lo hi ofs: Z),
  contentmap_agree lo hi c1 c2 ->
  lo <= ofs -> ofs + size_mem sz <= hi ->
  load_contents sz c2 ofs = load_contents sz c1 ofs.
Proof.
  intros sz c1 c2 lo hi ofs EX LO.
  unfold load_contents, size_mem; case sz; intro HI;
  rewrite (getN_agree c1 c2 lo hi EX); auto; simpl Z_of_nat; omega.
Qed.

Lemma set_cont_agree:
  forall (lo hi: Z) (n: nat) (c1 c2: contentmap) (ofs: Z),
  contentmap_agree lo hi c1 c2 ->
  contentmap_agree lo hi (set_cont n ofs c1) (set_cont n ofs c2).
Proof.
  induction n; simpl; intros.
  auto.
  red. intros p B. 
  case (zeq p ofs); intro.
  subst p. repeat (rewrite update_s). reflexivity.
  repeat (rewrite update_o). apply IHn. assumption.
  assumption. auto. auto.
Qed.

Lemma setN_agree:
  forall (lo hi: Z) (n: nat) (c1 c2: contentmap) (ofs: Z) (v: content),
  contentmap_agree lo hi c1 c2 ->
  contentmap_agree lo hi (setN n ofs v c1) (setN n ofs v c2).
Proof.
  intros. unfold setN. red; intros p B.
  case (zeq p ofs); intro.
  subst p. repeat (rewrite update_s). reflexivity.
  repeat (rewrite update_o; auto). 
  exact (set_cont_agree lo hi n c1 c2 (ofs + 1) H p B).  
Qed.

Lemma store_contentmap_agree:
  forall (sz: memory_size) (c1 c2: contentmap) (lo hi ofs: Z) (v: val),
  contentmap_agree lo hi c1 c2 ->
  contentmap_agree lo hi
       (store_contents sz c1 ofs v) (store_contents sz c2 ofs v).
Proof.
  intros. unfold store_contents; case sz; apply setN_agree; auto.
Qed.

Lemma set_cont_outside_agree:
  forall (lo hi: Z) (n: nat) (c1 c2: contentmap) (ofs: Z),
  contentmap_agree lo hi c1 c2 ->
  ofs + Z_of_nat n <= lo \/ hi <= ofs ->
  contentmap_agree lo hi c1 (set_cont n ofs c2).
Proof.
  induction n; intros; simpl.
  auto.
  red; intros p R. rewrite inj_S in H0.
  unfold update. case (zeq p ofs); intro.
  subst p. omegaContradiction.
  apply IHn. auto. omega. auto. 
Qed.

Lemma setN_outside_agree:
  forall (lo hi: Z) (n: nat) (c1 c2: contentmap) (ofs: Z) (v: content),
  contentmap_agree lo hi c1 c2 ->
  ofs + Z_of_nat n < lo \/ hi <= ofs ->
  contentmap_agree lo hi c1 (setN n ofs v c2).
Proof.
  intros. unfold setN. red; intros p R.
  unfold update. case (zeq p ofs); intro.
  omegaContradiction.
  apply (set_cont_outside_agree lo hi n c1 c2 (ofs + 1) H).
  omega. auto.
Qed.

Lemma store_contentmap_outside_agree:
  forall (sz: memory_size) (c1 c2: contentmap) (lo hi ofs: Z) (v: val),
  contentmap_agree lo hi c1 c2 ->
  ofs + size_mem sz <= lo \/ hi <= ofs ->
  contentmap_agree lo hi c1 (store_contents sz c2 ofs v).
Proof.
  intros until v.
  unfold store_contents; case sz; simpl; intros;
  apply setN_outside_agree; auto; simpl Z_of_nat; omega.
Qed.

Theorem load_agree:
  forall (chunk: memory_chunk) (m1 m2: mem) 
         (b: block) (lo hi: Z) (ofs: Z) (v1 v2: val),
  block_agree b lo hi m1 m2 ->
  lo <= ofs -> ofs + size_chunk chunk <= hi ->
  load chunk m1 b ofs = Some v1 ->
  load chunk m2 b ofs = Some v2 ->
  v1 = v2.
Proof.
  intros. 
  generalize (load_inv _ _ _ _ _ H2). intros [K [L [M N]]].
  generalize (load_inv _ _ _ _ _ H3). intros [P [Q [R S]]].
  subst v1; subst v2. symmetry.
  decEq. eapply load_contentmap_agree. 
  apply H. auto. auto. 
Qed.

Theorem store_agree:
  forall (chunk: memory_chunk) (m1 m2 m1' m2': mem)
         (b: block) (lo hi: Z)
         (b': block) (ofs: Z) (v: val),
  block_agree b lo hi m1 m2 ->
  store chunk m1 b' ofs v = Some m1' ->
  store chunk m2 b' ofs v = Some m2' ->
  block_agree b lo hi m1' m2'.
Proof.
  intros.
  generalize (store_inv _ _ _ _ _ _ H0).
  intros [I [J [K [L [x M]]]]].
  generalize (store_inv _ _ _ _ _ _ H1).
  intros [P [Q [R [S [y T]]]]].
  red. red. 
  rewrite M; rewrite T; unfold update.
  case (zeq b b'); intro; simpl.
  subst b'. apply store_contentmap_agree. assumption.
  apply H. 
Qed.

Theorem store_outside_agree:
  forall (chunk: memory_chunk) (m1 m2 m2': mem)
         (b: block) (lo hi: Z)
         (b': block) (ofs: Z) (v: val),
  block_agree b lo hi m1 m2 ->
  b <> b' \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  store chunk m2 b' ofs v = Some m2' ->
  block_agree b lo hi m1 m2'.
Proof.
  intros.
  generalize (store_inv _ _ _ _ _ _ H1).
  intros [I [J [K [L [x M]]]]].
  red. red. rewrite M; unfold update;
  case (zeq b b'); intro; simpl. 
  subst b'. apply store_contentmap_outside_agree.
  assumption. 
  elim H0; intro. tauto. exact H2.
  apply H.
Qed.

(** * Store extensions *)

(** A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by increasing the sizes of the memory blocks of [m1] (decreasing
  the low bounds, increasing the high bounds), while still keeping the
  same contents for block offsets that are valid in [m1]. 
  This notion is used in the proof of semantic equivalence in 
  module [Machenv]. *)

Definition block_contents_extends (c1 c2: block_contents) :=
  c2.(low) <= c1.(low) /\ c1.(high) <= c2.(high) /\
  contentmap_agree c1.(low) c1.(high) c1.(contents) c2.(contents).

Definition extends (m1 m2: mem) :=
  m1.(nextblock) = m2.(nextblock) /\
  forall (b: block),
  b < m1.(nextblock) ->
  block_contents_extends (m1.(blocks) b) (m2.(blocks) b).

Theorem extends_refl:
  forall (m: mem), extends m m.
Proof.
  intro. red. split.
  reflexivity.
  intros. red. 
  split. omega. split. omega. 
  red. intros. reflexivity.
Qed.

Theorem alloc_extends:
  forall (m1 m2 m1' m2': mem) (lo1 hi1 lo2 hi2: Z) (b1 b2: block),
  extends m1 m2 ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  alloc m1 lo1 hi1 = (m1', b1) ->
  alloc m2 lo2 hi2 = (m2', b2) ->
  b1 = b2 /\ extends m1' m2'.
Proof.
  unfold extends, alloc; intros.
  injection H2; intros; subst m1'; subst b1.
  injection H3; intros; subst m2'; subst b2.
  simpl. intuition.
  rewrite <- H4. case (zeq b (nextblock m1)); intro.
  subst b. repeat rewrite update_s.
  red; simpl. intuition. 
  red; intros; reflexivity.
  repeat rewrite update_o.  apply H5.  omega.
  auto. auto.
Qed.

Theorem free_extends:
  forall (m1 m2: mem) (b: block),
  extends m1 m2 ->
  extends (free m1 b) (free m2 b).
Proof.
  unfold extends, free; intros.
  simpl. intuition. 
  red; intros; simpl. 
  case (zeq b0 b); intro.
  subst b0; repeat (rewrite update_s). 
  simpl. split. omega. split. omega. 
  red. intros. omegaContradiction. 
  repeat (rewrite update_o). 
  exact (H1 b0 H).
  auto. auto.  
Qed.

Theorem load_extends:
  forall (chunk: memory_chunk) (m1 m2: mem) (b: block) (ofs: Z) (v: val),
  extends m1 m2 ->
  load chunk m1 b ofs = Some v ->
  load chunk m2 b ofs = Some v.
Proof.
  intros sz m1 m2 b ofs v (X, Y) L.
  generalize (load_inv _ _ _ _ _ L).
  intros (A, (B, (C, D))).
  unfold load. rewrite <- X. rewrite zlt_true; auto.
  generalize (Y b A); intros [M [P Q]].
  rewrite in_bounds_holds.
  rewrite <- D. 
  decEq. decEq.
  apply load_contentmap_agree with
    (lo := low((blocks m1) b))
    (hi := high((blocks m1) b)); auto.
  omega. omega. 
Qed.

Theorem store_within_extends:
  forall (chunk: memory_chunk) (m1 m2 m1': mem) (b: block) (ofs: Z) (v: val),
  extends m1 m2 ->
  store chunk m1 b ofs v = Some m1' ->
  exists m2', store chunk m2 b ofs v = Some m2' /\ extends m1' m2'.
Proof.
  intros sz m1 m2 m1' b ofs v (X, Y) STORE.
  generalize (store_inv _ _ _ _ _ _ STORE).
  intros (A, (B, (C, (D, (x, E))))).
  generalize (Y b A); intros [M [P Q]].
  unfold store. rewrite <- X. rewrite zlt_true; auto.
  case (in_bounds sz ofs (blocks m2 b)); intro.
  exists (unchecked_store sz m2 b ofs v a).
  split. auto.
  split. 
  unfold unchecked_store; simpl. congruence.
  intros b' LT. 
  unfold block_contents_extends, unchecked_store, block_contents_agree.
  rewrite E; unfold update; simpl.
  case (zeq b' b); intro; simpl.
  subst b'. split. omega. split. omega. 
  apply store_contentmap_agree. auto.
  apply Y. rewrite <- D. auto.
  omegaContradiction.
Qed.

Theorem store_outside_extends:
  forall (chunk: memory_chunk) (m1 m2 m2': mem) (b: block) (ofs: Z) (v: val),
  extends m1 m2 ->
  ofs + size_chunk chunk <= low_bound m1 b \/ high_bound m1 b <= ofs ->
  store chunk m2 b ofs v = Some m2' ->
  extends m1 m2'.
Proof.
  intros sz m1 m2 m2' b ofs v (X, Y) BOUNDS STORE.
  generalize (store_inv _ _ _ _ _ _ STORE).
  intros (A, (B, (C, (D, (x, E))))).
  split.
  congruence.
  intros b' LT.
  rewrite E; unfold update; case (zeq b' b); intro.
  subst b'. generalize (Y b LT). intros [M [P Q]].
  red; simpl. split. omega. split. omega. 
  apply store_contentmap_outside_agree.
  assumption. exact BOUNDS. 
  auto. 
Qed.

(** * Memory extensionality properties *)

Lemma block_contents_exten:
  forall (c1 c2: block_contents),
  c1.(low) = c2.(low) ->
  c1.(high) = c2.(high) ->
  block_contents_agree c1.(low) c1.(high) c1 c2 ->
  c1 = c2.
Proof.
  intros. caseEq c1; intros lo1 hi1 m1 UO1 EQ1. subst c1.
  caseEq c2; intros lo2 hi2 m2 UO2 EQ2. subst c2.
  simpl in *. subst lo2 hi2. 
  assert (m1 = m2). 
    unfold contentmap. apply extensionality. intro.
    case (zlt x lo1); intro.
    rewrite UO1. rewrite UO2. auto. tauto. tauto.
    case (zlt x hi1); intro.
    apply H1. omega.
    rewrite UO1. rewrite UO2. auto. tauto. tauto.
  subst m2. 
  assert (UO1 = UO2).
    apply proof_irrelevance.
  subst UO2. reflexivity.
Qed.

Theorem mem_exten:
  forall m1 m2,
  m1.(nextblock) = m2.(nextblock) ->
  (forall b, m1.(blocks) b = m2.(blocks) b) ->
  m1 = m2.
Proof.
  intros. destruct m1 as [map1 nb1 nextpos1]. destruct m2 as [map2 nb2 nextpos2].
  simpl in *. subst nb2. 
  assert (map1 = map2). apply extensionality. assumption.
  assert (nextpos1 = nextpos2). apply proof_irrelevance. 
  congruence.
Qed.

(** * Store injections *)

(** A memory injection [f] is a function from addresses to either [None]
  or [Some] of an address and an offset.  It defines a correspondence
  between the blocks of two memory states [m1] and [m2]:
- if [f b = None], the block [b] of [m1] has no equivalent in [m2];
- if [f b = Some(b', ofs)], the block [b] of [m2] corresponds to
  a sub-block at offset [ofs] of the block [b'] in [m2].
*)

Definition meminj := (block -> option (block * Z))%type.

Section MEM_INJECT.

Variable f: meminj.

(** A memory injection defines a relation between values that is the
  identity relation, except for pointer values which are shifted
  as prescribed by the memory injection. *)

Inductive val_inject: val -> val -> Prop :=
  | val_inject_int:
      forall i, val_inject (Vint i) (Vint i)
  | val_inject_float:
      forall f, val_inject (Vfloat f) (Vfloat f)
  | val_inject_ptr:
      forall b1 ofs1 b2 ofs2 x,
      f b1 = Some (b2, x) ->
      ofs2 = Int.add ofs1 (Int.repr x) ->
      val_inject (Vptr b1 ofs1) (Vptr b2 ofs2)
  | val_inject_undef: forall v,
      val_inject Vundef v.

Hint Resolve val_inject_int val_inject_float val_inject_ptr 
val_inject_undef.

Inductive val_list_inject: list val -> list val-> Prop:= 
  | val_nil_inject :
      val_list_inject nil nil
  | val_cons_inject : forall v v' vl vl' , 
      val_inject v v' -> val_list_inject vl vl'->
      val_list_inject (v::vl) (v':: vl').  

Inductive val_content_inject: memory_size -> val -> val -> Prop :=
  | val_content_inject_base:
      forall sz v1 v2,
      val_inject v1 v2 ->
      val_content_inject sz v1 v2
  | val_content_inject_8:
      forall n1 n2,
      Int.cast8unsigned n1 = Int.cast8unsigned n2 ->
      val_content_inject Size8 (Vint n1) (Vint n2)
  | val_content_inject_16:
      forall n1 n2,
      Int.cast16unsigned n1 = Int.cast16unsigned n2 ->
      val_content_inject Size16 (Vint n1) (Vint n2)
  | val_content_inject_32:
      forall f1 f2,
      Float.singleoffloat f1 = Float.singleoffloat f2 ->
      val_content_inject Size32 (Vfloat f1) (Vfloat f2).

Hint Resolve val_content_inject_base.

Inductive content_inject: content -> content -> Prop :=
  | content_inject_undef: 
      forall c,
      content_inject Undef c
  | content_inject_datum8:
      forall v1 v2,
      val_content_inject Size8 v1 v2 ->
      content_inject (Datum8 v1) (Datum8 v2)
  | content_inject_datum16:
      forall v1 v2,
      val_content_inject Size16 v1 v2 ->
      content_inject (Datum16 v1) (Datum16 v2)
  | content_inject_datum32:
      forall v1 v2,
      val_content_inject Size32 v1 v2 ->
      content_inject (Datum32 v1) (Datum32 v2)
  | content_inject_datum64:
      forall v1 v2,
      val_content_inject Size64 v1 v2 ->
      content_inject (Datum64 v1) (Datum64 v2)
  | content_inject_cont:
      content_inject Cont Cont.

Hint Resolve content_inject_undef content_inject_datum8 
content_inject_datum16 content_inject_datum32 content_inject_datum64
content_inject_cont.

Definition contentmap_inject (c1 c2: contentmap) (lo hi delta: Z) : Prop :=
  forall x, lo <= x < hi ->
    content_inject (c1 x) (c2 (x + delta)).

(** A block contents [c1] injects into another block content [c2] at
  offset [delta] if the contents of [c1] at all valid offsets
  correspond to the contents of [c2] at the same offsets shifted by [delta].
  Some additional conditions are imposed to guard against arithmetic
  overflow in address computations. *)

Record block_contents_inject (c1 c2: block_contents) (delta: Z) : Prop :=
  mk_block_contents_inject {
    bci_range1: Int.min_signed <= delta <= Int.max_signed;
    bci_range2: delta = 0 \/
                (Int.min_signed <= c2.(low) /\ c2.(high) <= Int.max_signed);
    bci_lowhigh:forall x, c1.(low) <= x < c1.(high) ->
                          c2.(low) <= x+delta < c2.(high) ;
    bci_contents: 
      contentmap_inject c1.(contents) c2.(contents) c1.(low) c1.(high) delta
  }.

(** A memory state [m1] injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- unallocated blocks in [m1] must be mapped to [None] by [f];
- if [f b = Some(b', delta)], [b'] must be valid in [m2] and
  the contents of [b] in [m1] must inject into the contents of [b'] in [m2]
  with offset [delta];
- distinct blocks in [m1] cannot be mapped to overlapping sub-blocks in [m2].
*)

Record mem_inject (m1 m2: mem) : Prop :=
  mk_mem_inject {
    mi_freeblocks:
      forall b, b >= m1.(nextblock) -> f b = None;
    mi_mappedblocks:
      forall b b' delta,
      f b = Some(b', delta) ->
      b' < m2.(nextblock) /\
      block_contents_inject (m1.(blocks) b) 
                            (m2.(blocks) b') 
                            delta;
    mi_no_overlap:
      forall b1 b2 b1' b2' delta1 delta2,
      b1 <> b2 ->
      f b1 = Some (b1', delta1) ->
      f b2 = Some (b2', delta2) ->
      b1' <> b2' 
      \/ (forall x1 x2, low_bound m1 b1 <= x1 < high_bound m1 b1 ->
                              low_bound m1 b2 <= x2 < high_bound m1 b2 ->
                              x1+delta1 <> x2+delta2)
 }.

(** The following lemmas establish the absence of machine integer overflow
  during address computations. *)

Lemma size_mem_pos: forall sz, size_mem sz > 0.
Proof.  destruct sz; simpl; omega. Qed.

Lemma size_chunk_pos: forall chunk, size_chunk chunk > 0.
Proof. intros. unfold size_chunk. apply size_mem_pos. Qed.

Lemma address_inject:
  forall m1 m2 chunk b1 ofs1 b2 ofs2 x,
  mem_inject m1 m2 ->
  (m1.(blocks) b1).(low) <= Int.signed ofs1 ->
  Int.signed ofs1 + size_chunk chunk <= (m1.(blocks) b1).(high) ->
  f b1 = Some (b2, x) ->
  ofs2 = Int.add ofs1 (Int.repr x) ->
  Int.signed ofs2 = Int.signed ofs1 + x.
Proof.
  intros. 
  generalize (size_chunk_pos chunk). intro.
  generalize (mi_mappedblocks m1 m2 H _ _ _ H2). intros [C D].
  inversion D. 
  elim  bci_range4 ; intro. 
  (**x=0**)
  subst x .  rewrite Zplus_0_r.  rewrite Int.add_zero in H3. 
  subst ofs2 ; auto . 
  (**x<>0**)
  rewrite H3. rewrite Int.add_signed. repeat rewrite Int.signed_repr.
  auto.  auto.
  assert (low (blocks m1 b1) <= Int.signed ofs1 < high (blocks m1 b1)).
  omega.
  generalize (bci_lowhigh0 (Int.signed ofs1) H6). omega.
  auto.
Qed.

Lemma valid_pointer_inject_no_overflow:
  forall m1 m2 b ofs b' x,
  mem_inject m1 m2 ->
  valid_pointer m1 b (Int.signed ofs) = true ->
  f b = Some(b', x) ->
  Int.min_signed <= Int.signed ofs + Int.signed (Int.repr x) <= Int.max_signed.
Proof.
  intros. unfold valid_pointer in H0.
  destruct (zlt b (nextblock m1)); try discriminate.
  destruct (zle (low (blocks m1 b)) (Int.signed ofs)); try discriminate.
  destruct (zlt (Int.signed ofs) (high (blocks m1 b))); try discriminate.
  inversion H. generalize (mi_mappedblocks0 _ _ _ H1).
  intros [A B]. inversion B. 
  elim  bci_range4 ; intro. 
  (**x=0**)
  rewrite Int.signed_repr ; auto.  
  subst x .  rewrite Zplus_0_r.  apply Int.signed_range . 
  (**x<>0**)
  generalize (bci_lowhigh0 _ (conj z0 z1)). intro.
  rewrite Int.signed_repr. omega. auto.
Qed.

(** Relation between injections and loads. *)

Lemma check_cont_inject:
  forall c1 c2 lo hi delta,
  contentmap_inject c1 c2 lo hi delta ->
  forall n p,
  lo <= p -> p + Z_of_nat n <= hi ->
  check_cont n p c1 = true ->
  check_cont n (p + delta) c2 = true.
Proof.
  induction n.
  intros. simpl. reflexivity.
  simpl check_cont. rewrite inj_S. intros p H0 H1.
  assert (lo <= p < hi). omega.  
  generalize (H p H2). intro. inversion H3; intros; try discriminate.
  replace (p + delta + 1) with ((p + 1) + delta). 
  apply IHn. omega. omega. auto. 
  omega.
Qed.

Hint Resolve check_cont_inject.

Lemma getN_inject:
  forall c1 c2 lo hi delta,
  contentmap_inject c1 c2 lo hi delta ->
  forall n p,
  lo <= p -> p + Z_of_nat n < hi ->
  content_inject (getN n p c1) (getN n (p + delta) c2).
Proof.
  intros. simpl in H1.
  assert (lo <= p < hi). omega.
  unfold getN.
  caseEq (check_cont n (p + 1) c1); intro.
  replace (check_cont n (p + delta + 1) c2) with true.
  apply H. assumption. 
  symmetry. replace (p + delta + 1) with ((p + 1) + delta).
  eapply check_cont_inject; eauto.
  omega. omega. omega.
  constructor. 
Qed.

Hint Resolve getN_inject.

Definition ztonat (z:Z): nat:=
match z with
| Z0 => O
| Zpos p =>  (nat_of_P p)
| Zneg p =>O 
end.

Lemma load_contents_inject:
  forall sz c1 c2 lo hi delta p,
  contentmap_inject c1 c2 lo hi delta ->
  lo <= p -> p + size_mem sz <= hi ->
  val_content_inject sz (load_contents sz c1 p) (load_contents sz c2 (p + delta)).
Proof.
intros.
assert (content_inject (getN (ztonat (size_mem sz)-1) p c1) 
(getN (ztonat(size_mem sz)-1) (p + delta) c2)).
induction sz; assert (lo<= p< hi); simpl in H1; try omega;
apply getN_inject with lo hi; try assumption; simpl ; try omega. 
induction sz ; simpl; inversion H2; auto.
Qed.

Hint Resolve load_contents_inject.

Lemma load_result_inject:
  forall chunk v1 v2,
  val_content_inject (mem_chunk chunk) v1 v2 ->
  val_inject (Val.load_result chunk v1) (Val.load_result chunk v2).
Proof.
intros.
destruct chunk; simpl in H; inversion H; simpl; auto;
try (inversion H0; simpl; auto; fail).
replace (Int.cast8signed n2) with (Int.cast8signed n1). constructor. 
apply Int.cast8_signed_equal_if_unsigned_equal; auto.
rewrite H0; constructor.
replace (Int.cast16signed n2) with (Int.cast16signed n1). constructor. 
apply Int.cast16_signed_equal_if_unsigned_equal; auto.
rewrite H0; constructor.
inversion H0; simpl; auto. 
apply val_inject_ptr with x; auto.
Qed.

Lemma in_bounds_inject:
  forall chunk c1 c2 delta p,
  block_contents_inject c1 c2 delta ->
  c1.(low) <= p /\ p + size_chunk chunk <= c1.(high) ->
  c2.(low) <= p + delta /\ (p + delta) + size_chunk chunk <= c2.(high).
Proof.
  intros.
  inversion H. 
  generalize (size_chunk_pos chunk); intro.
  assert (low c1 <= p + size_chunk chunk - 1 < high c1).
  omega.
  generalize (bci_lowhigh0 _ H2). intro.
  assert (low c1 <= p < high c1).
  omega.
  generalize (bci_lowhigh0 _ H4). intro.
  omega. 
Qed.

Lemma block_cont_val:
forall c1 c2 delta p sz,
block_contents_inject c1 c2 delta ->
c1.(low) <= p -> p + size_mem sz <= c1.(high) ->
  val_content_inject sz (load_contents sz c1.(contents) p) 
    (load_contents sz c2.(contents) (p + delta)).
Proof.
intros.
inversion H .
apply load_contents_inject with c1.(low) c1.(high) ;assumption. 
Qed.

Lemma load_inject:
  forall m1 m2 chunk b1 ofs b2 delta v1,
  mem_inject m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ val_inject v1 v2.
Proof.
  intros.
  generalize (load_inv _ _ _ _ _ H0).  intros [A [B [C D]]].
  inversion H.
  generalize (mi_mappedblocks0 _ _ _ H1). intros [U V].
  inversion V.
  exists (Val.load_result chunk (load_contents (mem_chunk chunk)
           (m2.(blocks) b2).(contents) (ofs+delta))). 
  split.
  unfold load. 
  generalize (size_chunk_pos chunk); intro. 
  rewrite zlt_true. rewrite in_bounds_holds. auto.
  assert (low (blocks m1 b1) <= ofs < high (blocks m1 b1)).
    omega.
  generalize (bci_lowhigh0 _ H3). tauto.
  assert (low (blocks m1 b1) <= ofs + size_chunk chunk - 1 < high(blocks m1 b1)).
    omega.
  generalize (bci_lowhigh0 _ H3). omega.
  assumption.
  rewrite <- D. apply load_result_inject. 
  eapply load_contents_inject; eauto.
Qed.

Lemma loadv_inject:
  forall m1 m2 chunk a1 a2 v1,
  mem_inject m1 m2 ->
  loadv chunk m1 a1 = Some v1 ->
  val_inject a1 a2 ->
  exists v2, loadv chunk m2 a2 = Some v2 /\ val_inject v1 v2.
Proof.
  intros.
  induction H1 ; simpl in H0 ; try discriminate H0.
  simpl. 
  replace (Int.signed ofs2) with (Int.signed ofs1 + x).
  apply load_inject with m1 b1 ; assumption.
  symmetry. generalize (load_inv _ _ _ _ _ H0). intros [A [B [C D]]].
  apply address_inject with m1 m2 chunk b1 b2; auto.
Qed.

(** Relation between injections and stores. *)

Lemma set_cont_inject:
  forall c1 c2 lo hi delta,
  contentmap_inject c1 c2 lo hi delta ->
  forall n p,
  lo <= p -> p + Z_of_nat n <= hi ->
  contentmap_inject (set_cont n p c1) (set_cont n (p + delta) c2) lo hi delta.
Proof.
induction n. intros. simpl. assumption.
intros. simpl. unfold contentmap_inject.
intros p2 Hp2. unfold update.
case (zeq p2 p); intro.
subst p2. rewrite zeq_true. constructor.
rewrite zeq_false. replace (p + delta + 1) with ((p + 1) + delta).
apply IHn. omega. rewrite inj_S in H1. omega. assumption.
omega. omega.
Qed.

Lemma setN_inject:
  forall c1 c2 lo hi delta n p v1 v2,
  contentmap_inject c1 c2 lo hi delta ->
  content_inject v1 v2 ->
  lo <= p -> p + Z_of_nat n < hi ->
  contentmap_inject (setN n p v1 c1) (setN n (p + delta) v2 c2)
                    lo hi delta.
Proof.
  intros. unfold setN. red; intros.
  unfold update. 
  case (zeq x p); intro. 
  subst p. rewrite zeq_true. assumption.
  rewrite zeq_false. 
  replace (p + delta + 1) with ((p + 1) + delta).
  apply set_cont_inject with lo hi. 
  assumption. omega. omega. assumption. omega.
  omega.
Qed.

Lemma store_contents_inject:
  forall c1 c2 lo hi delta sz p v1 v2,
  contentmap_inject c1 c2 lo hi delta ->
  val_content_inject sz v1 v2 ->
  lo <= p -> p + size_mem sz <= hi ->
  contentmap_inject (store_contents sz c1 p v1) 
                    (store_contents sz c2 (p + delta) v2)
                    lo hi delta.
Proof.
  intros.
  destruct sz; simpl in *; apply setN_inject; auto; simpl; omega.
Qed.

Lemma set_cont_outside1 :
  forall n  p m q ,
  (forall x , p <= x < p + Z_of_nat n -> x <> q) ->
  (set_cont n p m) q = m q.
Proof.
  induction n; intros; simpl.
  auto.
  rewrite inj_S in H. rewrite update_o. apply IHn.
  intros. apply H.  omega. 
  apply H. omega.
Qed.

Lemma set_cont_outside_inject:
  forall c1 c2 lo hi delta,
  contentmap_inject c1 c2 lo hi delta ->
  forall n p,
  (forall x1 x2, p <= x1 < p + Z_of_nat n ->
                 lo <= x2 < hi -> 
                 x1 <> x2 + delta) ->
  contentmap_inject c1 (set_cont n p c2) lo hi delta.
Proof.
  unfold contentmap_inject. intros.  
  rewrite set_cont_outside1. apply H. assumption. 
  intros. apply H0. auto. auto.
Qed.

Lemma setN_outside_inject:
  forall n c1 c2 lo hi delta  p v,
  contentmap_inject c1 c2 lo hi delta ->
  (forall x1 x2, p <= x1 < p + Z_of_nat (S n) ->
                 lo <= x2 < hi ->
                 x1 <> x2 + delta) ->
  contentmap_inject c1 (setN n p v c2) lo hi delta.
Proof.
  intros. unfold setN. red; intros. rewrite update_o.
  apply set_cont_outside_inject with lo hi. auto.
  intros. apply H0. rewrite inj_S. omega. auto. auto. 
  apply H0. rewrite inj_S. omega. auto.
Qed.

Lemma store_contents_outside_inject:
  forall c1 c2 lo hi delta sz p v,
  contentmap_inject c1 c2 lo hi delta ->
  (forall x1 x2, p <= x1 < p + size_mem sz ->
                 lo <= x2 < hi ->
                 x1 <> x2 + delta)->
  contentmap_inject c1 (store_contents sz c2 p v) lo hi delta.
Proof.
  intros c1 c2 lo hi delta sz. generalize (size_mem_pos sz) . intro . 
  induction sz ;intros ;simpl ; apply setN_outside_inject ; assumption . 
Qed.

Lemma store_mapped_inject_1:
  forall chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  mem_inject m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  val_content_inject (mem_chunk chunk) v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ mem_inject n1 n2.
Proof.
intros. 
generalize (size_chunk_pos chunk); intro SIZEPOS.
generalize (store_inv _ _ _ _ _ _ H0).
intros [A [B [C [D [P E]]]]].
inversion H.
generalize (mi_mappedblocks0 _ _ _ H1). intros [U V].
inversion V.
generalize (in_bounds_inject _ _ _ _ _ V (conj B C)). intro BND.
exists  (unchecked_store chunk m2 b2 (ofs+delta) v2 BND).
split. unfold store.
rewrite zlt_true; auto.
case (in_bounds chunk (ofs + delta) (blocks m2 b2)); intro.
assert (a = BND). apply proof_irrelevance. congruence.
omegaContradiction.
constructor.
intros. apply mi_freeblocks0. rewrite <- D. assumption.
intros. generalize (mi_mappedblocks0 b b' delta0 H3).
intros [W Y]. split. simpl. auto.
rewrite E; simpl. unfold update.
(* Cas 1: memes blocs b = b1  b'= b2 *)
case (zeq b b1); intro.
subst b. assert (b'= b2). congruence. subst b'. 
assert (delta0 = delta). congruence. subst delta0.
rewrite zeq_true. inversion Y. constructor; simpl; auto.
apply store_contents_inject; auto.
(* Cas 2: blocs differents dans m1 mais mappes sur le meme bloc de m2 *)
case (zeq b' b2); intro.
subst b'.  
inversion Y. constructor; simpl; auto.
generalize (store_contents_outside_inject _ _ _ _ _ (mem_chunk chunk) 
  (ofs+delta) v2 bci_contents1).
intros.
apply H4. 
elim (mi_no_overlap0 b b1 b2 b2 delta0 delta n H3 H1).
tauto.
unfold high_bound, low_bound. intros. 
apply sym_not_equal. replace x1 with ((x1 - delta) + delta).
apply H5. assumption. unfold size_chunk in C. omega. omega. 
(* Cas 3: blocs differents dans m1 et dans m2 *)
auto.

unfold high_bound, low_bound. 
rewrite E; simpl; intros.
unfold high_bound, low_bound in mi_no_overlap0. 
unfold update.
case (zeq b0 b1).
intro. subst b1. simpl.
rewrite zeq_false; auto.
intro. case (zeq b3 b1); intro.
subst b3. simpl. auto.
auto.
Qed.

Lemma store_mapped_inject:
  forall chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  mem_inject m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  val_inject v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ mem_inject n1 n2.
Proof.
  intros. eapply store_mapped_inject_1; eauto.
Qed.

Lemma store_unmapped_inject:
  forall chunk m1 b1 ofs v1 n1 m2,
  mem_inject m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  mem_inject n1 m2.
Proof.
intros.
inversion H.
generalize (store_inv _ _ _ _ _ _ H0).
intros [A [B [C [D [P E]]]]].
constructor.
rewrite D. assumption.
intros. elim (mi_mappedblocks0 _ _ _ H2); intros.
split. auto. 
rewrite E; unfold update.
rewrite zeq_false. assumption.
congruence.
intros. 
assert (forall b, low_bound n1 b = low_bound m1 b).
  intros. unfold low_bound; rewrite E; unfold update.
  case (zeq b b1); intros. subst b1; reflexivity. reflexivity.
assert (forall b, high_bound n1 b = high_bound m1 b).
  intros. unfold high_bound; rewrite E; unfold update.
  case (zeq b b1); intros. subst b1; reflexivity. reflexivity.
repeat rewrite H5. repeat rewrite H6. auto.
Qed.

Lemma storev_mapped_inject_1:
  forall chunk m1 a1 v1 n1 m2 a2 v2,
  mem_inject m1 m2 ->
  storev chunk m1 a1 v1 = Some n1 ->
  val_inject a1 a2 ->
  val_content_inject (mem_chunk chunk) v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 = Some n2 /\ mem_inject n1 n2.
Proof.
  intros. destruct a1; simpl in H0; try discriminate.
  inversion H1. subst b.
  simpl. replace (Int.signed ofs2) with (Int.signed i + x).
  eapply store_mapped_inject_1; eauto.
  symmetry. generalize (store_inv _ _ _ _ _ _ H0). intros [A [B [C [D [P E]]]]].
  apply address_inject with m1 m2 chunk b1 b2; auto.
Qed.

Lemma storev_mapped_inject:
  forall chunk m1 a1 v1 n1 m2 a2 v2,
  mem_inject m1 m2 ->
  storev chunk m1 a1 v1 = Some n1 ->
  val_inject a1 a2 ->
  val_inject v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 = Some n2 /\ mem_inject n1 n2.
Proof.
  intros. eapply storev_mapped_inject_1; eauto.
Qed.

(** Relation between injections and [free] *)

Lemma free_first_inject :
  forall m1 m2 b,
  mem_inject m1 m2 ->
  mem_inject (free m1 b) m2.
Proof.
  intros.  inversion H.  constructor . auto.
  simpl. intros. 
  generalize (mi_mappedblocks0 b0 b' delta H0).
  intros [A B] . split. assumption . unfold update.
  case (zeq b0 b); intro.  inversion B. constructor; simpl; auto.
  intros.  omega.
  unfold contentmap_inject.
  intros. omegaContradiction.
  auto.  intros. 
  unfold free . unfold low_bound , high_bound.  simpl. unfold update.
  case (zeq b1 b);intro.  simpl.
  right. intros. omegaContradiction.
  case (zeq b2 b);intro.  simpl.
  right . intros. omegaContradiction. 
  unfold low_bound, high_bound in mi_no_overlap0. auto.
Qed.  

Lemma free_first_list_inject :
  forall l m1 m2,
  mem_inject m1 m2 ->
  mem_inject (free_list m1 l) m2.
Proof.
  induction l; simpl; intros.
  auto.
  apply free_first_inject. auto.
Qed.

Lemma free_snd_inject:
  forall m1 m2 b,
  (forall b1 delta, f b1 = Some(b, delta) -> 
                    low_bound m1 b1 >= high_bound m1 b1) ->
  mem_inject m1 m2 ->
  mem_inject m1 (free m2 b).
Proof.
  intros. inversion H0. constructor. auto.
  simpl. intros. 
  generalize (mi_mappedblocks0 b0 b' delta H1).
  intros [A B] . split. assumption . 
  inversion B. unfold update.
  case (zeq b' b); intro.
  subst b'. generalize (H _ _ H1). unfold low_bound, high_bound; intro.
  constructor. auto.  elim bci_range4 ; intro.
  (**delta=0**)
  left ; auto .  
  (** delta<>0**)
  right . 
  simpl. compute. split; intro; congruence. 
 intros. omegaContradiction.
  red; intros. omegaContradiction.
  auto.
  auto.
Qed.

Lemma bounds_free_block: 
  forall m1 b m1' , free m1 b = m1' ->
  low_bound m1' b >= high_bound m1' b.
Proof.
  intros.  unfold free in H.
  rewrite<- H . unfold low_bound , high_bound .
  simpl . rewrite update_s. simpl.  omega.  
Qed.

Lemma free_empty_bounds:
  forall l m1 ,
  let m1' := free_list m1 l in
  (forall b, In b l -> low_bound m1' b >= high_bound m1' b).
Proof.
  induction l . intros .  inversion H.  
  intros.
  generalize (in_inv H).
  intro . elim H0.   intro .  subst b.  simpl in m1' .  
  generalize ( bounds_free_block  
  (fold_right (fun (b : block) (m : mem) => free m b) m1 l) a m1') . 
  intros.  apply H1. auto .  intros.  simpl in m1'. unfold m1' . 
  unfold low_bound , high_bound .  simpl . 
  unfold update; case (zeq b a); intro; simpl.
  omega . 
  unfold low_bound , high_bound in IHl . auto.
Qed.       

Lemma free_inject:
  forall m1 m2 l b,
  (forall b1 delta, f b1 = Some(b, delta) -> In b1 l) ->
  mem_inject m1 m2 ->
  mem_inject (free_list m1 l) (free m2 b).
Proof.
   intros. apply free_snd_inject. 
   intros. apply free_empty_bounds. apply H with delta. auto. 
   apply free_first_list_inject. auto.
Qed. 

Lemma contents_init_data_inject:
  forall id, contentmap_inject (contents_init_data 0 id) (contents_init_data 0 id) 0 (size_init_data_list id) 0.
Proof.
  intro id0. 
  set (sz0 := size_init_data_list id0).
  assert (forall id pos,
    0 <= pos -> pos + size_init_data_list id <= sz0 ->
    contentmap_inject (contents_init_data pos id) (contents_init_data pos id) 0 sz0 0).
  induction id; simpl; intros.
  red; intros; constructor.
  assert (forall n dt,
    size_init_data a = 1 + Z_of_nat n ->
    content_inject dt dt ->
    contentmap_inject (setN n pos dt (contents_init_data (pos + size_init_data a) id))
                      (setN n pos dt (contents_init_data (pos + size_init_data a) id))
                      0 sz0 0).
  intros. set (pos' := pos) in |- * at 3. replace pos' with (pos + 0).
  apply setN_inject. apply IHid. omega. omega. auto. auto. 
  generalize (size_init_data_list_pos id). omega. unfold pos'; omega.
  destruct a;
  try (apply H1; [reflexivity|repeat constructor]).
  apply IHid. generalize (Zmax2 z 0). omega. simpl in H0; omega.
  apply IHid. omega. simpl size_init_data in H0. omega. 
  apply H. omega. unfold sz0. omega.
Qed.

End MEM_INJECT.

Hint Resolve val_inject_int val_inject_float val_inject_ptr val_inject_undef.
Hint Resolve val_nil_inject val_cons_inject.

(** Monotonicity properties of memory injections. *)

Definition inject_incr (f1 f2: meminj) : Prop :=
  forall b, f1 b = f2 b \/ f1 b = None.

Lemma inject_incr_refl :
   forall f , inject_incr f f .
Proof. unfold inject_incr . intros. left . auto . Qed.

Lemma inject_incr_trans :
  forall f1 f2 f3  , 
  inject_incr f1 f2 -> inject_incr f2 f3 -> inject_incr f1 f3 .
Proof .
  unfold inject_incr . intros . 
  generalize (H b) . intro . generalize (H0 b) . intro . 
  elim H1 ; elim H2 ; intros.  
  rewrite H3 in H4 . left . auto .
  rewrite H3 in H4 . right . auto .
  right ; auto . 
  right ; auto .
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
  induction vl ;  intros;  inversion H0. auto . 
  subst a . generalize (val_inject_incr f1 f2 v v' H H3) .  
  intro .  auto .
Qed.       

Hint Resolve inject_incr_refl val_inject_incr val_list_inject_incr.

Section MEM_INJECT_INCR.

Variable f1 f2: meminj.
Hypothesis INCR: inject_incr f1 f2.

Lemma val_content_inject_incr:
  forall chunk v v',
  val_content_inject f1 chunk v v' ->
  val_content_inject f2 chunk v v'.
Proof.
  intros. inversion H.
  apply val_content_inject_base. eapply val_inject_incr; eauto.
  apply val_content_inject_8; auto.
  apply val_content_inject_16; auto.
  apply val_content_inject_32; auto.
Qed.

Lemma content_inject_incr:
  forall c c', content_inject f1 c c' -> content_inject f2 c c'.
Proof.
  induction 1; constructor; eapply val_content_inject_incr; eauto.
Qed.

Lemma contentmap_inject_incr:
  forall c c' lo hi delta,
  contentmap_inject f1 c c' lo hi delta -> 
  contentmap_inject f2 c c' lo hi delta.
Proof.
  unfold contentmap_inject; intros.
  apply content_inject_incr. auto.
Qed.

Lemma block_contents_inject_incr:
  forall c c' delta,
  block_contents_inject f1 c c' delta ->
  block_contents_inject f2 c c' delta.
Proof.
  intros. inversion H. constructor; auto.
  apply contentmap_inject_incr; auto.
Qed.

End MEM_INJECT_INCR.

(** Properties of injections and allocations. *)

Definition extend_inject
       (b: block) (x: option (block * Z)) (f: meminj) : meminj :=
  fun b' => if eq_block b' b then x else f b'.

Lemma extend_inject_incr:
  forall f b x,
  f b = None ->
  inject_incr f (extend_inject b x f).
Proof.
  intros; red; intros. unfold extend_inject. 
  case (eq_block b0 b); intro. subst b0. right; auto. left; auto.
Qed.

Lemma alloc_right_inject:
  forall f m1 m2 lo hi m2' b,
  mem_inject f m1 m2 ->
  alloc m2 lo hi = (m2', b) ->
  mem_inject f m1 m2'.
Proof.
  intros. unfold alloc in H0. injection H0; intros A B; clear H0.
  inversion H.
  constructor.
  assumption.
  intros. generalize (mi_mappedblocks0 _ _ _ H0). intros [C D].
  rewrite <- B; simpl. split. omega. 
  rewrite update_o. auto. omega.
  assumption.
Qed.

Lemma alloc_unmapped_inject:
  forall f m1 m2 lo hi m1' b,
  mem_inject f m1 m2 ->
  alloc m1 lo hi = (m1', b) ->
  mem_inject (extend_inject b None f) m1' m2 /\
  inject_incr f (extend_inject b None f).
Proof.
  intros. unfold alloc in H0. injection H0; intros; clear H0.
  inversion H.
  assert (inject_incr f (extend_inject b None f)).
  apply extend_inject_incr. apply mi_freeblocks0. rewrite H1. omega. 
  split; auto.
  constructor. 
  rewrite <- H2; simpl; intros. unfold extend_inject.
  case (eq_block b0 b); intro. auto. apply mi_freeblocks0. omega.
  intros until delta. unfold extend_inject at 1. case (eq_block b0 b); intro.
  intros; discriminate.
  intros. rewrite <- H2; simpl. rewrite H1. 
  rewrite update_o; auto. 
  elim (mi_mappedblocks0 _ _ _ H3). intros A B.
  split. auto. apply block_contents_inject_incr with f. auto. auto.
  intros until delta2. unfold extend_inject.
  case (eq_block b1 b); intro. congruence.
  case (eq_block b2 b); intro. congruence.
  rewrite <- H2. unfold low_bound, high_bound; simpl. rewrite H1.
  repeat rewrite update_o; auto.
  exact (mi_no_overlap0 b1 b2 b1' b2' delta1 delta2).
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
  intros. 
  generalize (fun b' => low_bound_alloc _ _ b' _ _ _ H0).
  intro LOW.
  generalize (fun b' => high_bound_alloc _ _ b' _ _ _ H0).
  intro HIGH.
  unfold alloc in H0. injection H0; intros A B; clear H0.
  inversion H.
  (* inject_incr *)
  assert (inject_incr f (extend_inject b (Some (b', ofs)) f)).
  apply extend_inject_incr. apply mi_freeblocks0. rewrite A. omega. 
  split; auto.
  constructor. 
  (* mi_freeblocks *)
  rewrite <- B; simpl; intros. unfold extend_inject.
  case (eq_block b0 b); intro. unfold block in *. omegaContradiction.
  apply mi_freeblocks0. omega.
  (* mi_mappedblocks *)
  intros until delta. unfold extend_inject at 1. 
  case (eq_block b0 b); intro.
  intros. subst b0. inversion H8. subst b'0; subst delta. 
  split. assumption. 
  rewrite <- B; simpl. rewrite A. rewrite update_s.
  constructor; auto.
  unfold empty_block. simpl. intros. unfold low_bound in H5. unfold high_bound in H6. omega.
  simpl. red; intros. constructor.
  intros. 
  generalize (mi_mappedblocks0 _ _ _ H8). intros [C D].
  split. auto. 
  rewrite <- B; simpl; rewrite A; rewrite update_o; auto.
  apply block_contents_inject_incr with f; auto.
  (* no overlap *)
  intros until delta2. unfold extend_inject.
  repeat rewrite LOW. repeat rewrite HIGH. unfold eq_block.
  case (zeq b1 b); case (zeq b2 b); intros.
  congruence.
  inversion H9. subst b1'; subst delta1.
  case (eq_block b' b2'); intro.
  subst b2'. generalize (H7 _ _ H10). intro. 
  right. intros. omega. left. auto.
  inversion H10. subst b2'; subst delta2.
  case (eq_block b' b1'); intro.
  subst b1'. generalize (H7 _ _ H9). intro.
  right. intros. omega. left. auto.
  apply mi_no_overlap0; auto.
Qed.

Lemma alloc_parallel_inject:
  forall f m1 m2 lo hi m1' m2' b1 b2,
  mem_inject f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  alloc m2 lo hi = (m2', b2) ->
  Int.min_signed <= lo -> hi <= Int.max_signed ->
  mem_inject (extend_inject b1 (Some(b2,0)) f) m1' m2' /\
  inject_incr f (extend_inject b1 (Some(b2,0)) f).
Proof.
  intros. 
  generalize (low_bound_alloc _ _ b2 _ _ _ H1). rewrite zeq_true; intro LOW.
  generalize (high_bound_alloc _ _ b2 _ _ _ H1). rewrite zeq_true; intro HIGH.
  eapply alloc_mapped_inject; eauto.
  eapply alloc_right_inject; eauto.
  eapply valid_new_block; eauto.
  compute. intuition congruence.
  rewrite LOW; auto.
  rewrite HIGH; auto.
  rewrite LOW; omega.
  rewrite HIGH; omega.
  intros. elim (mi_mappedblocks _ _ _ H _ _ _ H4); intros.
  injection H1; intros. rewrite H7 in H5. omegaContradiction.
Qed.
