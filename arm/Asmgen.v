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

(** Translation from Mach to ARM. *)

Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import Asm.

(** Recognition of integer immediate arguments.
- For arithmetic operations, immediates are
  8-bit quantities zero-extended and rotated right by 0, 2, 4, ... 30 bits.
- For memory accesses of type [Mint32], immediate offsets are
  12-bit quantities plus a sign bit.
- For other memory accesses, immediate offsets are
  8-bit quantities plus a sign bit. *)

Fixpoint is_immed_arith_aux (n: nat) (x msk: int) {struct n}: bool :=
  match n with
  | Datatypes.O => false
  | Datatypes.S n' =>
      Int.eq (Int.and x (Int.not msk)) Int.zero ||
      is_immed_arith_aux n' x (Int.ror msk (Int.repr 2))
  end.

Definition is_immed_arith (x: int) : bool :=
  is_immed_arith_aux 16%nat x (Int.repr 255).

Definition is_immed_mem_word (x: int) : bool :=
  Int.lt x (Int.repr 4096) && Int.lt (Int.repr (-4096)) x.
  
Definition is_immed_mem_small (x: int) : bool :=
  Int.lt x (Int.repr 256) && Int.lt (Int.repr (-256)) x.
  
Definition is_immed_mem_float (x: int) : bool :=
  Int.eq (Int.and x (Int.repr 3)) Int.zero
  && Int.lt x (Int.repr 1024) && Int.lt (Int.repr (-1024)) x.
  
(** Decomposition of a 32-bit integer into a list of immediate arguments,
    whose sum or "or" or "xor" equals the integer. *)

Fixpoint decompose_int_rec (N: nat) (n p: int) : list int :=
  match N with
  | Datatypes.O =>
      if Int.eq_dec n Int.zero then nil else n :: nil
  | Datatypes.S M =>
      if Int.eq_dec (Int.and n (Int.shl (Int.repr 3) p)) Int.zero then
        decompose_int_rec M n (Int.add p (Int.repr 2))
      else
        let m := Int.shl (Int.repr 255) p in
        Int.and n m ::
        decompose_int_rec M (Int.and n (Int.not m)) (Int.add p (Int.repr 2))
  end.

Definition decompose_int (n: int) : list int :=
  match decompose_int_rec 12%nat n Int.zero with
  | nil => Int.zero :: nil
  | l   => l
  end.

Definition iterate_op (op1 op2: shift_op -> instruction) (l: list int) (k: code) :=
  match l with
  | nil =>
      op1 (SOimm Int.zero) :: k                 (**r should never happen *)
  | i :: l' =>
      op1 (SOimm i) :: map (fun i => op2 (SOimm i)) l' ++ k
  end.

(** Smart constructors for integer immediate arguments. *)

Definition loadimm (r: ireg) (n: int) (k: code) :=
  let d1 := decompose_int n in
  let d2 := decompose_int (Int.not n) in
  if le_dec (List.length d1) (List.length d2)
  then iterate_op (Pmov r) (Porr r r) d1 k
  else iterate_op (Pmvn r) (Pbic r r) d2 k.

Definition addimm (r1 r2: ireg) (n: int) (k: code) :=
  let d1 := decompose_int n in
  let d2 := decompose_int (Int.neg n) in
  if le_dec (List.length d1) (List.length d2)
  then iterate_op (Padd r1 r2) (Padd r1 r1) d1 k
  else iterate_op (Psub r1 r2) (Psub r1 r1) d2 k.

Definition andimm (r1 r2: ireg) (n: int) (k: code) :=
  if is_immed_arith n 
  then Pand r1 r2 (SOimm n) :: k
  else iterate_op (Pbic r1 r2) (Pbic r1 r1) (decompose_int (Int.not n)) k.

Definition rsubimm (r1 r2: ireg) (n: int) (k: code) :=
  iterate_op (Prsb r1 r2) (Padd r1 r1) (decompose_int n) k.

Definition orimm  (r1 r2: ireg) (n: int) (k: code) :=
  iterate_op (Porr r1 r2) (Porr r1 r1) (decompose_int n) k.

Definition xorimm  (r1 r2: ireg) (n: int) (k: code) :=
  iterate_op (Peor r1 r2) (Peor r1 r1) (decompose_int n) k.

(** Translation of a shift immediate operation (type [Op.shift]) *)

Definition transl_shift (s: shift) (r: ireg) : shift_op :=
  match s with
  | Slsl n => SOlslimm r (s_amount n)
  | Slsr n => SOlsrimm r (s_amount n)
  | Sasr n => SOasrimm r (s_amount n)
  | Sror n => SOrorimm r (s_amount n)
  end.

(** Translation of a condition.  Prepends to [k] the instructions
  that evaluate the condition and leave its boolean result in one of
  the bits of the condition register.  The bit in question is
  determined by the [crbit_for_cond] function. *)

Definition transl_cond
              (cond: condition) (args: list mreg) (k: code) :=
  match cond, args with
  | Ccomp c, a1 :: a2 :: nil =>
      Pcmp (ireg_of a1) (SOreg (ireg_of a2)) :: k
  | Ccompu c, a1 :: a2 :: nil =>
      Pcmp (ireg_of a1) (SOreg (ireg_of a2)) :: k
  | Ccompshift c s, a1 :: a2 :: nil =>
      Pcmp (ireg_of a1) (transl_shift s (ireg_of a2)) :: k
  | Ccompushift c s, a1 :: a2 :: nil =>
      Pcmp (ireg_of a1) (transl_shift s (ireg_of a2)) :: k
  | Ccompimm c n, a1 :: nil =>
      if is_immed_arith n then
        Pcmp (ireg_of a1) (SOimm n) :: k
      else
        loadimm IR14 n (Pcmp (ireg_of a1) (SOreg IR14) :: k)
  | Ccompuimm c n, a1 :: nil =>
      if is_immed_arith n then
        Pcmp (ireg_of a1) (SOimm n) :: k
      else
        loadimm IR14 n (Pcmp (ireg_of a1) (SOreg IR14) :: k)
  | Ccompf cmp, a1 :: a2 :: nil =>
      Pfcmpd (freg_of a1) (freg_of a2) :: k
  | Cnotcompf cmp, a1 :: a2 :: nil =>
      Pfcmpd (freg_of a1) (freg_of a2) :: k
  | Ccompfzero cmp, a1 :: nil =>
      Pfcmpzd (freg_of a1) :: k
  | Cnotcompfzero cmp, a1 :: nil =>
      Pfcmpzd (freg_of a1) :: k
  | _, _ =>
     k (**r never happens for well-typed code *)
  end.

Definition crbit_for_signed_cmp (cmp: comparison) :=
  match cmp with
  | Ceq => CReq
  | Cne => CRne
  | Clt => CRlt
  | Cle => CRle
  | Cgt => CRgt
  | Cge => CRge
  end.

Definition crbit_for_unsigned_cmp (cmp: comparison) :=
  match cmp with
  | Ceq => CReq
  | Cne => CRne
  | Clt => CRlo
  | Cle => CRls
  | Cgt => CRhi
  | Cge => CRhs
  end.

Definition crbit_for_float_cmp (cmp: comparison) :=
  match cmp with
  | Ceq => CReq
  | Cne => CRne
  | Clt => CRmi
  | Cle => CRls
  | Cgt => CRgt
  | Cge => CRge
  end.

Definition crbit_for_float_not_cmp (cmp: comparison) :=
  match cmp with
  | Ceq => CRne
  | Cne => CReq
  | Clt => CRpl
  | Cle => CRhi
  | Cgt => CRle
  | Cge => CRlt
  end.

Definition crbit_for_cond (cond: condition) :=
  match cond with
  | Ccomp cmp => crbit_for_signed_cmp cmp
  | Ccompu cmp => crbit_for_unsigned_cmp cmp
  | Ccompshift cmp s => crbit_for_signed_cmp cmp
  | Ccompushift cmp s => crbit_for_unsigned_cmp cmp
  | Ccompimm cmp n => crbit_for_signed_cmp cmp
  | Ccompuimm cmp n => crbit_for_unsigned_cmp cmp
  | Ccompf cmp => crbit_for_float_cmp cmp
  | Cnotcompf cmp => crbit_for_float_not_cmp cmp
  | Ccompfzero cmp => crbit_for_float_cmp cmp
  | Cnotcompfzero cmp => crbit_for_float_not_cmp cmp
  end.

(** Translation of the arithmetic operation [r <- op(args)].
  The corresponding instructions are prepended to [k]. *)

Definition transl_op
              (op: operation) (args: list mreg) (r: mreg) (k: code) :=
  match op, args with
  | Omove, a1 :: nil =>
      match mreg_type a1 with
      | Tint => Pmov (ireg_of r) (SOreg (ireg_of a1)) :: k
      | Tfloat => Pfcpyd (freg_of r) (freg_of a1) :: k
      end
  | Ointconst n, nil =>
      loadimm (ireg_of r) n k
  | Ofloatconst f, nil =>
      Pflid (freg_of r) f :: k
  | Oaddrsymbol s ofs, nil =>
      Ploadsymbol (ireg_of r) s ofs :: k
  | Oaddrstack n, nil =>
      addimm (ireg_of r) IR13 n k
  | Oadd, a1 :: a2 :: nil =>
      Padd (ireg_of r) (ireg_of a1) (SOreg (ireg_of a2)) :: k
  | Oaddshift s, a1 :: a2 :: nil =>
      Padd (ireg_of r) (ireg_of a1) (transl_shift s (ireg_of a2)) :: k
  | Oaddimm n, a1 :: nil =>
      addimm (ireg_of r) (ireg_of a1) n k
  | Osub, a1 :: a2 :: nil =>
      Psub (ireg_of r) (ireg_of a1) (SOreg (ireg_of a2)) :: k
  | Osubshift s, a1 :: a2 :: nil =>
      Psub (ireg_of r) (ireg_of a1) (transl_shift s (ireg_of a2)) :: k
  | Orsubshift s, a1 :: a2 :: nil =>
      Prsb (ireg_of r) (ireg_of a1) (transl_shift s (ireg_of a2)) :: k
  | Orsubimm n, a1 :: nil =>
      rsubimm (ireg_of r) (ireg_of a1) n k
  | Omul, a1 :: a2 :: nil =>
      if ireg_eq (ireg_of r) (ireg_of a1)
      || ireg_eq (ireg_of r) (ireg_of a2)
      then Pmul IR14 (ireg_of a1) (ireg_of a2) :: Pmov (ireg_of r) (SOreg IR14) :: k
      else Pmul (ireg_of r) (ireg_of a1) (ireg_of a2) :: k
  | Odiv, a1 :: a2 :: nil =>
      Psdiv (ireg_of r) (ireg_of a1) (ireg_of a2) :: k
  | Odivu, a1 :: a2 :: nil =>
      Pudiv (ireg_of r) (ireg_of a1) (ireg_of a2) :: k
  | Oand, a1 :: a2 :: nil =>
      Pand (ireg_of r) (ireg_of a1) (SOreg (ireg_of a2)) :: k
  | Oandshift s, a1 :: a2 :: nil =>
      Pand (ireg_of r) (ireg_of a1) (transl_shift s (ireg_of a2)) :: k
  | Oandimm n, a1 :: nil =>
      andimm (ireg_of r) (ireg_of a1) n k
  | Oor, a1 :: a2 :: nil =>
      Porr (ireg_of r) (ireg_of a1) (SOreg (ireg_of a2)) :: k
  | Oorshift s, a1 :: a2 :: nil =>
      Porr (ireg_of r) (ireg_of a1) (transl_shift s (ireg_of a2)) :: k
  | Oorimm n, a1 :: nil =>
      orimm (ireg_of r) (ireg_of a1) n k
  | Oxor, a1 :: a2 :: nil =>
      Peor (ireg_of r) (ireg_of a1) (SOreg (ireg_of a2)) :: k
  | Oxorshift s, a1 :: a2 :: nil =>
      Peor (ireg_of r) (ireg_of a1) (transl_shift s (ireg_of a2)) :: k
  | Oxorimm n, a1 :: nil =>
      xorimm (ireg_of r) (ireg_of a1) n k
  | Obic, a1 :: a2 :: nil =>
      Pbic (ireg_of r) (ireg_of a1) (SOreg (ireg_of a2)) :: k
  | Obicshift s, a1 :: a2 :: nil =>
      Pbic (ireg_of r) (ireg_of a1) (transl_shift s (ireg_of a2)) :: k
  | Onot, a1 :: nil =>
      Pmvn (ireg_of r) (SOreg (ireg_of a1)) :: k
  | Onotshift s, a1 :: nil =>
      Pmvn (ireg_of r) (transl_shift s (ireg_of a1)) :: k
  | Oshl, a1 :: a2 :: nil =>
      Pmov (ireg_of r) (SOlslreg (ireg_of a1) (ireg_of a2)) :: k
  | Oshr, a1 :: a2 :: nil =>
      Pmov (ireg_of r) (SOasrreg (ireg_of a1) (ireg_of a2)) :: k
  | Oshru, a1 :: a2 :: nil =>
      Pmov (ireg_of r) (SOlsrreg (ireg_of a1) (ireg_of a2)) :: k
  | Oshift s, a1 :: nil =>
      Pmov (ireg_of r) (transl_shift s (ireg_of a1)) :: k
  | Oshrximm n, a1 :: nil =>
      Pcmp (ireg_of a1) (SOimm Int.zero) ::
      addimm IR14 (ireg_of a1) (Int.sub (Int.shl Int.one n) Int.one)
         (Pmovc CRge IR14 (SOreg (ireg_of a1)) ::
          Pmov (ireg_of r) (SOasrimm IR14 n) :: k)
  | Onegf, a1 :: nil =>
      Pfnegd (freg_of r) (freg_of a1) :: k
  | Oabsf, a1 :: nil =>
      Pfabsd (freg_of r) (freg_of a1) :: k
  | Oaddf, a1 :: a2 :: nil =>
      Pfaddd (freg_of r) (freg_of a1) (freg_of a2) :: k
  | Osubf, a1 :: a2 :: nil =>
      Pfsubd (freg_of r) (freg_of a1) (freg_of a2) :: k
  | Omulf, a1 :: a2 :: nil =>
      Pfmuld (freg_of r) (freg_of a1) (freg_of a2) :: k
  | Odivf, a1 :: a2 :: nil =>
      Pfdivd (freg_of r) (freg_of a1) (freg_of a2) :: k
  | Osingleoffloat, a1 :: nil =>
      Pfcvtsd (freg_of r) (freg_of a1) :: k
  | Ointoffloat, a1 :: nil =>
      Pftosizd (ireg_of r) (freg_of a1) :: k
  | Ointuoffloat, a1 :: nil =>
      Pftouizd (ireg_of r) (freg_of a1) :: k
  | Ofloatofint, a1 :: nil =>
      Pfsitod (freg_of r) (ireg_of a1) :: k
  | Ofloatofintu, a1 :: nil =>
      Pfuitod (freg_of r) (ireg_of a1) :: k
  | Ocmp cmp, _ =>
      transl_cond cmp args
        (Pmov (ireg_of r) (SOimm Int.zero) ::
         Pmovc (crbit_for_cond cmp) (ireg_of r) (SOimm Int.one) ::
         k)
  | _, _ =>
      k (**r never happens for well-typed code *)
  end.

(** Common code to translate [Mload] and [Mstore] instructions. *)

Definition transl_shift_addr (s: shift) (r: ireg) : shift_addr :=
  match s with
  | Slsl n => SAlsl r (s_amount n)
  | Slsr n => SAlsr r (s_amount n)
  | Sasr n => SAasr r (s_amount n)
  | Sror n => SAror r (s_amount n)
  end.

Definition transl_load_store
     (mk_instr_imm: ireg -> int -> instruction)
     (mk_instr_gen: option (ireg -> shift_addr -> instruction))
     (is_immed: int -> bool)
     (addr: addressing) (args: list mreg) (k: code) : code :=
  match addr, args with
  | Aindexed n, a1 :: nil =>
      if is_immed n then
        mk_instr_imm (ireg_of a1) n :: k
      else
        addimm IR14 (ireg_of a1) n
          (mk_instr_imm IR14 Int.zero :: k)
  | Aindexed2, a1 :: a2 :: nil =>
      match mk_instr_gen with
      | Some f =>
          f (ireg_of a1) (SAreg (ireg_of a2)) :: k
      | None =>
          Padd IR14 (ireg_of a1) (SOreg (ireg_of a2)) ::
          mk_instr_imm IR14 Int.zero :: k
      end
  | Aindexed2shift s, a1 :: a2 :: nil =>
      match mk_instr_gen with
      | Some f =>
          f (ireg_of a1) (transl_shift_addr s (ireg_of a2)) :: k
      | None =>
          Padd IR14 (ireg_of a1) (transl_shift s (ireg_of a2)) ::
          mk_instr_imm IR14 Int.zero :: k
      end
  | Ainstack n, nil =>
      if is_immed n then
        mk_instr_imm IR13 n :: k
      else
        addimm IR14 IR13 n
          (mk_instr_imm IR14 Int.zero :: k)
  | _, _ =>
      (* should not happen *) k
  end.

Definition transl_load_store_int
     (mk_instr: ireg -> ireg -> shift_addr -> instruction)
     (is_immed: int -> bool)
     (rd: mreg) (addr: addressing) (args: list mreg) (k: code) :=
  transl_load_store
    (fun r n => mk_instr (ireg_of rd) r (SAimm n))
    (Some (mk_instr (ireg_of rd)))
    is_immed addr args k.

Definition transl_load_store_float
     (mk_instr: freg -> ireg -> int -> instruction)
     (is_immed: int -> bool)
     (rd: mreg) (addr: addressing) (args: list mreg) (k: code) :=
  transl_load_store
    (mk_instr (freg_of rd))
    None
    is_immed addr args k.

Definition loadind_int (base: ireg) (ofs: int) (dst: ireg) (k: code) :=
  if is_immed_mem_word ofs then
    Pldr dst base (SAimm ofs) :: k
  else
    addimm IR14 base ofs
      (Pldr dst IR14 (SAimm Int.zero) :: k).

Definition loadind_float (base: ireg) (ofs: int) (dst: freg) (k: code) :=
  if is_immed_mem_float ofs then
    Pfldd dst base ofs :: k
  else
    addimm IR14 base ofs
      (Pfldd dst IR14 Int.zero :: k).

Definition loadind (base: ireg) (ofs: int) (ty: typ) (dst: mreg) (k: code) :=
  match ty with
  | Tint => loadind_int base ofs (ireg_of dst) k
  | Tfloat => loadind_float base ofs (freg_of dst) k
  end.

Definition storeind_int (src: ireg) (base: ireg) (ofs: int) (k: code) :=
  if is_immed_mem_word ofs then
    Pstr src base (SAimm ofs) :: k
  else
    addimm IR14 base ofs
      (Pstr src IR14 (SAimm Int.zero) :: k).

Definition storeind_float (src: freg) (base: ireg) (ofs: int) (k: code) :=
  if is_immed_mem_float ofs then
    Pfstd src base ofs :: k
  else
    addimm IR14 base ofs
      (Pfstd src IR14 Int.zero :: k).

Definition storeind (src: mreg) (base: ireg) (ofs: int) (ty: typ) (k: code) :=
  match ty with
  | Tint => storeind_int (ireg_of src) base ofs k
  | Tfloat => storeind_float (freg_of src) base ofs k
  end.

(** Translation of arguments to annotations *)

Definition transl_annot_param (p: Mach.annot_param) : Asm.annot_param :=
  match p with
  | Mach.APreg r => APreg (preg_of r)
  | Mach.APstack chunk ofs => APstack chunk ofs
  end.

(** Translation of a Mach instruction. *)

Definition transl_instr (f: Mach.function) (i: Mach.instruction) (k: code) :=
  match i with
  | Mgetstack ofs ty dst =>
      loadind IR13 ofs ty dst k
  | Msetstack src ofs ty =>
      storeind src IR13 ofs ty k
  | Mgetparam ofs ty dst =>
      loadind_int IR13 f.(fn_link_ofs) IR14 (loadind IR14 ofs ty dst k)
  | Mop op args res =>
      transl_op op args res k
  | Mload chunk addr args dst =>
      match chunk with
      | Mint8signed =>
          transl_load_store_int Pldrsb is_immed_mem_small dst addr args k
      | Mint8unsigned =>
          transl_load_store_int Pldrb is_immed_mem_word dst addr args k
      | Mint16signed =>
          transl_load_store_int Pldrsh is_immed_mem_small dst addr args k
      | Mint16unsigned =>
          transl_load_store_int Pldrh is_immed_mem_small dst addr args k
      | Mint32 =>
          transl_load_store_int Pldr is_immed_mem_word dst addr args k
      | Mfloat32 =>
          transl_load_store_float Pflds is_immed_mem_float dst addr args k
      | Mfloat64 | Mfloat64al32 =>
          transl_load_store_float Pfldd is_immed_mem_float dst addr args k
      end
  | Mstore chunk addr args src =>
      match chunk with
      | Mint8signed =>
          transl_load_store_int Pstrb is_immed_mem_small src addr args k
      | Mint8unsigned =>
          transl_load_store_int Pstrb is_immed_mem_word src addr args k
      | Mint16signed =>
          transl_load_store_int Pstrh is_immed_mem_small src addr args k
      | Mint16unsigned =>
          transl_load_store_int Pstrh is_immed_mem_small src addr args k
      | Mint32 =>
          transl_load_store_int Pstr is_immed_mem_word src addr args k
      | Mfloat32 =>
          transl_load_store_float Pfsts is_immed_mem_float src addr args k
      | Mfloat64 | Mfloat64al32 =>
          transl_load_store_float Pfstd is_immed_mem_float src addr args k
      end
  | Mcall sig (inl r) =>
      Pblreg (ireg_of r) sig :: k
  | Mcall sig (inr symb) =>
      Pblsymb symb sig :: k
  | Mtailcall sig (inl r) =>
      loadind_int IR13 f.(fn_retaddr_ofs) IR14
        (Pfreeframe f.(fn_stacksize) f.(fn_link_ofs) :: Pbreg (ireg_of r) sig :: k)
  | Mtailcall sig (inr symb) =>
      loadind_int IR13 f.(fn_retaddr_ofs) IR14
        (Pfreeframe f.(fn_stacksize) f.(fn_link_ofs) :: Pbsymb symb sig :: k)
  | Mbuiltin ef args res =>
      Pbuiltin ef (map preg_of args) (preg_of res) :: k
  | Mannot ef args =>
      Pannot ef (map transl_annot_param args) :: k
  | Mlabel lbl =>
      Plabel lbl :: k
  | Mgoto lbl =>
      Pb lbl :: k
  | Mcond cond args lbl =>
      transl_cond cond args (Pbc (crbit_for_cond cond) lbl :: k)
  | Mjumptable arg tbl =>
      Pmov IR14 (SOlslimm (ireg_of arg) (Int.repr 2)) ::
      Pbtbl IR14 tbl :: k
  | Mreturn =>
      loadind_int IR13 f.(fn_retaddr_ofs) IR14
        (Pfreeframe f.(fn_stacksize) f.(fn_link_ofs) :: Pbreg IR14 f.(Mach.fn_sig) :: k)
  end.

Definition transl_code (f: Mach.function) (il: list Mach.instruction) :=
  List.fold_right (transl_instr f) nil il.

(** Translation of a whole function.  Note that we must check
  that the generated code contains less than [2^32] instructions,
  otherwise the offset part of the [PC] code pointer could wrap
  around, leading to incorrect executions. *)

Definition transl_function (f: Mach.function) :=
  mkfunction f.(Mach.fn_sig)
    (Pallocframe f.(fn_stacksize) f.(fn_link_ofs) ::
     Pstr IR14 IR13 (SAimm f.(fn_retaddr_ofs)) ::
     transl_code f f.(Mach.fn_code)).

Fixpoint code_size (c: code) : Z :=
  match c with
  | nil => 0
  | instr :: c' => code_size c' + 1
  end.

Open Local Scope string_scope.

Definition transf_function (f: Mach.function) : res Asm.function :=
  let tf := transl_function f in
  if zlt Int.max_unsigned (code_size tf.(fn_code))
  then Errors.Error (msg "code size exceeded")
  else Errors.OK tf.

Definition transf_fundef (f: Mach.fundef) : res Asm.fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: Mach.program) : res Asm.program :=
  transform_partial_program transf_fundef p.

