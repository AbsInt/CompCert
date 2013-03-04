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
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import Asm.

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

(** Extracting integer or float registers. *)

Definition ireg_of (r: mreg) : res ireg :=
  match preg_of r with IR mr => OK mr | _ => Error(msg "Asmgen.ireg_of") end.

Definition freg_of (r: mreg) : res freg :=
  match preg_of r with FR mr => OK mr | _ => Error(msg "Asmgen.freg_of") end.

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

Definition mk_immed_mem_word (x: int) : int :=
  Int.sign_ext 13 x.
  
Definition is_immed_mem_small (x: int) : bool :=
  Int.lt x (Int.repr 256) && Int.lt (Int.repr (-256)) x.
  
Definition mk_immed_mem_small (x: int) : int :=
  Int.sign_ext 9 x.
  
Definition is_immed_mem_float (x: int) : bool :=
  Int.eq (Int.and x (Int.repr 3)) Int.zero
  && Int.lt x (Int.repr 1024) && Int.lt (Int.repr (-1024)) x.
  
Definition mk_immed_mem_float (x: int) : int :=
  Int.and (Int.sign_ext 11 x) (Int.repr 4294967288).  (**r 0xfffffff8 *)
  
(** Decomposition of a 32-bit integer into a list of immediate arguments,
    whose sum or "or" or "xor" equals the integer. *)

Fixpoint decompose_int_rec (N: nat) (n p: int) : list int :=
  match N with
  | Datatypes.O =>
      if Int.eq n Int.zero then nil else n :: nil
  | Datatypes.S M =>
      if Int.eq (Int.and n (Int.shl (Int.repr 3) p)) Int.zero then
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
  if NPeano.leb (List.length d1) (List.length d2)
  then iterate_op (Pmov r) (Porr r r) d1 k
  else iterate_op (Pmvn r) (Pbic r r) d2 k.

Definition addimm (r1 r2: ireg) (n: int) (k: code) :=
  let d1 := decompose_int n in
  let d2 := decompose_int (Int.neg n) in
  if NPeano.leb (List.length d1) (List.length d2)
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
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pcmp r1(SOreg r2) :: k)
  | Ccompu c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pcmp r1 (SOreg r2) :: k)
  | Ccompshift c s, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pcmp r1 (transl_shift s r2) :: k)
  | Ccompushift c s, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pcmp r1 (transl_shift s r2) :: k)
  | Ccompimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (if is_immed_arith n then
            Pcmp r1 (SOimm n) :: k
          else
            loadimm IR14 n (Pcmp r1 (SOreg IR14) :: k))
  | Ccompuimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (if is_immed_arith n then
            Pcmp r1 (SOimm n) :: k
          else
            loadimm IR14 n (Pcmp r1 (SOreg IR14) :: k))
  | Ccompf cmp, a1 :: a2 :: nil =>
      do r1 <- freg_of a1; do r2 <- freg_of a2;
      OK (Pfcmpd r1 r2 :: k)
  | Cnotcompf cmp, a1 :: a2 :: nil =>
      do r1 <- freg_of a1; do r2 <- freg_of a2;
      OK (Pfcmpd r1 r2 :: k)
  | Ccompfzero cmp, a1 :: nil =>
      do r1 <- freg_of a1;
      OK (Pfcmpzd r1 :: k)
  | Cnotcompfzero cmp, a1 :: nil =>
      do r1 <- freg_of a1;
      OK (Pfcmpzd r1 :: k)
  | _, _ =>
      Error(msg "Asmgen.transl_cond")
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
              (op: operation) (args: list mreg) (res: mreg) (k: code) :=
  match op, args with
  | Omove, a1 :: nil =>
      match preg_of res, preg_of a1 with
      | IR r, IR a => OK (Pmov r (SOreg a) :: k)
      | FR r, FR a => OK (Pfcpyd r a :: k)
      |  _  ,  _   => Error(msg "Asmgen.Omove")
      end
  | Ointconst n, nil =>
      do r <- ireg_of res;
      OK (loadimm r n k)
  | Ofloatconst f, nil =>
      do r <- freg_of res;
      OK (Pflid r f :: k)
  | Oaddrsymbol s ofs, nil =>
      do r <- ireg_of res;
      OK (Ploadsymbol r s ofs :: k)
  | Oaddrstack n, nil =>
      do r <- ireg_of res;
      OK (addimm r IR13 n k)
  | Oadd, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Padd r r1 (SOreg r2) :: k)
  | Oaddshift s, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Padd r r1 (transl_shift s r2) :: k)
  | Oaddimm n, a1 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1;
      OK (addimm r r1 n k)
  | Osub, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Psub r r1 (SOreg r2) :: k)
  | Osubshift s, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Psub r r1 (transl_shift s r2) :: k)
  | Orsubshift s, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Prsb r r1 (transl_shift s r2) :: k)
  | Orsubimm n, a1 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1;
      OK (rsubimm r r1 n k)
  | Omul, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (if ireg_eq r r1 || ireg_eq r r2
          then Pmul IR14 r1 r2 :: Pmov r (SOreg IR14) :: k
          else Pmul r r1 r2 :: k)
  | Odiv, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Psdiv r r1 r2 :: k)
  | Odivu, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pudiv r r1 r2 :: k)
  | Oand, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pand r r1 (SOreg r2) :: k)
  | Oandshift s, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pand r r1 (transl_shift s r2) :: k)
  | Oandimm n, a1 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1;
      OK (andimm r r1 n k)
  | Oor, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Porr r r1 (SOreg r2) :: k)
  | Oorshift s, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Porr r r1 (transl_shift s r2) :: k)
  | Oorimm n, a1 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1;
      OK (orimm r r1 n k)
  | Oxor, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Peor r r1 (SOreg r2) :: k)
  | Oxorshift s, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Peor r r1 (transl_shift s r2) :: k)
  | Oxorimm n, a1 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1;
      OK (xorimm r r1 n k)
  | Obic, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pbic r r1 (SOreg r2) :: k)
  | Obicshift s, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pbic r r1 (transl_shift s r2) :: k)
  | Onot, a1 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1;
      OK (Pmvn r (SOreg r1) :: k)
  | Onotshift s, a1 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1;
      OK (Pmvn r (transl_shift s r1) :: k)
  | Oshl, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pmov r (SOlslreg r1 r2) :: k)
  | Oshr, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pmov r (SOasrreg r1 r2) :: k)
  | Oshru, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pmov r (SOlsrreg r1 r2) :: k)
  | Oshift s, a1 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1;
      OK (Pmov r (transl_shift s r1) :: k)
  | Oshrximm n, a1 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1;
      OK (Pcmp r1 (SOimm Int.zero) ::
          addimm IR14 r1 (Int.sub (Int.shl Int.one n) Int.one)
             (Pmovc CRge IR14 (SOreg r1) ::
              Pmov r (SOasrimm IR14 n) :: k))
  | Onegf, a1 :: nil =>
      do r <- freg_of res; do r1 <- freg_of a1;
      OK (Pfnegd r r1 :: k)
  | Oabsf, a1 :: nil =>
      do r <- freg_of res; do r1 <- freg_of a1;
      OK (Pfabsd r r1 :: k)
  | Oaddf, a1 :: a2 :: nil =>
      do r <- freg_of res; do r1 <- freg_of a1; do r2 <- freg_of a2;
      OK (Pfaddd r r1 r2 :: k)
  | Osubf, a1 :: a2 :: nil =>
      do r <- freg_of res; do r1 <- freg_of a1; do r2 <- freg_of a2;
      OK (Pfsubd r r1 r2 :: k)
  | Omulf, a1 :: a2 :: nil =>
      do r <- freg_of res; do r1 <- freg_of a1; do r2 <- freg_of a2;
      OK (Pfmuld r r1 r2 :: k)
  | Odivf, a1 :: a2 :: nil =>
      do r <- freg_of res; do r1 <- freg_of a1; do r2 <- freg_of a2;
      OK (Pfdivd r r1 r2 :: k)
  | Osingleoffloat, a1 :: nil =>
      do r <- freg_of res; do r1 <- freg_of a1;
      OK (Pfcvtsd r r1 :: k)
  | Ointoffloat, a1 :: nil =>
      do r <- ireg_of res; do r1 <- freg_of a1;
      OK (Pftosizd r r1 :: k)
  | Ointuoffloat, a1 :: nil =>
      do r <- ireg_of res; do r1 <- freg_of a1;
      OK (Pftouizd r r1 :: k)
  | Ofloatofint, a1 :: nil =>
      do r <- freg_of res; do r1 <- ireg_of a1;
      OK (Pfsitod r r1 :: k)
  | Ofloatofintu, a1 :: nil =>
      do r <- freg_of res; do r1 <- ireg_of a1;
      OK (Pfuitod r r1 :: k)
  | Ocmp cmp, _ =>
      do r <- ireg_of res;
      transl_cond cmp args
        (Pmov r (SOimm Int.zero) ::
         Pmovc (crbit_for_cond cmp) r (SOimm Int.one) ::
         k)
  | _, _ =>
      Error(msg "Asmgen.transl_op")
  end.

(** Accessing data in the stack frame. *)

Definition indexed_memory_access
    (mk_instr: ireg -> int -> instruction)
    (mk_immed: int -> int)
    (base: ireg) (n: int) (k: code) :=
  let n1 := mk_immed n in
  if Int.eq n n1
  then mk_instr base n :: k
  else addimm IR14 base (Int.sub n n1) (mk_instr IR14 n1 :: k).

Definition loadind_int (base: ireg) (ofs: int) (dst: ireg) (k: code) :=
  indexed_memory_access (fun base n => Pldr dst base (SAimm n)) mk_immed_mem_word base ofs k.

Definition loadind_float (base: ireg) (ofs: int) (dst: freg) (k: code) :=
  indexed_memory_access (Pfldd dst) mk_immed_mem_float base ofs k.

Definition loadind (base: ireg) (ofs: int) (ty: typ) (dst: mreg) (k: code) :=
  match ty with
  | Tint   => do r <- ireg_of dst; OK (loadind_int base ofs r k)
  | Tfloat => do r <- freg_of dst; OK (loadind_float base ofs r k)
  end.

Definition storeind_int (src: ireg) (base: ireg) (ofs: int) (k: code) :=
  indexed_memory_access (fun base n => Pstr src base (SAimm n)) mk_immed_mem_word base ofs k.

Definition storeind_float (src: freg) (base: ireg) (ofs: int) (k: code) :=
  indexed_memory_access (Pfstd src) mk_immed_mem_float base ofs k.

Definition storeind (src: mreg) (base: ireg) (ofs: int) (ty: typ) (k: code) :=
  match ty with
  | Tint   => do r <- ireg_of src; OK (storeind_int r base ofs k)
  | Tfloat => do r <- freg_of src; OK (storeind_float r base ofs k)
  end.

(** Translation of memory accesses *)

Definition transl_shift_addr (s: shift) (r: ireg) : shift_addr :=
  match s with
  | Slsl n => SAlsl r (s_amount n)
  | Slsr n => SAlsr r (s_amount n)
  | Sasr n => SAasr r (s_amount n)
  | Sror n => SAror r (s_amount n)
  end.

Definition transl_memory_access
     (mk_instr_imm: ireg -> int -> instruction)
     (mk_instr_gen: option (ireg -> shift_addr -> instruction))
     (mk_immed: int -> int)
     (addr: addressing) (args: list mreg) (k: code) :=
  match addr, args with
  | Aindexed n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (indexed_memory_access mk_instr_imm mk_immed r1 n k)
  | Aindexed2, a1 :: a2 :: nil =>
      match mk_instr_gen with
      | Some f =>
          do r1 <- ireg_of a1; do r2 <- ireg_of a2;
          OK (f r1 (SAreg r2) :: k)
      | None =>
          Error (msg "Asmgen.Aindexed2")
      end
  | Aindexed2shift s, a1 :: a2 :: nil =>
      match mk_instr_gen with
      | Some f =>
          do r1 <- ireg_of a1; do r2 <- ireg_of a2;
          OK (f r1 (transl_shift_addr s r2) :: k)
      | None =>
          Error (msg "Asmgen.Aindexed2shift")
      end
  | Ainstack n, nil =>
      OK (indexed_memory_access mk_instr_imm mk_immed IR13 n k)
  | _, _ =>
      Error(msg "Asmgen.transl_memory_access")
  end.

Definition transl_memory_access_int
     (mk_instr: ireg -> ireg -> shift_addr -> instruction)
     (mk_immed: int -> int)
     (dst: mreg) (addr: addressing) (args: list mreg) (k: code) :=
  do rd <- ireg_of dst;
  transl_memory_access
    (fun r n => mk_instr rd r (SAimm n))
    (Some (mk_instr rd))
    mk_immed addr args k.

Definition transl_memory_access_float
     (mk_instr: freg -> ireg -> int -> instruction)
     (mk_immed: int -> int)
     (dst: mreg) (addr: addressing) (args: list mreg) (k: code) :=
  do rd <- freg_of dst;
  transl_memory_access
    (mk_instr rd)
    None
    mk_immed addr args k.

Definition transl_load (chunk: memory_chunk) (addr: addressing)
                       (args: list mreg) (dst: mreg) (k: code) :=
  match chunk with
  | Mint8signed =>
      transl_memory_access_int Pldrsb mk_immed_mem_small dst addr args k
  | Mint8unsigned =>
      transl_memory_access_int Pldrb mk_immed_mem_word dst addr args k
  | Mint16signed =>
      transl_memory_access_int Pldrsh mk_immed_mem_small dst addr args k
  | Mint16unsigned =>
      transl_memory_access_int Pldrh mk_immed_mem_small dst addr args k
  | Mint32 =>
      transl_memory_access_int Pldr mk_immed_mem_word dst addr args k
  | Mfloat32 =>
      transl_memory_access_float Pflds mk_immed_mem_float dst addr args k
  | Mfloat64 | Mfloat64al32 =>
      transl_memory_access_float Pfldd mk_immed_mem_float dst addr args k
  end.

Definition transl_store (chunk: memory_chunk) (addr: addressing)
                       (args: list mreg) (src: mreg) (k: code) :=
  match chunk with
  | Mint8signed =>
      transl_memory_access_int Pstrb mk_immed_mem_small src addr args k
  | Mint8unsigned =>
      transl_memory_access_int Pstrb mk_immed_mem_word src addr args k
  | Mint16signed =>
      transl_memory_access_int Pstrh mk_immed_mem_small src addr args k
  | Mint16unsigned =>
      transl_memory_access_int Pstrh mk_immed_mem_small src addr args k
  | Mint32 =>
      transl_memory_access_int Pstr mk_immed_mem_word src addr args k
  | Mfloat32 =>
      transl_memory_access_float Pfsts mk_immed_mem_float src addr args k
  | Mfloat64 | Mfloat64al32 =>
      transl_memory_access_float Pfstd mk_immed_mem_float src addr args k
  end.

(** Translation of arguments to annotations *)

Definition transl_annot_param (p: Mach.annot_param) : Asm.annot_param :=
  match p with
  | Mach.APreg r => APreg (preg_of r)
  | Mach.APstack chunk ofs => APstack chunk ofs
  end.

(** Translation of a Mach instruction. *)

Definition transl_instr (f: Mach.function) (i: Mach.instruction)
                        (r10_is_parent: bool) (k: code) :=
  match i with
  | Mgetstack ofs ty dst =>
      loadind IR13 ofs ty dst k
  | Msetstack src ofs ty =>
      storeind src IR13 ofs ty k
  | Mgetparam ofs ty dst =>
      do c <- loadind IR10 ofs ty dst k;
      OK (if r10_is_parent
          then c
          else loadind_int IR13 f.(fn_link_ofs) IR10 c)
  | Mop op args res =>
      transl_op op args res k
  | Mload chunk addr args dst =>
      transl_load chunk addr args dst k
  | Mstore chunk addr args src =>
      transl_store chunk addr args src k
  | Mcall sig (inl arg) =>
      do r <- ireg_of arg; OK (Pblreg r sig :: k)
  | Mcall sig (inr symb) =>
      OK (Pblsymb symb sig :: k)
  | Mtailcall sig (inl arg) =>
      do r <- ireg_of arg;
      OK (loadind_int IR13 f.(fn_retaddr_ofs) IR14
           (Pfreeframe f.(fn_stacksize) f.(fn_link_ofs) :: Pbreg r sig :: k))
  | Mtailcall sig (inr symb) =>
      OK (loadind_int IR13 f.(fn_retaddr_ofs) IR14
           (Pfreeframe f.(fn_stacksize) f.(fn_link_ofs) :: Pbsymb symb sig :: k))
  | Mbuiltin ef args res =>
      OK (Pbuiltin ef (map preg_of args) (preg_of res) :: k)
  | Mannot ef args =>
      OK (Pannot ef (map transl_annot_param args) :: k)
  | Mlabel lbl =>
      OK (Plabel lbl :: k)
  | Mgoto lbl =>
      OK (Pb lbl :: k)
  | Mcond cond args lbl =>
      transl_cond cond args (Pbc (crbit_for_cond cond) lbl :: k)
  | Mjumptable arg tbl =>
      do r <- ireg_of arg;
      OK (Pbtbl r tbl :: k)
  | Mreturn =>
      OK (loadind_int IR13 f.(fn_retaddr_ofs) IR14
            (Pfreeframe f.(fn_stacksize) f.(fn_link_ofs) ::
             Pbreg IR14 f.(Mach.fn_sig) :: k))
  end.

(** Translation of a code sequence *)

Definition r10_is_parent (before: bool) (i: Mach.instruction) : bool :=
  match i with
  | Msetstack src ofs ty => before
  | Mgetparam ofs ty dst => negb (mreg_eq dst IT1)
  | Mop Omove args res => before && negb (mreg_eq res IT1)
  | _ => false
  end.

Fixpoint transl_code (f: Mach.function) (il: list Mach.instruction)  (r10p: bool) :=
  match il with
  | nil => OK nil
  | i1 :: il' =>
      do k <- transl_code f il' (r10_is_parent r10p i1);
      transl_instr f i1 r10p k
  end.

(** Translation of a whole function.  Note that we must check
  that the generated code contains less than [2^32] instructions,
  otherwise the offset part of the [PC] code pointer could wrap
  around, leading to incorrect executions. *)

Definition transl_function (f: Mach.function) :=
  do c <- transl_code f f.(Mach.fn_code) true;
  OK (mkfunction f.(Mach.fn_sig)
        (Pallocframe f.(fn_stacksize) f.(fn_link_ofs) ::
         Pstr IR14 IR13 (SAimm f.(fn_retaddr_ofs)) :: c)).

Definition transf_function (f: Mach.function) : res Asm.function :=
  do tf <- transl_function f;
  if zlt Int.max_unsigned (list_length_z tf.(fn_code))
  then Error (msg "code size exceeded")
  else OK tf.

Definition transf_fundef (f: Mach.fundef) : res Asm.fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: Mach.program) : res Asm.program :=
  transform_partial_program transf_fundef p.

