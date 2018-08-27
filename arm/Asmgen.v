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
Require Import Compopts.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope error_monad_scope.

(** Extracting integer or float registers. *)

Definition ireg_of (r: mreg) : res ireg :=
  match preg_of r with IR mr => OK mr | _ => Error(msg "Asmgen.ireg_of") end.

Definition freg_of (r: mreg) : res freg :=
  match preg_of r with FR mr => OK mr | _ => Error(msg "Asmgen.freg_of") end.

(** Recognition of integer immediate arguments for arithmetic operations.
- ARM: immediates are 8-bit quantities zero-extended and rotated right
  by 0, 2, 4, ... 30 bits.  In other words, [n] is an immediate iff
  [rotate-left(n, p)] is between 0 and 255 for some [p = 0, 2, 4, ..., 30].
- Thumb: immediates are 8-bit quantities zero-extended and shifted left
  by 0, 1, ..., 31 bits.  In other words, [n] is an immediate if
  all bits are 0 except a run of 8 adjacent bits.  In addition,
  [00XY00XY] and [XY00XY00] and [XYXYXYXY] are immediates for
  a given [XY] 8-bit constant.
*)

Fixpoint is_immed_arith_arm (n: nat) (x: int) {struct n}: bool :=
  match n with
  | Datatypes.O => false
  | Datatypes.S n =>
      Int.eq x (Int.and x (Int.repr 255)) ||
      is_immed_arith_arm n (Int.rol x (Int.repr 2))
  end.

Fixpoint is_immed_arith_thumb (n: nat) (x: int) {struct n}: bool :=
  match n with
  | Datatypes.O => true
  | Datatypes.S n =>
      Int.eq x (Int.and x (Int.repr 255)) ||
      (Int.eq (Int.and x Int.one) Int.zero
       && is_immed_arith_thumb n (Int.shru x Int.one))
  end.

Definition is_immed_arith_thumb_special (x: int): bool :=
  let l1 := Int.and x (Int.repr 255) in
  let l2 := Int.shl l1 (Int.repr 8) in
  let l3 := Int.shl l2 (Int.repr 8) in
  let l4 := Int.shl l3 (Int.repr 8) in
  let l13 := Int.or l1 l3 in
  let l24 := Int.or l2 l4 in
  Int.eq x l13 || Int.eq x l24 || Int.eq x (Int.or l13 l24).

Definition is_immed_arith (x: int): bool :=
  if thumb tt
  then is_immed_arith_thumb 24%nat x || is_immed_arith_thumb_special x
  else is_immed_arith_arm 16%nat x.

(** Recognition of integer immediate arguments for indexed memory accesses.
- For 32-bit integers, immediate offsets are [(-2^12,2^12)] for ARM classic
  and [(-2^8,2^12)] for Thumb2.
- For 8- and 16-bit integers, immediate offsets are [(-2^8,2^8)].
- For 32- and 64-bit integers, immediate offsets are multiples of 4
  in [(-2^10,2^10)].

For all 3 kinds of accesses, we provide not a recognizer but a synthesizer:
a function taking an arbitrary offset [n] and returning a valid offset [n']
that contains as many useful bits of [n] as possible, so that the
computation of the remainder [n - n'] is as simple as possible.
In particular, if [n] is a representable immediate argument, we should have
[n' = n].
*)

Definition mk_immed_mem_word (x: int): int :=
  if Int.ltu x Int.zero then
    Int.neg (Int.zero_ext (if thumb tt then 8 else 12) (Int.neg x))
  else
    Int.zero_ext 12 x.

Definition mk_immed_mem_small (x: int): int :=
  if Int.ltu x Int.zero then
    Int.neg (Int.zero_ext 8 (Int.neg x))
  else
    Int.zero_ext 8 x.

Definition mk_immed_mem_float (x: int): int :=
  let x := Int.and x (Int.repr (-4)) in   (**r mask low 2 bits off *)
  if Int.ltu x Int.zero then
    Int.neg (Int.zero_ext 10 (Int.neg x))
  else
    Int.zero_ext 10 x.

(** Decomposition of a 32-bit integer into a list of immediate arguments,
    whose sum or "or" or "xor" equals the integer. *)

Fixpoint decompose_int_arm (N: nat) (n p: int) : list int :=
  match N with
  | Datatypes.O =>
      if Int.eq n Int.zero then nil else n :: nil
  | Datatypes.S M =>
      if Int.eq (Int.and n (Int.shl (Int.repr 3) p)) Int.zero then
        decompose_int_arm M n (Int.add p (Int.repr 2))
      else
        let m := Int.shl (Int.repr 255) p in
        Int.and n m ::
        decompose_int_arm M (Int.and n (Int.not m)) (Int.add p (Int.repr 2))
  end.

Fixpoint decompose_int_thumb (N: nat) (n p: int) : list int :=
  match N with
  | Datatypes.O =>
      if Int.eq n Int.zero then nil else n :: nil
  | Datatypes.S M =>
      if Int.eq (Int.and n (Int.shl Int.one p)) Int.zero then
        decompose_int_thumb M n (Int.add p Int.one)
      else
        let m := Int.shl (Int.repr 255) p in
        Int.and n m ::
        decompose_int_thumb M (Int.and n (Int.not m)) (Int.add p Int.one)
  end.

Definition decompose_int_base (n: int): list int :=
  if thumb tt
  then if is_immed_arith_thumb_special n
       then n :: nil
       else decompose_int_thumb 24%nat n Int.zero
  else decompose_int_arm 12%nat n Int.zero.

Definition decompose_int (n: int) : list int :=
  match decompose_int_base n with
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

Definition loadimm_word (r: ireg) (n: int) (k: code) :=
  let hi := Int.shru n (Int.repr 16) in
  if Int.eq hi Int.zero
  then Pmovw r n :: k
  else Pmovw r (Int.zero_ext 16 n) :: Pmovt r hi :: k.

Definition loadimm (r: ireg) (n: int) (k: code) :=
  let d1 := decompose_int n in
  let d2 := decompose_int (Int.not n) in
  let l1 := List.length d1 in
  let l2 := List.length d2 in
  if Nat.leb l1 1%nat then
    Pmov r (SOimm n) :: k
  else if Nat.leb l2 1%nat then
    Pmvn r (SOimm (Int.not n)) :: k
  else if Archi.thumb2_support then
    loadimm_word r n k
  else if Nat.leb l1 l2 then
    iterate_op (Pmov r) (Porr r r) d1 k
  else
    iterate_op (Pmvn r) (Pbic r r) d2 k.

Definition addimm (r1 r2: ireg) (n: int) (k: code) :=
  if Int.ltu (Int.repr (-256)) n then
    Psub r1 r2 (SOimm (Int.neg n)) :: k
  else
   (let d1 := decompose_int n in
    let d2 := decompose_int (Int.neg n) in
    if Nat.leb (List.length d1) (List.length d2)
    then iterate_op (Padd r1 r2) (Padd r1 r1) d1 k
    else iterate_op (Psub r1 r2) (Psub r1 r1) d2 k).

Definition rsubimm (r1 r2: ireg) (n: int) (k: code) :=
  iterate_op (Prsb r1 r2) (Padd r1 r1) (decompose_int n) k.

Definition andimm (r1 r2: ireg) (n: int) (k: code) :=
  if is_immed_arith n
  then Pand r1 r2 (SOimm n) :: k
  else iterate_op (Pbic r1 r2) (Pbic r1 r1) (decompose_int (Int.not n)) k.

Definition orimm  (r1 r2: ireg) (n: int) (k: code) :=
  iterate_op (Porr r1 r2) (Porr r1 r1) (decompose_int n) k.

Definition xorimm  (r1 r2: ireg) (n: int) (k: code) :=
  iterate_op (Peor r1 r2) (Peor r1 r1) (decompose_int n) k.

(** Translation of a shift immediate operation (type [Op.shift]) *)

Definition transl_shift (s: shift) (r: ireg) : shift_op :=
  match s with
  | Slsl n => SOlsl r (s_amount n)
  | Slsr n => SOlsr r (s_amount n)
  | Sasr n => SOasr r (s_amount n)
  | Sror n => SOror r (s_amount n)
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
          else if is_immed_arith (Int.neg n) then
            Pcmn r1 (SOimm (Int.neg n)) :: k
          else
            loadimm IR14 n (Pcmp r1 (SOreg IR14) :: k))
  | Ccompuimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (if is_immed_arith n then
            Pcmp r1 (SOimm n) :: k
          else if is_immed_arith (Int.neg n) then
            Pcmn r1 (SOimm (Int.neg n)) :: k
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
  | Ccompfs cmp, a1 :: a2 :: nil =>
      do r1 <- freg_of a1; do r2 <- freg_of a2;
      OK (Pfcmps r1 r2 :: k)
  | Cnotcompfs cmp, a1 :: a2 :: nil =>
      do r1 <- freg_of a1; do r2 <- freg_of a2;
      OK (Pfcmps r1 r2 :: k)
  | Ccompfszero cmp, a1 :: nil =>
      do r1 <- freg_of a1;
      OK (Pfcmpzs r1 :: k)
  | Cnotcompfszero cmp, a1 :: nil =>
      do r1 <- freg_of a1;
      OK (Pfcmpzs r1 :: k)
  | _, _ =>
      Error(msg "Asmgen.transl_cond")
  end.

Definition cond_for_signed_cmp (cmp: comparison) :=
  match cmp with
  | Ceq => TCeq
  | Cne => TCne
  | Clt => TClt
  | Cle => TCle
  | Cgt => TCgt
  | Cge => TCge
  end.

Definition cond_for_unsigned_cmp (cmp: comparison) :=
  match cmp with
  | Ceq => TCeq
  | Cne => TCne
  | Clt => TClo
  | Cle => TCls
  | Cgt => TChi
  | Cge => TChs
  end.

Definition cond_for_float_cmp (cmp: comparison) :=
  match cmp with
  | Ceq => TCeq
  | Cne => TCne
  | Clt => TCmi
  | Cle => TCls
  | Cgt => TCgt
  | Cge => TCge
  end.

Definition cond_for_float_not_cmp (cmp: comparison) :=
  match cmp with
  | Ceq => TCne
  | Cne => TCeq
  | Clt => TCpl
  | Cle => TChi
  | Cgt => TCle
  | Cge => TClt
  end.

Definition cond_for_cond (cond: condition) :=
  match cond with
  | Ccomp cmp => cond_for_signed_cmp cmp
  | Ccompu cmp => cond_for_unsigned_cmp cmp
  | Ccompshift cmp s => cond_for_signed_cmp cmp
  | Ccompushift cmp s => cond_for_unsigned_cmp cmp
  | Ccompimm cmp n => cond_for_signed_cmp cmp
  | Ccompuimm cmp n => cond_for_unsigned_cmp cmp
  | Ccompf cmp => cond_for_float_cmp cmp
  | Cnotcompf cmp => cond_for_float_not_cmp cmp
  | Ccompfzero cmp => cond_for_float_cmp cmp
  | Cnotcompfzero cmp => cond_for_float_not_cmp cmp
  | Ccompfs cmp => cond_for_float_cmp cmp
  | Cnotcompfs cmp => cond_for_float_not_cmp cmp
  | Ccompfszero cmp => cond_for_float_cmp cmp
  | Cnotcompfszero cmp => cond_for_float_not_cmp cmp
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
  | Osingleconst f, nil =>
      do r <- freg_of res;
      OK (Pflis r f :: k)
  | Oaddrsymbol s ofs, nil =>
      do r <- ireg_of res;
      OK (Ploadsymbol r s ofs :: k)
  | Oaddrstack n, nil =>
      do r <- ireg_of res;
      OK (addimm r IR13 (Ptrofs.to_int n) k)
  | Ocast8signed, a1 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1;
      OK (if Archi.thumb2_support then
            Psbfx r r1 Int.zero (Int.repr 8) :: k
          else
            Pmov r (SOlsl r1 (Int.repr 24)) ::
            Pmov r (SOasr r (Int.repr 24)) :: k)
  | Ocast16signed, a1 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1;
      OK (if Archi.thumb2_support then
            Psbfx r r1 Int.zero (Int.repr 16) :: k
          else
            Pmov r (SOlsl r1 (Int.repr 16)) ::
            Pmov r (SOasr r (Int.repr 16)) :: k)
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
      OK (Pmul r r1 r2 :: k)
  | Omla, a1 :: a2 :: a3 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1;
      do r2 <- ireg_of a2; do r3 <- ireg_of a3;
      OK (Pmla r r1 r2 r3 :: k)
  | Omulhs, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Psmull IR14 r r1 r2 :: k)
  | Omulhu, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pumull IR14 r r1 r2 :: k)
  | Odiv, a1 :: a2 :: nil =>
      assertion (mreg_eq res R0);
      assertion (mreg_eq a1 R0);
      assertion (mreg_eq a2 R1);
      OK (Psdiv :: k)
  | Odivu, a1 :: a2 :: nil =>
      assertion (mreg_eq res R0);
      assertion (mreg_eq a1 R0);
      assertion (mreg_eq a2 R1);
      OK (Pudiv :: k)
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
      OK (Plsl r r1 r2 :: k)
  | Oshr, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pasr r r1 r2 :: k)
  | Oshru, a1 :: a2 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Plsr r r1 r2 :: k)
  | Oshift s, a1 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1;
      OK (Pmov r (transl_shift s r1) :: k)
  | Oshrximm n, a1 :: nil =>
      do r <- ireg_of res; do r1 <- ireg_of a1;
      if Int.eq n Int.zero then
        OK (Pmov r (SOreg r1) :: k)
      else
        OK (Pmov IR14 (SOasr r1 (Int.repr 31)) ::
            Padd IR14 r1 (SOlsr IR14 (Int.sub Int.iwordsize n)) ::
            Pmov r (SOasr IR14 n) :: k)
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
  | Onegfs, a1 :: nil =>
      do r <- freg_of res; do r1 <- freg_of a1;
      OK (Pfnegs r r1 :: k)
  | Oabsfs, a1 :: nil =>
      do r <- freg_of res; do r1 <- freg_of a1;
      OK (Pfabss r r1 :: k)
  | Oaddfs, a1 :: a2 :: nil =>
      do r <- freg_of res; do r1 <- freg_of a1; do r2 <- freg_of a2;
      OK (Pfadds r r1 r2 :: k)
  | Osubfs, a1 :: a2 :: nil =>
      do r <- freg_of res; do r1 <- freg_of a1; do r2 <- freg_of a2;
      OK (Pfsubs r r1 r2 :: k)
  | Omulfs, a1 :: a2 :: nil =>
      do r <- freg_of res; do r1 <- freg_of a1; do r2 <- freg_of a2;
      OK (Pfmuls r r1 r2 :: k)
  | Odivfs, a1 :: a2 :: nil =>
      do r <- freg_of res; do r1 <- freg_of a1; do r2 <- freg_of a2;
      OK (Pfdivs r r1 r2 :: k)
  | Osingleoffloat, a1 :: nil =>
      do r <- freg_of res; do r1 <- freg_of a1;
      OK (Pfcvtsd r r1 :: k)
  | Ofloatofsingle, a1 :: nil =>
      do r <- freg_of res; do r1 <- freg_of a1;
      OK (Pfcvtds r r1 :: k)
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
  | Ointofsingle, a1 :: nil =>
      do r <- ireg_of res; do r1 <- freg_of a1;
      OK (Pftosizs r r1 :: k)
  | Ointuofsingle, a1 :: nil =>
      do r <- ireg_of res; do r1 <- freg_of a1;
      OK (Pftouizs r r1 :: k)
  | Osingleofint, a1 :: nil =>
      do r <- freg_of res; do r1 <- ireg_of a1;
      OK (Pfsitos r r1 :: k)
  | Osingleofintu, a1 :: nil =>
      do r <- freg_of res; do r1 <- ireg_of a1;
      OK (Pfuitos r r1 :: k)
  | Ocmp cmp, _ =>
      do r <- ireg_of res;
      transl_cond cmp args
        (Pmovite (cond_for_cond cmp) r (SOimm Int.one) (SOimm Int.zero) :: k)
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

Definition loadind_int (base: ireg) (ofs: ptrofs) (dst: ireg) (k: code) :=
  indexed_memory_access (fun base n => Pldr dst base (SOimm n)) mk_immed_mem_word base (Ptrofs.to_int ofs) k.

Definition loadind (base: ireg) (ofs: ptrofs) (ty: typ) (dst: mreg) (k: code) :=
  let ofs := Ptrofs.to_int ofs in
  match ty, preg_of dst with
  | Tint, IR r =>
      OK (indexed_memory_access (fun base n => Pldr r base (SOimm n)) mk_immed_mem_word base ofs k)
  | Tany32, IR r =>
      OK (indexed_memory_access (fun base n => Pldr_a r base (SOimm n)) mk_immed_mem_word base ofs k)
  | Tsingle, FR r =>
      OK (indexed_memory_access (Pflds r) mk_immed_mem_float base ofs k)
  | Tfloat, FR r =>
      OK (indexed_memory_access (Pfldd r) mk_immed_mem_float base ofs k)
  | Tany64, FR r =>
      OK (indexed_memory_access (Pfldd_a r) mk_immed_mem_float base ofs k)
  | _, _ =>
      Error (msg "Asmgen.loadind")
  end.

Definition storeind (src: mreg) (base: ireg) (ofs: ptrofs) (ty: typ) (k: code) :=
  let ofs := Ptrofs.to_int ofs in
  match ty, preg_of src with
  | Tint, IR r =>
      OK (indexed_memory_access (fun base n => Pstr r base (SOimm n)) mk_immed_mem_word base ofs k)
  | Tany32, IR r =>
      OK (indexed_memory_access (fun base n => Pstr_a r base (SOimm n)) mk_immed_mem_word base ofs k)
  | Tsingle, FR r =>
      OK (indexed_memory_access (Pfsts r) mk_immed_mem_float base ofs k)
  | Tfloat, FR r =>
      OK (indexed_memory_access (Pfstd r) mk_immed_mem_float base ofs k)
  | Tany64, FR r =>
      OK (indexed_memory_access (Pfstd_a r) mk_immed_mem_float base ofs k)
  | _, _ =>
      Error (msg "Asmgen.storeind")
  end.

(** This is a variant of [storeind] that is used to save the return address
  at the beginning of a function.  It uses [R12] instead of [R14] as
  temporary register. *)

Definition save_lr (ofs: ptrofs) (k: code) :=
  let n := Ptrofs.to_int ofs in
  let n1 := mk_immed_mem_word n in
  if Int.eq n n1
  then Pstr IR14 IR13 (SOimm n) :: k
  else addimm IR12 IR13 (Int.sub n n1) (Pstr IR14 IR12 (SOimm n1) :: k).

Definition save_lr_preserves_R12 (ofs: ptrofs) : bool :=
  let n := Ptrofs.to_int ofs in
  let n1 := mk_immed_mem_word n in
  Int.eq n n1.

(** Translation of memory accesses *)

Definition transl_memory_access
     (mk_instr_imm: ireg -> int -> instruction)
     (mk_instr_gen: option (ireg -> shift_op -> instruction))
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
          OK (f r1 (SOreg r2) :: k)
      | None =>
          Error (msg "Asmgen.Aindexed2")
      end
  | Aindexed2shift s, a1 :: a2 :: nil =>
      match mk_instr_gen with
      | Some f =>
          do r1 <- ireg_of a1; do r2 <- ireg_of a2;
          OK (f r1 (transl_shift s r2) :: k)
      | None =>
          Error (msg "Asmgen.Aindexed2shift")
      end
  | Ainstack n, nil =>
      OK (indexed_memory_access mk_instr_imm mk_immed IR13 (Ptrofs.to_int n) k)
  | _, _ =>
      Error(msg "Asmgen.transl_memory_access")
  end.

Definition transl_memory_access_int
     (mk_instr: ireg -> ireg -> shift_op -> instruction)
     (mk_immed: int -> int)
     (dst: mreg) (addr: addressing) (args: list mreg) (k: code) :=
  do rd <- ireg_of dst;
  transl_memory_access
    (fun r n => mk_instr rd r (SOimm n))
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
  | Mfloat64 =>
      transl_memory_access_float Pfldd mk_immed_mem_float dst addr args k
  | _ =>
      Error (msg "Asmgen.transl_load")
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
  | Mfloat64 =>
      transl_memory_access_float Pfstd mk_immed_mem_float src addr args k
  | _ =>
      Error (msg "Asmgen.transl_store")
  end.

(** Translation of a Mach instruction. *)

Definition transl_instr (f: Mach.function) (i: Mach.instruction)
                        (r12_is_parent: bool) (k: code) :=
  match i with
  | Mgetstack ofs ty dst =>
      loadind IR13 ofs ty dst k
  | Msetstack src ofs ty =>
      storeind src IR13 ofs ty k
  | Mgetparam ofs ty dst =>
      do c <- loadind IR12 ofs ty dst k;
      OK (if r12_is_parent
          then c
          else loadind_int IR13 f.(fn_link_ofs) IR12 c)
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
      OK (Pbuiltin ef (List.map (map_builtin_arg preg_of) args) (map_builtin_res preg_of res) :: k)
  | Mlabel lbl =>
      OK (Plabel lbl :: k)
  | Mgoto lbl =>
      OK (Pb lbl :: k)
  | Mcond cond args lbl =>
      transl_cond cond args (Pbc (cond_for_cond cond) lbl :: k)
  | Mjumptable arg tbl =>
      do r <- ireg_of arg;
      OK (Pbtbl r tbl :: k)
  | Mreturn =>
      OK (loadind_int IR13 f.(fn_retaddr_ofs) IR14
            (Pfreeframe f.(fn_stacksize) f.(fn_link_ofs) ::
             Pbreg IR14 f.(Mach.fn_sig) :: k))
  end.

(** Translation of a code sequence *)

Definition it1_is_parent (before: bool) (i: Mach.instruction) : bool :=
  match i with
  | Msetstack src ofs ty => before
  | Mgetparam ofs ty dst => negb (mreg_eq dst R12)
  | Mop Omove args res => before && negb (mreg_eq res R12)
  | _ => false
  end.

(** This is the naive definition that we no longer use because it
  is not tail-recursive.  It is kept as specification. *)

Fixpoint transl_code (f: Mach.function) (il: list Mach.instruction) (it1p: bool) :=
  match il with
  | nil => OK nil
  | i1 :: il' =>
      do k <- transl_code f il' (it1_is_parent it1p i1);
      transl_instr f i1 it1p k
  end.

(** This is an equivalent definition in continuation-passing style
  that runs in constant stack space. *)

Fixpoint transl_code_rec (f: Mach.function) (il: list Mach.instruction)
                         (it1p: bool) (k: code -> res code) :=
  match il with
  | nil => k nil
  | i1 :: il' =>
      transl_code_rec f il' (it1_is_parent it1p i1)
        (fun c1 => do c2 <- transl_instr f i1 it1p c1; k c2)
  end.

Definition transl_code' (f: Mach.function) (il: list Mach.instruction) (it1p: bool) :=
  transl_code_rec f il it1p (fun c => OK c).

(** Translation of a whole function.  Note that we must check
  that the generated code contains less than [2^32] instructions,
  otherwise the offset part of the [PC] code pointer could wrap
  around, leading to incorrect executions. *)

Definition transl_function (f: Mach.function) :=
  do c <- transl_code f f.(Mach.fn_code)
                      (save_lr_preserves_R12 f.(fn_retaddr_ofs));
  OK (mkfunction f.(Mach.fn_sig)
        (Pallocframe f.(fn_stacksize) f.(fn_link_ofs) ::
         save_lr f.(fn_retaddr_ofs)
           (Pcfi_rel_offset (Ptrofs.to_int f.(fn_retaddr_ofs)):: c))).

Definition transf_function (f: Mach.function) : res Asm.function :=
  do tf <- transl_function f;
  if zlt Ptrofs.max_unsigned (list_length_z tf.(fn_code))
  then Error (msg "code size exceeded")
  else OK tf.

Definition transf_fundef (f: Mach.fundef) : res Asm.fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: Mach.program) : res Asm.program :=
  transform_partial_program transf_fundef p.
