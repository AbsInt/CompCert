(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*         Xavier Leroy, Collège de France and INRIA Paris             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Translation from Mach to AArch64. *)

Require Import Recdef Coqlib Zwf Zbits.
Require Import Errors AST Integers Floats Op.
Require Import Locations Mach Asm.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope error_monad_scope.

(** Alignment check for symbols *)

Parameter symbol_is_aligned : ident -> Z -> bool.
(** [symbol_is_aligned id sz] checks whether the symbol [id] is [sz] aligned *)

(** Extracting integer or float registers. *)

Definition ireg_of (r: mreg) : res ireg :=
  match preg_of r with IR mr => OK mr | _ => Error(msg "Asmgen.ireg_of") end.

Definition freg_of (r: mreg) : res freg :=
  match preg_of r with FR mr => OK mr | _ => Error(msg "Asmgen.freg_of") end.

(** Recognition of immediate arguments for logical integer operations.*)

(** Valid immediate arguments are repetitions of a bit pattern [B]
  of length [e] = 2, 4, 8, 16, 32 or 64.
  The bit pattern [B] must be of the form [0*1*0*] or [1*0*1*]
  but must not be all zeros or all ones. *)

(** The following automaton recognizes [0*1*0*|1*0*1*].
<<
               0          1          0
              / \        / \        / \
              \ /        \ /        \ /
        -0--> [B] --1--> [D] --0--> [F]
       /
     [A]
       \
        -1--> [C] --0--> [E] --1--> [G]
              / \        / \        / \
              \ /        \ /        \ /
               1          0          1
>>
*)

Module Automaton.

Inductive state : Type := SA | SB | SC | SD | SE | SF | SG | Sbad.

Definition start := SA.

Definition next (s: state) (b: bool) :=
  match s, b with
    | SA,false => SB      | SA,true => SC
    | SB,false => SB      | SB,true => SD
    | SC,false => SE      | SC,true => SC
    | SD,false => SF      | SD,true => SD
    | SE,false => SE      | SE,true => SG
    | SF,false => SF      | SF,true => Sbad
    | SG,false => Sbad    | SG,true => SG
    | Sbad,_ => Sbad
  end.

Definition accepting (s: state) :=
  match s with
  | SA | SB | SC | SD | SE | SF | SG => true
  | Sbad => false
  end.

Fixpoint run (len: nat) (s: state) (x: Z) : bool :=
  match len with
  | Datatypes.O => accepting s
  | Datatypes.S len => run len (next s (Z.odd x)) (Z.div2 x)
  end.

End Automaton.

(** The following function determines the candidate length [e],
    ensuring that [x] is a repetition [BB...B] 
    of a bit pattern [B] of length [e]. *)

Definition logical_imm_length (x: Z) (sixtyfour: bool) : nat :=
  (** [test n] checks that the low [2n] bits of [x] are of the
      form [BB], that is, two occurrences of the same [n] bits *)
  let test (n: Z) : bool :=
    Z.eqb (Zzero_ext n x) (Zzero_ext n (Z.shiftr x n)) in
  (** If [test n] fails, we know that the candidate length [e] is
      at least [2n].  Hence we test with decreasing values of [n]:
      32, 16, 8, 4, 2. *)
  if sixtyfour && negb (test 32) then 64%nat
  else if negb (test 16) then 32%nat
  else if negb (test 8) then 16%nat
  else if negb (test 4) then 8%nat
  else if negb (test 2) then 4%nat
  else 2%nat.

(** A valid logical immediate is 
- neither [0] nor [-1];
- composed of a repetition [BBBBB] of a bit-pattern [B] of length [e]
- the low [e] bits of the number, that is, [B], match [0*1*0*] or [1*0*1*].
*)

Definition is_logical_imm32 (x: int) : bool :=
  negb (Int.eq x Int.zero) && negb (Int.eq x Int.mone) &&
  Automaton.run (logical_imm_length (Int.unsigned x) false)
                Automaton.start (Int.unsigned x).

Definition is_logical_imm64 (x: int64) : bool :=
  negb (Int64.eq x Int64.zero) && negb (Int64.eq x Int64.mone) &&
  Automaton.run (logical_imm_length (Int64.unsigned x) true)
                Automaton.start (Int64.unsigned x).

(** Arithmetic immediates are 12-bit unsigned numbers, possibly shifted left 12 bits *)

Definition is_arith_imm32 (x: int) : bool :=
  Int.eq x (Int.zero_ext 12 x)
  || Int.eq x (Int.shl (Int.zero_ext 12 (Int.shru x (Int.repr 12))) (Int.repr 12)).

Definition is_arith_imm64 (x: int64) : bool :=
  Int64.eq x (Int64.zero_ext 12 x)
  || Int64.eq x (Int64.shl (Int64.zero_ext 12 (Int64.shru x (Int64.repr 12))) (Int64.repr 12)).

(** Decompose integer literals into 16-bit fragments *)

Fixpoint decompose_int (N: nat) (n p: Z) {struct N} : list (Z * Z) :=
  match N with
  | Datatypes.O => nil
  | Datatypes.S N =>
    let frag := Zzero_ext 16 (Z.shiftr n p) in
    if Z.eqb frag 0 then
      decompose_int N n (p + 16)
    else
      (frag, p) :: decompose_int N (Z.ldiff n (Z.shiftl 65535 p)) (p + 16)
  end.

Definition negate_decomposition (l: list (Z * Z)) :=
  List.map (fun np => (Z.lxor (fst np) 65535, snd np)) l.

Definition loadimm_k (sz: isize) (rd: ireg) (l: list (Z * Z)) (k: code) : code :=
  List.fold_right (fun np k => Pmovk sz rd (fst np) (snd np) :: k) k l.

Definition loadimm_z (sz: isize) (rd: ireg) (l: list (Z * Z)) (k: code) : code :=
  match l with
  | nil => Pmovz sz rd 0 0 :: k
  | (n1, p1) :: l => Pmovz sz rd n1 p1 :: loadimm_k sz rd l k
  end.

Definition loadimm_n (sz: isize) (rd: ireg) (l: list (Z * Z)) (k: code) : code :=
  match l with
  | nil => Pmovn sz rd 0 0 :: k
  | (n1, p1) :: l => Pmovn sz rd n1 p1 :: loadimm_k sz rd (negate_decomposition l) k
  end.

Definition loadimm (sz: isize) (rd: ireg) (n: Z) (k: code) : code :=
  let N := match sz with W => 2%nat | X => 4%nat end in
  let dz := decompose_int N n 0 in
  let dn := decompose_int N (Z.lnot n) 0 in
  if Nat.leb (List.length dz) (List.length dn)
  then loadimm_z sz rd dz k
  else loadimm_n sz rd dn k.

Definition loadimm32 (rd: ireg) (n: int) (k: code) : code :=
  if is_logical_imm32 n
  then Porrimm W rd XZR (Int.unsigned n) :: k
  else loadimm W rd (Int.unsigned n) k.

Definition loadimm64 (rd: ireg) (n: int64) (k: code) : code :=
  if is_logical_imm64 n
  then Porrimm X rd XZR (Int64.unsigned n) :: k
  else loadimm X rd (Int64.unsigned n) k.

(** Add immediate *)

Definition addimm_aux (insn: iregsp -> iregsp -> Z -> instruction)
                        (rd r1: iregsp) (n: Z) (k: code) :=
  let nlo := Zzero_ext 12 n in
  let nhi := n - nlo in
  if Z.eqb nhi 0 then
    insn rd r1 nlo :: k
  else if Z.eqb nlo 0 then
    insn rd r1 nhi :: k
  else
    insn rd r1 nhi :: insn rd rd nlo :: k.

Definition addimm32 (rd r1: ireg) (n: int) (k: code) : code :=
  let m := Int.neg n in
  if Int.eq n (Int.zero_ext 24 n) then
    addimm_aux (Paddimm W) rd r1 (Int.unsigned n) k
  else if Int.eq m (Int.zero_ext 24 m) then
    addimm_aux (Psubimm W) rd r1 (Int.unsigned m) k
  else if Int.lt n Int.zero then
    loadimm32 X16 m (Psub W rd r1 X16 SOnone :: k)
  else
    loadimm32 X16 n (Padd W rd r1 X16 SOnone :: k).

Definition addimm64 (rd r1: iregsp) (n: int64) (k: code) : code :=
  let m := Int64.neg n in
  if Int64.eq n (Int64.zero_ext 24 n) then
    addimm_aux (Paddimm X) rd r1 (Int64.unsigned n) k
  else if Int64.eq m (Int64.zero_ext 24 m) then
    addimm_aux (Psubimm X) rd r1 (Int64.unsigned m) k
  else if Int64.lt n Int64.zero then
    loadimm64 X16 m (Psubext rd r1 X16 (EOuxtx Int.zero) :: k)
  else
    loadimm64 X16 n (Paddext rd r1 X16 (EOuxtx Int.zero) :: k).

(** Logical immediate *)

Definition logicalimm32
              (insn1: ireg -> ireg0 -> Z -> instruction)
              (insn2: ireg -> ireg0 -> ireg -> shift_op -> instruction)
              (rd r1: ireg) (n: int) (k: code) : code :=
  if is_logical_imm32 n
  then insn1 rd r1 (Int.unsigned n) :: k
  else loadimm32 X16 n (insn2 rd r1 X16 SOnone :: k).

Definition logicalimm64
              (insn1: ireg -> ireg0 -> Z -> instruction)
              (insn2: ireg -> ireg0 -> ireg -> shift_op -> instruction)
              (rd r1: ireg) (n: int64) (k: code) : code :=
  if is_logical_imm64 n
  then insn1 rd r1 (Int64.unsigned n) :: k
  else loadimm64 X16 n (insn2 rd r1 X16 SOnone :: k).

(** Sign- or zero-extended arithmetic *)

Definition transl_extension (ex: extension) (a: int) : extend_op :=
  match ex with Xsgn32 => EOsxtw a | Xuns32 => EOuxtw a end.

Definition move_extended_base
              (rd: ireg) (r1: ireg) (ex: extension) (k: code) : code :=
  match ex with
  | Xsgn32 => Pcvtsw2x rd r1 :: k
  | Xuns32 => Pcvtuw2x rd r1 :: k
  end.

Definition move_extended
              (rd: ireg) (r1: ireg) (ex: extension) (a: int) (k: code) : code :=
  if Int.eq a Int.zero then
    move_extended_base rd r1 ex k
  else
    move_extended_base rd r1 ex (Padd X rd XZR rd (SOlsl a) :: k).

Definition arith_extended 
              (insnX: iregsp -> iregsp -> ireg -> extend_op -> instruction)
              (insnS: ireg -> ireg0 -> ireg -> shift_op -> instruction)
              (rd r1 r2: ireg) (ex: extension) (a: int) (k: code) : code :=
  if Int.ltu a (Int.repr 5) then
    insnX rd r1 r2 (transl_extension ex a) :: k
  else
    move_extended_base X16 r2 ex (insnS rd r1 X16 (SOlsl a) :: k).

(** Extended right shift *)

Definition shrx32 (rd r1: ireg) (n: int) (k: code) : code :=
  if Int.eq n Int.zero then
    Pmov rd r1 :: k
  else
    Porr W X16 XZR r1 (SOasr (Int.repr 31)) ::
    Padd W X16 r1 X16 (SOlsr (Int.sub Int.iwordsize n)) ::
    Porr W rd XZR X16 (SOasr n) :: k.

Definition shrx64 (rd r1: ireg) (n: int) (k: code) : code :=
  if Int.eq n Int.zero then
    Pmov rd r1 :: k
  else
    Porr X X16 XZR r1 (SOasr (Int.repr 63)) ::
    Padd X X16 r1 X16 (SOlsr (Int.sub Int64.iwordsize' n)) ::
    Porr X rd XZR X16 (SOasr n) :: k.

(** Load the address [id + ofs] in [rd] *)

Definition loadsymbol (rd: ireg) (id: ident) (ofs: ptrofs) (k: code) : code :=
  if Archi.pic_code tt then
    if Ptrofs.eq ofs Ptrofs.zero then
      Ploadsymbol rd id :: k
    else
      Ploadsymbol rd id :: addimm64 rd rd (Ptrofs.to_int64 ofs) k
  else
    Padrp rd id ofs :: Paddadr rd rd id ofs :: k.

(** Translate a shifted operand *)

Definition transl_shift (s: Op.shift) (a: int): Asm.shift_op :=
  match s with
  | Slsl => SOlsl a
  | Slsr => SOlsr a
  | Sasr => SOasr a
  | Sror => SOror a
  end.

(** Translation of a condition.  Prepends to [k] the instructions
  that evaluate the condition and leave its boolean result in one of
  the bits of the condition register.  The bit in question is
  determined by the [crbit_for_cond] function. *)

Definition transl_cond
              (cond: condition) (args: list mreg) (k: code) :=
  match cond, args with
  | (Ccomp c | Ccompu c), a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pcmp W r1 r2 SOnone :: k)
  | (Ccompshift c s a | Ccompushift c s a), a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pcmp W r1 r2 (transl_shift s a) :: k)
  | (Ccompimm c n | Ccompuimm c n), a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (if is_arith_imm32 n then
            Pcmpimm W r1 (Int.unsigned n) :: k
          else if is_arith_imm32 (Int.neg n) then
            Pcmnimm W r1 (Int.unsigned (Int.neg n)) :: k
          else
            loadimm32 X16 n (Pcmp W r1 X16 SOnone :: k))
  | (Cmaskzero n | Cmasknotzero n), a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (if is_logical_imm32 n then
            Ptstimm W r1 (Int.unsigned n) :: k
          else
            loadimm32 X16 n (Ptst W r1 X16 SOnone :: k))
  | (Ccompl c | Ccomplu c), a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pcmp X r1 r2 SOnone :: k)
  | (Ccomplshift c s a | Ccomplushift c s a), a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pcmp X r1 r2 (transl_shift s a) :: k)
  | (Ccomplimm c n | Ccompluimm c n), a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (if is_arith_imm64 n then
            Pcmpimm X r1 (Int64.unsigned n) :: k
          else if is_arith_imm64 (Int64.neg n) then
            Pcmnimm X r1 (Int64.unsigned (Int64.neg n)) :: k
          else
            loadimm64 X16 n (Pcmp X r1 X16 SOnone :: k))
  | (Cmasklzero n | Cmasklnotzero n), a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (if is_logical_imm64 n then
            Ptstimm X r1 (Int64.unsigned n) :: k
          else
            loadimm64 X16 n (Ptst X r1 X16 SOnone :: k))
  | Ccompf cmp, a1 :: a2 :: nil =>
      do r1 <- freg_of a1; do r2 <- freg_of a2;
      OK (Pfcmp D r1 r2 :: k)
  | Cnotcompf cmp, a1 :: a2 :: nil =>
      do r1 <- freg_of a1; do r2 <- freg_of a2;
      OK (Pfcmp D r1 r2 :: k)
  | Ccompfzero cmp, a1 :: nil =>
      do r1 <- freg_of a1;
      OK (Pfcmp0 D r1 :: k)
  | Cnotcompfzero cmp, a1 :: nil =>
      do r1 <- freg_of a1;
      OK (Pfcmp0 D r1 :: k)
  | Ccompfs cmp, a1 :: a2 :: nil =>
      do r1 <- freg_of a1; do r2 <- freg_of a2;
      OK (Pfcmp S r1 r2 :: k)
  | Cnotcompfs cmp, a1 :: a2 :: nil =>
      do r1 <- freg_of a1; do r2 <- freg_of a2;
      OK (Pfcmp S r1 r2 :: k)
  | Ccompfszero cmp, a1 :: nil =>
      do r1 <- freg_of a1;
      OK (Pfcmp0 S r1 :: k)
  | Cnotcompfszero cmp, a1 :: nil =>
      do r1 <- freg_of a1;
      OK (Pfcmp0 S r1 :: k)
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
  | Ccompshift cmp s a => cond_for_signed_cmp cmp
  | Ccompushift cmp s a => cond_for_unsigned_cmp cmp
  | Ccompimm cmp n => cond_for_signed_cmp cmp
  | Ccompuimm cmp n => cond_for_unsigned_cmp cmp
  | Cmaskzero n => TCeq
  | Cmasknotzero n => TCne
  | Ccompl cmp => cond_for_signed_cmp cmp
  | Ccomplu cmp => cond_for_unsigned_cmp cmp
  | Ccomplshift cmp s a => cond_for_signed_cmp cmp
  | Ccomplushift cmp s a => cond_for_unsigned_cmp cmp
  | Ccomplimm cmp n => cond_for_signed_cmp cmp
  | Ccompluimm cmp n => cond_for_unsigned_cmp cmp
  | Cmasklzero n => TCeq
  | Cmasklnotzero n => TCne
  | Ccompf cmp => cond_for_float_cmp cmp
  | Cnotcompf cmp => cond_for_float_not_cmp cmp
  | Ccompfzero cmp => cond_for_float_cmp cmp
  | Cnotcompfzero cmp => cond_for_float_not_cmp cmp
  | Ccompfs cmp => cond_for_float_cmp cmp
  | Cnotcompfs cmp => cond_for_float_not_cmp cmp
  | Ccompfszero cmp => cond_for_float_cmp cmp
  | Cnotcompfszero cmp => cond_for_float_not_cmp cmp
  end.

(** Translation of a conditional branch.  Prepends to [k] the instructions
  that evaluate the condition and ranch to [lbl] if it holds.
  We recognize some conditional branches that can be implemented
  without setting then testing condition flags.  *)

Definition transl_cond_branch_default
              (c: condition) (args: list mreg) (lbl: label) (k: code) :=
  transl_cond c args (Pbc (cond_for_cond c) lbl :: k).
 
Definition transl_cond_branch
              (c: condition) (args: list mreg) (lbl: label) (k: code) :=
  match args, c with
  | a1 :: nil, (Ccompimm Cne n | Ccompuimm Cne n) =>
      if Int.eq n Int.zero
      then (do r1 <- ireg_of a1; OK (Pcbnz W r1 lbl :: k))
      else transl_cond_branch_default c args lbl k
  | a1 :: nil, (Ccompimm Ceq n | Ccompuimm Ceq n) =>
      if Int.eq n Int.zero
      then (do r1 <- ireg_of a1; OK (Pcbz W r1 lbl :: k))
      else transl_cond_branch_default c args lbl k
  | a1 :: nil, (Ccomplimm Cne n | Ccompluimm Cne n) =>
      if Int64.eq n Int64.zero
      then (do r1 <- ireg_of a1; OK (Pcbnz X r1 lbl :: k))
      else transl_cond_branch_default c args lbl k
  | a1 :: nil, (Ccomplimm Ceq n | Ccompluimm Ceq n) =>
      if Int64.eq n Int64.zero
      then (do r1 <- ireg_of a1; OK (Pcbz X r1 lbl :: k))
      else transl_cond_branch_default c args lbl k
  | a1 :: nil, Cmaskzero n =>
      match Int.is_power2 n with
      | Some bit => do r1 <- ireg_of a1; OK (Ptbz W r1 bit lbl :: k)
      | None => transl_cond_branch_default c args lbl k
      end
  | a1 :: nil, Cmasknotzero n =>
      match Int.is_power2 n with
      | Some bit => do r1 <- ireg_of a1; OK (Ptbnz W r1 bit lbl :: k)
      | None => transl_cond_branch_default c args lbl k
      end
  | a1 :: nil, Cmasklzero n =>
      match Int64.is_power2' n with
      | Some bit => do r1 <- ireg_of a1; OK (Ptbz X r1 bit lbl :: k)
      | None => transl_cond_branch_default c args lbl k
      end
  | a1 :: nil, Cmasklnotzero n =>
      match Int64.is_power2' n with
      | Some bit => do r1 <- ireg_of a1; OK (Ptbnz X r1 bit lbl :: k)
      | None => transl_cond_branch_default c args lbl k
      end
  | _, _ =>
      transl_cond_branch_default c args lbl k
  end.
  
(** Translation of the arithmetic operation [res <- op(args)].
    The corresponding instructions are prepended to [k]. *)

Definition transl_op
              (op: operation) (args: list mreg) (res: mreg) (k: code) :=
  match op, args with
  | Omove, a1 :: nil =>
      match preg_of res, preg_of a1 with
      | IR r, IR a => OK (Pmov r a :: k)
      | FR r, FR a => OK (Pfmov r a :: k)
      |  _  ,  _   => Error(msg "Asmgen.Omove")
      end
  | Ointconst n, nil =>
      do rd <- ireg_of res;
      OK (loadimm32 rd n k)
  | Olongconst n, nil =>
      do rd <- ireg_of res;
      OK (loadimm64 rd n k)
  | Ofloatconst f, nil =>
      do rd <- freg_of res;
      OK (if Float.eq_dec f Float.zero
          then Pfmovi D rd XZR :: k
          else Pfmovimmd rd f :: k)
  | Osingleconst f, nil =>
      do rd <- freg_of res;
      OK (if Float32.eq_dec f Float32.zero
          then Pfmovi S rd XZR :: k
          else Pfmovimms rd f :: k)
  | Oaddrsymbol id ofs, nil =>
      do rd <- ireg_of res;
      OK (loadsymbol rd id ofs k)
  | Oaddrstack ofs, nil =>
      do rd <- ireg_of res;
      OK (addimm64 rd XSP (Ptrofs.to_int64 ofs) k)
(** 32-bit integer arithmetic *)
  | Oshift s a, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Porr W rd XZR r1 (transl_shift s a) :: k)
  | Oadd, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Padd W rd r1 r2 SOnone :: k)
  | Oaddshift s a, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Padd W rd r1 r2 (transl_shift s a) :: k)
  | Oaddimm n, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (addimm32 rd r1 n k)
  | Oneg, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Psub W rd XZR r1 SOnone :: k)
  | Onegshift s a, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Psub W rd XZR r1 (transl_shift s a) :: k)
  | Osub, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Psub W rd r1 r2 SOnone :: k)
  | Osubshift s a, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Psub W rd r1 r2 (transl_shift s a) :: k)
  | Omul, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pmadd W rd r1 r2 XZR :: k)
  | Omuladd, a1 :: a2 :: a3 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2; do r3 <- ireg_of a3;
      OK (Pmadd W rd r2 r3 r1 :: k)
  | Omulsub, a1 :: a2 :: a3 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2; do r3 <- ireg_of a3;
      OK (Pmsub W rd r2 r3 r1 :: k)
  | Odiv, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Psdiv W rd r1 r2 :: k)
  | Odivu, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pudiv W rd r1 r2 :: k)
  | Oand, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pand W rd r1 r2 SOnone :: k)
  | Oandshift s a, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pand W rd r1 r2 (transl_shift s a) :: k)
  | Oandimm n, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (logicalimm32 (Pandimm W) (Pand W) rd r1 n k)      
  | Oor, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Porr W rd r1 r2 SOnone :: k)
  | Oorshift s a, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Porr W rd r1 r2 (transl_shift s a) :: k)
  | Oorimm n, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (logicalimm32 (Porrimm W) (Porr W) rd r1 n k)      
  | Oxor, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Peor W rd r1 r2 SOnone :: k)
  | Oxorshift s a, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Peor W rd r1 r2 (transl_shift s a) :: k)
  | Oxorimm n, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (logicalimm32 (Peorimm W) (Peor W) rd r1 n k)      
  | Onot, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Porn W rd XZR r1 SOnone :: k)
  | Onotshift s a, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Porn W rd XZR r1 (transl_shift s a) :: k)
  | Obic, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pbic W rd r1 r2 SOnone :: k)
  | Obicshift s a, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pbic W rd r1 r2 (transl_shift s a) :: k)
  | Oorn, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Porn W rd r1 r2 SOnone :: k)
  | Oornshift s a, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Porn W rd r1 r2 (transl_shift s a) :: k)
  | Oeqv, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Peon W rd r1 r2 SOnone :: k)
  | Oeqvshift s a, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Peon W rd r1 r2 (transl_shift s a) :: k)
  | Oshl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Plslv W rd r1 r2 :: k)
  | Oshr, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pasrv W rd r1 r2 :: k)
  | Oshru, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Plsrv W rd r1 r2 :: k)
  | Oshrximm n, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (shrx32 rd r1 n k)
  | Ozext s, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Pubfiz W rd r1 Int.zero s :: k)
  | Osext s, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Psbfiz W rd r1 Int.zero s :: k)
  | Oshlzext s a, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Pubfiz W rd r1 a (Z.min s (Int.zwordsize - Int.unsigned a)) :: k)
  | Oshlsext s a, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Psbfiz W rd r1 a (Z.min s (Int.zwordsize - Int.unsigned a)) :: k)
  | Ozextshr a s, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Pubfx W rd r1 a (Z.min s (Int.zwordsize - Int.unsigned a)) :: k)
  | Osextshr a s, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Psbfx W rd r1 a (Z.min s (Int.zwordsize - Int.unsigned a)) :: k)
(** 64-bit integer arithmetic *)
  | Oshiftl s a, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Porr X rd XZR r1 (transl_shift s a) :: k)
  | Oextend x a, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (move_extended rd r1 x a k)
  (* [Omakelong] and [Ohighlong] should not occur *)
  | Olowlong, a1 :: nil => 
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      assertion (ireg_eq rd r1);
      OK (Pcvtx2w rd :: k)
  | Oaddl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Padd X rd r1 r2 SOnone :: k)
  | Oaddlshift s a, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Padd X rd r1 r2 (transl_shift s a) :: k)
  | Oaddlext x a, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (arith_extended Paddext (Padd X) rd r1 r2 x a k)
  | Oaddlimm n, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (addimm64 rd r1 n k)
  | Onegl, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Psub X rd XZR r1 SOnone :: k)
  | Oneglshift s a, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Psub X rd XZR r1 (transl_shift s a) :: k)
  | Osubl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Psub X rd r1 r2 SOnone :: k)
  | Osublshift s a, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Psub X rd r1 r2 (transl_shift s a) :: k)
  | Osublext x a, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (arith_extended Psubext (Psub X) rd r1 r2 x a k)
  | Omull, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pmadd X rd r1 r2 XZR :: k)
  | Omulladd, a1 :: a2 :: a3 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2; do r3 <- ireg_of a3;
      OK (Pmadd X rd r2 r3 r1 :: k)
  | Omullsub, a1 :: a2 :: a3 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2; do r3 <- ireg_of a3;
      OK (Pmsub X rd r2 r3 r1 :: k)
  | Omullhs, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Psmulh rd r1 r2 :: k)
  | Omullhu, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pumulh rd r1 r2 :: k)
  | Odivl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Psdiv X rd r1 r2 :: k)
  | Odivlu, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pudiv X rd r1 r2 :: k)
  | Oandl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pand X rd r1 r2 SOnone :: k)
  | Oandlshift s a, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pand X rd r1 r2 (transl_shift s a) :: k)
  | Oandlimm n, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (logicalimm64 (Pandimm X) (Pand X) rd r1 n k)      
  | Oorl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Porr X rd r1 r2 SOnone :: k)
  | Oorlshift s a, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Porr X rd r1 r2 (transl_shift s a) :: k)
  | Oorlimm n, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (logicalimm64 (Porrimm X) (Porr X) rd r1 n k)      
  | Oxorl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Peor X rd r1 r2 SOnone :: k)
  | Oxorlshift s a, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Peor X rd r1 r2 (transl_shift s a) :: k)
  | Oxorlimm n, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (logicalimm64 (Peorimm X) (Peor X) rd r1 n k)      
  | Onotl, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Porn X rd XZR r1 SOnone :: k)
  | Onotlshift s a, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Porn X rd XZR r1 (transl_shift s a) :: k)
  | Obicl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pbic X rd r1 r2 SOnone :: k)
  | Obiclshift s a, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pbic X rd r1 r2 (transl_shift s a) :: k)
  | Oornl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Porn X rd r1 r2 SOnone :: k)
  | Oornlshift s a, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Porn X rd r1 r2 (transl_shift s a) :: k)
  | Oeqvl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Peon X rd r1 r2 SOnone :: k)
  | Oeqvlshift s a, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Peon X rd r1 r2 (transl_shift s a) :: k)
  | Oshll, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Plslv X rd r1 r2 :: k)
  | Oshrl, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Pasrv X rd r1 r2 :: k)
  | Oshrlu, a1 :: a2 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (Plsrv X rd r1 r2 :: k)
  | Oshrlximm n, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (shrx64 rd r1 n k)
  | Ozextl s, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Pubfiz X rd r1 Int.zero s :: k)
  | Osextl s, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Psbfiz X rd r1 Int.zero s :: k)
  | Oshllzext s a, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Pubfiz X rd r1 a (Z.min s (Int64.zwordsize - Int.unsigned a)) :: k)
  | Oshllsext s a, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Psbfiz X rd r1 a (Z.min s (Int64.zwordsize - Int.unsigned a)) :: k)
  | Ozextshrl a s, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Pubfx X rd r1 a (Z.min s (Int64.zwordsize - Int.unsigned a)) :: k)
  | Osextshrl a s, a1 :: nil =>
      do rd <- ireg_of res; do r1 <- ireg_of a1;
      OK (Psbfx X rd r1 a (Z.min s (Int64.zwordsize - Int.unsigned a)) :: k)
(** 64-bit floating-point arithmetic *)
  | Onegf, a1 :: nil =>
      do rd <- freg_of res; do rs <- freg_of a1;
      OK (Pfneg D rd rs :: k)
  | Oabsf, a1 :: nil =>
      do rd <- freg_of res; do rs <- freg_of a1;
      OK (Pfabs D rd rs :: k)
  | Oaddf, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Pfadd D rd rs1 rs2 :: k)
  | Osubf, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Pfsub D rd rs1 rs2 :: k)
  | Omulf, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Pfmul D rd rs1 rs2 :: k)
  | Odivf, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Pfdiv D rd rs1 rs2 :: k)
(** 32-bit floating-point arithmetic *)
  | Onegfs, a1 :: nil =>
      do rd <- freg_of res; do rs <- freg_of a1;
      OK (Pfneg S rd rs :: k)
  | Oabsfs, a1 :: nil =>
      do rd <- freg_of res; do rs <- freg_of a1;
      OK (Pfabs S rd rs :: k)
  | Oaddfs, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Pfadd S rd rs1 rs2 :: k)
  | Osubfs, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Pfsub S rd rs1 rs2 :: k)
  | Omulfs, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Pfmul S rd rs1 rs2 :: k)
  | Odivfs, a1 :: a2 :: nil =>
      do rd <- freg_of res; do rs1 <- freg_of a1; do rs2 <- freg_of a2;
      OK (Pfdiv S rd rs1 rs2 :: k)
  | Osingleoffloat, a1 :: nil =>
      do rd <- freg_of res; do rs <- freg_of a1;
      OK (Pfcvtsd rd rs :: k)
  | Ofloatofsingle, a1 :: nil =>
      do rd <- freg_of res; do rs <- freg_of a1;
      OK (Pfcvtds rd rs :: k)
(** Conversions between int and float *)
  | Ointoffloat, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Pfcvtzs W D rd rs :: k)
  | Ointuoffloat, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Pfcvtzu W D rd rs :: k)
  | Ofloatofint, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Pscvtf D W rd rs :: k)
  | Ofloatofintu, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Pucvtf D W rd rs :: k)
  | Ointofsingle, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Pfcvtzs W S rd rs :: k)
  | Ointuofsingle, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Pfcvtzu W S rd rs :: k)
  | Osingleofint, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Pscvtf S W rd rs :: k)
  | Osingleofintu, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Pucvtf S W rd rs :: k)
  | Olongoffloat, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Pfcvtzs X D rd rs :: k)
  | Olonguoffloat, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Pfcvtzu X D rd rs :: k)
  | Ofloatoflong, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Pscvtf D X rd rs :: k)
  | Ofloatoflongu, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Pucvtf D X rd rs :: k)
  | Olongofsingle, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Pfcvtzs X S rd rs :: k)
  | Olonguofsingle, a1 :: nil =>
      do rd <- ireg_of res; do rs <- freg_of a1;
      OK (Pfcvtzu X S rd rs :: k)
  | Osingleoflong, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Pscvtf S X rd rs :: k)
  | Osingleoflongu, a1 :: nil =>
      do rd <- freg_of res; do rs <- ireg_of a1;
      OK (Pucvtf S X rd rs :: k)
(** Boolean tests *)
  | Ocmp c, _ =>
      do rd <- ireg_of res;
      transl_cond c args (Pcset rd (cond_for_cond c) :: k)
(** Conditional move *)
  | Osel cmp ty, a1 :: a2 :: args =>
      match preg_of res with
      | IR r => 
          do r1 <- ireg_of a1; do r2 <- ireg_of a2;
          transl_cond cmp args (Pcsel r r1 r2 (cond_for_cond cmp) :: k)
      | FR r =>
          do r1 <- freg_of a1; do r2 <- freg_of a2;
          transl_cond cmp args (Pfsel r r1 r2 (cond_for_cond cmp) :: k)
      | _ =>
          Error(msg "Asmgen.Osel")
      end
  | _, _ =>
      Error(msg "Asmgen.transl_op")
  end.

(** Translation of addressing modes *)

Definition offset_representable (sz: Z) (ofs: int64) : bool :=
  let isz := Int64.repr sz in
  (** either unscaled 9-bit signed *)
  Int64.eq ofs (Int64.sign_ext 9 ofs) ||
  (** or scaled 12-bit unsigned *)
  (Int64.eq (Int64.modu ofs isz) Int64.zero
   && Int64.ltu ofs (Int64.shl isz (Int64.repr 12))).
 
Definition transl_addressing (sz: Z) (addr: Op.addressing) (args: list mreg)
                             (insn: Asm.addressing -> instruction) (k: code) : res code :=
  match addr, args with
  | Aindexed ofs, a1 :: nil =>
      do r1 <- ireg_of a1;
       if offset_representable sz ofs then
        OK (insn (ADimm r1 ofs) :: k)
      else
        OK (loadimm64 X16 ofs (insn (ADreg r1 X16) :: k))
  | Aindexed2, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK (insn (ADreg r1 r2) :: k)
  | Aindexed2shift a, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      if Int.eq a Int.zero then
        OK (insn (ADreg r1 r2) :: k)
      else if Int.eq (Int.shl Int.one a) (Int.repr sz) then
        OK (insn (ADlsl r1 r2 a) :: k)
      else
        OK (Padd X X16 r1 r2 (SOlsl a) :: insn (ADimm X16 Int64.zero) :: k)
  | Aindexed2ext x a, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      if Int.eq a Int.zero || Int.eq (Int.shl Int.one a) (Int.repr sz) then
        OK (insn (match x with Xsgn32 => ADsxt r1 r2 a
                             | Xuns32 => ADuxt r1 r2 a end) :: k)
      else
        OK (arith_extended Paddext (Padd X) X16 r1 r2 x a
                           (insn (ADimm X16 Int64.zero) :: k))
  | Aglobal id ofs, nil =>
      assertion (negb (Archi.pic_code tt));
      if Ptrofs.eq (Ptrofs.modu ofs (Ptrofs.repr sz)) Ptrofs.zero && symbol_is_aligned id sz
      then OK (Padrp X16 id ofs :: insn (ADadr X16 id ofs) :: k)
      else OK (loadsymbol X16 id ofs (insn (ADimm X16 Int64.zero) :: k))
  | Ainstack ofs, nil =>
      let ofs := Ptrofs.to_int64 ofs in
      if offset_representable sz ofs then
        OK (insn (ADimm XSP ofs) :: k)
      else
        OK (loadimm64 X16 ofs (insn (ADreg XSP X16) :: k))
  | _, _ =>
      Error(msg "Asmgen.transl_addressing")
  end.

(** Translation of loads and stores *)

Definition transl_load (chunk: memory_chunk) (addr: Op.addressing)
                       (args: list mreg) (dst: mreg) (k: code) : res code :=
  match chunk with
  | Mint8unsigned =>
      do rd <- ireg_of dst; transl_addressing 1 addr args (Pldrb W rd) k
  | Mint8signed =>
      do rd <- ireg_of dst; transl_addressing 1 addr args (Pldrsb W rd) k
  | Mint16unsigned =>
      do rd <- ireg_of dst; transl_addressing 2 addr args (Pldrh W rd) k
  | Mint16signed =>
      do rd <- ireg_of dst; transl_addressing 2 addr args (Pldrsh W rd) k
  | Mint32 =>
      do rd <- ireg_of dst; transl_addressing 4 addr args (Pldrw rd) k
  | Mint64 =>
      do rd <- ireg_of dst; transl_addressing 8 addr args (Pldrx rd) k
  | Mfloat32 =>
      do rd <- freg_of dst; transl_addressing 4 addr args (Pldrs rd) k
  | Mfloat64 =>
      do rd <- freg_of dst; transl_addressing 8 addr args (Pldrd rd) k
  | Many32 =>
      do rd <- ireg_of dst; transl_addressing 4 addr args (Pldrw_a rd) k
  | Many64 =>
      do rd <- ireg_of dst; transl_addressing 8 addr args (Pldrx_a rd) k
  end.

Definition transl_store (chunk: memory_chunk) (addr: Op.addressing)
                        (args: list mreg) (src: mreg) (k: code) : res code :=
  match chunk with
  | Mint8unsigned | Mint8signed =>
      do r1 <- ireg_of src; transl_addressing 1 addr args (Pstrb r1) k
  | Mint16unsigned | Mint16signed =>
      do r1 <- ireg_of src; transl_addressing 2 addr args (Pstrh r1) k
  | Mint32 =>
      do r1 <- ireg_of src; transl_addressing 4 addr args (Pstrw r1) k
  | Mint64 =>
      do r1 <- ireg_of src; transl_addressing 8 addr args (Pstrx r1) k
  | Mfloat32 =>
      do r1 <- freg_of src; transl_addressing 4 addr args (Pstrs r1) k
  | Mfloat64 =>
      do r1 <- freg_of src; transl_addressing 8 addr args (Pstrd r1) k
  | Many32 =>
      do r1 <- ireg_of src; transl_addressing 4 addr args (Pstrw_a r1) k
  | Many64 =>
      do r1 <- ireg_of src; transl_addressing 8 addr args (Pstrx_a r1) k
  end.

(** Register-indexed loads and stores *)

Definition indexed_memory_access (insn: Asm.addressing -> instruction)
                                 (sz: Z) (base: iregsp) (ofs: ptrofs) (k: code) :=
  let ofs := Ptrofs.to_int64 ofs in
  if offset_representable sz ofs
  then insn (ADimm base ofs) :: k
  else loadimm64 X16 ofs (insn (ADreg base X16) :: k).

Definition loadind (base: iregsp) (ofs: ptrofs) (ty: typ) (dst: mreg) (k: code) :=
  match ty, preg_of dst with
  | Tint,    IR rd => OK (indexed_memory_access (Pldrw rd) 4 base ofs k)
  | Tlong,   IR rd => OK (indexed_memory_access (Pldrx rd) 8 base ofs k)
  | Tsingle, FR rd => OK (indexed_memory_access (Pldrs rd) 4 base ofs k)
  | Tfloat,  FR rd => OK (indexed_memory_access (Pldrd rd) 8 base ofs k)
  | Tany32,  IR rd => OK (indexed_memory_access (Pldrw_a rd) 4 base ofs k)
  | Tany64,  IR rd => OK (indexed_memory_access (Pldrx_a rd) 8 base ofs k)
  | Tany64,  FR rd => OK (indexed_memory_access (Pldrd_a rd) 8 base ofs k)
  | _, _           => Error (msg "Asmgen.loadind")
  end.

Definition storeind (src: mreg) (base: iregsp) (ofs: ptrofs) (ty: typ) (k: code) :=
  match ty, preg_of src with
  | Tint,    IR rd => OK (indexed_memory_access (Pstrw rd) 4 base ofs k)
  | Tlong,   IR rd => OK (indexed_memory_access (Pstrx rd) 8 base ofs k)
  | Tsingle, FR rd => OK (indexed_memory_access (Pstrs rd) 4 base ofs k)
  | Tfloat,  FR rd => OK (indexed_memory_access (Pstrd rd) 8 base ofs k)
  | Tany32,  IR rd => OK (indexed_memory_access (Pstrw_a rd) 4 base ofs k)
  | Tany64,  IR rd => OK (indexed_memory_access (Pstrx_a rd) 8 base ofs k)
  | Tany64,  FR rd => OK (indexed_memory_access (Pstrd_a rd) 8 base ofs k)
  | _, _           => Error (msg "Asmgen.storeind")
  end.

Definition loadptr (base: iregsp) (ofs: ptrofs) (dst: ireg) (k: code) :=
  indexed_memory_access (Pldrx dst) 8 base ofs k.

Definition storeptr (src: ireg) (base: iregsp) (ofs: ptrofs) (k: code) :=
  indexed_memory_access (Pstrx src) 8 base ofs k.

(** Function epilogue *)

Definition make_epilogue (f: Mach.function) (k: code) :=
  loadptr XSP f.(fn_retaddr_ofs) RA
    (Pfreeframe f.(fn_stacksize) f.(fn_link_ofs) :: k).
  
(** Translation of a Mach instruction. *)

Definition transl_instr (f: Mach.function) (i: Mach.instruction)
                        (r29_is_parent: bool) (k: code) : res code :=
  match i with
  | Mgetstack ofs ty dst =>
      loadind XSP ofs ty dst k
  | Msetstack src ofs ty =>
      storeind src XSP ofs ty k
  | Mgetparam ofs ty dst =>
      (* load via the frame pointer if it is valid *)
      do c <- loadind X29 ofs ty dst k;
      OK (if r29_is_parent then c else loadptr XSP f.(fn_link_ofs) X29 c)
  | Mop op args res =>
      transl_op op args res k
  | Mload chunk addr args dst =>
      transl_load chunk addr args dst k
  | Mstore chunk addr args src =>
      transl_store chunk addr args src k
  | Mcall sig (inl r) =>
      do r1 <- ireg_of r; OK (Pblr r1 sig :: k)
  | Mcall sig (inr symb) =>
      OK (Pbl symb sig :: k)
  | Mtailcall sig (inl r) =>
      do r1 <- ireg_of r;
      OK (make_epilogue f (Pbr r1 sig :: k))
  | Mtailcall sig (inr symb) =>
      OK (make_epilogue f (Pbs symb sig :: k))
  | Mbuiltin ef args res =>
      OK (Pbuiltin ef (List.map (map_builtin_arg preg_of) args) (map_builtin_res preg_of res) :: k)
  | Mlabel lbl =>
      OK (Plabel lbl :: k)
  | Mgoto lbl =>
      OK (Pb lbl :: k)
  | Mcond cond args lbl =>
      transl_cond_branch cond args lbl k
  | Mjumptable arg tbl =>
      do r <- ireg_of arg;
      OK (Pbtbl r tbl :: k)
  | Mreturn =>
      OK (make_epilogue f (Pret RA :: k))
  end.

(** Translation of a code sequence *)

Definition it1_is_parent (before: bool) (i: Mach.instruction) : bool :=
  match i with
  | Msetstack src ofs ty => before
  | Mgetparam ofs ty dst => negb (mreg_eq dst R29)
  | Mop op args res => before && negb (mreg_eq res R29)
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
  do c <- transl_code' f f.(Mach.fn_code) true;
  OK (mkfunction f.(Mach.fn_sig)
        (Pallocframe f.(fn_stacksize) f.(fn_link_ofs) ::
         storeptr RA XSP f.(fn_retaddr_ofs) c)).

Definition transf_function (f: Mach.function) : res Asm.function :=
  do tf <- transl_function f;
  if zlt Ptrofs.max_unsigned (list_length_z tf.(fn_code))
  then Error (msg "code size exceeded")
  else OK tf.

Definition transf_fundef (f: Mach.fundef) : res Asm.fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: Mach.program) : res Asm.program :=
  transform_partial_program transf_fundef p.
