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

(** Translation from Mach to PPC. *)

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

(** Decomposition of integer constants.  As noted in file [Asm],
  immediate arguments to PowerPC instructions must fit into 16 bits,
  and are interpreted after zero extension, sign extension, or
  left shift by 16 bits, depending on the instruction.  Integer
  constants that do not fit must be synthesized using two
  processor instructions.  The following functions decompose
  arbitrary 32-bit integers into two 16-bit halves (high and low
  halves).  They satisfy the following properties:
- [low_u n] is an unsigned 16-bit integer;
- [low_s n] is a signed 16-bit integer;
- [(high_u n) << 16 | low_u n] equals [n];
- [(high_s n) << 16 + low_s n] equals [n].
*)

Definition low_u (n: int) := Int.and n (Int.repr 65535).
Definition high_u (n: int) := Int.shru n (Int.repr 16).
Definition low_s (n: int) := Int.sign_ext 16 n.
Definition high_s (n: int) := Int.shru (Int.sub n (low_s n)) (Int.repr 16).

(** Smart constructors for arithmetic operations involving
  a 32-bit integer constant.  Depending on whether the
  constant fits in 16 bits or not, one or several instructions
  are generated as required to perform the operation
  and prepended to the given instruction sequence [k]. *)

Definition loadimm (r: ireg) (n: int) (k: code) :=
  if Int.eq (high_s n) Int.zero then
    Paddi r GPR0 (Cint n) :: k
  else if Int.eq (low_s n) Int.zero then
    Paddis r GPR0 (Cint (high_s n)) :: k
  else
    Paddis r GPR0 (Cint (high_u n)) ::
    Pori r r (Cint (low_u n)) :: k.

Definition addimm (r1 r2: ireg) (n: int) (k: code) :=
  if Int.eq (high_s n) Int.zero then
    Paddi r1 r2 (Cint n) :: k
  else if Int.eq (low_s n) Int.zero then
    Paddis r1 r2 (Cint (high_s n)) :: k
  else
    Paddis r1 r2 (Cint (high_s n)) ::
    Paddi r1 r1 (Cint (low_s n)) :: k.

Definition andimm (r1 r2: ireg) (n: int) (k: code) :=
  if Int.eq (high_u n) Int.zero then
    Pandi_ r1 r2 (Cint n) :: k
  else if Int.eq (low_u n) Int.zero then
    Pandis_ r1 r2 (Cint (high_u n)) :: k
  else
    loadimm GPR0 n (Pand_ r1 r2 GPR0 :: k).

Definition orimm (r1 r2: ireg) (n: int) (k: code) :=
  if Int.eq (high_u n) Int.zero then
    Pori r1 r2 (Cint n) :: k
  else if Int.eq (low_u n) Int.zero then
    Poris r1 r2 (Cint (high_u n)) :: k
  else
    Poris r1 r2 (Cint (high_u n)) ::
    Pori r1 r1 (Cint (low_u n)) :: k.

Definition xorimm (r1 r2: ireg) (n: int) (k: code) :=
  if Int.eq (high_u n) Int.zero then
    Pxori r1 r2 (Cint n) :: k
  else if Int.eq (low_u n) Int.zero then
    Pxoris r1 r2 (Cint (high_u n)) :: k
  else
    Pxoris r1 r2 (Cint (high_u n)) ::
    Pxori r1 r1 (Cint (low_u n)) :: k.

(** Accessing slots in the stack frame.  *)

Definition loadind (base: ireg) (ofs: int) (ty: typ) (dst: mreg) (k: code) :=
  if Int.eq (high_s ofs) Int.zero then
    match ty with
    | Tint => Plwz (ireg_of dst) (Cint ofs) base :: k
    | Tfloat => Plfd (freg_of dst) (Cint ofs) base :: k
    end
  else
    loadimm GPR0 ofs
      (match ty with
       | Tint => Plwzx (ireg_of dst) base GPR0 :: k
       | Tfloat => Plfdx (freg_of dst) base GPR0 :: k
       end).

Definition storeind (src: mreg) (base: ireg) (ofs: int) (ty: typ) (k: code) :=
  if Int.eq (high_s ofs) Int.zero then
    match ty with
    | Tint => Pstw (ireg_of src) (Cint ofs) base :: k
    | Tfloat => Pstfd (freg_of src) (Cint ofs) base :: k
    end
  else
    loadimm GPR0 ofs
      (match ty with
       | Tint => Pstwx (ireg_of src) base GPR0 :: k
       | Tfloat => Pstfdx (freg_of src) base GPR0 :: k
       end).

(** Constructor for a floating-point comparison.  The PowerPC has
  a single [fcmpu] instruction to compare floats, which sets
  bits 0, 1 and 2 of the condition register to reflect ``less'',
  ``greater'' and ``equal'' conditions, respectively.
  The ``less or equal'' and ``greater or equal'' conditions must be
  synthesized by a [cror] instruction that computes the logical ``or''
  of the corresponding two conditions. *)

Definition floatcomp (cmp: comparison) (r1 r2: freg) (k: code) :=
  Pfcmpu r1 r2 ::
  match cmp with
  | Cle => Pcror CRbit_3 CRbit_2 CRbit_0 :: k
  | Cge => Pcror CRbit_3 CRbit_2 CRbit_1 :: k
  | _ => k
  end.

(** Translation of a condition.  Prepends to [k] the instructions
  that evaluate the condition and leave its boolean result in one of
  the bits of the condition register.  The bit in question is
  determined by the [crbit_for_cond] function. *)

Definition transl_cond
              (cond: condition) (args: list mreg) (k: code) :=
  match cond, args with
  | Ccomp c, a1 :: a2 :: nil =>
      Pcmpw (ireg_of a1) (ireg_of a2) :: k
  | Ccompu c, a1 :: a2 :: nil =>
      Pcmplw (ireg_of a1) (ireg_of a2) :: k
  | Ccompimm c n, a1 :: nil =>
      if Int.eq (high_s n) Int.zero then
        Pcmpwi (ireg_of a1) (Cint n) :: k
      else
        loadimm GPR0 n (Pcmpw (ireg_of a1) GPR0 :: k)
  | Ccompuimm c n, a1 :: nil =>
      if Int.eq (high_u n) Int.zero then
        Pcmplwi (ireg_of a1) (Cint n) :: k
      else
        loadimm GPR0 n (Pcmplw (ireg_of a1) GPR0 :: k)
  | Ccompf cmp, a1 :: a2 :: nil =>
      floatcomp cmp (freg_of a1) (freg_of a2) k
  | Cnotcompf cmp, a1 :: a2 :: nil =>
      floatcomp cmp (freg_of a1) (freg_of a2) k
  | Cmaskzero n, a1 :: nil =>
      andimm GPR0 (ireg_of a1) n k
  | Cmasknotzero n, a1 :: nil =>
      andimm GPR0 (ireg_of a1) n k
  | _, _ =>
     k (**r never happens for well-typed code *)
  end.

(*  CRbit_0 = Less
    CRbit_1 = Greater
    CRbit_2 = Equal
    CRbit_3 = Other *)

Definition crbit_for_icmp (cmp: comparison) :=
  match cmp with
  | Ceq => (CRbit_2, true)
  | Cne => (CRbit_2, false)
  | Clt => (CRbit_0, true)
  | Cle => (CRbit_1, false)
  | Cgt => (CRbit_1, true)
  | Cge => (CRbit_0, false)
  end.

Definition crbit_for_fcmp (cmp: comparison) :=
  match cmp with
  | Ceq => (CRbit_2, true)
  | Cne => (CRbit_2, false)
  | Clt => (CRbit_0, true)
  | Cle => (CRbit_3, true)
  | Cgt => (CRbit_1, true)
  | Cge => (CRbit_3, true)
  end.

Definition crbit_for_cond (cond: condition) :=
  match cond with
  | Ccomp cmp => crbit_for_icmp cmp
  | Ccompu cmp => crbit_for_icmp cmp
  | Ccompimm cmp n => crbit_for_icmp cmp
  | Ccompuimm cmp n => crbit_for_icmp cmp
  | Ccompf cmp => crbit_for_fcmp cmp
  | Cnotcompf cmp => let p := crbit_for_fcmp cmp in (fst p, negb (snd p))
  | Cmaskzero n => (CRbit_2, true)
  | Cmasknotzero n => (CRbit_2, false)
  end.

(** Recognition of comparisons [>= 0] and [< 0]. *)

Inductive condition_class: condition -> list mreg -> Type :=
  | condition_ge0:
      forall n r, n = Int.zero -> condition_class (Ccompimm Cge n) (r :: nil)
  | condition_lt0:
      forall n r, n = Int.zero -> condition_class (Ccompimm Clt n) (r :: nil)
  | condition_default:
      forall c rl, condition_class c rl.

Definition classify_condition (c: condition) (args: list mreg): condition_class c args :=
  match c as z1, args as z2 return condition_class z1 z2 with
  | Ccompimm Cge n, r :: nil =>
      match Int.eq_dec n Int.zero with
      | left EQ => condition_ge0 n r EQ
      | right _ => condition_default (Ccompimm Cge n) (r :: nil)
      end
  | Ccompimm Clt n, r :: nil =>
      match Int.eq_dec n Int.zero with
      | left EQ => condition_lt0 n r EQ
      | right _ => condition_default (Ccompimm Clt n) (r :: nil)
      end
  | x, y =>
      condition_default x y
  end.

(** Translation of the arithmetic operation [r <- op(args)].
  The corresponding instructions are prepended to [k]. *)

Definition transl_op
              (op: operation) (args: list mreg) (r: mreg) (k: code) :=
  match op, args with
  | Omove, a1 :: nil =>
      match mreg_type a1 with
      | Tint => Pmr (ireg_of r) (ireg_of a1) :: k
      | Tfloat => Pfmr (freg_of r) (freg_of a1) :: k
      end
  | Ointconst n, nil =>
      loadimm (ireg_of r) n k
  | Ofloatconst f, nil =>
      Plfi (freg_of r) f :: k
  | Oaddrsymbol s ofs, nil =>
      Paddis GPR12 GPR0 (Csymbol_high s ofs) ::
      Paddi (ireg_of r) GPR12 (Csymbol_low s ofs) :: k
  | Oaddrstack n, nil =>
      addimm (ireg_of r) GPR1 n k
  | Ocast8signed, a1 :: nil =>
      Pextsb (ireg_of r) (ireg_of a1) :: k
  | Ocast8unsigned, a1 :: nil =>
      Prlwinm (ireg_of r) (ireg_of a1) Int.zero (Int.repr 255) :: k
  | Ocast16signed, a1 :: nil =>
      Pextsh (ireg_of r) (ireg_of a1) :: k
  | Ocast16unsigned, a1 :: nil =>
      Prlwinm (ireg_of r) (ireg_of a1) Int.zero (Int.repr 65535) :: k
  | Oadd, a1 :: a2 :: nil =>
      Padd (ireg_of r) (ireg_of a1) (ireg_of a2) :: k
  | Oaddimm n, a1 :: nil =>
      addimm (ireg_of r) (ireg_of a1) n k
  | Osub, a1 :: a2 :: nil =>
      Psubfc (ireg_of r) (ireg_of a2) (ireg_of a1) :: k
  | Osubimm n, a1 :: nil =>
      if Int.eq (high_s n) Int.zero then
        Psubfic (ireg_of r) (ireg_of a1) (Cint n) :: k
      else
        loadimm GPR0 n (Psubfc (ireg_of r) (ireg_of a1) GPR0 :: k)
  | Omul, a1 :: a2 :: nil =>
      Pmullw (ireg_of r) (ireg_of a1) (ireg_of a2) :: k
  | Omulimm n, a1 :: nil =>
      if Int.eq (high_s n) Int.zero then
        Pmulli (ireg_of r) (ireg_of a1) (Cint n) :: k
      else
        loadimm GPR0 n (Pmullw (ireg_of r) (ireg_of a1) GPR0 :: k)
  | Odiv, a1 :: a2 :: nil =>
      Pdivw (ireg_of r) (ireg_of a1) (ireg_of a2) :: k
  | Odivu, a1 :: a2 :: nil =>
      Pdivwu (ireg_of r) (ireg_of a1) (ireg_of a2) :: k
  | Oand, a1 :: a2 :: nil =>
      Pand_ (ireg_of r) (ireg_of a1) (ireg_of a2) :: k
  | Oandimm n, a1 :: nil =>
      andimm (ireg_of r) (ireg_of a1) n k
  | Oor, a1 :: a2 :: nil =>
      Por (ireg_of r) (ireg_of a1) (ireg_of a2) :: k
  | Oorimm n, a1 :: nil =>
      orimm (ireg_of r) (ireg_of a1) n k
  | Oxor, a1 :: a2 :: nil =>
      Pxor (ireg_of r) (ireg_of a1) (ireg_of a2) :: k
  | Oxorimm n, a1 :: nil =>
      xorimm (ireg_of r) (ireg_of a1) n k
  | Onand, a1 :: a2 :: nil =>
      Pnand (ireg_of r) (ireg_of a1) (ireg_of a2) :: k
  | Onor, a1 :: a2 :: nil =>
      Pnor (ireg_of r) (ireg_of a1) (ireg_of a2) :: k
  | Onxor, a1 :: a2 :: nil =>
      Peqv (ireg_of r) (ireg_of a1) (ireg_of a2) :: k
  | Oshl, a1 :: a2 :: nil =>
      Pslw (ireg_of r) (ireg_of a1) (ireg_of a2) :: k
  | Oshr, a1 :: a2 :: nil =>
      Psraw (ireg_of r) (ireg_of a1) (ireg_of a2) :: k
  | Oshrimm n, a1 :: nil =>
      Psrawi (ireg_of r) (ireg_of a1) n :: k
  | Oshrximm n, a1 :: nil =>
      Psrawi (ireg_of r) (ireg_of a1) n ::
      Paddze (ireg_of r) (ireg_of r) :: k
  | Oshru, a1 :: a2 :: nil =>
      Psrw (ireg_of r) (ireg_of a1) (ireg_of a2) :: k
  | Orolm amount mask, a1 :: nil =>
      Prlwinm (ireg_of r) (ireg_of a1) amount mask :: k
  | Onegf, a1 :: nil =>
      Pfneg (freg_of r) (freg_of a1) :: k
  | Oabsf, a1 :: nil =>
      Pfabs (freg_of r) (freg_of a1) :: k
  | Oaddf, a1 :: a2 :: nil =>
      Pfadd (freg_of r) (freg_of a1) (freg_of a2) :: k
  | Osubf, a1 :: a2 :: nil =>
      Pfsub (freg_of r) (freg_of a1) (freg_of a2) :: k
  | Omulf, a1 :: a2 :: nil =>
      Pfmul (freg_of r) (freg_of a1) (freg_of a2) :: k
  | Odivf, a1 :: a2 :: nil =>
      Pfdiv (freg_of r) (freg_of a1) (freg_of a2) :: k
  | Omuladdf, a1 :: a2 :: a3 :: nil =>
      Pfmadd (freg_of r) (freg_of a1) (freg_of a2) (freg_of a3) :: k
  | Omulsubf, a1 :: a2 :: a3 :: nil =>
      Pfmsub (freg_of r) (freg_of a1) (freg_of a2) (freg_of a3) :: k
  | Osingleoffloat, a1 :: nil =>
      Pfrsp (freg_of r) (freg_of a1) :: k
  | Ointoffloat, a1 :: nil =>
      Pfcti (ireg_of r) (freg_of a1) :: k
  | Ofloatofwords, a1 :: a2 :: nil =>
      Pfmake (freg_of r) (ireg_of a1) (ireg_of a2) :: k
  | Ocmp cmp, _ =>
      match classify_condition cmp args with
      | condition_ge0 _ a _ =>
          Prlwinm (ireg_of r) (ireg_of a) Int.one Int.one ::
          Pxori (ireg_of r) (ireg_of r) (Cint Int.one) :: k
      | condition_lt0 _ a _ =>
          Prlwinm (ireg_of r) (ireg_of a) Int.one Int.one :: k
      | condition_default _ _ =>
          let p := crbit_for_cond cmp in
          transl_cond cmp args
            (Pmfcrbit (ireg_of r) (fst p) ::
             if snd p
             then k
             else Pxori (ireg_of r) (ireg_of r) (Cint Int.one) :: k)
      end
  | _, _ =>
      k (**r never happens for well-typed code *)
  end.

(** Common code to translate [Mload] and [Mstore] instructions. *)

Definition int_temp_for (r: mreg) :=
  if mreg_eq r IT2 then GPR11 else GPR12.

Definition transl_load_store 
     (mk1: constant -> ireg -> instruction)
     (mk2: ireg -> ireg -> instruction)
     (addr: addressing) (args: list mreg) 
     (temp: ireg) (k: code) :=
  match addr, args with
  | Aindexed ofs, a1 :: nil =>
      if Int.eq (high_s ofs) Int.zero then
        mk1 (Cint ofs) (ireg_of a1) :: k
      else
        Paddis temp (ireg_of a1) (Cint (high_s ofs)) ::
        mk1 (Cint (low_s ofs)) temp :: k
  | Aindexed2, a1 :: a2 :: nil =>
      mk2 (ireg_of a1) (ireg_of a2) :: k
  | Aglobal symb ofs, nil =>
      if symbol_is_small_data symb ofs then
        mk1 (Csymbol_sda symb ofs) GPR0 :: k
      else
        Paddis temp GPR0 (Csymbol_high symb ofs) ::
        mk1 (Csymbol_low symb ofs) temp :: k
  | Abased symb ofs, a1 :: nil =>
      Paddis temp (ireg_of a1) (Csymbol_high symb ofs) ::
      mk1 (Csymbol_low symb ofs) temp :: k
  | Ainstack ofs, nil =>
      if Int.eq (high_s ofs) Int.zero then
        mk1 (Cint ofs) GPR1 :: k
      else
        Paddis temp GPR1 (Cint (high_s ofs)) ::
        mk1 (Cint (low_s ofs)) temp :: k
  | _, _ =>
      (* should not happen *) k
  end.

(** Translation of a Mach instruction. *)

Definition transl_instr (f: Mach.function) (i: Mach.instruction) (k: code) :=
  match i with
  | Mgetstack ofs ty dst =>
      loadind GPR1 ofs ty dst k
  | Msetstack src ofs ty =>
      storeind src GPR1 ofs ty k
  | Mgetparam ofs ty dst =>
      Plwz GPR11 (Cint f.(fn_link_ofs)) GPR1 :: loadind GPR11 ofs ty dst k
  | Mop op args res =>
      transl_op op args res k
  | Mload chunk addr args dst =>
      match chunk with
      | Mint8signed =>
          transl_load_store
            (Plbz (ireg_of dst)) (Plbzx (ireg_of dst)) addr args GPR12
            (Pextsb (ireg_of dst) (ireg_of dst) :: k)
      | Mint8unsigned =>
          transl_load_store
            (Plbz (ireg_of dst)) (Plbzx (ireg_of dst)) addr args GPR12 k
      | Mint16signed =>
          transl_load_store
            (Plha (ireg_of dst)) (Plhax (ireg_of dst)) addr args GPR12 k
      | Mint16unsigned =>
          transl_load_store
            (Plhz (ireg_of dst)) (Plhzx (ireg_of dst)) addr args GPR12 k
      | Mint32 =>
          transl_load_store
            (Plwz (ireg_of dst)) (Plwzx (ireg_of dst)) addr args GPR12 k
      | Mfloat32 =>
          transl_load_store
            (Plfs (freg_of dst)) (Plfsx (freg_of dst)) addr args GPR12 k
      | Mfloat64 =>
          transl_load_store
            (Plfd (freg_of dst)) (Plfdx (freg_of dst)) addr args GPR12 k
      end
  | Mstore chunk addr args src =>
      let temp := int_temp_for src in
      match chunk with
      | Mint8signed =>
          transl_load_store
            (Pstb (ireg_of src)) (Pstbx (ireg_of src)) addr args temp k
      | Mint8unsigned =>
          transl_load_store
            (Pstb (ireg_of src)) (Pstbx (ireg_of src)) addr args temp k
      | Mint16signed =>
          transl_load_store
            (Psth (ireg_of src)) (Psthx (ireg_of src)) addr args temp k
      | Mint16unsigned =>
          transl_load_store
            (Psth (ireg_of src)) (Psthx (ireg_of src)) addr args temp k
      | Mint32 =>
          transl_load_store
            (Pstw (ireg_of src)) (Pstwx (ireg_of src)) addr args temp k
      | Mfloat32 =>
          transl_load_store
            (Pstfs (freg_of src)) (Pstfsx (freg_of src)) addr args temp k
      | Mfloat64 =>
          transl_load_store
            (Pstfd (freg_of src)) (Pstfdx (freg_of src)) addr args temp k
      end
  | Mcall sig (inl r) =>
      Pmtctr (ireg_of r) :: Pbctrl :: k
  | Mcall sig (inr symb) =>
      Pbl symb :: k
  | Mtailcall sig (inl r) =>
      Pmtctr (ireg_of r) :: 
      Plwz GPR0 (Cint f.(fn_retaddr_ofs)) GPR1 ::
      Pmtlr GPR0 ::
      Pfreeframe (-f .(fn_framesize)) f.(fn_stacksize) f.(fn_link_ofs) :: 
      Pbctr :: k
  | Mtailcall sig (inr symb) =>
      Plwz GPR0 (Cint f.(fn_retaddr_ofs)) GPR1 ::
      Pmtlr GPR0 ::
      Pfreeframe (-f .(fn_framesize)) f.(fn_stacksize) f.(fn_link_ofs) :: 
      Pbs symb :: k
  | Mbuiltin ef args res =>
      Pbuiltin ef (map preg_of args) (preg_of res) :: k
  | Mlabel lbl =>
      Plabel lbl :: k
  | Mgoto lbl =>
      Pb lbl :: k
  | Mcond cond args lbl =>
      let p := crbit_for_cond cond in
      transl_cond cond args
        (if (snd p) then Pbt (fst p) lbl :: k else Pbf (fst p) lbl :: k)
  | Mjumptable arg tbl =>
      Prlwinm GPR12 (ireg_of arg) (Int.repr 2) (Int.repr (-4)) ::
      Pbtbl GPR12 tbl :: k
  | Mreturn =>
      Plwz GPR0 (Cint f.(fn_retaddr_ofs)) GPR1 ::
      Pmtlr GPR0 ::
      Pfreeframe (-f .(fn_framesize)) f.(fn_stacksize) f.(fn_link_ofs) ::
      Pblr :: k
  end.

Definition transl_code (f: Mach.function) (il: list Mach.instruction) :=
  List.fold_right (transl_instr f) nil il.

(** Translation of a whole function.  Note that we must check
  that the generated code contains less than [2^32] instructions,
  otherwise the offset part of the [PC] code pointer could wrap
  around, leading to incorrect executions. *)

Definition transl_function (f: Mach.function) :=
  Pallocframe (- f.(fn_framesize)) f.(fn_stacksize) f.(fn_link_ofs) ::
  Pmflr GPR0 ::
  Pstw GPR0 (Cint f.(fn_retaddr_ofs)) GPR1 ::
  transl_code f f.(fn_code).

Open Local Scope string_scope.

Definition transf_function (f: Mach.function) : res Asm.code :=
  let c := transl_function f in
  if zlt Int.max_unsigned (list_length_z c)
  then Errors.Error (msg "code size exceeded")
  else Errors.OK c.

Definition transf_fundef (f: Mach.fundef) : res Asm.fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: Mach.program) : res Asm.program :=
  transform_partial_program transf_fundef p.

