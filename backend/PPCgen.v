(** Translation from Mach to PPC. *)

Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Mem.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import PPC.

(** Translation of the LTL/Linear/Mach view of machine registers
  to the PPC view.  PPC has two different types for registers
  (integer and float) while LTL et al have only one.  The
  [ireg_of] and [freg_of] are therefore partial in principle.
  To keep things simpler, we make them return nonsensical
  results when applied to a LTL register of the wrong type.
  The proof in [PPCgenproof] will show that this never happens.

  Note that no LTL register maps to [GPR2] nor [FPR13].
  These two registers are reserved as temporaries, to be used
  by the generated PPC code.  *)

Definition ireg_of (r: mreg) : ireg :=
  match r with
  | R3 => GPR3  | R4 => GPR4  | R5 => GPR5  | R6 => GPR6
  | R7 => GPR7  | R8 => GPR8  | R9 => GPR9  | R10 => GPR10
  | R13 => GPR13 | R14 => GPR14 | R15 => GPR15 | R16 => GPR16
  | R17 => GPR17 | R18 => GPR18 | R19 => GPR19 | R20 => GPR20
  | R21 => GPR21 | R22 => GPR22 | R23 => GPR23 | R24 => GPR24
  | R25 => GPR25 | R26 => GPR26 | R27 => GPR27 | R28 => GPR28
  | R29 => GPR29 | R30 => GPR30 | R31 => GPR31
  | IT1 => GPR11 | IT2 => GPR12 | IT3 => GPR0
  | _ => GPR0 (* should not happen *)
  end.

Definition freg_of (r: mreg) : freg :=
  match r with
  | F1 => FPR1  | F2 => FPR2  | F3 => FPR3  | F4 => FPR4
  | F5 => FPR5  | F6 => FPR6  | F7 => FPR7  | F8 => FPR8
  | F9 => FPR9  | F10 => FPR10 | F14 => FPR14 | F15 => FPR15
  | F16 => FPR16 | F17 => FPR17 | F18 => FPR18 | F19 => FPR19
  | F20 => FPR20 | F21 => FPR21 | F22 => FPR22 | F23 => FPR23
  | F24 => FPR24 | F25 => FPR25 | F26 => FPR26 | F27 => FPR27
  | F28 => FPR28 | F29 => FPR29 | F30 => FPR30 | F31 => FPR31
  | FT1 => FPR0 | FT2 => FPR11 | FT3 => FPR12
  | _ => FPR0 (* should not happen *)
  end.

(** Decomposition of integer constants.  As noted in file [PPC],
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
Definition low_s (n: int) := Int.cast16signed n.
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

Definition addimm_1 (r1 r2: ireg) (n: int) (k: code) :=
  if Int.eq (high_s n) Int.zero then
    Paddi r1 r2 (Cint n) :: k
  else if Int.eq (low_s n) Int.zero then
    Paddis r1 r2 (Cint (high_s n)) :: k
  else
    Paddis r1 r2 (Cint (high_s n)) ::
    Paddi r1 r1 (Cint (low_s n)) :: k.

Definition addimm_2 (r1 r2: ireg) (n: int) (k: code) :=
  loadimm GPR2 n (Padd r1 r2 GPR2 :: k).

Definition addimm (r1 r2: ireg) (n: int) (k: code) :=
  if ireg_eq r1 GPR0 then
    addimm_2 r1 r2 n k
  else if ireg_eq r2 GPR0 then
    addimm_2 r1 r2 n k
  else
    addimm_1 r1 r2 n k.

Definition andimm (r1 r2: ireg) (n: int) (k: code) :=
  if Int.eq (high_u n) Int.zero then
    Pandi_ r1 r2 (Cint n) :: k
  else if Int.eq (low_u n) Int.zero then
    Pandis_ r1 r2 (Cint (high_u n)) :: k
  else
    loadimm GPR2 n (Pand_ r1 r2 GPR2 :: k).

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

(** Smart constructors for indexed loads and stores,
  where the address is the contents of a register plus
  an integer literal. *)

Definition loadind_aux (base: ireg) (ofs: int) (ty: typ) (dst: mreg) :=
  match ty with
  | Tint => Plwz (ireg_of dst) (Cint ofs) base
  | Tfloat => Plfd (freg_of dst) (Cint ofs) base
  end.

Definition loadind (base: ireg) (ofs: int) (ty: typ) (dst: mreg) (k: code) :=
  if Int.eq (high_s ofs) Int.zero then
    loadind_aux base ofs ty dst :: k
  else
    Paddis GPR2 base (Cint (high_s ofs)) ::
    loadind_aux GPR2 (low_s ofs) ty dst :: k.
  
Definition storeind_aux (src: mreg) (base: ireg) (ofs: int) (ty: typ) :=
  match ty with
  | Tint => Pstw (ireg_of src) (Cint ofs) base
  | Tfloat => Pstfd (freg_of src) (Cint ofs) base
  end.

Definition storeind (src: mreg) (base: ireg) (ofs: int) (ty: typ) (k: code) :=
  if Int.eq (high_s ofs) Int.zero then
    storeind_aux src base ofs ty :: k
  else
    Paddis GPR2 base (Cint (high_s ofs)) ::
    storeind_aux src GPR2 (low_s ofs) ty :: k.
  
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
        loadimm GPR2 n (Pcmpw (ireg_of a1) GPR2 :: k)
  | Ccompuimm c n, a1 :: nil =>
      if Int.eq (high_u n) Int.zero then
        Pcmplwi (ireg_of a1) (Cint n) :: k
      else
        loadimm GPR2 n (Pcmplw (ireg_of a1) GPR2 :: k)
  | Ccompf cmp, a1 :: a2 :: nil =>
      floatcomp cmp (freg_of a1) (freg_of a2) k
  | Cnotcompf cmp, a1 :: a2 :: nil =>
      floatcomp cmp (freg_of a1) (freg_of a2) k
  | Cmaskzero n, a1 :: nil =>
      andimm GPR2 (ireg_of a1) n k
  | Cmasknotzero n, a1 :: nil =>
      andimm GPR2 (ireg_of a1) n k
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
      Paddis (ireg_of r) GPR0 (Csymbol_high_unsigned s ofs) ::
      Pori (ireg_of r) (ireg_of r) (Csymbol_low_unsigned s ofs) :: k
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
        loadimm GPR2 n (Psubfc (ireg_of r) (ireg_of a1) GPR2 :: k)
  | Omul, a1 :: a2 :: nil =>
      Pmullw (ireg_of r) (ireg_of a1) (ireg_of a2) :: k
  | Omulimm n, a1 :: nil =>
      if Int.eq (high_s n) Int.zero then
        Pmulli (ireg_of r) (ireg_of a1) (Cint n) :: k
      else
        loadimm GPR2 n (Pmullw (ireg_of r) (ireg_of a1) GPR2 :: k)
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
  | Ofloatofint, a1 :: nil =>
      Pictf (freg_of r) (ireg_of a1) :: k
  | Ofloatofintu, a1 :: nil =>
      Piuctf (freg_of r) (ireg_of a1) :: k
  | Ocmp cmp, _ =>
      let p := crbit_for_cond cmp in
      transl_cond cmp args
        (Pmfcrbit (ireg_of r) (fst p) ::
         if snd p
         then k
         else Pxori (ireg_of r) (ireg_of r) (Cint Int.one) :: k)
  | _, _ =>
      k (**r never happens for well-typed code *)
  end.

(** Common code to translate [Mload] and [Mstore] instructions. *)

Definition transl_load_store 
     (mk1: constant -> ireg -> instruction)
     (mk2: ireg -> ireg -> instruction)
     (addr: addressing) (args: list mreg) (k: code) :=
  match addr, args with
  | Aindexed ofs, a1 :: nil =>
      if ireg_eq (ireg_of a1) GPR0 then
        Pmr GPR2 (ireg_of a1) ::
        Paddis GPR2 GPR2 (Cint (high_s ofs)) ::
        mk1 (Cint (low_s ofs)) GPR2 :: k
      else if Int.eq (high_s ofs) Int.zero then
        mk1 (Cint ofs) (ireg_of a1) :: k
      else
        Paddis GPR2 (ireg_of a1) (Cint (high_s ofs)) ::
        mk1 (Cint (low_s ofs)) GPR2 :: k
  | Aindexed2, a1 :: a2 :: nil =>
      mk2 (ireg_of a1) (ireg_of a2) :: k
  | Aglobal symb ofs, nil =>
      Paddis GPR2 GPR0 (Csymbol_high_signed symb ofs) ::
      mk1 (Csymbol_low_signed symb ofs) GPR2 :: k
  | Abased symb ofs, a1 :: nil =>
      if ireg_eq (ireg_of a1) GPR0 then
        Pmr GPR2 (ireg_of a1) ::
        Paddis GPR2 GPR2 (Csymbol_high_signed symb ofs) ::
        mk1 (Csymbol_low_signed symb ofs) GPR2 :: k
      else
        Paddis GPR2 (ireg_of a1) (Csymbol_high_signed symb ofs) ::
        mk1 (Csymbol_low_signed symb ofs) GPR2 :: k
  | Ainstack ofs, nil =>
      if Int.eq (high_s ofs) Int.zero then
        mk1 (Cint ofs) GPR1 :: k
      else
        Paddis GPR2 GPR1 (Cint (high_s ofs)) ::
        mk1 (Cint (low_s ofs)) GPR2 :: k
  | _, _ =>
      (* should not happen *) k
  end.

(** Translation of a Mach instruction. *)

Definition transl_instr (i: Mach.instruction) (k: code) :=
  match i with
  | Mgetstack ofs ty dst =>
      loadind GPR1 ofs ty dst k
  | Msetstack src ofs ty =>
      storeind src GPR1 ofs ty k
  | Mgetparam ofs ty dst =>
      Plwz GPR2 (Cint (Int.repr 0)) GPR1 :: loadind GPR2 ofs ty dst k
  | Mop op args res =>
      transl_op op args res k
  | Mload chunk addr args dst =>
      match chunk with
      | Mint8signed =>
          transl_load_store
            (Plbz (ireg_of dst)) (Plbzx (ireg_of dst)) addr args
            (Pextsb (ireg_of dst) (ireg_of dst) :: k)
      | Mint8unsigned =>
          transl_load_store
            (Plbz (ireg_of dst)) (Plbzx (ireg_of dst)) addr args k
      | Mint16signed =>
          transl_load_store
            (Plha (ireg_of dst)) (Plhax (ireg_of dst)) addr args k
      | Mint16unsigned =>
          transl_load_store
            (Plhz (ireg_of dst)) (Plhzx (ireg_of dst)) addr args k
      | Mint32 =>
          transl_load_store
            (Plwz (ireg_of dst)) (Plwzx (ireg_of dst)) addr args k
      | Mfloat32 =>
          transl_load_store
            (Plfs (freg_of dst)) (Plfsx (freg_of dst)) addr args k
      | Mfloat64 =>
          transl_load_store
            (Plfd (freg_of dst)) (Plfdx (freg_of dst)) addr args k
      end
  | Mstore chunk addr args src =>
      match chunk with
      | Mint8signed =>
          transl_load_store
            (Pstb (ireg_of src)) (Pstbx (ireg_of src)) addr args k
      | Mint8unsigned =>
          transl_load_store
            (Pstb (ireg_of src)) (Pstbx (ireg_of src)) addr args k
      | Mint16signed =>
          transl_load_store
            (Psth (ireg_of src)) (Psthx (ireg_of src)) addr args k
      | Mint16unsigned =>
          transl_load_store
            (Psth (ireg_of src)) (Psthx (ireg_of src)) addr args k
      | Mint32 =>
          transl_load_store
            (Pstw (ireg_of src)) (Pstwx (ireg_of src)) addr args k
      | Mfloat32 =>
          transl_load_store
            (Pstfs (freg_of src)) (Pstfsx (freg_of src)) addr args k
      | Mfloat64 =>
          transl_load_store
            (Pstfd (freg_of src)) (Pstfdx (freg_of src)) addr args k
      end
  | Mcall sig (inl r) =>
      Pmtctr (ireg_of r) :: Pbctrl :: k
  | Mcall sig (inr symb) =>
      Pbl symb :: k
  | Mtailcall sig (inl r) =>
      Pmtctr (ireg_of r) :: 
      Plwz GPR2 (Cint (Int.repr 12)) GPR1 ::
      Pmtlr GPR2 ::
      Pfreeframe :: 
      Pbctr :: k
  | Mtailcall sig (inr symb) =>
      Plwz GPR2 (Cint (Int.repr 12)) GPR1 ::
      Pmtlr GPR2 ::
      Pfreeframe :: 
      Pbs symb :: k
  | Malloc =>
      Pallocblock :: k
  | Mlabel lbl =>
      Plabel lbl :: k
  | Mgoto lbl =>
      Pb lbl :: k
  | Mcond cond args lbl =>
      let p := crbit_for_cond cond in
      transl_cond cond args
        (if (snd p) then Pbt (fst p) lbl :: k else Pbf (fst p) lbl :: k)
  | Mreturn =>
      Plwz GPR2 (Cint (Int.repr 12)) GPR1 ::
      Pmtlr GPR2 :: Pfreeframe :: Pblr :: k
  end.

Definition transl_code (il: list Mach.instruction) :=
  List.fold_right transl_instr nil il.

(** Translation of a whole function.  Note that we must check
  that the generated code contains less than [2^32] instructions,
  otherwise the offset part of the [PC] code pointer could wrap
  around, leading to incorrect executions. *)

Definition transl_function (f: Mach.function) :=
  Pallocframe (- f.(fn_framesize))
              (align_16_top (-f.(fn_framesize)) f.(fn_stacksize)) ::
  Pmflr GPR2 ::
  Pstw GPR2 (Cint (Int.repr 12)) GPR1 ::
  transl_code f.(fn_code).

Fixpoint code_size (c: code) : Z :=
  match c with
  | nil => 0
  | instr :: c' => code_size c' + 1
  end.

Open Local Scope string_scope.

Definition transf_function (f: Mach.function) : res PPC.code :=
  let c := transl_function f in
  if zlt Int.max_unsigned (code_size c)
  then Errors.Error (msg "code size exceeded")
  else Errors.OK c.

Definition transf_fundef (f: Mach.fundef) : res PPC.fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: Mach.program) : res PPC.program :=
  transform_partial_program transf_fundef p.

