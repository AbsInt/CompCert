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

(** Instruction selection for integer division and modulus *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.

Open Local Scope cminorsel_scope.

(** We try to turn divisions by a constant into a multiplication by
  a pseudo-inverse of the divisor.  The approach is described in
- Torbjörn Granlund, Peter L. Montgomery: "Division by Invariant
  Integers using Multiplication". PLDI 1994.
- Henry S. Warren, Jr: "Hacker's Delight". Addison-Wesley.  Chapter 10.
*)

Fixpoint find_div_mul_params (fuel: nat) (nc: Z) (d: Z) (p: Z) : option (Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
      let twp := two_p p in
      if zlt (nc * (d - twp mod d)) twp
      then Some(p - 32, (twp + d - twp mod d) / d)
      else find_div_mul_params fuel' nc d (p + 1)
  end.

Definition divs_mul_params (d: Z) : option (Z * Z) :=
  match find_div_mul_params
          Int.wordsize
          (Int.half_modulus - Int.half_modulus mod d - 1)
          d 32 with
  | None => None
  | Some(p, m) =>
      if zlt 0 d
      && zlt (two_p (32 + p)) (m * d)
      && zle (m * d) (two_p (32 + p) + two_p (p + 1))
      && zle 0 m && zlt m Int.modulus
      && zle 0 p && zlt p 32
      then Some(p, m) else None
  end.

Definition divu_mul_params (d: Z) : option (Z * Z) :=
  match find_div_mul_params
          Int.wordsize
          (Int.modulus - Int.modulus mod d - 1)
          d 32 with
  | None => None
  | Some(p, m) =>
      if zlt 0 d
      && zle (two_p (32 + p)) (m * d)
      && zle (m * d) (two_p (32 + p) + two_p p)
      && zle 0 m && zlt m Int.modulus
      && zle 0 p && zlt p 32
      then Some(p, m) else None
  end.

Definition divu_mul (p: Z) (m: Z) :=
  shruimm (Eop Omulhu (Eletvar O ::: Eop (Ointconst (Int.repr m)) Enil ::: Enil))
          (Int.repr p).

Definition divuimm (e1: expr) (n2: int) :=
  match Int.is_power2 n2 with
  | Some l => shruimm e1 l
  | None =>
      match divu_mul_params (Int.unsigned n2) with
      | None => divu_base e1 (Eop (Ointconst n2) Enil)
      | Some(p, m) => Elet e1 (divu_mul p m)
      end
  end.

(** Original definition:
<<
Nondetfunction divu (e1: expr) (e2: expr) := 
  match e2 with
  | Eop (Ointconst n2) Enil => divuimm e1 n2
  | _ => divu_base e1 e2
  end.
>>
*)

Inductive divu_cases: forall (e2: expr), Type :=
  | divu_case1: forall n2, divu_cases (Eop (Ointconst n2) Enil)
  | divu_default: forall (e2: expr), divu_cases e2.

Definition divu_match (e2: expr) :=
  match e2 as zz1 return divu_cases zz1 with
  | Eop (Ointconst n2) Enil => divu_case1 n2
  | e2 => divu_default e2
  end.

Definition divu (e1: expr) (e2: expr) :=
  match divu_match e2 with
  | divu_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      divuimm e1 n2
  | divu_default e2 =>
      divu_base e1 e2
  end.


Definition mod_from_div (equo: expr) (n: int) :=
  Eop Osub (Eletvar O ::: mulimm n equo ::: Enil).

Definition moduimm (e1: expr) (n2: int) :=
  match Int.is_power2 n2 with
  | Some l => andimm (Int.sub n2 Int.one) e1
  | None =>
      match divu_mul_params (Int.unsigned n2) with
      | None => modu_base e1 (Eop (Ointconst n2) Enil)
      | Some(p, m) => Elet e1 (mod_from_div (divu_mul p m) n2)
      end
  end.

(** Original definition:
<<
Nondetfunction modu (e1: expr) (e2: expr) := 
  match e2 with
  | Eop (Ointconst n2) Enil => moduimm e1 n2
  | _ => modu_base e1 e2
  end.
>>
*)

Inductive modu_cases: forall (e2: expr), Type :=
  | modu_case1: forall n2, modu_cases (Eop (Ointconst n2) Enil)
  | modu_default: forall (e2: expr), modu_cases e2.

Definition modu_match (e2: expr) :=
  match e2 as zz1 return modu_cases zz1 with
  | Eop (Ointconst n2) Enil => modu_case1 n2
  | e2 => modu_default e2
  end.

Definition modu (e1: expr) (e2: expr) :=
  match modu_match e2 with
  | modu_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      moduimm e1 n2
  | modu_default e2 =>
      modu_base e1 e2
  end.


Definition divs_mul (p: Z) (m: Z) :=
  let e2 :=
    Eop Omulhs (Eletvar O ::: Eop (Ointconst (Int.repr m)) Enil ::: Enil) in
  let e3 :=
    if zlt m Int.half_modulus then e2 else add e2 (Eletvar O) in
  add (shrimm e3 (Int.repr p))
      (shruimm (Eletvar O) (Int.repr (Int.zwordsize - 1))).

Definition divsimm (e1: expr) (n2: int) :=
  match Int.is_power2 n2 with
  | Some l => 
      if Int.ltu l (Int.repr 31)
      then shrximm e1 l
      else divs_base e1 (Eop (Ointconst n2) Enil)
  | None =>
      match divs_mul_params (Int.signed n2) with
      | None => divs_base e1 (Eop (Ointconst n2) Enil)
      | Some(p, m) => Elet e1 (divs_mul p m)
      end
  end.

(** Original definition:
<<
Nondetfunction divs (e1: expr) (e2: expr) := 
  match e2 with
  | Eop (Ointconst n2) Enil => divsimm e1 n2
  | _ => divs_base e1 e2
  end.
>>
*)

Inductive divs_cases: forall (e2: expr), Type :=
  | divs_case1: forall n2, divs_cases (Eop (Ointconst n2) Enil)
  | divs_default: forall (e2: expr), divs_cases e2.

Definition divs_match (e2: expr) :=
  match e2 as zz1 return divs_cases zz1 with
  | Eop (Ointconst n2) Enil => divs_case1 n2
  | e2 => divs_default e2
  end.

Definition divs (e1: expr) (e2: expr) :=
  match divs_match e2 with
  | divs_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      divsimm e1 n2
  | divs_default e2 =>
      divs_base e1 e2
  end.


Definition modsimm (e1: expr) (n2: int) :=
  match Int.is_power2 n2 with
  | Some l =>
      if Int.ltu l (Int.repr 31)
      then Elet e1 (mod_from_div (shrximm (Eletvar O) l) n2)
      else mods_base e1 (Eop (Ointconst n2) Enil)
  | None =>
      match divs_mul_params (Int.signed n2) with
      | None => mods_base e1 (Eop (Ointconst n2) Enil)
      | Some(p, m) => Elet e1 (mod_from_div (divs_mul p m) n2)
      end
  end.

(** Original definition:
<<
Nondetfunction mods (e1: expr) (e2: expr) := 
  match e2 with
  | Eop (Ointconst n2) Enil => modsimm e1 n2
  | _ => mods_base e1 e2
  end.
>>
*)

Inductive mods_cases: forall (e2: expr), Type :=
  | mods_case1: forall n2, mods_cases (Eop (Ointconst n2) Enil)
  | mods_default: forall (e2: expr), mods_cases e2.

Definition mods_match (e2: expr) :=
  match e2 as zz1 return mods_cases zz1 with
  | Eop (Ointconst n2) Enil => mods_case1 n2
  | e2 => mods_default e2
  end.

Definition mods (e1: expr) (e2: expr) :=
  match mods_match e2 with
  | mods_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      modsimm e1 n2
  | mods_default e2 =>
      mods_base e1 e2
  end.


