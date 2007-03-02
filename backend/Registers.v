(** Pseudo-registers and register states.

  This library defines the type of pseudo-registers used in the RTL
  intermediate language, and of mappings from pseudo-registers to
  values as used in the dynamic semantics of RTL. *)

Require Import Coqlib.
Require Import AST.
Require Import Maps.
Require Import Ordered.
Require Import FSets.
Require FSetAVL.

Definition reg: Set := positive.

Module Reg.

Definition eq := peq.

Definition typenv := PMap.t typ.

End Reg.

(** Mappings from registers to some type. *)

Module Regmap := PMap.

Set Implicit Arguments.

Definition regmap_optget
    (A: Set) (or: option reg) (dfl: A) (rs: Regmap.t A) : A :=
  match or with
  | None => dfl
  | Some r => Regmap.get r rs
  end.

Definition regmap_optset
    (A: Set) (or: option reg) (v: A) (rs: Regmap.t A) : Regmap.t A :=
  match or with
  | None => rs
  | Some r => Regmap.set r v rs
  end.

Notation "a # b" := (Regmap.get b a) (at level 1).
Notation "a ## b" := (List.map (fun r => Regmap.get r a) b) (at level 1).
Notation "a # b <- c" := (Regmap.set b c a) (at level 1, b at next level).

(** Sets of registers *)

Module Regset := FSetAVL.Make(OrderedPositive).
