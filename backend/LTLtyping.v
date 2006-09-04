(** Typing rules for LTL. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import RTL.
Require Import Locations.
Require Import LTL.
Require Import Conventions.

(** The following predicates define a type system for LTL similar to that
  of [RTL] (see file [RTLtyping]): it statically guarantees that operations
  and addressing modes are applied to the right number of arguments
  and that the arguments are of the correct types.  Moreover, it also
  enforces some correctness conditions on the offsets of stack slots
  accessed through [Bgetstack] and [Bsetstack] LTL instructions. *)

Section WT_BLOCK.

Variable funct: function.

Definition slot_bounded (s: slot) :=
  match s with
  | Local ofs ty => 0 <= ofs
  | Outgoing ofs ty => 6 <= ofs
  | Incoming ofs ty => 6 <= ofs /\ ofs + typesize ty <= size_arguments funct.(fn_sig)
  end.

Inductive wt_block : block -> Prop :=
  | wt_Bgetstack:
      forall s r b,
      slot_type s = mreg_type r ->
      slot_bounded s ->
      wt_block b ->
      wt_block (Bgetstack s r b)
  | wt_Bsetstack:
      forall r s b,
      match s with Incoming _ _ => False | _ => True end ->
      slot_type s = mreg_type r ->
      slot_bounded s ->
      wt_block b ->
      wt_block (Bsetstack r s b)
  | wt_Bopmove:
      forall r1 r b,
      mreg_type r1 = mreg_type r ->
      wt_block b ->
      wt_block (Bop Omove (r1 :: nil) r b)
  | wt_Bopundef:
      forall r b,
      wt_block b ->
      wt_block (Bop Oundef nil r b)
  | wt_Bop:
      forall op args res b,
      op <> Omove -> op <> Oundef ->
      (List.map mreg_type args, mreg_type res) = type_of_operation op ->
      wt_block b ->
      wt_block (Bop op args res b)
  | wt_Bload:
      forall chunk addr args dst b,
      List.map mreg_type args = type_of_addressing addr ->
      mreg_type dst = type_of_chunk chunk ->
      wt_block b ->
      wt_block (Bload chunk addr args dst b)
  | wt_Bstore:
      forall chunk addr args src b,
      List.map mreg_type args = type_of_addressing addr ->
      mreg_type src = type_of_chunk chunk ->
      wt_block b ->
      wt_block (Bstore chunk addr args src b)
  | wt_Bcall:
      forall sig ros b,
      match ros with inl r => mreg_type r = Tint | _ => True end ->
      wt_block b ->
      wt_block (Bcall sig ros b)
  | wt_Balloc:
      forall b,
      wt_block b ->
      wt_block (Balloc b)
  | wt_Bgoto:
      forall lbl,
      wt_block (Bgoto lbl)
  | wt_Bcond:
      forall cond args ifso ifnot,
      List.map mreg_type args = type_of_condition cond ->
      wt_block (Bcond cond args ifso ifnot)
  | wt_Breturn: 
      wt_block (Breturn).

End WT_BLOCK.

Definition wt_function (f: function) : Prop :=
  forall pc b, f.(fn_code)!pc = Some b -> wt_block f b.

Inductive wt_fundef: fundef -> Prop :=
  | wt_fundef_external: forall ef,
      Conventions.sig_external_ok ef.(ef_sig) ->
      wt_fundef (External ef)
  | wt_function_internal: forall f,
      wt_function f ->
      wt_fundef (Internal f).

Definition wt_program (p: program) : Prop :=
  forall i f, In (i, f) (prog_funct p) -> wt_fundef f.

