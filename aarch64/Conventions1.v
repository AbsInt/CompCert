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

(** Function calling conventions and other conventions regarding the use of
    machine registers and stack slots. *)

Require Import Coqlib Decidableplus.
Require Import AST Events Locations.
Require Archi.

(** * Classification of machine registers *)

(** Machine registers (type [mreg] in module [Locations]) are divided in:
- Callee-save registers, whose value is preserved across a function call.
- Caller-save registers that can be modified during a function call.

  We follow the Procedure Call Standard for the ARM 64-bit Architecture
  (AArch64) document: R19-R28 and F8-F15 are callee-save. *)

Definition is_callee_save (r: mreg): bool :=
  match r with
  | R0  | R1  | R2  | R3  | R4  | R5  | R6  | R7 => false
  | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15 => false
  | R17 => false
  | R19 | R20 | R21 |  R22 | R23 => true
  | R24 | R25 | R26 | R27 | R28 => true
  | R29 => false
  | F0  | F1  | F2  | F3  | F4  | F5  | F6  | F7 => false
  | F8  | F9  | F10 | F11 | F12 | F13 | F14 | F15 => true
  | F16 | F17 | F18 | F19 | F20 | F21 | F22 | F23 => false
  | F24 | F25 | F26 | F27 | F28 | F29 | F30 | F31 => false
  end.

Definition int_caller_save_regs :=
     R0  :: R1  :: R2  :: R3  :: R4  :: R5  :: R6  :: R7
  :: R8  :: R9  :: R10 :: R11 :: R12 :: R13 :: R14 :: R15
  :: R17 :: R29 :: nil.

Definition float_caller_save_regs :=
     F0  :: F1  :: F2  :: F3  :: F4  :: F5  :: F6  :: F7
  :: F16 :: F17 :: F18 :: F19 :: F20 :: F21 :: F22 :: F23
  :: F24 :: F25 :: F26 :: F27 :: F28 :: F29 :: F30 :: F31 :: nil.

Definition int_callee_save_regs :=
     R19 :: R20 :: R21 ::  R22 :: R23
  :: R24 :: R25 :: R26 :: R27 :: R28 :: nil.

Definition float_callee_save_regs :=
     F8  :: F9  :: F10 :: F11 :: F12 :: F13 :: F14 :: F15 :: nil.

Definition destroyed_at_call :=
  List.filter (fun r => negb (is_callee_save r)) all_mregs.

Definition dummy_int_reg := R0.     (**r Used in [Coloring]. *)
Definition dummy_float_reg := F0.   (**r Used in [Coloring]. *)

Definition callee_save_type := mreg_type.
  
Definition is_float_reg (r: mreg): bool :=
  match r with
  | R0  | R1  | R2  | R3  | R4  | R5  | R6  | R7
  | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15
  | R17 | R19 | R20 | R21 |  R22 | R23
  | R24 | R25 | R26 | R27 | R28
  | R29 => false
  | F0  | F1  | F2  | F3  | F4  | F5  | F6  | F7
  | F8  | F9  | F10 | F11 | F12 | F13 | F14 | F15
  | F16 | F17 | F18 | F19 | F20 | F21 | F22 | F23
  | F24 | F25 | F26 | F27 | F28 | F29 | F30 | F31 => true
  end.

(** * Function calling conventions *)

(** The functions in this section determine the locations (machine registers
  and stack slots) used to communicate arguments and results between the
  caller and the callee during function calls.  These locations are functions
  of the signature of the function and of the call instruction.
  Agreement between the caller and the callee on the locations to use
  is guaranteed by our dynamic semantics for Cminor and RTL, which demand
  that the signature of the call instruction is identical to that of the
  called function.

  Calling conventions are largely arbitrary: they must respect the properties
  proved in this section (such as no overlapping between the locations
  of function arguments), but this leaves much liberty in choosing actual
  locations.  *)

(** ** Location of function result *)

(** The result value of a function is passed back to the caller in
  registers [R0] or [F0], depending on the type of the
  returned value.  We treat a function without result as a function
  with one integer result. *)

Definition loc_result (s: signature) : rpair mreg :=
  match proj_sig_res s with
  | Tint | Tlong | Tany32 | Tany64 => One R0
  | Tfloat | Tsingle => One F0
  end.

(** The result registers have types compatible with that given in the signature. *)

Lemma loc_result_type:
  forall sig,
  subtype (proj_sig_res sig) (typ_rpair mreg_type (loc_result sig)) = true.
Proof.
  intros. unfold loc_result. destruct (proj_sig_res sig); auto.
Qed.

(** The result locations are caller-save registers *)

Lemma loc_result_caller_save:
  forall (s: signature),
  forall_rpair (fun r => is_callee_save r = false) (loc_result s).
Proof.
  intros.
  unfold loc_result. destruct (proj_sig_res s); simpl; auto.
Qed.

(** If the result is in a pair of registers, those registers are distinct and have type [Tint] at least. *)

Lemma loc_result_pair:
  forall sg,
  match loc_result sg with
  | One _ => True
  | Twolong r1 r2 =>
        r1 <> r2 /\ proj_sig_res sg = Tlong
     /\ subtype Tint (mreg_type r1) = true /\ subtype Tint (mreg_type r2) = true
     /\ Archi.ptr64 = false
  end.
Proof.
  intros; unfold loc_result; destruct (proj_sig_res sg); exact I.
Qed.

(** The location of the result depends only on the result part of the signature *)

Lemma loc_result_exten:
  forall s1 s2, s1.(sig_res) = s2.(sig_res) -> loc_result s1 = loc_result s2.
Proof.
  intros. unfold loc_result, proj_sig_res. rewrite H; auto.
Qed.

(** ** Location of function arguments *)

(**
- The first 8 integer arguments are passed in registers [R0...R7].
- The first 8 FP arguments are passed in registers [F0...F7].
- Extra arguments are passed on the stack, in [Outgoing] slots of size
  64 bits (2 words), consecutively assigned, starting at word offset 0.
**)

Definition int_param_regs :=
  R0  :: R1  :: R2  :: R3  :: R4  :: R5  :: R6  :: R7 :: nil.

Definition float_param_regs :=
  F0  :: F1  :: F2  :: F3  :: F4  :: F5  :: F6  :: F7 :: nil.

Fixpoint loc_arguments_rec
     (tyl: list typ) (ir fr ofs: Z) {struct tyl} : list (rpair loc) :=
  match tyl with
  | nil => nil
  | (Tint | Tlong | Tany32 | Tany64) as ty :: tys =>
      match list_nth_z int_param_regs ir with
      | None =>
          One (S Outgoing ofs ty) :: loc_arguments_rec tys ir fr (ofs + 2)
      | Some ireg =>
          One (R ireg) :: loc_arguments_rec tys (ir + 1) fr ofs
      end
  | (Tfloat | Tsingle) as ty :: tys =>
      match list_nth_z float_param_regs fr with
      | None =>
          One (S Outgoing ofs ty) :: loc_arguments_rec tys ir fr (ofs + 2)
      | Some freg =>
          One (R freg) :: loc_arguments_rec tys ir (fr + 1) ofs
      end
  end.

(** [loc_arguments s] returns the list of locations where to store arguments
  when calling a function with signature [s].  *)

Definition loc_arguments (s: signature) : list (rpair loc) :=
  loc_arguments_rec s.(sig_args) 0 0 0.

(** Argument locations are either caller-save registers or [Outgoing]
  stack slots at nonnegative offsets. *)

Definition loc_argument_acceptable (l: loc) : Prop :=
  match l with
  | R r => is_callee_save r = false
  | S Outgoing ofs ty => ofs >= 0 /\ (typealign ty | ofs)
  | _ => False
  end.

Definition loc_argument_charact (ofs: Z) (l: loc) : Prop :=
  match l with
  | R r => In r int_param_regs \/ In r float_param_regs
  | S Outgoing ofs' ty => ofs' >= ofs /\ (2 | ofs')
  | _ => False
  end.

Remark loc_arguments_rec_charact:
  forall tyl ir fr ofs p,
  In p (loc_arguments_rec tyl ir fr ofs) -> (2 | ofs) -> forall_rpair (loc_argument_charact ofs) p.
Proof.
  assert (X: forall ofs1 ofs2 l, loc_argument_charact ofs2 l -> ofs1 <= ofs2 -> loc_argument_charact ofs1 l).
  { destruct l; simpl; intros; auto. destruct sl; auto. intuition omega. }
  assert (Y: forall ofs1 ofs2 p, forall_rpair (loc_argument_charact ofs2) p -> ofs1 <= ofs2 -> forall_rpair (loc_argument_charact ofs1) p).
  { destruct p; simpl; intuition eauto. }
  assert (Z: forall ofs, (2 | ofs) -> (2 | ofs + 2)).
  { intros. apply Z.divide_add_r; auto. apply Z.divide_refl. }
Opaque list_nth_z.
  induction tyl; simpl loc_arguments_rec; intros.
- contradiction.
- assert (A: forall ty, In p
      match list_nth_z int_param_regs ir with
      | Some ireg => One (R ireg) :: loc_arguments_rec tyl (ir + 1) fr ofs
      | None => One (S Outgoing ofs ty) :: loc_arguments_rec tyl ir fr (ofs + 2)
      end ->
      forall_rpair (loc_argument_charact ofs) p).
  { intros. destruct (list_nth_z int_param_regs ir) as [r|] eqn:E; destruct H1.
    subst. left. eapply list_nth_z_in; eauto.
    eapply IHtyl; eauto.
    subst. split. omega. assumption.
    eapply Y; eauto. omega. }
  assert (B: forall ty, In p
      match list_nth_z float_param_regs fr with
      | Some ireg => One (R ireg) :: loc_arguments_rec tyl ir (fr + 1) ofs
      | None => One (S Outgoing ofs ty) :: loc_arguments_rec tyl ir fr (ofs + 2)
      end ->
      forall_rpair (loc_argument_charact ofs) p).
  { intros. destruct (list_nth_z float_param_regs fr) as [r|] eqn:E; destruct H1.
    subst. right. eapply list_nth_z_in; eauto.
    eapply IHtyl; eauto.
    subst. split. omega. assumption.
    eapply Y; eauto. omega. }
  destruct a; eauto.
Qed.

Lemma loc_arguments_acceptable:
  forall (s: signature) (p: rpair loc),
  In p (loc_arguments s) -> forall_rpair loc_argument_acceptable p.
Proof.
  unfold loc_arguments; intros.
  assert (A: forall r, In r int_param_regs -> is_callee_save r = false) by decide_goal.
  assert (B: forall r, In r float_param_regs -> is_callee_save r = false) by decide_goal.
  assert (X: forall l, loc_argument_charact 0 l -> loc_argument_acceptable l).
  { unfold loc_argument_charact, loc_argument_acceptable.
    destruct l as [r | [] ofs ty]; auto.  intros [C|C]; auto.
    intros [C D]. split; auto. apply Z.divide_trans with 2; auto.
    exists (2 / typealign ty); destruct ty; reflexivity.
  }
  exploit loc_arguments_rec_charact; eauto using Z.divide_0_r.
  unfold forall_rpair; destruct p; intuition auto.
Qed.

Hint Resolve loc_arguments_acceptable: locs.

Lemma loc_arguments_main:
  loc_arguments signature_main = nil.
Proof.
  unfold loc_arguments; reflexivity.
Qed.

(** ** Normalization of function results *)

(** According to the AAPCS64 ABI specification, "padding bits" in the return
    value of a function have unpredictable values and must be ignored.
    Consequently, we force normalization of return values of small integer
    types (8- and 16-bit integers), so that the top bits (the "padding bits")
    are proper sign- or zero-extensions of the small integer value. *)

Definition return_value_needs_normalization (t: rettype) : bool :=
  match t with
  | Tint8signed | Tint8unsigned | Tint16signed | Tint16unsigned => true
  | _ => false
  end.
