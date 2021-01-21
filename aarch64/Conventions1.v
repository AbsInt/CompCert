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
  (AArch64) document: R19-R28 and F8-F15 are callee-save.

  X16 is reserved as a temporary for asm generation.
  X18 is reserved as the platform register.
  X29 is reserved as the frame pointer register.
  X30 is reserved as the return address register. *)

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
- Extra arguments are passed on the stack, in [Outgoing] slots,
  consecutively assigned, starting at word offset 0.

In the standard AAPCS64, all stack slots are 8-byte wide (2 words).

In the Apple variant, a stack slot has the size of the type of the
corresponding argument, and is aligned accordingly.  We use 8-byte
slots (2 words) for C types [long] and [double], and 4-byte slots
(1 word) for C types [int] and [float].  For full conformance, we should
use 1-byte slots for [char] types and 2-byte slots for [short] types,
but this cannot be expressed in CompCert's type algebra, so we
incorrectly use 4-byte slots.

Concerning variable arguments to vararg functions:
- In the AAPCS64 standard, they are passed like regular, fixed arguments.
- In the Apple variant, they are always passed on stack, in 8-byte slots.
*)

Definition int_param_regs :=
  R0  :: R1  :: R2  :: R3  :: R4  :: R5  :: R6  :: R7 :: nil.

Definition float_param_regs :=
  F0  :: F1  :: F2  :: F3  :: F4  :: F5  :: F6  :: F7 :: nil.

Definition stack_arg (ty: typ) (ir fr ofs: Z)
                     (rec: Z -> Z -> Z -> list (rpair loc)) :=
  match Archi.abi with
  | Archi.AAPCS64 =>
      let ofs := align ofs 2 in
      One (S Outgoing ofs ty) :: rec ir fr (ofs + 2)
  | Archi.Apple =>
      let ofs := align ofs (typesize ty) in
      One (S Outgoing ofs ty) :: rec ir fr (ofs + typesize ty)
  end.

Definition int_arg (ty: typ) (ir fr ofs: Z)
                   (rec: Z -> Z -> Z -> list (rpair loc)) :=
  match list_nth_z int_param_regs ir with
  | None =>
      stack_arg ty ir fr ofs rec
  | Some ireg =>
      One (R ireg) :: rec (ir + 1) fr ofs
  end.

Definition float_arg (ty: typ) (ir fr ofs: Z)
                     (rec: Z -> Z -> Z -> list (rpair loc)) :=
  match list_nth_z float_param_regs fr with
  | None =>
      stack_arg ty ir fr ofs rec
  | Some freg =>
      One (R freg) :: rec ir (fr + 1) ofs
  end.

Fixpoint loc_arguments_stack (tyl: list typ) (ofs: Z) {struct tyl} : list (rpair loc) :=
  match tyl with
  | nil => nil
  | ty :: tys => One (S Outgoing ofs Tany64) :: loc_arguments_stack tys (ofs + 2)
  end.

Fixpoint loc_arguments_rec
     (tyl: list typ) (fixed ir fr ofs: Z) {struct tyl} : list (rpair loc) :=
  match tyl with
  | nil => nil
  | ty :: tys =>
      if zle fixed 0 then loc_arguments_stack tyl (align ofs 2) else
      match ty with
      | Tint | Tlong | Tany32 | Tany64 =>
          int_arg ty ir fr ofs (loc_arguments_rec tys (fixed - 1))
      | Tfloat | Tsingle =>
          float_arg ty ir fr ofs (loc_arguments_rec tys (fixed - 1))
      end
  end.

(** Number of fixed arguments for a function with signature [s].
    For AAPCS64, all arguments are treated as fixed, even for a vararg
    function. *)

Definition fixed_arguments (s: signature) : Z :=
  match Archi.abi, s.(sig_cc).(cc_vararg) with
  | Archi.Apple, Some n => n
  | _, _ => list_length_z s.(sig_args)
  end.

(** [loc_arguments s] returns the list of locations where to store arguments
  when calling a function with signature [s].  *)

Definition loc_arguments (s: signature) : list (rpair loc) :=
  loc_arguments_rec s.(sig_args) (fixed_arguments s) 0 0 0.

(** Argument locations are either caller-save registers or [Outgoing]
  stack slots at nonnegative offsets. *)

Definition loc_argument_acceptable (l: loc) : Prop :=
  match l with
  | R r => is_callee_save r = false
  | S Outgoing ofs ty => ofs >= 0 /\ (typealign ty | ofs)
  | _ => False
  end.

Lemma loc_arguments_rec_charact:
  forall tyl fixed ri rf ofs p,
  ofs >= 0 ->
  In p (loc_arguments_rec tyl fixed ri rf ofs) -> forall_rpair loc_argument_acceptable p.
Proof.
  set (OK := fun (l: list (rpair loc)) =>
             forall p, In p l -> forall_rpair loc_argument_acceptable p).
  set (OKF := fun (f: Z -> Z -> Z -> list (rpair loc)) =>
              forall ri rf ofs, ofs >= 0 -> OK (f ri rf ofs)).
  assert (CSI: forall r, In r int_param_regs -> is_callee_save r = false).
  { decide_goal. }
  assert (CSF: forall r, In r float_param_regs -> is_callee_save r = false).
  { decide_goal. }
  assert (ALP: forall ofs ty, ofs >= 0 -> align ofs (typesize ty) >= 0).
  { intros. 
    assert (ofs <= align ofs (typesize ty)) by (apply align_le; apply typesize_pos).
    lia. }
  assert (ALD: forall ofs ty, ofs >= 0 -> (typealign ty | align ofs (typesize ty))).
  { intros. apply Z.divide_trans with (typesize ty). apply typealign_typesize. apply align_divides. apply typesize_pos. }
  assert (ALP2: forall ofs, ofs >= 0 -> align ofs 2 >= 0).
  { intros. 
    assert (ofs <= align ofs 2) by (apply align_le; lia).
    lia. }
  assert (ALD2: forall ofs ty, ofs >= 0 -> (typealign ty | align ofs 2)).
  { intros. eapply Z.divide_trans with 2.
    exists (2 / typealign ty). destruct ty; reflexivity.
    apply align_divides. lia. }
  assert (STK: forall tyl ofs,
               ofs >= 0 -> OK (loc_arguments_stack tyl ofs)).
  { induction tyl as [ | ty tyl]; intros ofs OO; red; simpl; intros.
  - contradiction.
  - destruct H.
    + subst p. split. auto. simpl. apply Z.divide_1_l.
    + apply IHtyl with (ofs := ofs + 2). lia. auto.
  }  
  assert (A: forall ty ri rf ofs f,
             OKF f -> ofs >= 0 -> OK (stack_arg ty ri rf ofs f)).
  { intros until f; intros OF OO; red; unfold stack_arg; intros.
    destruct Archi.abi; destruct H.
  - subst p; simpl; auto.
  - eapply OF; [|eauto]. apply ALP2 in OO. lia.
  - subst p; simpl; auto.  
  - eapply OF; [|eauto]. apply (ALP ofs ty) in OO. generalize (typesize_pos ty). lia.
  }
  assert (B: forall ty ri rf ofs f,
             OKF f -> ofs >= 0 -> OK (int_arg ty ri rf ofs f)).
  { intros until f; intros OF OO; red; unfold int_arg; intros.
    destruct (list_nth_z int_param_regs ri) as [r|] eqn:NTH; [destruct H|].
  - subst p; simpl. apply CSI. eapply list_nth_z_in; eauto. 
  - eapply OF; eauto. 
  - eapply A; eauto.
  }
  assert (C: forall ty ri rf ofs f,
             OKF f -> ofs >= 0 -> OK (float_arg ty ri rf ofs f)).
  { intros until f; intros OF OO; red; unfold float_arg; intros.
    destruct (list_nth_z float_param_regs rf) as [r|] eqn:NTH; [destruct H|].
  - subst p; simpl. apply CSF. eapply list_nth_z_in; eauto.
  - eapply OF; eauto.
  - eapply A; eauto.
  }
  cut (forall tyl fixed ri rf ofs, ofs >= 0 -> OK (loc_arguments_rec tyl fixed ri rf ofs)).
  unfold OK. eauto.
  induction tyl as [ | ty1 tyl]; intros until ofs; intros OO; simpl.
- red; simpl; tauto.
- destruct (zle fixed  0).
  + apply (STK (ty1 :: tyl)); auto. 
  + unfold OKF in *; destruct ty1; eauto.
Qed.

Lemma loc_arguments_acceptable:
  forall (s: signature) (p: rpair loc),
  In p (loc_arguments s) -> forall_rpair loc_argument_acceptable p.
Proof.
  unfold loc_arguments; intros.
  eapply loc_arguments_rec_charact; eauto. lia.
Qed.

Global Hint Resolve loc_arguments_acceptable: locs.

Lemma loc_arguments_main:
  loc_arguments signature_main = nil.
Proof.
  unfold loc_arguments; reflexivity.
Qed.

(** ** Normalization of function results and parameters *)

(** According to the AAPCS64 ABI specification, "padding bits" in the return
    value of a function or in a function parameter have unpredictable
    values and must be ignored.  Consequently, we force normalization
    of return values and of function parameters when they have small
    integer types (8- and 16-bit integers), so that the top bits (the
    "padding bits") are proper sign- or zero-extensions of the small
    integer value.

    The Apple variant of the AAPCS64 requires the callee to return a normalized
    value, and the caller to pass normalized parameters, hence no
    normalization is needed.
 *)

Definition return_value_needs_normalization (t: rettype) : bool :=
  match Archi.abi with
  | Archi.Apple => false
  | Archi.AAPCS64 =>
      match t with
      | Tint8signed | Tint8unsigned | Tint16signed | Tint16unsigned => true
      | _ => false
      end
  end.

Definition parameter_needs_normalization := return_value_needs_normalization.
