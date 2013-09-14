(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Jacques-Henri Jourdan, INRIA Paris-Rocquencourt            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Formalization of floating-point numbers, using the Flocq library. *)

Require Import Axioms.
Require Import Coqlib.
Require Import Integers.
Require Import Fappli_IEEE.
Require Import Fappli_IEEE_bits.
Require Import Fcore.
Require Import Fcalc_round.
Require Import Fcalc_bracket.
Require Import Fprop_Sterbenz.
Require Import Program.

Close Scope R_scope.

Definition float := binary64. (**r the type of IEE754 doubles *)

Module Float.

Definition zero: float := B754_zero _ _ false. (**r the float [+0.0] *)

Definition eq_dec: forall (f1 f2: float), {f1 = f2} + {f1 <> f2}.
Proof.
  Ltac try_not_eq := try solve [right; congruence].
  destruct f1 as [| |? []|], f2 as [| |? []|];
  try destruct b; try destruct b0;
  try solve [left; auto]; try_not_eq.
  destruct (positive_eq_dec x x0); try_not_eq;
    subst; left; f_equal; f_equal; apply proof_irr.
  destruct (positive_eq_dec x x0); try_not_eq;
    subst; left; f_equal; f_equal; apply proof_irr.
  destruct (positive_eq_dec m m0); try_not_eq;
  destruct (Z_eq_dec e e1); try solve [right; intro H; inv H; congruence];
  subst; left; rewrite (proof_irr e0 e2); auto.
  destruct (positive_eq_dec m m0); try_not_eq;
  destruct (Z_eq_dec e e1); try solve [right; intro H; inv H; congruence];
  subst; left; rewrite (proof_irr e0 e2); auto.
Defined.

(* Transform a Nan payload to a quiet Nan payload.
   This is not part of the IEEE754 standard, but shared between all
   architectures of Compcert. *)
Program Definition transform_quiet_pl (pl:nan_pl 53) : nan_pl 53 :=
  Pos.lor pl (nat_iter 51 xO xH).
Next Obligation.
  destruct pl.
  simpl. rewrite Z.ltb_lt in *.
  assert (forall x, S (Fcore_digits.digits2_Pnat x) = Pos.to_nat (Pos.size x)).
  { induction x0; simpl; auto; rewrite IHx0; zify; omega. }
  fold (Z.of_nat (S (Fcore_digits.digits2_Pnat (Pos.lor x 2251799813685248)))).
  rewrite H, positive_nat_Z, Psize_log_inf, <- Zlog2_log_inf in *. clear H.
  change (Z.pos (Pos.lor x 2251799813685248)) with (Z.lor (Z.pos x) 2251799813685248%Z).
  rewrite Z.log2_lor by (zify; omega).
  apply Z.max_case. auto. simpl. omega.
Qed.

Lemma nan_payload_fequal:
  forall prec p1 e1 p2 e2, p1 = p2 -> (exist _ p1 e1:nan_pl prec) = exist _ p2 e2.
Proof.
  simpl; intros; subst. f_equal. apply Fcore_Zaux.eqbool_irrelevance.
Qed.

Lemma lor_idempotent:
  forall x y, Pos.lor (Pos.lor x y) y = Pos.lor x y.
Proof.
  induction x; destruct y; simpl; f_equal; auto;
  induction y; simpl; f_equal; auto.
Qed.

Lemma transform_quiet_pl_idempotent:
  forall pl, transform_quiet_pl (transform_quiet_pl pl) = transform_quiet_pl pl.
Proof.
  intros []; simpl; intros. apply nan_payload_fequal.
  simpl. apply lor_idempotent.
Qed.

(** Arithmetic operations *)

(* The Nan payload operations for neg and abs is not part of the IEEE754
   standard, but shared between all architectures of Compcert. *)
Definition neg_pl (s:bool) (pl:nan_pl 53) := (negb s, pl).
Definition abs_pl (s:bool) (pl:nan_pl 53) := (false, pl).

Definition neg: float -> float := b64_opp neg_pl. (**r opposite (change sign) *)
Definition abs (x: float): float := (**r absolute value (set sign to [+]) *)
  match x with
  | B754_nan s pl => let '(s, pl) := abs_pl s pl in B754_nan _ _ s pl
  | B754_infinity _ => B754_infinity _ _ false
  | B754_finite _ m e H => B754_finite _ _ false m e H
  | B754_zero _ => B754_zero _ _ false
  end.

Definition binary_normalize64 (m e:Z) (s:bool): float :=
  binary_normalize 53 1024 eq_refl eq_refl mode_NE m e s.

Definition binary_normalize64_correct (m e:Z) (s:bool) :=
  binary_normalize_correct 53 1024 eq_refl eq_refl mode_NE m e s.
Global Opaque binary_normalize64_correct.

Definition binary_normalize32 (m e:Z) (s:bool) : binary32 :=
  binary_normalize 24 128 eq_refl eq_refl mode_NE m e s.

Definition binary_normalize32_correct (m e:Z) (s:bool) :=
  binary_normalize_correct 24 128 eq_refl eq_refl mode_NE m e s.
Global Opaque binary_normalize32_correct.

(* The Nan payload operations for single <-> double conversions are not part of
   the IEEE754 standard, but shared between all architectures of Compcert. *)
Definition floatofbinary32_pl (s:bool) (pl:nan_pl 24) : (bool * nan_pl 53).
  refine (s, transform_quiet_pl (exist _ (Pos.shiftl_nat (proj1_sig pl) 29) _)).
  abstract (
    destruct pl; unfold proj1_sig, Pos.shiftl_nat, nat_iter, Fcore_digits.digits2_Pnat;
    fold (Fcore_digits.digits2_Pnat x);
    rewrite Z.ltb_lt in *;
    zify; omega).
Defined.

Definition binary32offloat_pl (s:bool) (pl:nan_pl 53) : (bool * nan_pl 24).
  refine (s, exist _ (Pos.shiftr_nat (proj1_sig (transform_quiet_pl pl)) 29) _).
  abstract (
    destruct (transform_quiet_pl pl); unfold proj1_sig, Pos.shiftr_nat, nat_iter;
    rewrite Z.ltb_lt in *;
    assert (forall x, Fcore_digits.digits2_Pnat (Pos.div2 x) =
                      (Fcore_digits.digits2_Pnat x - 1)%nat) by (destruct x0; simpl; zify; omega);
    rewrite !H, <- !NPeano.Nat.sub_add_distr; zify; omega).
Defined.

Definition floatofbinary32 (f: binary32) : float := (**r single precision embedding in double precision *)
  match f with
    | B754_nan s pl => let '(s, pl) := floatofbinary32_pl s pl in B754_nan _ _ s pl
    | B754_infinity s => B754_infinity _ _ s
    | B754_zero s => B754_zero _ _ s
    | B754_finite s m e _ =>
      binary_normalize64 (cond_Zopp s (Zpos m)) e s
  end.

Definition binary32offloat (f: float) : binary32 := (**r conversion to single precision *)
  match f with
    | B754_nan s pl => let '(s, pl) := binary32offloat_pl s pl in B754_nan _ _ s pl
    | B754_infinity s => B754_infinity _ _ s
    | B754_zero s => B754_zero _ _ s
    | B754_finite s m e _ =>
      binary_normalize32 (cond_Zopp s (Zpos m)) e s
  end.

Definition singleoffloat (f: float): float := (**r conversion to single precision, embedded in double *)
  floatofbinary32 (binary32offloat f).

Definition Zoffloat (f:float): option Z := (**r conversion to Z *)
  match f with
    | B754_finite s m (Zpos e) _ => Some (cond_Zopp s (Zpos m) * Zpower_pos radix2 e)
    | B754_finite s m 0 _ => Some (cond_Zopp s (Zpos m))
    | B754_finite s m (Zneg e) _ => Some (cond_Zopp s (Zpos m / Zpower_pos radix2 e))
    | B754_zero _ => Some 0
    | _ => None
  end.

Definition intoffloat (f:float): option int := (**r conversion to signed 32-bit int *)
  match Zoffloat f with
    | Some n =>
      if Zle_bool Int.min_signed n && Zle_bool n Int.max_signed then
        Some (Int.repr n)
      else
        None
    | None => None
  end.

Definition intuoffloat (f:float): option int := (**r conversion to unsigned 32-bit int *)
  match Zoffloat f with
    | Some n =>
      if Zle_bool 0 n && Zle_bool n Int.max_unsigned then
        Some (Int.repr n)
      else
        None
    | None => None
  end.

Definition longoffloat (f:float): option int64 := (**r conversion to signed 64-bit int *)
  match Zoffloat f with
    | Some n =>
      if Zle_bool Int64.min_signed n && Zle_bool n Int64.max_signed then
        Some (Int64.repr n)
      else
        None
    | None => None
  end.

Definition longuoffloat (f:float): option int64 := (**r conversion to unsigned 64-bit int *)
  match Zoffloat f with
    | Some n =>
      if Zle_bool 0 n && Zle_bool n Int64.max_unsigned then
        Some (Int64.repr n)
      else
        None
    | None => None
  end.

(* Functions used to parse floats *)
Program Definition build_from_parsed
  (prec:Z) (emax:Z) (prec_gt_0 :Prec_gt_0 prec) (Hmax:prec < emax)
  (base:positive) (intPart:positive) (expPart:Z) :=
  match expPart return _ with
    | Z0 =>
      binary_normalize prec emax prec_gt_0 Hmax mode_NE (Zpos intPart) Z0 false
    | Zpos p =>
      binary_normalize prec emax prec_gt_0 Hmax mode_NE ((Zpos intPart) * Zpower_pos (Zpos base) p) Z0 false
    | Zneg p =>
      let exp := Zpower_pos (Zpos base) p in
      match exp return 0 < exp -> _ with
        | Zneg _ | Z0 => _
        | Zpos p =>
          fun _ =>
          FF2B prec emax _ (proj1 (Bdiv_correct_aux prec emax prec_gt_0 Hmax mode_NE false intPart Z0 false p Z0))
      end _
  end.
Next Obligation.
apply Zpower_pos_gt_0.
reflexivity.
Qed.

Definition build_from_parsed64 (base:positive) (intPart:positive) (expPart:Z) : float :=
  build_from_parsed 53 1024 eq_refl eq_refl  base intPart expPart.

Definition build_from_parsed32 (base:positive) (intPart:positive) (expPart:Z) : float :=
  floatofbinary32 (build_from_parsed 24 128 eq_refl eq_refl  base intPart expPart).

Definition floatofint (n:int): float := (**r conversion from signed 32-bit int *)
  binary_normalize64 (Int.signed n) 0 false.
Definition floatofintu (n:int): float:= (**r conversion from unsigned 32-bit int *)
  binary_normalize64 (Int.unsigned n) 0 false.

Definition floatoflong (n:int64): float := (**r conversion from signed 64-bit int *)
  binary_normalize64 (Int64.signed n) 0 false.
Definition floatoflongu (n:int64): float:= (**r conversion from unsigned 64-bit int *)
  binary_normalize64 (Int64.unsigned n) 0 false.

Definition singleofint (n:int): float := (**r conversion from signed 32-bit int to single-precision float *)
  floatofbinary32 (binary_normalize32 (Int.signed n) 0 false).
Definition singleofintu (n:int): float:= (**r conversion from unsigned 32-bit int to single-precision float *)
  floatofbinary32 (binary_normalize32 (Int.unsigned n) 0 false).

Definition singleoflong (n:int64): float := (**r conversion from signed 64-bit int to single-precision float *)
  floatofbinary32 (binary_normalize32 (Int64.signed n) 0 false).
Definition singleoflongu (n:int64): float:= (**r conversion from unsigned 64-bit int to single-precision float *)
  floatofbinary32 (binary_normalize32 (Int64.unsigned n) 0 false).

(* The Nan payload operations for two-argument arithmetic operations are not part of
   the IEEE754 standard, but all architectures of Compcert share a similar
   NaN behavior, parameterized by:
- a "default" payload which occurs when an operation generates a NaN from
  non-NaN arguments;
- a choice function determining which of the payload arguments to choose,
  when an operation is given two NaN arguments. *)

Parameter default_pl : bool*nan_pl 53.
Parameter choose_binop_pl : bool -> nan_pl 53 -> bool -> nan_pl 53 -> bool.

Definition binop_pl (x y: binary64) : bool*nan_pl 53 :=
  match x, y with
  | B754_nan s1 pl1, B754_nan s2 pl2 =>
      if choose_binop_pl s1 pl1 s2 pl2
      then (s2, transform_quiet_pl pl2)
      else (s1, transform_quiet_pl pl1)
  | B754_nan s1 pl1, _ => (s1, transform_quiet_pl pl1)
  | _, B754_nan s2 pl2 => (s2, transform_quiet_pl pl2)
  | _, _ => default_pl
  end.

Definition add: float -> float -> float := b64_plus binop_pl mode_NE. (**r addition *)
Definition sub: float -> float -> float := b64_minus binop_pl mode_NE. (**r subtraction *)
Definition mul: float -> float -> float := b64_mult binop_pl mode_NE. (**r multiplication *)
Definition div: float -> float -> float := b64_div binop_pl mode_NE. (**r division *)

Definition order_float (f1 f2:float): option Datatypes.comparison :=
  match f1, f2 with
    | B754_nan _ _,_ | _,B754_nan _ _ => None
    | B754_infinity true, B754_infinity true
    | B754_infinity false, B754_infinity false => Some Eq
    | B754_infinity true, _ => Some Lt
    | B754_infinity false, _ => Some Gt
    | _, B754_infinity true => Some Gt
    | _, B754_infinity false => Some Lt
    | B754_finite true _ _ _, B754_zero _ => Some Lt
    | B754_finite false _ _ _, B754_zero _ => Some Gt
    | B754_zero _, B754_finite true _ _ _ => Some Gt
    | B754_zero _, B754_finite false _ _ _ => Some Lt
    | B754_zero _, B754_zero _ => Some Eq
    | B754_finite s1 m1 e1 _, B754_finite s2 m2 e2 _ =>
      match s1, s2 with
        | true, false => Some Lt
        | false, true => Some Gt
        | false, false =>
          match Zcompare e1 e2 with
            | Lt => Some Lt
            | Gt => Some Gt
            | Eq => Some (Pcompare m1 m2 Eq)
          end
        | true, true =>
          match Zcompare e1 e2 with
            | Lt => Some Gt
            | Gt => Some Lt
            | Eq => Some (CompOpp (Pcompare m1 m2 Eq))
          end
      end
  end.

Definition cmp (c:comparison) (f1 f2:float) : bool := (**r comparison *)
  match c with
  | Ceq =>
      match order_float f1 f2 with Some Eq => true | _ => false end
  | Cne =>
      match order_float f1 f2 with Some Eq => false | _ => true end
  | Clt =>
      match order_float f1 f2 with Some Lt => true | _ => false end
  | Cle =>
      match order_float f1 f2 with Some(Lt|Eq) => true | _ => false end
  | Cgt =>
      match order_float f1 f2 with Some Gt => true | _ => false end
  | Cge =>
      match order_float f1 f2 with Some(Gt|Eq) => true | _ => false end
  end.

(** Conversions between floats and their concrete in-memory representation
    as a sequence of 64 bits (double precision) or 32 bits (single precision). *)

Definition bits_of_double (f: float): int64 := Int64.repr (bits_of_b64 f).
Definition double_of_bits (b: int64): float := b64_of_bits (Int64.unsigned b).

Definition bits_of_single (f: float) : int := Int.repr (bits_of_b32 (binary32offloat f)).
Definition single_of_bits (b: int): float := floatofbinary32 (b32_of_bits (Int.unsigned b)).

Definition from_words (hi lo: int) : float := double_of_bits (Int64.ofwords hi lo).

(** Below are the only properties of floating-point arithmetic that we
  rely on in the compiler proof. *)

(** Some tactics **)

Ltac compute_this val :=
  let x := fresh in set val as x in *; vm_compute in x; subst x.

Ltac smart_omega :=
  simpl radix_val in *; simpl Zpower in *;
  compute_this Int.modulus; compute_this Int.half_modulus;
  compute_this Int.max_unsigned;
  compute_this Int.min_signed; compute_this Int.max_signed;
  compute_this Int64.modulus; compute_this Int64.half_modulus;
  compute_this Int64.max_unsigned;
  compute_this (Zpower_pos 2 1024); compute_this (Zpower_pos 2 53); compute_this (Zpower_pos 2 52);
  zify; omega.

Lemma floatofbinary32_exact :
  forall f, is_finite_strict _ _ f = true ->
    is_finite_strict _ _ (floatofbinary32 f) = true /\ B2R _ _ f = B2R _ _ (floatofbinary32 f).
Proof.
  destruct f as [ | | |s m e]; try discriminate; intro.
  pose proof (binary_normalize64_correct (cond_Zopp s (Zpos m)) e s).
  match goal with [H0:if Rlt_bool (Rabs ?x) _ then _ else _ |- _ /\ ?y = _] => assert (x=y)%R end.
  apply round_generic; [now apply valid_rnd_round_mode|].
  apply (generic_inclusion_ln_beta _ (FLT_exp (3 - 128 - 24) 24)).
  intro; eapply Zle_trans; [apply Zle_max_compat_l | apply Zle_max_compat_r]; omega.
  apply generic_format_canonic; apply canonic_canonic_mantissa; apply (proj1 (andb_prop _ _ e0)).
  rewrite H1, Rlt_bool_true in H0; intuition; unfold floatofbinary32, binary_normalize64.
  match goal with [ |- _ _ _ ?x = true ] => destruct x end; try discriminate.
  symmetry in H2; apply F2R_eq_0_reg in H2; destruct s; discriminate.
  reflexivity.
  eapply Rlt_trans.
  unfold B2R; rewrite <- F2R_Zabs, abs_cond_Zopp; eapply bounded_lt_emax; now apply e0.
  now apply bpow_lt.
Qed.

Lemma binary32offloatofbinary32_num :
  forall f, is_nan _ _ f = false ->
            binary32offloat (floatofbinary32 f) = f.
Proof.
  intros f Hnan; pose proof (floatofbinary32_exact f); destruct f as [ | | |s m e]; try reflexivity.
  discriminate.
  specialize (H eq_refl); destruct H.
  destruct (floatofbinary32 (B754_finite 24 128 s m e e0)) as [ | | |s1 m1 e1]; try discriminate.
  unfold binary32offloat.
  pose proof (binary_normalize32_correct (cond_Zopp s1 (Zpos m1)) e1 s1).
  unfold B2R at 2 in H0; cbv iota zeta beta in H0; rewrite <- H0, round_generic in H1.
  rewrite Rlt_bool_true in H1.
  unfold binary_normalize32.
  apply B2R_inj; intuition; match goal with [|- _ _ _ ?f = true] => destruct f end; try discriminate.
  symmetry in H2; apply F2R_eq_0_reg in H2; destruct s; discriminate.
  reflexivity.
  unfold B2R; rewrite <- F2R_Zabs, abs_cond_Zopp; eapply bounded_lt_emax; apply e0.
  now apply valid_rnd_round_mode.
  now apply generic_format_B2R.
Qed.

Lemma floatofbinary32offloatofbinary32_pl:
  forall s pl,
    prod_rect (fun _ => _) floatofbinary32_pl (prod_rect (fun _ => _) binary32offloat_pl (floatofbinary32_pl s pl)) = floatofbinary32_pl s pl.
Proof.
  destruct pl. unfold binary32offloat_pl, floatofbinary32_pl.
  unfold transform_quiet_pl, proj1_sig. simpl.
  f_equal. apply nan_payload_fequal.
  unfold Pos.shiftr_nat. simpl.
  rewrite !lor_idempotent. reflexivity.
Qed.

Lemma floatofbinary32offloatofbinary32 :
  forall f, floatofbinary32 (binary32offloat (floatofbinary32 f)) = floatofbinary32 f.
Proof.
  destruct f; try (rewrite binary32offloatofbinary32_num; tauto).
  unfold floatofbinary32, binary32offloat.
  rewrite <- floatofbinary32offloatofbinary32_pl at 2.
  reflexivity.
Qed.

Lemma binary32offloatofbinary32offloat_pl:
  forall s pl,
    prod_rect (fun _ => _) binary32offloat_pl (prod_rect  (fun _ => _) floatofbinary32_pl (binary32offloat_pl s pl)) = binary32offloat_pl s pl.
Proof.
  destruct pl. unfold binary32offloat_pl, floatofbinary32_pl. unfold prod_rect.
  f_equal. apply nan_payload_fequal.
  rewrite transform_quiet_pl_idempotent.
  unfold transform_quiet_pl, proj1_sig.
  change 51 with (29+22).
  clear - x. revert x. unfold Pos.shiftr_nat, Pos.shiftl_nat.
  induction (29)%nat. intro. simpl. apply lor_idempotent.
  intro.
  rewrite !nat_iter_succ_r with (f:=Pos.div2).
  destruct x; simpl; try apply IHn.
  clear IHn. induction n. reflexivity.
  rewrite !nat_iter_succ_r with (f:=Pos.div2). auto.
Qed.

Lemma binary32offloatofbinary32offloat :
  forall f, binary32offloat (floatofbinary32 (binary32offloat f)) = binary32offloat f.
Proof.
  destruct f; try (rewrite binary32offloatofbinary32_num; simpl; tauto).
  unfold floatofbinary32, binary32offloat.
  rewrite <- binary32offloatofbinary32offloat_pl at 2.
  reflexivity.
  rewrite binary32offloatofbinary32_num; simpl. auto.
  unfold binary_normalize32.
  pose proof (binary_normalize32_correct (cond_Zopp b (Z.pos m)) e b).
  destruct binary_normalize; auto. simpl in H.
  destruct Rlt_bool in H. intuition.
  unfold binary_overflow in H. destruct n.
  destruct overflow_to_inf in H; discriminate.
Qed.

Theorem singleoffloat_idem:
  forall f, singleoffloat (singleoffloat f) = singleoffloat f.
Proof.
  intros; unfold singleoffloat; rewrite binary32offloatofbinary32offloat; reflexivity.
Qed.

Theorem singleoflong_idem:
  forall n, singleoffloat (singleoflong n) = singleoflong n.
Proof.
  intros; unfold singleoffloat, singleoflong. rewrite floatofbinary32offloatofbinary32; reflexivity.
Qed.

Theorem singleoflongu_idem:
  forall n, singleoffloat (singleoflongu n) = singleoflongu n.
Proof.
  intros; unfold singleoffloat, singleoflongu. rewrite floatofbinary32offloatofbinary32; reflexivity.
Qed.

Definition is_single (f: float) : Prop := exists s, f = floatofbinary32 s.

Theorem singleoffloat_is_single:
  forall f, is_single (singleoffloat f).
Proof.
  intros. exists (binary32offloat f); auto.
Qed.

Theorem singleoffloat_of_single:
  forall f, is_single f -> singleoffloat f = f.
Proof.
  intros. destruct H as [s EQ]. subst f. unfold singleoffloat.
  apply floatofbinary32offloatofbinary32.
Qed.

Theorem is_single_dec: forall f, {is_single f} + {~is_single f}.
Proof.
  intros. case (eq_dec (singleoffloat f) f); intros.
  unfold singleoffloat in e. left. exists (binary32offloat f). auto.
  right; red; intros; elim n. apply singleoffloat_of_single; auto.
Defined.

(** Commutativity properties of addition and multiplication. *)

Theorem add_commut:
  forall x y, is_nan _ _ x = false \/ is_nan _ _ y = false -> add x y = add y x.
Proof.
  intros x y NAN. unfold add, b64_plus. 
  pose proof (Bplus_correct 53 1024 eq_refl eq_refl binop_pl mode_NE x y).
  pose proof (Bplus_correct 53 1024 eq_refl eq_refl binop_pl mode_NE y x).
  unfold Bplus in *; destruct x; destruct y; auto.
- rewrite (eqb_sym b0 b). destruct (eqb b b0) eqn:EQB; auto. f_equal; apply eqb_prop; auto.
- rewrite (eqb_sym b0 b). destruct (eqb b b0) eqn:EQB.
  f_equal; apply eqb_prop; auto.
  auto.
- simpl in NAN; intuition congruence.
- exploit H; auto. clear H. exploit H0; auto. clear H0. 
  set (x := B754_finite 53 1024 b0 m0 e1 e2). 
  set (rx := B2R 53 1024 x).
  set (y := B754_finite 53 1024 b m e e0).
  set (ry := B2R 53 1024 y).
  rewrite (Rplus_comm ry rx). destruct Rlt_bool. 
  intros (A1 & A2 & A3) (B1 & B2 & B3).
  apply B2R_Bsign_inj; auto. rewrite <- B1 in A1. auto. 
  rewrite Z.add_comm. rewrite Z.min_comm. auto.
  intros (A1 & A2) (B1 & B2). apply B2FF_inj. rewrite B2 in B1. rewrite <- B1 in A1. auto. 
Qed.

Theorem mul_commut:
  forall x y, is_nan _ _ x = false \/ is_nan _ _ y = false -> mul x y = mul y x.
Proof.
  intros x y NAN. unfold mul, b64_mult. 
  pose proof (Bmult_correct 53 1024 eq_refl eq_refl binop_pl mode_NE x y).
  pose proof (Bmult_correct 53 1024 eq_refl eq_refl binop_pl mode_NE y x).
  unfold Bmult in *; destruct x; destruct y; auto.
- f_equal. apply xorb_comm. 
- f_equal. apply xorb_comm. 
- f_equal. apply xorb_comm. 
- f_equal. apply xorb_comm. 
- simpl in NAN. intuition congruence.
- f_equal. apply xorb_comm. 
- f_equal. apply xorb_comm. 
- set (x := B754_finite 53 1024 b0 m0 e1 e2) in *. 
  set (rx := B2R 53 1024 x) in *.
  set (y := B754_finite 53 1024 b m e e0) in *.
  set (ry := B2R 53 1024 y) in *.
  rewrite (Rmult_comm ry rx) in *. destruct Rlt_bool. 
  destruct H as (A1 & A2 & A3); destruct H0 as (B1 & B2 & B3).
  apply B2R_Bsign_inj; auto. rewrite <- B1 in A1. auto. 
  rewrite ! Bsign_FF2B. f_equal. f_equal. apply xorb_comm. apply Pos.mul_comm. apply Z.add_comm.
  apply B2FF_inj. etransitivity. eapply H. rewrite xorb_comm. auto. 
Qed.

(** Properties of comparisons. *)

Theorem order_float_finite_correct:
  forall f1 f2, is_finite _ _ f1 = true -> is_finite _ _ f2 = true ->
    match order_float f1 f2 with
      | Some c => Rcompare (B2R _ _ f1) (B2R _ _ f2) = c
      | None => False
    end.
Proof.
  Ltac apply_Rcompare :=
    match goal with
      | [ |- Rcompare _ _ = Lt ] => apply Rcompare_Lt
      | [ |- Rcompare _ _ = Eq ] => apply Rcompare_Eq
      | [ |- Rcompare _ _ = Gt ] => apply Rcompare_Gt
    end.
  unfold order_float; intros.
  destruct f1, f2; try discriminate; unfold B2R, F2R, Fnum, Fexp, cond_Zopp;
    try (replace 0%R with (Z2R 0 * bpow radix2 e)%R by (simpl Z2R; ring);
         rewrite Rcompare_mult_r by (apply bpow_gt_0); rewrite Rcompare_Z2R).
  apply_Rcompare; reflexivity.
  destruct b0; reflexivity.
  destruct b; reflexivity.
  clear H H0.
  apply andb_prop in e0; destruct e0; apply (canonic_canonic_mantissa _ _ false) in H.
  apply andb_prop in e2; destruct e2; apply (canonic_canonic_mantissa _ _ false) in H1.
  pose proof (Zcompare_spec e e1); unfold canonic, Fexp in H1, H.
  assert (forall m1 m2 e1 e2,
    let x := (Z2R (Zpos m1) * bpow radix2 e1)%R in
    let y := (Z2R (Zpos m2) * bpow radix2 e2)%R in
    canonic_exp radix2 (FLT_exp (3-1024-53) 53) x < canonic_exp radix2 (FLT_exp (3-1024-53) 53) y -> (x < y)%R).
  intros; apply Rnot_le_lt; intro; apply (ln_beta_le radix2) in H5.
  apply (fexp_monotone 53 1024) in H5; unfold canonic_exp in H4; omega.
  apply Rmult_gt_0_compat; [apply (Z2R_lt 0); reflexivity|now apply bpow_gt_0].
  assert (forall m1 m2 e1 e2, (Z2R (- Zpos m1) * bpow radix2 e1 < Z2R (Zpos m2) * bpow radix2 e2)%R).
  intros; apply (Rlt_trans _ 0%R).
  replace 0%R with (0*bpow radix2 e0)%R by ring; apply Rmult_lt_compat_r;
    [apply bpow_gt_0; reflexivity|now apply (Z2R_lt _ 0)].
  apply Rmult_gt_0_compat; [apply (Z2R_lt 0); reflexivity|now apply bpow_gt_0].
  destruct b, b0; try (now apply_Rcompare; apply H5); inversion H3;
    try (apply_Rcompare; apply H4; rewrite H, H1 in H7; assumption);
    try (apply_Rcompare; do 2 rewrite Z2R_opp, Ropp_mult_distr_l_reverse;
      apply Ropp_lt_contravar; apply H4; rewrite H, H1 in H7; assumption);
    rewrite H7, Rcompare_mult_r, Rcompare_Z2R by (apply bpow_gt_0); reflexivity.
Qed.

Theorem cmp_swap:
  forall c x y, Float.cmp (swap_comparison c) x y = Float.cmp c y x.
Proof.
  destruct c, x, y; simpl; try destruct b; try destruct b0; try reflexivity;
  rewrite <- (Zcompare_antisym e e1); destruct (e ?= e1); try reflexivity;
  change Eq with (CompOpp Eq); rewrite <- (Pcompare_antisym m m0 Eq);
    simpl; destruct (Pcompare m m0 Eq); reflexivity.
Qed.

Theorem cmp_ne_eq:
  forall f1 f2, cmp Cne f1 f2 = negb (cmp Ceq f1 f2).
Proof.
  unfold cmp; intros; destruct (order_float f1 f2) as [ [] | ]; reflexivity.
Qed.

Theorem cmp_lt_eq_false:
  forall f1 f2, cmp Clt f1 f2 = true -> cmp Ceq f1 f2 = true -> False.
Proof.
  unfold cmp; intros; destruct (order_float f1 f2) as [ [] | ]; discriminate.
Qed.

Theorem cmp_le_lt_eq:
  forall f1 f2, cmp Cle f1 f2 = cmp Clt f1 f2 || cmp Ceq f1 f2.
Proof.
  unfold cmp; intros; destruct (order_float f1 f2) as [ [] | ]; reflexivity.
Qed.

Corollary cmp_gt_eq_false:
  forall x y, cmp Cgt x y = true -> cmp Ceq x y = true -> False.
Proof.
  intros; rewrite <- cmp_swap in H; rewrite <- cmp_swap in H0;
  eapply cmp_lt_eq_false; now eauto.
Qed.

Corollary cmp_ge_gt_eq:
  forall f1 f2, cmp Cge f1 f2 = cmp Cgt f1 f2 || cmp Ceq f1 f2.
Proof.
  intros.
  change Cge with (swap_comparison Cle); change Cgt with (swap_comparison Clt);
    change Ceq with (swap_comparison Ceq).
  repeat rewrite cmp_swap.
  now apply cmp_le_lt_eq.
Qed.

Theorem cmp_lt_gt_false:
  forall f1 f2, cmp Clt f1 f2 = true -> cmp Cgt f1 f2 = true -> False.
Proof.
  unfold cmp; intros; destruct (order_float f1 f2) as [ [] | ]; discriminate.
Qed.

(** Properties of conversions to/from in-memory representation.
  The double-precision conversions are bijective (one-to-one).
  The single-precision conversions lose precision exactly
  as described by [singleoffloat] rounding. *)

Theorem double_of_bits_of_double:
  forall f, double_of_bits (bits_of_double f) = f.
Proof.
  intros; unfold double_of_bits, bits_of_double, bits_of_b64, b64_of_bits.
  rewrite Int64.unsigned_repr, binary_float_of_bits_of_binary_float; [reflexivity|].
  destruct f.
  simpl; try destruct b; vm_compute; split; congruence.
  simpl; try destruct b; vm_compute; split; congruence.
  destruct n as [p Hp].
  simpl. rewrite Z.ltb_lt in Hp.
  apply Zlt_succ_le with (m:=52) in Hp.
  apply Zpower_le with (r:=radix2) in Hp.
  edestruct Fcore_digits.digits2_Pnat_correct.
  rewrite Zpower_nat_Z in H0.
  eapply Z.lt_le_trans in Hp; eauto.
  unfold join_bits; destruct b.
  compute_this ((2 ^ 11 + 2047) * 2 ^ 52). smart_omega.
  compute_this ((0 + 2047) * 2 ^ 52). smart_omega.
  unfold bits_of_binary_float, join_bits.
  destruct (andb_prop _ _ e0); apply Zle_bool_imp_le in H0; apply Zeq_bool_eq in H; unfold FLT_exp in H.
  match goal with [H:Zmax ?x ?y = e|-_] => pose proof (Zle_max_l x y); pose proof (Zle_max_r x y) end.
  rewrite H, Fcalc_digits.Z_of_nat_S_digits2_Pnat in *.
  lapply (Fcalc_digits.Zpower_gt_Zdigits radix2 53 (Zpos m)). intro.
  unfold radix2, radix_val, Zabs in H3.
  pose proof (Zle_bool_spec (2 ^ 52) (Zpos m)).
  assert (Zpos m > 0); [vm_compute; exact eq_refl|].
  compute_this (2^11); compute_this (2^(11-1)).
  inversion H4; fold (2^52) in *; destruct H6; destruct b; now smart_omega.
  change Fcalc_digits.radix2 with radix2 in H1; omega.
Qed.

Theorem single_of_bits_of_single:
  forall f, single_of_bits (bits_of_single f) = singleoffloat f.
Proof.
  intros; unfold single_of_bits, bits_of_single, bits_of_b32, b32_of_bits.
  rewrite Int.unsigned_repr, binary_float_of_bits_of_binary_float; [reflexivity|].
  destruct (binary32offloat f).
  simpl; try destruct b; vm_compute; split; congruence.
  simpl; try destruct b; vm_compute; split; congruence.
  destruct n as [p Hp].
  simpl. rewrite Z.ltb_lt in Hp.
  apply Zlt_succ_le with (m:=23) in Hp.
  apply Zpower_le with (r:=radix2) in Hp.
  edestruct Fcore_digits.digits2_Pnat_correct.
  rewrite Zpower_nat_Z in H0.
  eapply Z.lt_le_trans in Hp; eauto.
  compute_this (radix2^23).
  unfold join_bits; destruct b.
  compute_this ((2 ^ 8 + 255) * 2 ^ 23). smart_omega.
  compute_this ((0 + 255) * 2 ^ 23). smart_omega.
  unfold bits_of_binary_float, join_bits.
  destruct (andb_prop _ _ e0); apply Zle_bool_imp_le in H0; apply Zeq_bool_eq in H.
  unfold FLT_exp in H.
  match goal with [H:Zmax ?x ?y = e|-_] => pose proof (Zle_max_l x y); pose proof (Zle_max_r x y) end.
  rewrite H, Fcalc_digits.Z_of_nat_S_digits2_Pnat in *.
  lapply (Fcalc_digits.Zpower_gt_Zdigits radix2 24 (Zpos m)). intro.
  unfold radix2, radix_val, Zabs in H3.
  pose proof (Zle_bool_spec (2 ^ 23) (Zpos m)).
  compute_this (2^23); compute_this (2^24); compute_this (2^8); compute_this (2^(8-1)).
  assert (Zpos m > 0); [exact eq_refl|].
  inversion H4; destruct b; now smart_omega.
  change Fcalc_digits.radix2 with radix2 in H1; omega.
Qed.

Theorem bits_of_singleoffloat:
  forall f, bits_of_single (singleoffloat f) = bits_of_single f.
Proof.
  intro; unfold singleoffloat, bits_of_single; rewrite binary32offloatofbinary32offloat; reflexivity.
Qed.

Theorem singleoffloat_of_bits:
  forall b, singleoffloat (single_of_bits b) = single_of_bits b.
Proof.
  intro; unfold singleoffloat, single_of_bits; rewrite floatofbinary32offloatofbinary32; reflexivity.
Qed.

Theorem single_of_bits_is_single:
  forall b, is_single (single_of_bits b).
Proof.
  intros. exists (b32_of_bits (Int.unsigned b)); auto.
Qed.

(** Conversions between floats and unsigned ints can be defined
  in terms of conversions between floats and signed ints.
  (Most processors provide only the latter, forcing the compiler
  to emulate the former.)   *)

Definition ox8000_0000 := Int.repr Int.half_modulus.  (**r [0x8000_0000] *)

Lemma round_exact:
  forall n, -2^53 < n < 2^53 ->
    round radix2 (FLT_exp (3 - 1024 - 53) 53)
      (round_mode mode_NE) (Z2R n) = Z2R n.
Proof.
  intros; rewrite round_generic; [reflexivity|now apply valid_rnd_round_mode|].
  apply generic_format_FLT; exists (Float radix2 n 0).
  unfold F2R, Fnum, Fexp, bpow; rewrite Rmult_1_r; intuition.
  pose proof (Zabs_spec n); now smart_omega.
Qed.

Lemma binary_normalize64_exact:
  forall n, -2^53 < n < 2^53 ->
    B2R _ _ (binary_normalize64 n 0 false) = Z2R n /\
    is_finite _ _ (binary_normalize64 n 0 false) = true.
Proof.
  intros; pose proof (binary_normalize64_correct n 0 false).
  unfold F2R, Fnum, Fexp, bpow in H0; rewrite Rmult_1_r, round_exact, Rlt_bool_true in H0; try now intuition.
  rewrite <- Z2R_abs; apply Z2R_lt; pose proof (Zabs_spec n); now smart_omega.
Qed.

Theorem floatofintu_floatofint_1:
  forall x,
  Int.ltu x ox8000_0000 = true ->
  floatofintu x = floatofint x.
Proof.
  unfold floatofintu, floatofint, Int.signed, Int.ltu; intro.
  change (Int.unsigned ox8000_0000) with Int.half_modulus.
  destruct (zlt (Int.unsigned x) Int.half_modulus); now intuition.
Qed.

Theorem floatofintu_floatofint_2:
  forall x,
  Int.ltu x ox8000_0000 = false ->
  floatofintu x = add (floatofint (Int.sub x ox8000_0000))
                      (floatofintu ox8000_0000).
Proof.
  unfold floatofintu, floatofint, Int.signed, Int.ltu, Int.sub; intros.
  pose proof (Int.unsigned_range x).
  compute_this (Int.unsigned ox8000_0000).
  destruct (zlt (Int.unsigned x) 2147483648); try  discriminate.
  rewrite Int.unsigned_repr by smart_omega.
  destruct (zlt ((Int.unsigned x) - 2147483648) Int.half_modulus).
  unfold add, b64_plus.
  match goal with [|- _ = Bplus _ _ _ _ _ _ ?x ?y] =>
    pose proof (Bplus_correct 53 1024 eq_refl eq_refl binop_pl mode_NE x y) end.
  do 2 rewrite (fun x H => proj1 (binary_normalize64_exact x H)) in H1 by smart_omega.
  do 2 rewrite (fun x H => proj2 (binary_normalize64_exact x H)) in H1 by smart_omega.
  rewrite <- Z2R_plus, round_exact in H1 by smart_omega.
  rewrite Rlt_bool_true in H1;
    replace (Int.unsigned x - 2147483648 + 2147483648) with (Int.unsigned x) in * by ring.
  apply B2R_inj.
  destruct (binary_normalize64_exact (Int.unsigned x)); [now smart_omega|].
  match goal with [|- _ _ _ ?f = _] => destruct f end; intuition.
  exfalso; simpl in H2; change 0%R with (Z2R 0) in H2; apply eq_Z2R in H2; omega.
  try (change (53 ?= 1024) with Lt in H1).  (* for Coq 8.4 *)
  simpl Zcompare in *.
  match goal with [|- _ _ _ ?f = _] => destruct f end; intuition.
  exfalso; simpl in H0; change 0%R with (Z2R 0) in H0; apply eq_Z2R in H0; omega.
  rewrite (fun x H => proj1 (binary_normalize64_exact x H)) by smart_omega; now intuition.
  rewrite <- Z2R_Zpower, <- Z2R_abs by omega; apply Z2R_lt;
    pose proof (Zabs_spec (Int.unsigned x)); now smart_omega.
  exfalso; now smart_omega.
Qed.

Lemma Zoffloat_correct:
  forall f,
    match Zoffloat f with
      | Some n =>
        is_finite _ _ f = true /\
        Z2R n = round radix2 (FIX_exp 0) (round_mode mode_ZR) (B2R _ _ f)
      | None =>
        is_finite _ _ f = false
    end.
Proof.
  destruct f; try now intuition.
  simpl B2R. rewrite round_0. now intuition. now apply valid_rnd_round_mode.
  destruct e. split. reflexivity.
  rewrite round_generic. symmetry. now apply Rmult_1_r.
  now apply valid_rnd_round_mode.
  apply generic_format_FIX. exists (Float radix2 (cond_Zopp b (Zpos m)) 0). split; reflexivity.
  split; [reflexivity|].
  rewrite round_generic, Z2R_mult, Z2R_Zpower_pos, <- bpow_powerRZ;
    [reflexivity|now apply valid_rnd_round_mode|apply generic_format_F2R; discriminate].
  rewrite (inbetween_float_ZR_sign _ _ _ ((Zpos m) / Zpower_pos radix2 p)
    (new_location (Zpower_pos radix2 p) (Zpos m mod Zpower_pos radix2 p) loc_Exact)).
  unfold B2R, F2R, Fnum, Fexp, canonic_exp, bpow, FIX_exp, Zoffloat, radix2, radix_val.
  pose proof (Rlt_bool_spec (Z2R (cond_Zopp b (Zpos m)) * / Z2R (Zpower_pos 2 p)) 0).
  inversion H; rewrite <- (Rmult_0_l (bpow radix2 (Zneg p))) in H1.
  apply Rmult_lt_reg_r in H1. apply (lt_Z2R _ 0) in H1.
  destruct b; [split; [|ring_simplify];reflexivity|discriminate].
  now apply bpow_gt_0.
  apply Rmult_le_reg_r in H1. apply (le_Z2R 0) in H1.
  destruct b; [destruct H1|split; [|ring_simplify]]; reflexivity.
  now apply (bpow_gt_0 radix2 (Zneg p)).
  unfold canonic_exp, FIX_exp; replace 0 with (Zneg p + Zpos p) by apply Zplus_opp_r.
  apply (inbetween_float_new_location radix2 _ _ _ _ (Zpos p)); [reflexivity|].
  apply inbetween_Exact; unfold B2R, F2R, Fnum, Fexp; destruct b.
  rewrite  Rabs_left; [simpl; ring_simplify; reflexivity|].
  replace 0%R with (0*(bpow radix2 (Zneg p)))%R by ring; apply Rmult_gt_compat_r.
  now apply bpow_gt_0.
  apply (Z2R_lt _ 0); reflexivity.
  apply Rabs_right; replace 0%R with (0*(bpow radix2 (Zneg p)))%R by ring; apply Rgt_ge.
  apply Rmult_gt_compat_r; [now apply bpow_gt_0|apply (Z2R_lt 0); reflexivity].
Qed.

Theorem intoffloat_correct:
  forall f,
    match intoffloat f with
      | Some n =>
        is_finite _ _ f = true /\
        Z2R (Int.signed n) = round radix2 (FIX_exp 0) (round_mode mode_ZR) (B2R _ _ f)
      | None =>
        is_finite _ _ f = false \/
        (B2R _ _ f <= Z2R (Zpred Int.min_signed)\/
        Z2R (Zsucc Int.max_signed) <= B2R _ _ f)%R
    end.
Proof.
  intro; pose proof (Zoffloat_correct f); unfold intoffloat; destruct (Zoffloat f).
  pose proof (Zle_bool_spec Int.min_signed z); pose proof (Zle_bool_spec z Int.max_signed). 
  compute_this Int.min_signed; compute_this Int.max_signed; destruct H.
  inversion H0; [inversion H1|].
  rewrite <- (Int.signed_repr z) in H2 by smart_omega; split; assumption.
  right; right; eapply Rle_trans; [apply Z2R_le; apply Zlt_le_succ; now apply H6|].
  rewrite H2, round_ZR_pos.
  unfold round, scaled_mantissa, canonic_exp, FIX_exp, F2R, Fnum, Fexp; simpl bpow.
  do 2 rewrite Rmult_1_r; now apply Zfloor_lb.
  apply Rnot_lt_le; intro; apply Rlt_le in H7; apply (round_le radix2 (FIX_exp 0) (round_mode mode_ZR)) in H7;
    rewrite <- H2, round_0 in H7; [apply (le_Z2R _ 0) in H7; now smart_omega|now apply valid_rnd_round_mode].
  right; left; eapply Rle_trans; [|apply (Z2R_le z); simpl; omega].
  rewrite H2, round_ZR_neg.
  unfold round, scaled_mantissa, canonic_exp, FIX_exp, F2R, Fnum, Fexp; simpl bpow.
  do 2 rewrite Rmult_1_r; now apply Zceil_ub.
  apply Rnot_lt_le; intro; apply Rlt_le in H5; apply (round_le radix2 (FIX_exp 0) (round_mode mode_ZR)) in H5.
  rewrite <- H2, round_0 in H5; [apply (le_Z2R 0) in H5; omega|now apply valid_rnd_round_mode].
  left; assumption.
Qed.

Theorem intuoffloat_correct:
  forall f,
    match intuoffloat f with
      | Some n =>
        is_finite _ _ f = true /\
        Z2R (Int.unsigned n) = round radix2 (FIX_exp 0) (round_mode mode_ZR) (B2R _ _ f)
      | None =>
        is_finite _ _ f = false \/
        (B2R _ _ f <= -1 \/
        Z2R (Zsucc Int.max_unsigned) <= B2R _ _ f)%R
    end.
Proof.
  intro; pose proof (Zoffloat_correct f); unfold intuoffloat; destruct (Zoffloat f).
  pose proof (Zle_bool_spec 0 z); pose proof (Zle_bool_spec z Int.max_unsigned).
  compute_this Int.max_unsigned; destruct H.
  inversion H0. inversion H1.
  rewrite <- (Int.unsigned_repr z) in H2 by smart_omega; split; assumption.
  right; right; eapply Rle_trans; [apply Z2R_le; apply Zlt_le_succ; now apply H6|].
  rewrite H2, round_ZR_pos.
  unfold round, scaled_mantissa, canonic_exp, FIX_exp, F2R, Fnum, Fexp; simpl bpow;
    do 2 rewrite Rmult_1_r; now apply Zfloor_lb.
  apply Rnot_lt_le; intro; apply Rlt_le in H7; eapply (round_le radix2 (FIX_exp 0) (round_mode mode_ZR)) in H7;
    rewrite <- H2, round_0 in H7; [apply (le_Z2R _ 0) in H7; now smart_omega|now apply valid_rnd_round_mode].
  right; left; eapply Rle_trans; [|change (-1)%R with (Z2R (-1)); apply (Z2R_le z); omega].
  rewrite H2, round_ZR_neg; unfold round, scaled_mantissa, canonic_exp, FIX_exp, F2R, Fnum, Fexp; simpl bpow.
  do 2 rewrite Rmult_1_r; now apply Zceil_ub.
  apply Rnot_lt_le; intro; apply Rlt_le in H5; apply (round_le radix2 (FIX_exp 0) (round_mode mode_ZR)) in H5;
    rewrite <- H2, round_0 in H5; [apply (le_Z2R 0) in H5; omega|now apply valid_rnd_round_mode].
  left; assumption.
Qed.

Lemma intuoffloat_interval:
  forall f n,
    intuoffloat f = Some n ->
    (-1 < B2R _ _ f < Z2R (Zsucc Int.max_unsigned))%R.
Proof.
  intro; pose proof (intuoffloat_correct f); destruct (intuoffloat f); try discriminate; destruct H.
  destruct f; try discriminate; intros.
  simpl B2R; change 0%R with (Z2R 0); change (-1)%R with (Z2R (-1)); split; apply Z2R_lt; reflexivity.
  pose proof (Int.unsigned_range i).
  unfold round, scaled_mantissa, B2R, F2R, Fnum, Fexp in H0 |- *; simpl bpow in H0; do 2 rewrite Rmult_1_r in H0;
    apply eq_Z2R in H0.
  split; apply Rnot_le_lt; intro.
  rewrite Ztrunc_ceil in H0;
    [apply Zceil_le in H3; change (-1)%R with (Z2R (-1)) in H3; rewrite Zceil_Z2R in H3; omega|].
  eapply Rle_trans; [now apply H3|apply (Z2R_le (-1) 0); discriminate].
  rewrite Ztrunc_floor in H0; [apply Zfloor_le in H3; rewrite Zfloor_Z2R in H3; now smart_omega|].
  eapply Rle_trans; [|now apply H3]; apply (Z2R_le 0); discriminate.
Qed.

Theorem intuoffloat_intoffloat_1:
  forall x n,
  cmp Clt x (floatofintu ox8000_0000) = true ->
  intuoffloat x = Some n ->
  intoffloat x = Some n.
Proof.
  intros; unfold cmp in H; pose proof (order_float_finite_correct x (floatofintu ox8000_0000)).
  destruct (order_float x (floatofintu ox8000_0000)); try destruct c; try discriminate.
  pose proof (intuoffloat_correct x); rewrite H0 in H2; destruct H2.
  specialize (H1 H2 eq_refl); pose proof (intoffloat_correct x); destruct (intoffloat x).
  f_equal; rewrite <- (proj2 H4) in H3; apply eq_Z2R in H3.
  pose proof (eq_refl (Int.repr (Int.unsigned n))); rewrite H3 in H5 at 1.
  rewrite Int.repr_signed, Int.repr_unsigned in H5; assumption.
  destruct H4; [rewrite H2 in H4; discriminate|].
  apply intuoffloat_interval in H0; exfalso; destruct H0, H4.
  eapply Rlt_le_trans in H0; [|now apply H4]; apply (lt_Z2R (-1)) in H0; discriminate.
  apply Rcompare_Lt_inv in H1; eapply Rle_lt_trans in H1; [|now apply H4].
  unfold floatofintu in H1; rewrite (fun x H => proj1 (binary_normalize64_exact x H)) in H1;
    [apply lt_Z2R in H1; discriminate|split; reflexivity].
Qed.

Lemma Zfloor_minus :
  forall x n, Zfloor(x-Z2R n) = Zfloor(x)-n.
Proof.
  intros; apply Zfloor_imp; replace (Zfloor x - n + 1) with (Zfloor x + 1 - n) by ring; do 2 rewrite Z2R_minus.
  split;
    [apply Rplus_le_compat_r; now apply Zfloor_lb|
     apply Rplus_lt_compat_r; rewrite Z2R_plus; now apply Zfloor_ub].
Qed.

Theorem intuoffloat_intoffloat_2:
  forall x n,
  cmp Clt x (floatofintu ox8000_0000) = false ->
  intuoffloat x = Some n ->
  intoffloat (sub x (floatofintu ox8000_0000)) = Some (Int.sub n ox8000_0000).
Proof.
  assert (B2R _ _ (floatofintu ox8000_0000) = Z2R (Int.unsigned ox8000_0000)).
  apply (fun x H => proj1 (binary_normalize64_exact x H)); split; reflexivity.
  intros; unfold cmp in H0; pose proof (order_float_finite_correct x (floatofintu ox8000_0000)).
  destruct (order_float x (floatofintu ox8000_0000)); try destruct c; try discriminate;
  pose proof (intuoffloat_correct x); rewrite H1 in H3; destruct H3; specialize (H2 H3 eq_refl).
  apply Rcompare_Eq_inv in H2; apply B2R_inj in H2.
  subst x; vm_compute in H1; injection H1; intro; subst n; vm_compute; reflexivity.
  destruct x; try discriminate H3;
    [rewrite H in H2; simpl B2R in H2; apply (eq_Z2R 0) in H2; discriminate|reflexivity].
  reflexivity.
  rewrite H in H2; apply Rcompare_Gt_inv in H2; pose proof (intuoffloat_interval _ _ H1).
  unfold sub, b64_minus.
  exploit (Bminus_correct 53 1024 eq_refl eq_refl binop_pl mode_NE x (floatofintu ox8000_0000)); [assumption|reflexivity|]; intro.
  rewrite H, round_generic in H6.
  match goal with [H6:if Rlt_bool ?x ?y then _ else _|-_] =>
    pose proof (Rlt_bool_spec x y); destruct (Rlt_bool x y) end.
  destruct H6 as [? []].
  match goal with [|- _ ?y = _] => pose proof (intoffloat_correct y); destruct (intoffloat y) end.
  destruct H10.
  f_equal; rewrite <- (Int.repr_signed i); unfold Int.sub; f_equal; apply eq_Z2R. 
  rewrite Z2R_minus, H11, H4.
  unfold round, scaled_mantissa, F2R, Fexp, Fnum, round_mode; simpl bpow; repeat rewrite Rmult_1_r;
    rewrite <- Z2R_minus; f_equal.
  rewrite (Ztrunc_floor (B2R _ _ x)), <- Zfloor_minus, <- Ztrunc_floor;
    [f_equal; assumption|apply Rle_0_minus; left; assumption|].
  left; eapply Rlt_trans; [|now apply H2]; apply (Z2R_lt 0); reflexivity.
  try (change (0 ?= 53) with Lt in H6,H8).  (* for Coq 8.4 *)
  try (change (53 ?= 1024) with Lt in H6,H8).  (* for Coq 8.4 *)
  exfalso; simpl Zcompare in H6, H8; rewrite H6, H8 in H10.
  destruct H10 as [|[]]; [discriminate|..].
  eapply Rle_trans in H10; [|apply Rle_0_minus; left; assumption]; apply (le_Z2R 0) in H10; apply H10; reflexivity.
  eapply Rle_lt_trans in H10; [|apply Rplus_lt_compat_r; now apply (proj2 H5)].
  rewrite <- Z2R_opp, <- Z2R_plus in H10; apply lt_Z2R in H10; discriminate.
  exfalso; inversion H7; rewrite Rabs_right in H8.
  eapply Rle_lt_trans in H8. apply Rle_not_lt in H8; [assumption|apply (bpow_le _ 31); discriminate].
  change (bpow radix2 31) with (Z2R(Zsucc Int.max_unsigned - Int.unsigned ox8000_0000)); rewrite Z2R_minus.
  apply Rplus_lt_compat_r; exact (proj2 H5).
  apply Rle_ge; apply Rle_0_minus; left; assumption.
  now apply valid_rnd_round_mode.
  apply Fprop_Sterbenz.sterbenz_aux; [now apply fexp_monotone|now apply generic_format_B2R| |].
  rewrite <- H; now apply generic_format_B2R.
  destruct H5; split; left; assumption.
  now destruct H2.
Qed.

(** Conversions from ints to floats can be defined as bitwise manipulations
  over the in-memory representation.  This is what the PowerPC port does.
  The trick is that [from_words 0x4330_0000 x] is the float
  [2^52 + floatofintu x]. *)

Definition ox4330_0000 := Int.repr 1127219200.        (**r [0x4330_0000] *)

Lemma split_bits_or:
  forall x,
  split_bits 52 11 (Int64.unsigned (Int64.ofwords ox4330_0000 x)) = (false, Int.unsigned x, 1075).
Proof.
  intros.
  transitivity (split_bits 52 11 (join_bits 52 11 false (Int.unsigned x) 1075)).
  - f_equal. rewrite Int64.ofwords_add'. reflexivity.
  - apply split_join_bits.
    compute; auto.
    generalize (Int.unsigned_range x).
    compute_this Int.modulus; compute_this (2^52); omega.
    compute_this (2^11); omega.
Qed.

Lemma from_words_value:
  forall x,
    B2R _ _ (from_words ox4330_0000 x) =
    (bpow radix2 52 + Z2R (Int.unsigned x))%R /\
    is_finite _ _ (from_words ox4330_0000 x) = true.
Proof.
  intros; unfold from_words, double_of_bits, b64_of_bits, binary_float_of_bits.
  rewrite B2R_FF2B. rewrite is_finite_FF2B.
  unfold binary_float_of_bits_aux; rewrite split_bits_or; simpl; pose proof (Int.unsigned_range x).
  destruct (Int.unsigned x + Zpower_pos 2 52) eqn:?.
  exfalso; now smart_omega.
  simpl; rewrite <- Heqz;  unfold F2R; simpl.
  rewrite <- (Z2R_plus 4503599627370496), Rmult_1_r.
  split; [f_equal; compute_this (Zpower_pos 2 52); ring | reflexivity].
  assert (Zneg p < 0) by reflexivity.
  exfalso; now smart_omega.
Qed.

Theorem floatofintu_from_words:
  forall x,
  floatofintu x =
    sub (from_words ox4330_0000 x) (from_words ox4330_0000 Int.zero).
Proof.
  intros; destruct (Int.eq_dec x Int.zero); [subst; vm_compute; reflexivity|].
  assert (Int.unsigned x <> 0).
  intro; destruct n; rewrite <- (Int.repr_unsigned x), H; reflexivity.
  pose proof (Int.unsigned_range x).
  pose proof (binary_normalize64_exact (Int.unsigned x)). destruct H1; [smart_omega|].
  unfold floatofintu, sub, b64_minus.
  match goal with [|- _ = Bminus _ _ _ _ _ _ ?x ?y] =>
    pose proof (Bminus_correct 53 1024 eq_refl eq_refl binop_pl mode_NE x y) end.
  apply (fun f x y => f x y) in H3; try apply (fun x => proj2 (from_words_value x)).
  do 2 rewrite (fun x => proj1 (from_words_value x)) in H3.
  rewrite Int.unsigned_zero in H3.
  replace (bpow radix2 52 + Z2R (Int.unsigned x) -
    (bpow radix2 52 + Z2R 0))%R with (Z2R (Int.unsigned x)) in H3 by (simpl; ring).
  rewrite round_exact in H3 by smart_omega.
  match goal with [H3:if Rlt_bool ?x ?y then _ else _ |- _] =>
    pose proof (Rlt_bool_spec x y); destruct (Rlt_bool x y) end; destruct H3 as [? []].
  try (change (53 ?= 1024) with Lt in H3,H5).  (* for Coq 8.4 *)
  simpl Zcompare in *; apply B2R_inj;
    try match goal with [H':B2R _ _ ?f = _ , H'':is_finite _ _ ?f = true |- is_finite_strict _ _ ?f = true] => 
      destruct f; [
        simpl in H'; change 0%R with (Z2R 0) in H'; apply eq_Z2R in H'; now destruct (H (eq_sym H')) | 
        discriminate H'' | discriminate H'' | reflexivity
      ]
    end.
  rewrite H3; assumption.
  inversion H4; change (bpow radix2 1024) with (Z2R (radix2 ^ 1024)) in H5; rewrite <- Z2R_abs in H5.
  apply le_Z2R in H5; pose proof (Zabs_spec (Int.unsigned x));
    exfalso; now smart_omega.
Qed.

Lemma ox8000_0000_signed_unsigned:
  forall x,
    Int.unsigned (Int.add x ox8000_0000) = Int.signed x + Int.half_modulus.
Proof.
  intro; unfold Int.signed, Int.add; pose proof (Int.unsigned_range x).
  destruct (zlt (Int.unsigned x) Int.half_modulus).
  rewrite Int.unsigned_repr; compute_this (Int.unsigned ox8000_0000); now smart_omega.
  rewrite (Int.eqm_samerepr _ (Int.unsigned x + -2147483648)).
  rewrite Int.unsigned_repr; now smart_omega.
  apply Int.eqm_add; [now apply Int.eqm_refl|exists 1;reflexivity].
Qed.

Theorem floatofint_from_words:
  forall x,
  floatofint x =
    sub (from_words ox4330_0000 (Int.add x ox8000_0000))
        (from_words ox4330_0000 ox8000_0000).
Proof.
Local Transparent Int.repr Int64.repr.
  intros; destruct (Int.eq_dec x Int.zero); [subst; vm_compute; reflexivity|].
  assert (Int.signed x <> 0).
  intro; destruct n; rewrite <- (Int.repr_signed x), H; reflexivity.
  pose proof (Int.signed_range x).
  pose proof (binary_normalize64_exact (Int.signed x)); destruct H1; [now smart_omega|].
  unfold floatofint, sub, b64_minus.
  match goal with [|- _ = Bminus _ _ _ _ _ _ ?x ?y] =>
    pose proof (Bminus_correct 53 1024 eq_refl eq_refl binop_pl mode_NE x y) end.
  apply (fun f x y => f x y) in H3; try apply (fun x => proj2 (from_words_value x)).
  do 2 rewrite (fun x => proj1 (from_words_value x)) in H3.
  replace (bpow radix2 52 + Z2R (Int.unsigned (Int.add x ox8000_0000)) -
    (bpow radix2 52 + Z2R (Int.unsigned ox8000_0000)))%R with (Z2R (Int.signed x)) in H3
  by (rewrite ox8000_0000_signed_unsigned; rewrite Z2R_plus; simpl; ring).
  rewrite round_exact in H3 by smart_omega.
  match goal with [H3:if Rlt_bool ?x ?y then _ else _ |- _] =>
    pose proof (Rlt_bool_spec x y); destruct (Rlt_bool x y) end; destruct H3 as [? []].
  try (change (0 ?= 53) with Lt in H3,H5).  (* for Coq 8.4 *)
  try (change (53 ?= 1024) with Lt in H3,H5).  (* for Coq 8.4 *)
  simpl Zcompare in *; apply B2R_inj;
    try match goal with [H':B2R _ _ ?f = _ , H'':is_finite _ _ ?f = true |- is_finite_strict _ _ ?f = true] => 
      destruct f; [
        simpl in H'; change 0%R with (Z2R 0) in H'; apply eq_Z2R in H'; now destruct (H (eq_sym H')) | 
        discriminate H'' | discriminate H'' | reflexivity
      ]
    end.
  rewrite H3; assumption.
  inversion H4; unfold bpow in H5; rewrite <- Z2R_abs in H5;
    apply le_Z2R in H5; pose proof (Zabs_spec (Int.signed x)); exfalso; now smart_omega.
Qed.

(** Conversions from 32-bit integers to single-precision floats can
  be decomposed into a conversion to a double-precision float,
  followed by a [singleoffloat] normalization.  No double rounding occurs. *)

Lemma is_finite_strict_ge_1:
  forall (f: binary32),
  is_finite _ _ f = true ->
  (1 <= Rabs (B2R _ _ f))%R ->
  is_finite_strict _ _ f = true.
Proof.
  intros. destruct f; auto. simpl in H0.
  change 0%R with (Z2R 0) in H0.
  change 1%R with (Z2R 1) in H0.
  rewrite <- Z2R_abs in H0.
  exploit le_Z2R; eauto.
Qed.

Lemma single_float_of_int:
  forall n,
  -2^53 < n < 2^53 ->
  singleoffloat (binary_normalize64 n 0 false) = floatofbinary32 (binary_normalize32 n 0 false).
Proof.
  intros. unfold singleoffloat. f_equal.
  assert (EITHER: n = 0 \/ Z.abs n > 0) by (destruct n; compute; auto).
  destruct EITHER as [EQ|GT].
  subst n; reflexivity.
  exploit binary_normalize64_exact; eauto. intros [A B].
  destruct (binary_normalize64 n 0 false) as [ | | | s m e] eqn:B64; simpl in *.
- assert (0 = n) by (apply eq_Z2R; auto). subst n. simpl in GT. omegaContradiction.
- discriminate.
- discriminate.
- set (n1 := cond_Zopp s (Z.pos m)) in *.
  generalize (binary_normalize32_correct n1 e s).
  fold (binary_normalize32 n1 e s). intros C.
  generalize (binary_normalize32_correct n 0 false).
  fold (binary_normalize32 n 0 false). intros D.
  assert (A': @F2R radix2 {| Fnum := n; Fexp := 0 |} = Z2R n).
  { unfold F2R. apply Rmult_1_r. }
  rewrite A in C. rewrite A' in D.
  destruct (Rlt_bool
         (Rabs
            (round radix2 (FLT_exp (3 - 128 - 24) 24) (round_mode mode_NE)
               (Z2R n))) (bpow radix2 128)).
+ destruct C as [C1 [C2 _]]; destruct D as [D1 [D2 _]].
  assert (1 <= Rabs (round radix2 (FLT_exp (3 - 128 - 24) 24) (round_mode mode_NE) (Z2R n)))%R.
  { apply abs_round_ge_generic.
    apply fexp_correct. red. omega.
    apply valid_rnd_round_mode.
    apply generic_format_bpow with (e := 0). compute. congruence.
    rewrite <- Z2R_abs. change 1%R with (Z2R 1). apply Z2R_le. omega. }
  apply B2R_inj.
  apply is_finite_strict_ge_1; auto. rewrite C1; auto.
  apply is_finite_strict_ge_1; auto. rewrite D1; auto.
  congruence.
+ apply B2FF_inj. congruence.
Qed.

Theorem singleofint_floatofint:
  forall n, singleofint n = singleoffloat (floatofint n).
Proof.
  intros. symmetry. apply single_float_of_int.
  generalize (Int.signed_range n). smart_omega.
Qed.

Theorem singleofintu_floatofintu:
  forall n, singleofintu n = singleoffloat (floatofintu n).
Proof.
  intros. symmetry. apply single_float_of_int.
  generalize (Int.unsigned_range n). smart_omega.
Qed.

Theorem mul2_add:
  forall f, add f f = mul f (floatofint (Int.repr 2%Z)).
Proof.
  intros. unfold add, b64_plus, mul, b64_mult.
  destruct (is_finite_strict _ _ f) eqn:EQFINST.
  - assert (EQFIN:is_finite _ _ f = true) by (destruct f; simpl in *; congruence).
    pose proof (Bplus_correct 53 1024 eq_refl eq_refl binop_pl mode_NE f f EQFIN EQFIN).
    pose proof (Bmult_correct 53 1024 eq_refl eq_refl binop_pl mode_NE f
                              (floatofint (Int.repr 2%Z))).
    rewrite <- double, Rmult_comm in H.
    replace (B2R 53 1024 (floatofint (Int.repr 2))) with 2%R in H0 by (compute; field).
    destruct Rlt_bool.
    + destruct H0 as [? []], H as [? []].
      rewrite EQFIN in H1.
      apply B2R_Bsign_inj; auto.
      etransitivity. apply H. symmetry. apply H0.
      etransitivity. apply H4. symmetry. etransitivity. apply H2.
      destruct Bmult; try reflexivity; discriminate.
      simpl. rewrite xorb_false_r.
      erewrite <- Rmult_0_l, Rcompare_mult_r.
      destruct f; try discriminate EQFINST.
      simpl. unfold F2R.
      erewrite <- Rmult_0_l, Rcompare_mult_r.
      rewrite Rcompare_Z2R with (y:=0).
      destruct b; reflexivity.
      apply bpow_gt_0.
      apply (Z2R_lt 0 2). omega.
    + destruct H.
      apply B2FF_inj.
      etransitivity. apply H.
      symmetry. etransitivity. apply H0.
      f_equal. destruct Bsign; reflexivity.
  - destruct f as [[]|[]| |]; try discriminate; try reflexivity.
    simpl. destruct (choose_binop_pl b n b n); auto.
Qed.

Program Definition pow2_float (b:bool) (e:Z) (H:-1023 < e < 1023) : float :=
  B754_finite _ _ b (nat_iter 52 xO xH) (e-52) _.
Next Obligation.
  unfold Fappli_IEEE.bounded, canonic_mantissa.
  rewrite andb_true_iff, Zle_bool_true by omega. split; auto.
  apply Zeq_bool_true. unfold FLT_exp. simpl Z.of_nat.
  apply Z.max_case_strong; omega.
Qed.

Theorem mul_div_pow2:
  forall b e f H H',
    mul f (pow2_float b e H) = div f (pow2_float b (-e) H').
Proof.
  intros. unfold mul, b64_mult, div, b64_div.
  pose proof (Bmult_correct 53 1024 eq_refl eq_refl binop_pl mode_NE f (pow2_float b e H)).
  pose proof (Bdiv_correct 53 1024 eq_refl eq_refl binop_pl mode_NE f (pow2_float b (-e) H')).
  lapply H1. clear H1. intro.
  change (is_finite 53 1024 (pow2_float b e H)) with true in H0.
  unfold Rdiv in H1.
  replace (/ B2R 53 1024 (pow2_float b (-e) H'))%R
    with (B2R 53 1024 (pow2_float b e H)) in H1.
  destruct (is_finite _ _ f) eqn:EQFIN.
  - destruct Rlt_bool.
    + destruct H0 as [? []], H1 as [? []].
      apply B2R_Bsign_inj; auto.
      etransitivity. apply H0. symmetry. apply H1.
      etransitivity. apply H3. destruct Bmult; try discriminate H2; reflexivity.
      symmetry. etransitivity. apply H5. destruct Bdiv; try discriminate H4; reflexivity.
      reflexivity.
    + apply B2FF_inj.
      etransitivity. apply H0. symmetry. etransitivity. apply H1.
      reflexivity.
  - destruct f; try discriminate EQFIN; auto. 
  - simpl.
    assert ((4503599627370496 * bpow radix2 (e - 52))%R =
            (/ (4503599627370496 * bpow radix2 (- e - 52)))%R).
    { etransitivity. symmetry. apply (bpow_plus radix2 52).
      symmetry. etransitivity. apply f_equal. symmetry. apply (bpow_plus radix2 52).
      rewrite <- bpow_opp. f_equal. ring. }
    destruct b. unfold cond_Zopp.
    rewrite !F2R_Zopp, <- Ropp_inv_permute. f_equal. auto.
    intro. apply F2R_eq_0_reg in H3. omega.
    apply H2.
  - simpl. intro. apply F2R_eq_0_reg in H2.
    destruct b; simpl in H2; omega.
Qed.

Definition exact_inverse_mantissa := nat_iter 52 xO xH.

Program Definition exact_inverse (f: float) : option float :=
  match f with
  | B754_finite s m e B =>
      if peq m exact_inverse_mantissa then
      if zlt (-1023) (e + 52) then
      if zlt (e + 52) 1023 then
        Some(B754_finite _ _ s m (-e - 104) _)
      else None else None else None
  | _ => None
  end.
Next Obligation.
  unfold Fappli_IEEE.bounded, canonic_mantissa. apply andb_true_iff; split.
  simpl Z.of_nat. apply Zeq_bool_true. unfold FLT_exp. apply Z.max_case_strong; omega.
  apply Zle_bool_true. omega.  
Qed.

Remark B754_finite_eq:
  forall s1 m1 e1 B1 s2 m2 e2 B2,
  s1 = s2 -> m1 = m2 -> e1 = e2 ->
  B754_finite _ _ s1 m1 e1 B1 = (B754_finite _ _ s2 m2 e2 B2 : float).
Proof.
  intros. subst. f_equal. apply proof_irrelevance. 
Qed.

Theorem div_mul_inverse:
  forall x y z, exact_inverse y = Some z -> div x y = mul x z.
Proof with (try discriminate).
  unfold exact_inverse; intros. destruct y...
  destruct (peq m exact_inverse_mantissa)...
  destruct (zlt (-1023) (e + 52))...
  destruct (zlt (e + 52) 1023)...
  inv H.
  set (n := - e - 52).
  assert (RNG1: -1023 < n < 1023) by (unfold n; omega).
  assert (RNG2: -1023 < -n < 1023) by (unfold n; omega).
  symmetry. 
  transitivity (mul x (pow2_float b n RNG1)).
  f_equal. apply B754_finite_eq; auto. unfold n; omega.
  transitivity (div x (pow2_float b (-n) RNG2)).
  apply mul_div_pow2. 
  f_equal. apply B754_finite_eq; auto. unfold n; omega.
Qed.

Global Opaque
  zero eq_dec neg abs singleoffloat intoffloat intuoffloat floatofint floatofintu
  add sub mul div cmp bits_of_double double_of_bits bits_of_single single_of_bits from_words.

End Float.
