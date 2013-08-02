Require Import Fappli_IEEE.
Require Import Fappli_IEEE_bits.
Require Import Floats.
Require Import ZArith.
Require Import Integers.

(* Needed to break a circular reference after extraction *)
Definition transform_quiet_pl :=
  Eval unfold Float.transform_quiet_pl in Float.transform_quiet_pl.

Program Definition default_pl : bool * nan_pl 53 := (true, nat_iter 51 xO xH).

Definition binop_pl (pl1 pl2:binary64) : bool*nan_pl 53 :=
  match pl1, pl2 with
    | B754_nan s1 pl1, _ => (s1, transform_quiet_pl pl1)
    | _, B754_nan s2 pl2 => (s2, transform_quiet_pl pl2)
    | _, _ => default_pl
  end.

Theorem binop_propagate1: Float.binop_propagate1_prop binop_pl.
Proof.
  repeat intro. destruct f1, f2; try discriminate; simpl; reflexivity.
Qed.

Theorem binop_propagate2: Float.binop_propagate2_prop binop_pl.
Proof.
  repeat intro. destruct f1, f2, f3; try discriminate; simpl; reflexivity.
Qed.
