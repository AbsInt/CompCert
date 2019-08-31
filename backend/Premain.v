
Require Import Coqlib Locations Conventions Integers.
Require Import AST Values.


(* Arguemnts fit in the stack *)
Definition bounded_args (sg: signature):=
  4 * (size_arguments sg) < Ptrofs.max_unsigned - 30.

Lemma args_bound_to_stack_bound_helper:
  forall a b,
    let  w := (if Archi.ptr64 then 8 else 4) in
    4 * a < b - 30 ->
    align (align (4*a) w + w) 8 + w < b.
Proof.
  intros.
  unfold align.
  clear - H.
  rewrite Z.mul_comm.
  eapply Z.le_lt_trans.
  instantiate(1:=((4 * a + w - 1) / w * w + w + 8 - 1) + w).
  eapply Zplus_le_compat_r.
  apply Z.mul_div_le. xomega.
  
  eapply Z.le_lt_trans.
  instantiate(1:=(4 * a + w - 1) + w + 8 - 1 + w).
  unfold Z.sub.
  repeat eapply Zplus_le_compat_r.
  rewrite Z.mul_comm.
  apply Z.mul_div_le. subst w; destruct Archi.ptr64; xomega.
  eapply Z.le_lt_trans.
  eapply Zplus_le_compat_l.
  reflexivity.
  match goal with
    |- ?lhs < _ => replace lhs with
      (4 * a + 3 * w + 6) by xomega
  end.
  assert (w <= 8).
  { subst w. match_case; xomega. }
  eapply (Z.le_lt_trans _ (4 * a + 30)); try xomega.
Qed.

Lemma args_bound_max:
  forall sg, 
    bounded_args sg ->
    let  w := (if Archi.ptr64 then 8 else 4) in
    align (align (4*(size_arguments sg)) w + w) 8 + w < Ptrofs.max_unsigned.
Proof. intros. apply args_bound_to_stack_bound_helper; eauto. Qed.

(* Monad for rpair *)
Section RPairMonad.
  Variables T K:Type.
  Variables F: T -> val -> K -> K.
  Definition rpair_wrap (x:rpair T)(v:val) (k1: K): K:=
    match x with
      | One a => F a v k1
      | Twolong a b => F b (Val.loword v) (F a ((Val.hiword v) ) k1)
    end.
End RPairMonad.
Arguments rpair_wrap {_ _}.

Section ZipFold.
  Variables T1 T2 K:Type.
  Variables F: T1 -> T2 -> K -> K.
  Fixpoint zip_fold (ls1: list T1)(ls2: list T2)(k:K): K:=
    match ls1, ls2 with
    | a::ls1',b::ls2' => F a b (zip_fold ls1' ls2' k)
    | _, _ => k
    end.
End ZipFold.
Arguments zip_fold {_ _ _}.

(* Build a locset for pre_main *)

Definition set_outgoing (l:loc) v ls :=
  match l with
  | S Outgoing _ _ => Locmap.set l v ls
  | _ => ls
  end.
Definition make_locset {T K} (set_func: T -> val -> K -> K) :=
  zip_fold (rpair_wrap set_func).

Definition make_locset_all:= make_locset Locmap.set.
Definition make_locset_outgoing:= make_locset set_outgoing.

Notation locset := Locmap.t.
Definition sig_wrapper targs:signature :=
  {| sig_args := targs; sig_res := None; sig_cc := cc_default |}.
Definition pre_main_locset_outgoing targs args: locset:=
  let sg:= sig_wrapper targs in
  make_locset_outgoing (loc_arguments sg) args (Locmap.init Vundef).
Definition pre_main_locset_all targs args: locset:=
  let sg:= sig_wrapper targs in
  make_locset_all (loc_arguments sg) args (Locmap.init Vundef).