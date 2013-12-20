Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Op.
Require Import NeedDomain.
Require Import RTL.

(** Neededness analysis for PowerPC operators *)

Definition needs_of_condition (cond: condition): nval :=
  match cond with
  | Cmaskzero n | Cmasknotzero n => maskzero n
  | _ => All
  end.

Definition needs_of_operation (op: operation) (nv: nval): nval :=
  match op with
  | Omove => nv
  | Ointconst n => Nothing
  | Ofloatconst n => Nothing
  | Oaddrsymbol id ofs => Nothing
  | Oaddrstack ofs => Nothing
  | Ocast8signed => sign_ext 8 nv
  | Ocast16signed => sign_ext 16 nv
  | Oadd => modarith nv
  | Oaddimm n => modarith nv
  | Omul => modarith nv
  | Omulimm n => modarith nv
  | Oand => bitwise nv
  | Oandimm n => andimm nv n
  | Oor => bitwise nv
  | Oorimm n => orimm nv n
  | Oxor => bitwise nv
  | Oxorimm n => bitwise nv
  | Onot => bitwise nv
  | Onand => bitwise nv
  | Onor => bitwise nv
  | Onxor => bitwise nv
  | Oandc => bitwise nv
  | Oorc => bitwise nv
  | Oshrimm n => shrimm nv n
  | Orolm amount mask => rolm nv amount mask
  | Osingleoffloat => singleoffloat nv
  | Ocmp c => needs_of_condition c
  | _ => default nv
  end.

Definition operation_is_redundant (op: operation) (nv: nval): bool :=
  match op with
  | Ocast8signed => sign_ext_redundant 8 nv
  | Ocast16signed => sign_ext_redundant 16 nv
  | Oandimm n => andimm_redundant nv n
  | Oorimm n => orimm_redundant nv n
  | Orolm amount mask => rolm_redundant nv amount mask
  | Osingleoffloat => singleoffloat_redundant nv
  | _ => false
  end.

Ltac InvAgree :=
  match goal with
  | [H: vagree_list nil _ _ |- _ ] => inv H; InvAgree
  | [H: vagree_list (_::_) _ _ |- _ ] => inv H; InvAgree
  | [H: list_forall2 _ nil _ |- _ ] => inv H; InvAgree
  | [H: list_forall2 _ (_::_) _ |- _ ] => inv H; InvAgree
  | _ => idtac
  end.

Ltac TrivialExists :=
  match goal with
  | [ |- exists v, Some ?x = Some v /\ _ ] => exists x; split; auto
  | _ => idtac
  end.

Section SOUNDNESS.

Variable ge: genv.
Variable sp: block.
Variables m m': mem.
Hypothesis PERM: forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p.

Lemma needs_of_condition_sound:
  forall cond args b args',
  eval_condition cond args m = Some b ->
  vagree_list args args' (needs_of_condition cond) ->
  eval_condition cond args' m' = Some b.
Proof.
  intros. destruct cond; simpl in H;
  try (eapply default_needs_of_condition_sound; eauto; fail);
  simpl in *; FuncInv; InvAgree.
- eapply maskzero_sound; eauto. 
- destruct (Val.maskzero_bool v i) as [b'|] eqn:MZ; try discriminate.
  erewrite maskzero_sound; eauto.
Qed.

Lemma needs_of_operation_sound:
  forall op args v nv args',
  eval_operation ge (Vptr sp Int.zero) op args m = Some v ->
  vagree_list args args' (needs_of_operation op nv) ->
  nv <> Nothing ->
  exists v',
     eval_operation ge (Vptr sp Int.zero) op args' m' = Some v'
  /\ vagree v v' nv.
Proof.
  unfold needs_of_operation; intros; destruct op; try (eapply default_needs_of_operation_sound; eauto; fail);
  simpl in *; FuncInv; InvAgree; TrivialExists.
- auto with na.
- auto with na.
- auto with na.
- auto with na.
- apply sign_ext_sound; auto. compute; auto. 
- apply sign_ext_sound; auto. compute; auto.
- apply add_sound; auto.
- apply add_sound; auto with na.
- apply mul_sound; auto.
- apply mul_sound; auto with na.
- apply and_sound; auto.
- apply andimm_sound; auto.
- apply or_sound; auto.
- apply orimm_sound; auto.
- apply xor_sound; auto.
- apply xor_sound; auto with na.
- apply notint_sound; auto.
- apply notint_sound. apply and_sound; rewrite bitwise_idem; auto.
- apply notint_sound. apply or_sound; rewrite bitwise_idem; auto.
- apply notint_sound. apply xor_sound; rewrite bitwise_idem; auto.
- apply and_sound; auto. apply notint_sound; rewrite bitwise_idem; auto.
- apply or_sound; auto. apply notint_sound; rewrite bitwise_idem; auto.
- apply shrimm_sound; auto.
- apply rolm_sound; auto. 
- apply singleoffloat_sound; auto. 
- destruct (eval_condition c args m) as [b|] eqn:EC; simpl in H2. 
  erewrite needs_of_condition_sound by eauto.
  subst v; simpl. auto with na.
  subst v; auto with na.
Qed.

Lemma operation_is_redundant_sound:
  forall op nv arg1 args v arg1',
  operation_is_redundant op nv = true ->
  eval_operation ge (Vptr sp Int.zero) op (arg1 :: args) m = Some v ->
  vagree arg1 arg1' (needs_of_operation op nv) ->
  vagree v arg1' nv.
Proof.
  intros. destruct op; simpl in *; try discriminate; FuncInv; subst.
- apply sign_ext_redundant_sound; auto. omega.
- apply sign_ext_redundant_sound; auto. omega.
- apply andimm_redundant_sound; auto. 
- apply orimm_redundant_sound; auto.
- apply rolm_redundant_sound; auto.
- apply singleoffloat_redundant_sound; auto.
Qed.

End SOUNDNESS.



