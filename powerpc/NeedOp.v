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

Definition op1 (nv: nval) := nv :: nil.
Definition op2 (nv: nval) := nv :: nv :: nil.

Definition needs_of_condition (cond: condition): list nval :=
  match cond with
  | Cmaskzero n | Cmasknotzero n => op1 (maskzero n)
  | _ => nil
  end.

Definition needs_of_operation (op: operation) (nv: nval): list nval :=
  match op with
  | Omove => op1 nv
  | Ointconst n => nil
  | Ofloatconst n => nil
  | Osingleconst n => nil
  | Oaddrsymbol id ofs => nil
  | Oaddrstack ofs => nil
  | Ocast8signed => op1 (sign_ext 8 nv)
  | Ocast16signed => op1 (sign_ext 16 nv)
  | Oadd => op2 (modarith nv)
  | Oaddimm n => op1 (modarith nv)
  | Oaddsymbol id ofs => op1 (modarith nv)
  | Osub => op2 (default nv)
  | Osubimm n => op1 (default nv)
  | Omul => op2 (modarith nv)
  | Omulimm n => op1 (modarith nv)
  | Omulhs | Omulhu | Odiv | Odivu => op2 (default nv)
  | Oand => op2 (bitwise nv)
  | Oandimm n => op1 (andimm nv n)
  | Oor => op2 (bitwise nv)
  | Oorimm n => op1 (orimm nv n)
  | Oxor => op2 (bitwise nv)
  | Oxorimm n => op1 (bitwise nv)
  | Onot => op1 (bitwise nv)
  | Onand | Onor | Onxor | Oandc | Oorc => op2 (bitwise nv)
  | Oshl | Oshr | Oshru => op2 (default nv)
  | Oshrimm n => op1 (shrimm nv n)
  | Oshrximm n => op1 (default nv)
  | Orolm amount mask => op1 (rolm nv amount mask)
  | Oroli amount mask => op1 (default nv)
  | Olongconst n => nil
  | Ocast32signed | Ocast32unsigned | Onegl | Onotl => op1 (default nv)
  | Oaddl | Osubl | Omull | Omullhs | Omullhu | Odivl | Odivlu | Oandl | Oorl | Oxorl | Oshll | Oshrl | Oshrlu => op2 (default nv)
  | Oaddlimm _ | Oandlimm _ | Oorlimm _ | Oxorlimm _ | Oshrlimm _ | Oshrxlimm _=> op1 (default nv)
  | Orolml _ _ | Olongoffloat | Ofloatoflong => op1 (default nv)
  | Onegf | Oabsf => op1 (default nv)
  | Oaddf | Osubf | Omulf | Odivf => op2 (default nv)
  | Onegfs | Oabsfs => op1 (default nv)
  | Oaddfs | Osubfs | Omulfs | Odivfs => op2 (default nv)
  | Osingleoffloat | Ofloatofsingle => op1 (default nv)
  | Ointoffloat | Ointuoffloat | Ofloatofint | Ofloatofintu => op1 (default nv)
  | Ofloatofwords | Omakelong => op2 (default nv)
  | Olowlong | Ohighlong => op1 (default nv)
  | Ocmp c => needs_of_condition c
  end.

Definition operation_is_redundant (op: operation) (nv: nval): bool :=
  match op with
  | Ocast8signed => sign_ext_redundant 8 nv
  | Ocast16signed => sign_ext_redundant 16 nv
  | Oandimm n => andimm_redundant nv n
  | Oorimm n => orimm_redundant nv n
  | Orolm amount mask => rolm_redundant nv amount mask
  | _ => false
  end.

Ltac InvAgree :=
  match goal with
  | [H: vagree_list nil _ _ |- _ ] => inv H; InvAgree
  | [H: vagree_list (_::_) _ _ |- _ ] => inv H; InvAgree
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
  eval_operation ge (Vptr sp Ptrofs.zero) op args m = Some v ->
  vagree_list args args' (needs_of_operation op nv) ->
  nv <> Nothing ->
  exists v',
     eval_operation ge (Vptr sp Ptrofs.zero) op args' m' = Some v'
  /\ vagree v v' nv.
Proof.
  unfold needs_of_operation; intros; destruct op; try (eapply default_needs_of_operation_sound; eauto; fail);
  simpl in *; FuncInv; InvAgree; TrivialExists.
- apply sign_ext_sound; auto. compute; auto.
- apply sign_ext_sound; auto. compute; auto.
- apply add_sound; auto.
- apply add_sound; auto with na.
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
- destruct (eval_condition c args m) as [b|] eqn:EC; simpl in H2.
  erewrite needs_of_condition_sound by eauto.
  subst v; simpl. auto with na.
  subst v; auto with na.
Qed.

Lemma operation_is_redundant_sound:
  forall op nv arg1 args v arg1' args',
  operation_is_redundant op nv = true ->
  eval_operation ge (Vptr sp Ptrofs.zero) op (arg1 :: args) m = Some v ->
  vagree_list (arg1 :: args) (arg1' :: args') (needs_of_operation op nv) ->
  vagree v arg1' nv.
Proof.
  intros. destruct op; simpl in *; try discriminate; inv H1; FuncInv; subst.
- apply sign_ext_redundant_sound; auto. omega.
- apply sign_ext_redundant_sound; auto. omega.
- apply andimm_redundant_sound; auto.
- apply orimm_redundant_sound; auto.
- apply rolm_redundant_sound; auto.
Qed.

End SOUNDNESS.



