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

(** Neededness analysis for IA32 operators *)

Definition needs_of_condition (cond: condition): nval :=
  match cond with
  | Cmaskzero n | Cmasknotzero n => maskzero n
  | _ => All
  end.

Definition needs_of_addressing (addr: addressing) (nv: nval): nval :=
  modarith nv.

Definition needs_of_operation (op: operation) (nv: nval): nval :=
  match op with
  | Omove => nv
  | Ointconst n => Nothing
  | Ofloatconst n => Nothing
  | Oindirectsymbol id => Nothing
  | Ocast8signed => sign_ext 8 nv
  | Ocast8unsigned => zero_ext 8 nv
  | Ocast16signed => sign_ext 16 nv
  | Ocast16unsigned => zero_ext 16 nv
  | Omul => modarith nv
  | Omulimm n => modarith nv
  | Oand => bitwise nv
  | Oandimm n => andimm nv n
  | Oor => bitwise nv
  | Oorimm n => orimm nv n
  | Oxor => bitwise nv
  | Oxorimm n => bitwise nv
  | Oshlimm n => shlimm nv n
  | Oshrimm n => shrimm nv n
  | Oshruimm n => shruimm nv n
  | Ororimm n => ror nv n
  | Olea addr => needs_of_addressing addr nv
  | Ocmp c => needs_of_condition c
  | Osingleoffloat => singleoffloat nv
  | _ => default nv
  end.

Definition operation_is_redundant (op: operation) (nv: nval): bool :=
  match op with
  | Ocast8signed => sign_ext_redundant 8 nv
  | Ocast8unsigned => zero_ext_redundant 8 nv
  | Ocast16signed => sign_ext_redundant 16 nv
  | Ocast16unsigned => zero_ext_redundant 16 nv
  | Oandimm n => andimm_redundant nv n
  | Oorimm n => orimm_redundant nv n
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

Lemma needs_of_addressing_sound:
  forall (ge: genv) sp addr args v nv args',
  eval_addressing ge (Vptr sp Int.zero) addr args = Some v ->
  vagree_list args args' (needs_of_addressing addr nv) ->
  exists v',
     eval_addressing ge (Vptr sp Int.zero) addr args' = Some v'
  /\ vagree v v' nv.
Proof.
  unfold needs_of_addressing; intros.
  destruct addr; simpl in *; FuncInv; InvAgree; TrivialExists;
  auto using add_sound, add_sound_2, mul_sound, mul_sound_2 with na.
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
- apply sign_ext_sound; auto. compute; auto. 
- apply zero_ext_sound; auto. omega.
- apply sign_ext_sound; auto. compute; auto. 
- apply zero_ext_sound; auto. omega.
- apply mul_sound; auto.
- apply mul_sound; auto with na.
- apply and_sound; auto.
- apply andimm_sound; auto.
- apply or_sound; auto.
- apply orimm_sound; auto.
- apply xor_sound; auto.
- apply xor_sound; auto with na.
- apply shlimm_sound; auto.
- apply shrimm_sound; auto.
- apply shruimm_sound; auto. 
- apply ror_sound; auto. 
- eapply needs_of_addressing_sound; eauto.
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
- apply zero_ext_redundant_sound; auto. omega.
- apply sign_ext_redundant_sound; auto. omega.
- apply zero_ext_redundant_sound; auto. omega.
- apply andimm_redundant_sound; auto. 
- apply orimm_redundant_sound; auto.
- apply singleoffloat_redundant_sound; auto.
Qed.

End SOUNDNESS.


