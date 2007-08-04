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
  guarantees that the locations of arguments and results are "acceptable",
  i.e. either non-temporary registers or [Local] stack locations. *)

Section WT_INSTR.

Variable funct: function.

Definition valid_successor (s: node) : Prop :=
  exists i, funct.(fn_code)!s = Some i.

Inductive wt_instr : instruction -> Prop :=
  | wt_Lnop:
      forall s,
      valid_successor s ->
      wt_instr (Lnop s)
  | wt_Lopmove:
      forall r1 r s,
      Loc.type r1 = Loc.type r -> loc_acceptable r1 -> loc_acceptable r ->
      valid_successor s ->
      wt_instr (Lop Omove (r1 :: nil) r s)
  | wt_Lop:
      forall op args res s,
      op <> Omove ->
      (List.map Loc.type args, Loc.type res) = type_of_operation op ->
      locs_acceptable args -> loc_acceptable res ->
      valid_successor s ->
      wt_instr (Lop op args res s)
  | wt_Lload:
      forall chunk addr args dst s,
      List.map Loc.type args = type_of_addressing addr ->
      Loc.type dst = type_of_chunk chunk ->
      locs_acceptable args -> loc_acceptable dst ->
      valid_successor s ->
      wt_instr (Lload chunk addr args dst s)
  | wt_Lstore:
      forall chunk addr args src s,
      List.map Loc.type args = type_of_addressing addr ->
      Loc.type src = type_of_chunk chunk ->
      locs_acceptable args -> loc_acceptable src ->
      valid_successor s ->
      wt_instr (Lstore chunk addr args src s)
  | wt_Lcall:
      forall sig ros args res s,
      match ros with inl r => Loc.type r = Tint | inr s => True end ->
      List.map Loc.type args = sig.(sig_args) ->
      Loc.type res = proj_sig_res sig ->
      match ros with inl r => loc_acceptable r | inr s => True end ->
      locs_acceptable args -> loc_acceptable res ->
      valid_successor s ->
      wt_instr (Lcall sig ros args res s)
  | wt_Ltailcall:
      forall sig ros args,
      match ros with inl r => Loc.type r = Tint | inr s => True end ->
      List.map Loc.type args = sig.(sig_args) ->
      match ros with inl r => loc_acceptable r | inr s => True end ->
      locs_acceptable args ->
      sig.(sig_res) = funct.(fn_sig).(sig_res) ->
      Conventions.tailcall_possible sig ->
      wt_instr (Ltailcall sig ros args)
  | wt_Lalloc:
      forall arg res s,
      Loc.type arg = Tint -> Loc.type res = Tint ->
      loc_acceptable arg -> loc_acceptable res ->
      valid_successor s ->
      wt_instr (Lalloc arg res s)
  | wt_Lcond:
      forall cond args s1 s2,
      List.map Loc.type args = type_of_condition cond ->
      locs_acceptable args ->
      valid_successor s1 -> valid_successor s2 ->
      wt_instr (Lcond cond args s1 s2)
  | wt_Lreturn: 
      forall optres,
      option_map Loc.type optres = funct.(fn_sig).(sig_res) ->
      match optres with None => True | Some r => loc_acceptable r end ->
      wt_instr (Lreturn optres).

End WT_INSTR.

Record wt_function (f: function): Prop :=
  mk_wt_function {
    wt_params:
      List.map Loc.type f.(fn_params) = f.(fn_sig).(sig_args);
    wt_acceptable:
      locs_acceptable f.(fn_params);
    wt_norepet:
      Loc.norepet f.(fn_params);
    wt_instrs:
      forall pc instr, 
      f.(fn_code)!pc = Some instr -> wt_instr f instr;
    wt_entrypoint:
      valid_successor f f.(fn_entrypoint)
}.

Inductive wt_fundef: fundef -> Prop :=
  | wt_fundef_external: forall ef,
      wt_fundef (External ef)
  | wt_function_internal: forall f,
      wt_function f ->
      wt_fundef (Internal f).

Definition wt_program (p: program): Prop :=
  forall i f, In (i, f) (prog_funct p) -> wt_fundef f.
