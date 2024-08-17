(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, Collège de France and Inria Paris            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open AST
open Cminor

(* Heuristics to guide if conversion *)

(* Estimate a cost for evaluating a safe expression.
   Unsafe operators need not be estimated.
   Basic integer operations (add, and, ...) have cost 1 by convention.
   The other costs are rough estimates. *)

let cost_unop = function
  | Ocast8unsigned | Ocast8signed
  | Ocast16unsigned | Ocast16signed
  | Onegint | Onotint -> 1
  | Onegf | Oabsf -> 1
  | Onegfs | Oabsfs -> 1
  | Osingleoffloat | Ofloatofsingle -> 2
  | Ointoffloat | Ointuoffloat
  | Ofloatofint | Ofloatofintu
  | Ointofsingle | Ointuofsingle
  | Osingleofint | Osingleofintu -> assert false
  | Onegl | Onotl -> if Archi.splitlong then 2 else 1
  | Ointoflong | Olongofint | Olongofintu -> 1
  | Olongoffloat | Olonguoffloat
  | Ofloatoflong | Ofloatoflongu
  | Olongofsingle | Olonguofsingle
  | Osingleoflong | Osingleoflongu -> assert false

let cost_binop = function
  | Oadd  | Osub -> 1
  | Omul -> 2
  | Odiv  | Odivu | Omod  | Omodu -> assert false
  | Oand  | Oor   | Oxor  | Oshl  | Oshr  | Oshru -> 1
  | Oaddf | Osubf | Omulf -> 2
  | Odivf -> 10
  | Oaddfs| Osubfs| Omulfs -> 2
  | Odivfs -> 10
  | Oaddl | Osubl -> if Archi.splitlong then 3 else 1
  | Omull -> if Archi.splitlong then 6 else 2
  | Odivl | Odivlu | Omodl | Omodlu -> assert false
  | Oandl | Oorl  | Oxorl -> if Archi.splitlong then 2 else 1
  | Oshll | Oshrl | Oshrlu -> if Archi.splitlong then 4 else 1
  | Ocmp _ | Ocmpu _ -> 2
  | Ocmpf _ | Ocmpfs _ -> 2
  | Ocmpl _ | Ocmplu _ -> assert false

let rec cost_expr = function
  | Evar _ -> 0
  | Econst _ -> 1
  | Eunop(op, e1) -> cost_unop op + cost_expr e1
  | Ebinop(op, e1, e2) -> cost_binop op + cost_expr e1 + cost_expr e2
  | Eload(_, e1) -> assert false

(* Does the target architecture support an efficient "conditional move"
   at the given type? *)

let fast_cmove ty =
  match Configuration.arch, Configuration.model with
  | "aarch64", _ ->
      (match ty with Tint | Tlong | Tfloat | Tsingle -> true | _ -> false)
  | "arm", _ ->
      (match ty with Tint | Tfloat | Tsingle -> true | _ -> false)
  | "powerpc", "e5500" -> 
      (match ty with Tint -> true | Tlong -> true | _ -> false)
  | "powerpc", _ -> false
  | "riscV", _ -> false
  | "x86", _ -> 
      (match ty with Tint -> true | Tlong -> Archi.ptr64 | _ -> false)
  | _, _ ->
      assert false

(* The if-conversion heuristic depend on the [-fif-conversion]
and [-Obranchless] flags.

With [-fno-if-conversion] or [-0O], if-conversion is turned off entirely.

With [-Obranchless], if-conversion is performed whenever semantically
correct, regardless of how much it could cost.

Otherwise (and by default), optimization is performed when it seems beneficial.

If-conversion seems beneficial if:
- the target architecture supports an efficient "conditional move" instruction
  (not an emulation that takes several instructions);
- the total cost the "then" and "else" branches is not too high;
- the cost difference between the "then" and "else" branches is low enough;
- if-conversion will not inhibit further optimization such as
  the [successor] optimization in [Constprop].

Intuitions for the two cost criteria:

On a modern processor, the "then" and the "else" branches can
generally be computed in parallel, there is enough ILP for that.
But, if one of the branches is much cheaper than the other, and happens
to be the most taken branch, we're wasting CPU time computing the other
branch every time.

Another bad case is if both branches are big: since the code for one
branch precedes entirely the code for the other branch, if the first
branch contains a lot of instructions, dynamic reordering of
instructions will not look ahead far enough to execute instructions
from the other branch in parallel with instructions from the first
branch.
*)

let cost_criterion ifso ifnot =
  let c1 = cost_expr ifso and c2 = cost_expr ifnot in
  c1 + c2 <= 24 && abs (c1 - c2) <= 8

(*
Intuition for the later optimization that should not be prevented:

Consider the C code
<<
     if (c1 && c2) goto lbl1; else goto lbl2;
>>
where [c1] and [c2] are simple comparisons.  The corresponding Cminor code is
<<
     if (c1) t = (_Bool) c2; else t = 0;
     if (t != 0) goto lbl1; else goto lbl2;
>>
Without if-conversion of the first [if], the Constprop and CSE/CombineOp
passes manage to produce RTL code equivalent to
<<
     if (c1) { if (c2) goto lbl1; else goto lbl2;} else goto lbl2;
>>
With if-conversion of the first [if], we obtain the following RTL code
<<
     t = select(c1, (_Bool) c2, 0);
     if (t != 0) goto lbl1; else goto lbl2;
>>
which is generally less efficient, as the conversion of [c2] to a Boolean value
and the selection on [c1] take significantly more instructions than
two conditional branches on [c1] and [c2].

We recognize the following pattern, for which we turn if-conversion off:
- one of the arms of the [if] statement is [t := constant];
- just after the [if] statement comes a [if (t cmp constant)] conditional
  statement.

For this pattern, we know that the [successor] optimization in [Constprop]
will generate a direct jump from the [t := constant] to the appropriate
arm of the [if (t cmp constant)] conditional.
*)

let is_const = function
  | Econst(Ointconst _) -> true
  | _ -> false

let rec is_if (k : CminorSel.stmt) =
  let open! CminorSel in
  match k with
  | Sifthenelse(CEcond(Op.Ccompuimm _, Econs (Evar id, Enil)), _, _) -> Some id
  | Sseq(Sskip, s2) -> is_if s2
  | Sseq(Sbuiltin(_, EF_debug _, _), s2) -> is_if s2
  | Sseq(s1, s2) -> is_if s1
  | _ -> None

let optimization_criterion id ifso ifnot kont =
  match is_if kont with
  | Some id' -> not (id' = id && (is_const ifso || is_const ifnot))
  | _ -> true

let if_conversion_heuristic id cond ifso ifnot ty kont =
  if not !Clflags.option_fifconversion then false else
  if !Clflags.option_Obranchless then true else
  if not (fast_cmove ty) then false else
  cost_criterion ifso ifnot && optimization_criterion id ifso ifnot kont

