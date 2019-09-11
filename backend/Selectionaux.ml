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

(* The if-conversion heuristic depend on the
   -fif-conversion and -Obranchless flags.

With [-fno-if-conversion] or [-0O], if-conversion is turned off entirely.
With [-Obranchless], if-conversion is performed whenever semantically
correct, regardless of how much it could cost.
Otherwise (and by default), optimization is performed when it seems beneficial.

If-conversion seems beneficial if:
- the target architecture supports an efficient "conditional move" instruction
  (not an emulation that takes several instructions)
- the total cost the "then" and "else" branches is not too high
- the cost difference between the "then" and "else" branches is low enough.

Intuition: on a modern processor, the "then" and the "else" branches
can generally be computed in parallel, there is enough ILP for that.
So, the bad case is if the most taken branch is much cheaper than the
other branch.  Another bad case is if both branches are big: since the
code for one branch precedes entirely the code for the other branch,
if the first branch contains a lot of instructions,
dynamic reordering of instructions will not look ahead far enough
to execute instructions from the other branch in parallel with
instructions from the first branch.
*)

let if_conversion_heuristic cond ifso ifnot ty =
  if not !Clflags.option_fifconversion then false else
  if !Clflags.option_Obranchless then true else
  if not (fast_cmove ty) then false else
  let c1 = cost_expr ifso and c2 = cost_expr ifnot in
  c1 + c2 <= 24 && abs (c1 - c2) <= 8

