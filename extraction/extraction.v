Require Floats.
Require Kildall.
Require RTLgen.
Require Coloring.
Require Allocation.
Require Cmconstr.
Require Main.

(* Standard lib *)
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].

(* Float *)
Extract Inlined Constant Floats.float => "float".
Extract Constant Floats.Float.zero   => "0.".
Extract Constant Floats.Float.one   => "1.".
Extract Constant Floats.Float.neg => "( ~-. )".
Extract Constant Floats.Float.abs => "abs_float".
Extract Constant Floats.Float.singleoffloat => "Floataux.singleoffloat".
Extract Constant Floats.Float.intoffloat => "Floataux.intoffloat".
Extract Constant Floats.Float.floatofint => "Floataux.floatofint".
Extract Constant Floats.Float.floatofintu => "Floataux.floatofintu".
Extract Constant Floats.Float.add => "( +. )".
Extract Constant Floats.Float.sub => "( -. )".
Extract Constant Floats.Float.mul => "( *. )".
Extract Constant Floats.Float.div => "( /. )".
Extract Constant Floats.Float.cmp => "Floataux.cmp".
Extract Constant Floats.Float.eq_dec => "fun (x: float) (y: float) -> x = y".

(* RTLgen *)
Extract Constant RTLgen.more_likely => "RTLgenaux.more_likely".

(* Coloring *)
Extract Constant Coloring.graph_coloring => "Coloringaux.graph_coloring".

(* PPC *)
Extract Constant PPC.low_half_signed => "fun _ -> assert false".
Extract Constant PPC.high_half_signed => "fun _ -> assert false".
Extract Constant PPC.low_half_unsigned => "fun _ -> assert false".
Extract Constant PPC.high_half_unsigned => "fun _ -> assert false".

(* Suppression of stupidly big equality functions *)
Extract Constant CSE.eq_rhs => "fun (x: rhs) (y: rhs) -> x = y".
Extract Constant Locations.mreg_eq => "fun (x: mreg) (y: mreg) -> x = y".
Extract Constant PPC.ireg_eq => "fun (x: ireg) (y: ireg) -> x = y".
Extract Constant PPC.freg_eq => "fun (x: freg) (y: freg) -> x = y".
Extract Constant PPC.preg_eq => "fun (x: preg) (y: preg) -> x = y".

(* Go! *)
Recursive Extraction Library Main.
(*Extraction Library Compare_dec.
  Extraction Library Cmconstr.*)
