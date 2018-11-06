(** TODO: add a proper header *)
From Coq Require Extraction.
From Coq Require Int31.

(* Emulated Int31 *)
Extract Constant Int31.twice => "(fun x -> Uint63.of_int (Camlcoq.Int31.twice (snd (Uint63.to_int2 x))))".
Extract Constant Int31.twice_plus_one => "(fun x -> Uint63.of_int (Camlcoq.Int31.twice_plus_one (snd (Uint63.to_int2 x))))".
Extract Constant Int31.compare31 => "(fun x y -> Camlcoq.Int31.compare (snd (Uint63.to_int2 x)) (snd (Uint63.to_int2 y)))".
Extract Constant Int31.On => "Uint63.zero".
Extract Constant Int31.In => "Uint63.one".
