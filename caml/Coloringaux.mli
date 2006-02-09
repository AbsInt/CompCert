open Registers
open Locations
open RTL
open RTLtyping
open InterfGraph

val graph_coloring:
  coq_function -> graph -> regenv -> Regset.t -> (reg -> loc)
