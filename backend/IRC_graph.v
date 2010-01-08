Require Import FSets.
Require Import InterfGraphMapImp.

Record irc_graph := Make_IRC_Graph {
irc_g : tt;
irc_wl : WS;
pal : VertexSet.t;
irc_k : nat;
HWS_irc : WS_properties irc_g irc_k irc_wl;
Hk : VertexSet.cardinal pal = irc_k
}.

Definition graph_to_IRC_graph g palette :=
let K := VertexSet.cardinal palette in
Make_IRC_Graph g (get_WL g K) palette K (WS_prop_get _ _) (refl_equal _).
