Require Import Recdef.
Require Import FSetInterface.
Require Import InterfGraphMapImp.
Require Import OrderedOption.
Require Import FMapAVL.
Require Import IRC_termination.
Require Import IRC_graph.
Require Import IRC_Graph_Functions.
Require Import Edges.

Import Edge RegFacts Props OTFacts.

(* Definition of Register options *)

Module OptionReg := OrderedOpt Register.

(* Definition of the type of colorings *)

Definition Coloring := Register.t -> OptionReg.t.

(* Map used to build a coloring of the graph.
   A coloring is a the function find applied to the map *)

Module ColorMap := FMapAVL.Make Register.

(* Function to complete a coloring by giving the 
   same color to coalesced vertices *)

Definition complete_coloring e col : ColorMap.t Register.t := 
let x := snd_ext e in let y := fst_ext e in
match ColorMap.find y col with
| None => col
| Some c => ColorMap.add x c col
end.

(* Function to compute forbidden colors when completing the coloring
   for simplified or spilled registers (optimistic spilling) *)

Section add_monad.

Definition vertex_add_monad (o : option Register.t) (VS : VertexSet.t) :=
match o with
|Some v => VertexSet.add v VS
|None => VS
end.

Variable A : Type.

Lemma monad_fold : forall f a l s,
VertexSet.Equal (fold_left 
                (fun (x : VertexSet.t) (e : A) => vertex_add_monad (f e) x) 
                (a :: l) s)
       (vertex_add_monad (f a) 
       (fold_left (fun (x : VertexSet.t) (e : A) => vertex_add_monad (f e) x) l s)).

Proof.
intros f a l s;apply fold_left_assoc.
intros y z e;unfold vertex_add_monad.
destruct (f y);destruct (f z);[apply add_add|intuition|intuition|intuition].
intros e1 e2 y H. unfold vertex_add_monad.
destruct (f y);intuition.
apply Dec.F.add_m; intuition.
Qed.

End add_monad.

Definition forbidden_colors x col g := 
VertexSet.fold (fun v => vertex_add_monad (ColorMap.find v col)) 
                       (interference_adj x g)
                       VertexSet.empty.

(* Function to complete the coloring for simplified or spilled vertices.
   Calls forbidden_colors. Is choosing yet any available color *)

Definition available_coloring ircg x (col : ColorMap.t Register.t) :=
let g := (irc_g ircg) in let palette := (pal ircg) in
match (VertexSet.choose (VertexSet.diff palette (forbidden_colors x col g))) with
| None => col
| Some c => ColorMap.add x c col
end.

(* Definition of the empty coloring as the coloring where the only
   colored vertices are the precolored ones *)

Definition precoloring_map g := 
VertexSet.fold (fun x => ColorMap.add x x) (precolored g) (ColorMap.empty Register.t).

Function IRC_map (g : irc_graph)
{measure irc_measure g} : ColorMap.t Register.t :=
match simplify g with
|Some rg' => let (r,g') := rg' in available_coloring g r (IRC_map g')
|None     => match coalesce g with
          |Some eg' => let (e,g') := eg' in complete_coloring e (IRC_map g')
          |None     => match freeze g with
                    |Some rg' => let (r,g') := rg' in IRC_map g'
                    |None     => match spill g with
                              |Some rg' => let (r,g') := rg' in available_coloring g r (IRC_map g')
                              |None    => precoloring_map (irc_g g)
                           end
                  end
         end
end.

Proof.
intros. apply (simplify_dec g r g' teq).
intros. apply (coalesce_dec g e g' teq0).
intros. apply (freeze_dec g r g' teq1).
intros. apply (spill_dec g r g' teq2).
Qed.

(* Definition of the transformation from a map to a coloring,
   simply by using find *)

Definition map_to_coloring (colmap : ColorMap.t Register.t) := 
fun x => ColorMap.find x colmap.

(* Final definition of iterated register coalescing *)

Definition IRC g palette := 
let g' := graph_to_IRC_graph g palette in map_to_coloring (IRC_map g').

Definition precoloring g := map_to_coloring (precoloring_map g).
