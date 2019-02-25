(****************************************************************************)
(*                                                                          *)
(*                                   Menhir                                 *)
(*                                                                          *)
(*           Jacques-Henri Jourdan, CNRS, LRI, Université Paris Sud         *)
(*                                                                          *)
(*  Copyright Inria. All rights reserved. This file is distributed under    *)
(*  the terms of the GNU Lesser General Public License as published by the  *)
(*  Free Software Foundation, either version 3 of the License, or (at your  *)
(*  option) any later version, as described in the file LICENSE.            *)
(*                                                                          *)
(****************************************************************************)

From Coq Require Import List Syntax Orders.
Require Import Alphabet.

(** The terminal non-terminal alphabets of the grammar. **)
Module Type Alphs.
  Parameters terminal nonterminal : Type.
  Declare Instance TerminalAlph: Alphabet terminal.
  Declare Instance NonTerminalAlph: Alphabet nonterminal.
End Alphs.

(** Definition of the alphabet of symbols, given the alphabet of terminals
    and the alphabet of non terminals **)
Module Symbol(Import A:Alphs).

  Inductive symbol :=
    | T: terminal -> symbol
    | NT: nonterminal -> symbol.

  Program Instance SymbolAlph : Alphabet symbol :=
    { AlphabetComparable := {| compare := fun x y =>
        match x, y return comparison with
          | T _, NT _ => Gt
          | NT _, T _ => Lt
          | T x, T y => compare x y
          | NT x, NT y => compare x y
        end |};
      AlphabetFinite := {| all_list :=
        map T all_list++map NT all_list |} }.
  Next Obligation.
    destruct x; destruct y; intuition; apply compare_antisym.
  Qed.
  Next Obligation.
    destruct x; destruct y; destruct z; intuition; try discriminate.
    apply (compare_trans _ t0); intuition.
    apply (compare_trans _ n0); intuition.
  Qed.
  Next Obligation.
    intros x y.
    destruct x; destruct y; try discriminate; intros.
    rewrite (compare_eq t t0); now intuition.
    rewrite (compare_eq n n0); now intuition.
  Defined.
  Next Obligation.
    rewrite in_app_iff.
    destruct x; [left | right]; apply in_map; apply all_list_forall.
  Qed.

End Symbol.

(** A curryfied function with multiple parameters **)
Definition arrows_right: Type -> list Type -> Type :=
  fold_right (fun A B => A -> B).

Module Type T.
  Include Alphs <+ Symbol.

  (** [symbol_semantic_type] maps a symbols to the type of its semantic
     values. **)
  Parameter symbol_semantic_type: symbol -> Type.

  (** The type of productions identifiers **)
  Parameter production : Type.
  Declare Instance ProductionAlph : Alphabet production.

  (** Accessors for productions: left hand side, right hand side,
     and semantic action. The semantic actions are given in the form
     of curryfied functions, that take arguments in the reverse order. **)
  Parameter prod_lhs: production -> nonterminal.
  (* The RHS of a production is given in reversed order, so that symbols  *)
  Parameter prod_rhs_rev: production -> list symbol.
  Parameter prod_action:
    forall p:production,
      arrows_right
        (symbol_semantic_type (NT (prod_lhs p)))
        (map symbol_semantic_type (prod_rhs_rev p)).

  (** Tokens are the atomic elements of the input stream: they contain
     a terminal and a semantic value of the type corresponding to this
     terminal. *)
  Parameter token : Type.
  Parameter token_term : token -> terminal.
  Parameter token_sem :
    forall tok : token, symbol_semantic_type (T (token_term tok)).
End T.

Module Defs(Import G:T).

  (** The semantics of a grammar is defined in two stages. First, we
    define the notion of parse tree, which represents one way of
    recognizing a word with a head symbol. Semantic values are stored
    at the leaves.

      This notion is defined in two mutually recursive flavours:
    either for a single head symbol, or for a list of head symbols. *)
  Inductive parse_tree:
    forall (head_symbol:symbol) (word:list token), Type :=

  (** Parse tree for a terminal symbol. *)
  | Terminal_pt:
    forall (tok:token), parse_tree (T (token_term tok)) [tok]

  (** Parse tree for a non-terminal symbol.  *)
  | Non_terminal_pt:
    forall (prod:production) {word:list token},
      parse_tree_list (prod_rhs_rev prod) word ->
      parse_tree (NT (prod_lhs prod)) word

  (* Note : the list head_symbols_rev is reversed. *)
  with parse_tree_list:
    forall (head_symbols_rev:list symbol) (word:list token), Type :=

  | Nil_ptl: parse_tree_list [] []

  | Cons_ptl:
    forall {head_symbolsq:list symbol} {wordq:list token},
      parse_tree_list head_symbolsq wordq ->

    forall {head_symbolt:symbol} {wordt:list token},
      parse_tree head_symbolt wordt ->

      parse_tree_list (head_symbolt::head_symbolsq) (wordq++wordt).

  (** We can now finish the definition of the semantics of a grammar,
    by giving the semantic value assotiated with a parse tree. *)
  Fixpoint pt_sem {head_symbol word} (tree:parse_tree head_symbol word) :
    symbol_semantic_type head_symbol :=
    match tree with
    | Terminal_pt tok => token_sem tok
    | Non_terminal_pt prod ptl => ptl_sem ptl (prod_action prod)
    end
  with ptl_sem {A head_symbols word} (tree:parse_tree_list head_symbols word) :
    arrows_right A (map symbol_semantic_type head_symbols) -> A :=
    match tree with
    | Nil_ptl => fun act => act
    | Cons_ptl q t => fun act => ptl_sem q (act (pt_sem t))
    end.

  Fixpoint pt_size {head_symbol word} (tree:parse_tree head_symbol word) :=
    match tree with
      | Terminal_pt _ => 1
      | Non_terminal_pt _ l => S (ptl_size l)
    end
  with ptl_size {head_symbols word} (tree:parse_tree_list head_symbols word) :=
    match tree with
      | Nil_ptl => 0
      | Cons_ptl q t =>
         pt_size t + ptl_size q
    end.
End Defs.
