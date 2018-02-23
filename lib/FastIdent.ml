(* The functions below are used in Symbols.v to implement a fast way to
  refer to global identifiers, where they are axiomatized as a bijective
  mapping. The bijection is built incrementally, and of_coqstring may
  insert a new entry in the hashtable, but cruicially the statefulness
  is not observable from the outside. As far as Coq knows, the mapping
  existed all along and we simply observed it for the first time.

  The functions below should not be used directly from ML code. Instead,
  the Camlcoq module provides wrappers to access them through the Ident
  module defined in Symbols.v. *)

open BinNums
open BinPos

let atom_of_coqstring = (Hashtbl.create 17 : (char list, positive) Hashtbl.t)
let coqstring_of_atom = (Hashtbl.create 17 : (positive, char list) Hashtbl.t)
let next_atom = ref Coq_xH

let of_coqstring s =
  try
    Hashtbl.find atom_of_coqstring s
  with Not_found ->
    let a = !next_atom in
    next_atom := Pos.succ !next_atom;
    Hashtbl.add atom_of_coqstring s a;
    Hashtbl.add coqstring_of_atom a s;
    a

let to_coqstring a =
  Hashtbl.find coqstring_of_atom a

