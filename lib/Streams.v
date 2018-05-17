(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Set Implicit Arguments.

CoInductive Stream (A : Type) : Type :=
    Cons : A -> Stream A -> Stream A.

Definition hd (A : Type) (x:Stream A) := match x with
                            | Cons a _ => a
                            end.

Definition tl (A : Type) (x:Stream A) := match x with
                            | Cons _ s => s
                            end.

CoFixpoint const (A : Type) (a : A) : Stream A := Cons a (const a).

Unset Implicit Arguments.
