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

(* Platform-dependent handling of pragmas *)

(* No pragmas supported on PowerPC/MacOS *)

let initialize () = ()

(* PowerPC-specific: say if an atom is in a small data area *)

let atom_is_small_data a ofs = false

(* PowerPC-specific: determine section to use for a particular symbol *)

let section_for_atom a init = None
