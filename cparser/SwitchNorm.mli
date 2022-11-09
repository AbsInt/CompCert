(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, Collège de France and Inria                  *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(* Normalization of structured "switch" statements
   and emulation of unstructured "switch" statements (e.g. Duff's device) *)

(* Assumes: nothing
   Produces: code with normalized "switch" statements *)

(* A normalized switch has the following form:
     Sswitch(e, Sblock [ Slabeled(lbl1, case1); ...
                         Slabeled(lblN,caseN) ])
*)

val program: bool -> C.program -> C.program
