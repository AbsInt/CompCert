(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Jacques-Henri Jourdan, INRIA Paris-Rocquencourt            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

type identifier_type =
  | VarId
  | TypedefId
  | OtherId

let save_context:(unit -> (unit -> unit)) ref = ref (fun _ -> assert false)
let declare_varname:(string -> unit) ref = ref (fun _ -> assert false)
let declare_typename:(string -> unit) ref = ref (fun _ -> assert false)
