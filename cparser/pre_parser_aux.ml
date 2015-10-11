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

(* These functions push and pop a context on the contexts stack. *)
let open_context:(unit -> unit) ref = ref (fun () -> assert false)
let close_context:(unit -> unit) ref = ref (fun () -> assert false)

(* Applying once this functions saves the whole contexts stack, and
   applying it the second time restores it.

   This is mainly used to rollback the context stack to a previous
   state. This is usefull for example when we pop too much contexts at
   the end of the first branch of an if statement. See
   pre_parser.mly. *)
let save_contexts_stk:(unit -> (unit -> unit)) ref = ref (fun _ -> assert false)

(* Change the context at the top of the top stack of context, by
   changing an identifier to be a varname or a typename*)
let declare_varname:(string -> unit) ref = ref (fun _ -> assert false)
let declare_typename:(string -> unit) ref = ref (fun _ -> assert false)
