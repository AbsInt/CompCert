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

(* Management of errors and warnings *)

open Format

let warn_error = ref false

let num_errors = ref 0
let num_warnings = ref 0

let reset () = num_errors := 0; num_warnings := 0

exception Abort

let fatal_error fmt =
  incr num_errors;
  kfprintf
    (fun _ -> raise Abort)
    err_formatter
    ("@[<hov 2>" ^^ fmt ^^ ".@]@.@[<hov 0>Fatal error.@]@.")

let error fmt =
  incr num_errors;
  eprintf  ("@[<hov 2>" ^^ fmt ^^ ".@]@.")

let warning fmt =
  incr num_warnings;
  eprintf  ("@[<hov 2>" ^^ fmt ^^ ".@]@.")

let check_errors () =
  if !num_errors > 0 then
    eprintf "@[<hov 0>%d error%s detected.@]@."
            !num_errors
            (if !num_errors = 1 then "" else "s");
  if !warn_error && !num_warnings > 0 then
    eprintf "@[<hov 0>%d error-enabled warning%s detected.@]@."
            !num_warnings
            (if !num_warnings = 1 then "" else "s");
  !num_errors > 0 || (!warn_error && !num_warnings > 0)


