(**
This file is part of the Flocq formalization of floating-point
arithmetic in Coq: http://flocq.gforge.inria.fr/

Copyright (C) 2011-2013 Sylvie Boldo
#<br />#
Copyright (C) 2011-2013 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(** Helper for detecting the version of Flocq *)
Require Import BinNat.
Require Import Ascii String.

Definition Flocq_version := Eval vm_compute in
  let fix parse s major minor :=
    match s with
    | String "."%char t => parse t (major * 100 + minor)%N N0
    | String h t =>
      parse t major (minor * 10 + N_of_ascii h - N_of_ascii "0"%char)%N
    | Empty_string => (major * 100 + minor)%N
    end in
  parse "2.6.1"%string N0 N0.
