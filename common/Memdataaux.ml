(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open Camlcoq
open Integers
open AST

let big_endian =
  match Configuration.arch with
  | "powerpc" -> true
  | "arm" -> false
  | _ -> assert false

let encode_float chunk f =
  match chunk with
  | Mint8unsigned | Mint8signed ->
      [Byte.zero]
  | Mint16unsigned | Mint16signed ->
      [Byte.zero; Byte.zero]
  | Mint32 ->
      [Byte.zero; Byte.zero; Byte.zero; Byte.zero]
  | Mfloat32 ->
      let bits = Int32.bits_of_float f in
      let byte n =
        coqint_of_camlint
          (Int32.logand (Int32.shift_right_logical bits n) 0xFFl) in
      if big_endian then
        [byte 24; byte 16; byte 8; byte 0]
      else
        [byte 0; byte 8; byte 16; byte 24]
  | Mfloat64 ->
      let bits = Int64.bits_of_float f in
      let byte n =
        coqint_of_camlint
          (Int64.to_int32
            (Int64.logand (Int64.shift_right_logical bits n) 0xFFL)) in
      if big_endian then
        [byte 56; byte 48; byte 40; byte 32; byte 24; byte 16; byte 8; byte 0]
      else
        [byte 0; byte 8; byte 16; byte 24; byte 32; byte 40; byte 48; byte 56]

let decode_float chunk bytes =
  match chunk with
  | Mfloat32 ->
      let combine accu b =
        Int32.logor (Int32.shift_left accu 8) (camlint_of_coqint b) in
      Int32.float_of_bits
        (List.fold_left combine 0l
          (if big_endian then bytes else List.rev bytes))
  | Mfloat64 ->
      let combine accu b =
        Int64.logor (Int64.shift_left accu 8)
                    (Int64.of_int32 (camlint_of_coqint b)) in
      Int64.float_of_bits
        (List.fold_left combine 0L
          (if big_endian then bytes else List.rev bytes))
  | _ ->
      0.0 (* unspecified *)

