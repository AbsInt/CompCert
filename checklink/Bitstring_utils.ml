(** Note that a bitstring is a triple (string * int * int), where the string
    contains the contents (the last char is filled up with zeros if necessary),
    the firts int gives the first bit to consider, and the second int gives the
    bit length of the considered bitstring.
*)
type bitstring = Bitstring.bitstring

(** Checks whether a given number of bits of a bitstring are zeroed. The
    bitstring may be longer.
    @param size number of bits to check
*)
let rec is_zeros (bs: bitstring) (size: int): bool =
  size = 0 ||
  if size >= 64
  then (
    bitmatch bs with
    | { 0L : 64 : int ; rest : -1 : bitstring } ->
        is_zeros rest (size - 64)
    | { _ } -> false
  )
  else (
    bitmatch bs with
    | { 0L : size : int } -> true
    | { _ } -> false
  )
