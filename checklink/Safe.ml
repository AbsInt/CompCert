(* "Hacker's Delight", section 2.12 *)

let ( + ) x y =
  let z = x + y in
  (* Overflow occurs iff x and y have same sign and z's sign is different *)
  if (z lxor x) land (z lxor y) < 0
  then raise Exc.IntOverflow
  else z

let ( - ) x y =
  let z = x - y in
  (* Overflow occurs iff x and y have opposite signs and z and x have
     opposite signs *)
  if (x lxor y) land (z lxor x) < 0
  then raise Exc.IntOverflow
  else z

let ( * ) x y =
  let z = x * y in
  if (x = min_int && y < 0) || (y <> 0 && z / y <> x)
  then raise Exc.IntOverflow
  else z

let of_int32 = Safe32.to_int
let to_int32 = Safe32.of_int
