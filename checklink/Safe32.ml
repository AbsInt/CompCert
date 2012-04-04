(* "Hacker's Delight", section 2.12 *)

let ( + ) x y = Int32.(
  let z = add x y in
  (* Overflow occurs iff x and y have same sign and z's sign is different *)
  if logand (logxor z x) (logxor z y) < 0l
  then raise Exc.Int32Overflow
  else z
)

let ( - ) x y = Int32.(
  let z = sub x y in
  (* Overflow occurs iff x and y have opposite signs and z and x have
     opposite signs *)
  if logand (logxor x y) (logxor z x) < 0l
  then raise Exc.Int32Overflow
  else z
)

let ( * ) x y = Int32.(
  let z = mul x y in
  if (x = min_int && y < 0l) || (y <> 0l && div z y <> x)
  then raise Exc.Int32Overflow
  else z
)

let to_int i32 = Int32.(
  let i = to_int i32 in
  if i32 = of_int i
  then i
  else raise Exc.IntOverflow
)

let of_int = Int32.of_int
