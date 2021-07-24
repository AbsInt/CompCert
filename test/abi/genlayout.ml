open Printf

type typ = Bool | Char | Short | Int

type field =
  | Plain of typ
  | Bitfield of typ * int
  | Padding of typ * int

type struct_ = field list

(* Concise description of a struct *)

let print_typ oc = function
  | Bool -> fprintf oc "b"
  | Char -> fprintf oc "c"
  | Short -> fprintf oc "s"
  | Int -> fprintf oc "i"

let print_padding_typ oc = function
  | Bool -> fprintf oc "B"
  | Char -> fprintf oc "C"
  | Short -> fprintf oc "S"
  | Int -> fprintf oc "I"

let print_field oc = function
  | Plain t -> print_typ oc t
  | Bitfield(t, w) -> fprintf oc "%a%d" print_typ t w
  | Padding(t, w) -> fprintf oc "%a%d" print_padding_typ t w

let rec print_struct oc = function
  | [] -> ()
  | f :: s -> print_field oc f; print_struct oc s

(* Printing a struct in C syntax *)

let c_typ oc = function
  | Bool -> fprintf oc "_Bool"
  | Char -> fprintf oc "char"
  | Short -> fprintf oc "short"
  | Int -> fprintf oc "int"

let c_name oc n = fprintf oc "%c" (Char.chr (Char.code 'a' + n))

let c_field oc n = function
  | Plain t ->
      fprintf oc "  %a %a;\n" c_typ t c_name n; 
      n + 1
  | Bitfield(t, w) -> 
      fprintf oc "  %a %a:%d;\n" c_typ t c_name n w;
      n + 1
  | Padding(t, w) ->
      fprintf oc "  %a :%d;\n" c_typ t w;
      n

let c_struct oc s =
  fprintf oc "struct %a {\n" print_struct s;
  let rec c_str n = function
    | [] -> ()
    | f :: s -> let n' = c_field oc n f in c_str n' s in
  c_str 0 s;
  fprintf oc "};\n"

(* Random generation of structs *)

let random_1_8 () =
  let n1 = Random.bits() in
  let n2 = n1 lsr 2 in
  match n1 land 3 with
  | 0 -> 1
  | 1 -> 2 + (n2 land 1)   (* 2-3 *)
  | 2 -> 4 + (n2 land 1)   (* 4-5 *)
  | 3 -> 6 + (n2 mod 3)    (* 6-8 *)
  | _ -> assert false

let random_1_16 () =
  let n1 = Random.bits() in
  let n2 = n1 lsr 2 in
  match n1 land 3 with
  | 0 -> 1 + (n2 land 1)   (* 1-2 *)
  | 1 -> 3 + (n2 mod 3)    (* 3-4-5 *)
  | 2 -> 6 + (n2 land 3)   (* 6-7-8-9 *)
  | 3 -> 10 + (n2 mod 7)   (* 10-16 *)
  | _ -> assert false

let random_1_32 () =
  let n1 = Random.bits() in
  let n2 = n1 lsr 2 in
  match n1 land 3 with
  | 0 -> 1 + (n2 land 1)   (* 1-2 *)
  | 1 -> 3 + (n2 mod 5)    (* 3-4-5-6-7 *)
  | 2 -> 8 + (n2 mod 8)    (* 8-15 *)
  | 3 -> 16 + (n2 mod 17)  (* 16-32 *)
  | _ -> assert false

let random_field () =
  let (t, w) =
    match Random.int 9 with
    | 0   -> (Bool, 1)
    | 1|2 -> (Char, random_1_8())
    | 3|4 -> (Short, random_1_16())
    | _ -> (Int, random_1_32()) in
  match Random.int 10 with
  | 0 -> Padding(t, (if Random.int 3 = 0 then 0 else w))
  | 1 | 2 -> Plain t
  | _ -> Bitfield(t, w)

let rec random_struct len =
  if len <= 0 then [] else begin
    let f = random_field () in
    f :: random_struct (match f with Padding _ -> len | _ -> len - 1)
  end

(* Optional filtering of structs where padding fields can increase alignment.
   ELF says that padding fields are ignored to determine struct alignment,
   but ARM does otherwise. *)

let alignof = function Bool -> 1 | Char -> 1 | Short -> 2 | Int -> 4

let unstable_alignment str =
  let rec alignments al_data al_padding = function
    | [] ->
        al_padding > al_data
    | (Plain t | Bitfield(t, _)) :: l ->
        alignments (max (alignof t) al_data) al_padding l
    | Padding(t, _) :: l ->
        alignments al_data (max (alignof t) al_padding) l
  in
    alignments 1 1 str

(* Random testing *)

let structsize = ref 4
let ntests = ref 1000
let stable = ref false

let _ =
  Arg.parse [
     "-size", Arg.Int (fun n -> structsize := n),
       " <sz> produce structs with <sz> members (default: 4)";
     "-n", Arg.Int (fun n -> ntests := n),
       " <num> produce <num> random structs";
     "-seed", Arg.Int Random.init,
       " <seed> use the given seed for randomization";
     "-stable", Arg.Set stable,
       " don't generate padding fields that could cause differences in alignment"
  ]
  (fun s -> raise (Arg.Bad ("don't know what to do with " ^ s)))
  "Usage: genlayout [options]\n\nOptions are:";
  for _i = 1 to !ntests do
    let s = random_struct !structsize in
    if not (!stable && unstable_alignment s) then begin
      printf "{\n";
      c_struct stdout s;
      printf "TEST%d(%a)\n" !structsize print_struct s;
      printf "}\n"
    end
  done
