type exp = Addition of exp*exp | Numeral of int | Variable of string;;
type b_exp = Greater of exp*exp;;
type inst = Assignment of string * exp | Sequence of inst * inst
            | While of b_exp * inst | Skip;;

type environment = (string * int) list;;

let rec lookup (env:environment) (var:string) =
  match env with
      [] -> failwith(var ^ " : no such variable in environment for lookup")
    | (a,v)::tl -> if a = var then v else lookup tl var;;

let rec update (env:environment) (var:string) (n:int) =
  match env with
      [] -> failwith(var ^ " : no such variable in environment for update")
    | ((a,v) as pair)::tl ->
	if a = var then (a,n)::tl else pair::(update tl var n);;

let rec evaluate (env:environment)(e:exp) =
  match e with
      Numeral n -> n
    | Variable s -> lookup env s
    | Addition(e1,e2) -> evaluate env e1 + evaluate env e2;;


let evaluate_bool (env:environment)(e:b_exp) =
  match e with
      Greater(e1,e2) -> evaluate env e1 > evaluate env e2;;

let rec execute (env:environment)(i:inst) =
  match i with
      Skip -> env
    | Assignment(s,e) -> update env s (evaluate env e)
    | Sequence(i1,i2) -> execute (execute env i1) i2
    | While(b,i) as it ->
	if (evaluate_bool env b) then
            execute (execute env i) it
        else
            env;;

let print_env = 
   List.iter
     (fun (s,n) -> print_string (s ^ " : " ^ (string_of_int n) ^ "\n"));;
