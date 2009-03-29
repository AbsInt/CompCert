open Cil

(* Contributed by Nathan Cooprider *)

let isOne e = 
  isInteger e = Some Int64.one


(* written by Zach *)
let is_volatile_tp tp =
  List.exists (function (Attr("volatile",_)) -> true 
    | _ -> false) (typeAttrs tp) 
    
(* written by Zach *)
let is_volatile_vi vi =
  let vi_vol =
    List.exists (function (Attr("volatile",_)) -> true 
      | _ -> false) vi.vattr in
  let typ_vol = is_volatile_tp vi.vtype in
  vi_vol || typ_vol

(*****************************************************************************
 * A collection of useful functions that were not already in CIL as far as I 
 * could tell. However, I have been surprised before . . . 
 ****************************************************************************)

type sign = Signed | Unsigned 

exception Not_an_integer

(*****************************************************************************
 * A bunch of functions for accessing integers. Originally written for 
 * somebody who didn't know CIL and just wanted to mess with it at the 
 * OCaml level. 
 ****************************************************************************)

let unbox_int_type (ye : typ) : (int * sign) =
  let tp = unrollType ye in
  let s = 
    match tp with 
      TInt (i, _) -> 
	if (isSigned i) then
	  Signed
	else
	  Unsigned
    | _ -> raise Not_an_integer
  in
  (bitsSizeOf tp), s
  
(* depricated. Use isInteger directly instead *)
let unbox_int_exp (e : exp) : int64 = 
  match isInteger e with 
    None -> raise Not_an_integer
  | Some (x) -> x
  
let box_int_to_exp (n : int64) (ye : typ) : exp =
  let tp = unrollType ye in
  match tp with 
    TInt (i, _) -> 
      kinteger64 i n 
  | _ -> raise Not_an_integer

let cil_to_ocaml_int (e : exp) : (int64 * int * sign) = 
  let v, s = unbox_int_type (typeOf e) in
  unbox_int_exp (e), v, s

exception Weird_bitwidth

(* (int64 * int * sign) : exp *)
let ocaml_int_to_cil v n s =
  let char_size = bitsSizeOf charType in 
  let int_size = bitsSizeOf intType in
  let short_size = bitsSizeOf (TInt(IShort,[]))in 
  let long_size = bitsSizeOf longType in
  let longlong_size = bitsSizeOf (TInt(ILongLong,[])) in
  let i = 
    match s with
      Signed ->
	if (n = char_size) then 
	  ISChar
	else if (n = int_size) then
	  IInt
	else if (n = short_size) then
	  IShort
	else if (n = long_size) then
	  ILong
	else if (n = longlong_size) then
	  ILongLong
	else
	  raise Weird_bitwidth
    | Unsigned ->
	if (n = char_size) then 
	  IUChar
	else if (n = int_size) then
	  IUInt
	else if (n = short_size) then
	  IUShort
	else if (n = long_size) then
	  IULong
	else if (n = longlong_size) then
	  IULongLong
	else
	  raise Weird_bitwidth
  in
  kinteger64 i v

(*****************************************************************************
 * a couple of type functions that I thought would be useful:
 ****************************************************************************)

let rec isCompositeType tp =
  match tp with
    TComp _  -> true
  | TPtr(x, _) -> isCompositeType x
  | TArray(x,_,_) -> isCompositeType x
  | TFun(x,_,_,_) -> isCompositeType x
  | TNamed (x,_) -> isCompositeType x.ttype
  | _ -> false

(** START OF deepHasAttribute ************************************************)
let visited = ref [] 
class attribute_checker target rflag = object (self)
  inherit nopCilVisitor
  method vtype t =
    match t with 
      TComp(cinfo, a) ->
	if(not (List.exists (fun x -> cinfo.cname = x) !visited )) then begin
	  visited := cinfo.cname :: !visited;
	  List.iter 
	    (fun f -> 
	      if (hasAttribute target f.fattr) then 
		rflag := true
	      else
		ignore(visitCilType (new attribute_checker target rflag) 
			 f.ftype)) cinfo.cfields;
	end;
	DoChildren	
    | TNamed(t1, a) ->
	if(not (List.exists (fun x -> t1.tname = x) !visited )) then begin
	  visited := t1.tname :: !visited;
	  ignore(visitCilType (new attribute_checker target rflag) t1.ttype);
	end;
	DoChildren
    | _ ->
	DoChildren
  method vattr (Attr(name,params)) =
    if (name = target) then rflag := true;
    DoChildren
end

let deepHasAttribute s t =
  let found = ref false in
  visited := [];
  ignore(visitCilType (new attribute_checker s found) t);
  !found
(** END OF deepHasAttribute **************************************************)

(** Stuff from ptranal, slightly modified ************************************)

(*****************************************************************************
 * A transformation to make every instruction be in its own statement.  
 ****************************************************************************)

class callBBVisitor = object
  inherit nopCilVisitor 

  method vstmt s =
    match s.skind with
      Instr(il) -> begin
	if (List.length il > 1) then 
          let list_of_stmts = List.map (fun one_inst -> 
            mkStmtOneInstr one_inst) il in
          let block = mkBlock list_of_stmts in
	  s.skind <- Block block;
	  ChangeTo(s)
	else
	  SkipChildren
      end
    | _ -> DoChildren

  method vvdec _ = SkipChildren
  method vexpr _ = SkipChildren
  method vlval _ = SkipChildren
  method vtype _ = SkipChildren
end 

let one_instruction_per_statement f =
  let thisVisitor = new callBBVisitor in
  visitCilFileSameGlobals thisVisitor f  

(*****************************************************************************
 * A transformation that gives each variable a unique identifier. 
 ****************************************************************************)

class vidVisitor = object
  inherit nopCilVisitor 
  val count = ref 0 

  method vvdec vi = 
    vi.vid <- !count ;
    incr count ; SkipChildren
end 

let globally_unique_vids f =
  let thisVisitor = new vidVisitor in
  visitCilFileSameGlobals thisVisitor f 

(** End of stuff from ptranal ************************************************)

class sidVisitor = object
  inherit nopCilVisitor 
  val count = ref 0 

  method vstmt s = 
    s.sid <- !count ;
    incr count ;
    DoChildren
end 

let globally_unique_sids f =
  let thisVisitor = new sidVisitor in
  visitCilFileSameGlobals thisVisitor f 

(** Comparing expressions without a Out_of_memory error **********************)

let compare_exp x y =
  compare x y
    
