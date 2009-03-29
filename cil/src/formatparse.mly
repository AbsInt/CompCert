/* MODIF: Loop constructor replaced by 3 constructors: While, DoWhile, For. */

/*(* Parser for constructing CIL from format strings *)
(*
 *
 * Copyright (c) 2001-2002, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)
*/
%{
open Cil
open Pretty
module E = Errormsg

let parse_error msg : 'a =           (* sm: c++-mode highlight hack: -> ' <- *)
  E.hadErrors := true;
  E.parse_error
    msg


let getArg (argname: string) (args: (string * formatArg) list) = 
  try 
    snd (List.find (fun (n, a) -> n = argname) args)
  with _ -> 
    E.s (error "Pattern string %s does not have argument with name %s\n"
           !Lexerhack.currentPattern argname)

let wrongArgType (which: string) (expected: string) (found: formatArg) = 
  E.s (bug "Expecting %s argument (%s) and found %a\n" 
         expected which d_formatarg found)

let doUnop (uo: unop) subexp = 
  ((fun args -> 
        let e = (fst subexp) args in
        UnOp(uo, e, typeOf e)),

   (fun e -> match e with 
     UnOp(uo', e', _) when uo  = uo' -> (snd subexp) e' 
   | _ -> None)) 

let buildPlus e1 e2 : exp = 
  let t1 = typeOf e1 in
  if isPointerType t1 then 
    BinOp(PlusPI, e1, e2, t1)
  else 
    BinOp(PlusA, e1, e2, t1)

let buildMinus e1 e2 : exp = 
  let t1 = typeOf e1 in
  let t2 = typeOf e2 in
  if isPointerType t1 then
    if isPointerType t2 then
      BinOp(MinusPP, e1, e2, intType)
    else
      BinOp(MinusPI, e1, e2, t1)
  else
    BinOp(MinusA, e1, e2, t1)

let doBinop bop e1t e2t = 
  ((fun args -> 
    let e1 = (fst e1t) args in 
    let e2 = (fst e2t) args in 
    let t1 = typeOf e1 in
    BinOp(bop, e1, e2, t1)),

   (fun e -> match e with 
     BinOp(bop', e1, e2, _) when bop' = bop -> begin
       match (snd e1t) e1, (snd e2t) e2 with
         Some m1, Some m2 -> Some (m1 @ m2)
       | _, _ -> None
     end
   | _ -> None))

(* Check the equivalence of two format lists *)
let rec checkSameFormat (fl1: formatArg list) (fl2: formatArg list) = 
  match fl1, fl2 with 
    [], [] -> true
  | h1::t1, h2::t2 -> begin
      let rec checkOffsetEq o1 o2 = 
        match o1, o2 with
          NoOffset, NoOffset -> true
        | Field(f1, o1'), Field(f2, o2') -> 
            f1.fname = f2.fname && checkOffsetEq o1' o2'
        | Index(e1, o1'), Index(e2, o2') -> 
            checkOffsetEq o1' o2' && checkExpEq e1 e2
        | _, _ -> false

      and checkExpEq e1 e2 = 
        match e1, e2 with 
          Const(CInt64(n1, _, _)), Const(CInt64(n2, _, _)) -> n1 = n2
        | Lval l1, Lval l2 -> checkLvalEq l1 l2
        | UnOp(uo1, e1, _), UnOp(uo2, e2, _) -> 
            uo1 = uo2 && checkExpEq e1 e2
        | BinOp(bo1, e11, e12, _), BinOp(bo2, e21, e22, _) -> 
            bo1 = bo2 && checkExpEq e11 e21 && checkExpEq e21 e22
        | AddrOf l1, AddrOf l2 -> checkLvalEq l1 l2
        | StartOf l1, StartOf l2 -> checkLvalEq l1 l2
        | SizeOf t1, SizeOf t2 -> typeSig t1 = typeSig t2
        | _, _ -> 
            ignore (E.warn "checkSameFormat for Fe"); false

      and checkLvalEq l1 l2 = 
        match l1, l2 with
          (Var v1, o1), (Var v2, o2) -> v1 == v2 && checkOffsetEq o1 o2
        | (Mem e1, o1), (Mem e2, o2) -> 
            checkOffsetEq o1 o2 && checkExpEq e1 e2
        | _, _ -> false
      in
      let hdeq = 
        match h1, h2 with 
          Fv v1, Fv v2 -> v1 == v2
        | Fd n1, Fd n2 -> n1 = n2
        | Fe e1, Fe e2 -> checkExpEq e1 e2
        | Fi i1, Fi i2 -> ignore (E.warn "checkSameFormat for Fi"); false
        | Ft t1, Ft t2 -> typeSig t1 = typeSig t2
        | Fl l1, Fl l2 -> checkLvalEq l1 l2
        | Fo o1, Fo o2 -> checkOffsetEq o1 o2
        | Fc c1, Fc c2 -> c1 == c2
        | _, _ -> false
      in
      hdeq || checkSameFormat t1 t2
  end
  | _, _ -> false

let matchBinopEq (bopeq: binop -> bool) lvt et = 
  (fun i -> match i with 
    Set (lv, BinOp(bop', Lval (lv'), e', _), l) when bopeq bop' -> begin
      match lvt lv, lvt lv', et e' with 
        Some m1, Some m1', Some m2 -> 
          (* Must check that m1 and m2 are the same *)
          if checkSameFormat m1 m1' then 
            Some (m1 @ m2)
          else
            None
      | _, _, _ -> None
     end
  | _ -> None)

let doBinopEq bop lvt et = 
  ((fun loc args -> 
    let l = (fst lvt) args in
    Set(l, BinOp(bop, (Lval l), (fst et) args, typeOfLval l), loc)),

   matchBinopEq (fun bop' -> bop = bop') (snd lvt) (snd et))


let getField (bt: typ) (fname: string) : fieldinfo = 
  match unrollType bt with 
    TComp(ci, _) -> begin
      try
        List.find (fun f -> fname = f.fname) ci.cfields
      with Not_found -> 
        E.s (bug "Cannot find field %s in %s\n" fname (compFullName ci))
    end
  | t -> E.s (bug "Trying to access field %s in non-struct\n" fname) 


let matchIntType (ik: ikind) (t:typ) : formatArg list option = 
  match unrollType t with 
    TInt(ik', _) when ik = ik' -> Some []
  | _ -> None

let matchFloatType (fk: fkind) (t:typ) : formatArg list option = 
  match unrollType t with 
    TFloat(fk', _) when fk = fk' -> Some []
  | _ -> None

let doAttr (id: string) 
           (aargs: (((string * formatArg) list -> attrparam list) * 
                    (attrparam list -> formatArg list option)) option)
    = 
  let t = match aargs with 
    Some t -> t
  | None -> (fun _ -> []), 
            (function [] -> Some [] | _ -> None)
  in
  ((fun args -> Attr (id, (fst t) args)), 
   
   (fun attrs -> 
     (* Find the attributes with the same ID *)
     List.fold_left 
       (fun acc a -> 
         match acc, a with 
           Some _, _ -> acc (* We found one already *)
         | None, Attr(id', args) when id = id' -> 
             (* Now match the arguments *)
             (snd t) args 
         | None, _ -> acc)
       None
       attrs))


type falist = formatArg list

type maybeInit = 
    NoInit
  | InitExp of exp
  | InitCall of lval * exp list

%}

%token <string> IDENT
%token <string> CST_CHAR
%token <string> CST_INT
%token <string> CST_FLOAT
%token <string> CST_STRING
%token <string> CST_WSTRING
%token <string> NAMED_TYPE

%token EOF
%token CHAR INT DOUBLE FLOAT VOID INT64 INT32
%token ENUM STRUCT TYPEDEF UNION
%token SIGNED UNSIGNED LONG SHORT
%token VOLATILE EXTERN STATIC CONST RESTRICT AUTO REGISTER

%token <string> ARG_e ARG_eo ARG_E ARG_u ARG_b ARG_t ARG_d ARG_lo ARG_l ARG_i
%token <string> ARG_o ARG_va ARG_f ARG_F ARG_A ARG_v ARG_k ARG_c ARG_d
%token <string> ARG_s ARG_p ARG_P ARG_I ARG_S ARG_g

%token SIZEOF ALIGNOF

%token EQ 
%token ARROW DOT

%token EQ_EQ EXCLAM_EQ INF SUP INF_EQ SUP_EQ
%token MINUS_EQ PLUS_EQ STAR_EQ
%token PLUS MINUS STAR SLASH PERCENT
%token TILDE AND PIPE CIRC
%token EXCLAM AND_AND PIPE_PIPE
%token INF_INF SUP_SUP
%token PLUS_PLUS MINUS_MINUS

%token RPAREN LPAREN RBRACE LBRACE LBRACKET RBRACKET
%token COLON SEMICOLON COMMA ELLIPSIS QUEST

%token BREAK CONTINUE GOTO RETURN
%token SWITCH CASE DEFAULT
%token WHILE DO FOR
%token IF THEN ELSE

%token  PLUS_EQ MINUS_EQ STAR_EQ SLASH_EQ PERCENT_EQ
%token  AND_EQ PIPE_EQ CIRC_EQ INF_INF_EQ SUP_SUP_EQ

%token ATTRIBUTE INLINE ASM TYPEOF FUNCTION__ PRETTY_FUNCTION__ LABEL__
%token BUILTIN_VA_ARG BUILTIN_VA_LIST
%token BLOCKATTRIBUTE
%token DECLSPEC
%token <string> MSASM MSATTR
%token PRAGMA


/* operator precedence */
%nonassoc 	IF
%nonassoc 	ELSE


%left	COMMA

 /*(* Set the following precedences higer than COMMA *)*/
%nonassoc ARG_e ARG_d ARG_lo ARG_l ARG_i ARG_v ARG_I ARG_g
%right	EQ PLUS_EQ MINUS_EQ STAR_EQ SLASH_EQ PERCENT_EQ
                AND_EQ PIPE_EQ CIRC_EQ INF_INF_EQ SUP_SUP_EQ
%right	COLON
%left	PIPE_PIPE
%left	AND_AND
%left   ARG_b
%left	PIPE
%left 	CIRC
%left	AND
%left	EQ_EQ EXCLAM_EQ
%left	INF SUP INF_EQ SUP_EQ
%left	INF_INF SUP_SUP
%left	PLUS MINUS
%left	STAR SLASH PERCENT CONST RESTRICT VOLATILE
%right	ARG_u EXCLAM TILDE PLUS_PLUS MINUS_MINUS CAST RPAREN ADDROF SIZEOF ALIGNOF
%left 	LBRACKET
%left	DOT ARROW LPAREN LBRACE
%nonassoc IDENT QUEST CST_INT

%start initialize expression typename offset lval instr stmt stmt_list


%type <unit> initialize
%type <((string -> Cil.typ -> Cil.varinfo) -> Cil.location -> (string * Cil.formatArg) list -> Cil.stmt)> stmt
%type <((string -> Cil.typ -> Cil.varinfo) -> Cil.location -> (string * Cil.formatArg) list -> Cil.stmt list)> stmt_list

%type <((string * Cil.formatArg) list -> Cil.exp) * (Cil.exp -> Cil.formatArg list option)> expression

%type <((string * Cil.formatArg) list -> Cil.exp) * (Cil.exp -> Cil.formatArg list option)> constant

%type <((string * Cil.formatArg) list -> Cil.lval) * (Cil.lval -> Cil.formatArg list option)> lval

%type <((string * Cil.formatArg) list -> Cil.typ) * (Cil.typ -> Cil.formatArg list option)> typename

%type <(Cil.attributes -> (string * Cil.formatArg) list -> Cil.typ) * (Cil.typ -> Cil.formatArg list option)> type_spec

%type <((string * Cil.formatArg) list -> (string * Cil.typ * Cil.attributes) list option * bool) * ((string * Cil.typ * Cil.attributes) list option * bool -> Cil.formatArg list option)> parameters


%type <(Cil.location -> (string * Cil.formatArg) list -> Cil.instr) * (Cil.instr -> Cil.formatArg list option)> instr

%type <(Cil.typ -> (string * Cil.formatArg) list -> Cil.offset) * (Cil.offset -> Cil.formatArg list option)> offset


%%


initialize: 
 /* empty */   {  }
;

/* (*** Expressions ***) */


expression:
|               ARG_e  {  (* Count arguments eagerly *) 
                            let currentArg = $1 in 
                            ((fun args ->
                               match getArg currentArg args with 
                                   Fe e -> e
                                 | a -> wrongArgType currentArg 
                                            "expression" a),

                             (fun e -> Some [ Fe e ]))
                         } 

|        	constant { $1 }

|               lval     %prec IDENT
                        { ((fun args -> Lval ((fst $1) args)),

                             (fun e -> match e with 
                                Lval l -> (snd $1) l 
                              | _ -> None))
                         } 

|		SIZEOF expression
		        { ((fun args -> SizeOfE ((fst $2) args)),

                           fun e -> match e with 
                             SizeOfE e' -> (snd $2) e'
                           | _ -> None)
                        }

|	 	SIZEOF LPAREN typename RPAREN
                        { ((fun args -> SizeOf ((fst $3) args)),
                          
                           (fun e -> match e with 
                              SizeOf t -> (snd $3) t
                           |  _ -> None))
                        }

|		ALIGNOF expression
		        { ((fun args -> AlignOfE ((fst $2) args)),

                           (fun e -> match e with
                             AlignOfE e' -> (snd $2) e' | _ -> None))
                        }

|	 	ALIGNOF LPAREN typename RPAREN
		        { ((fun args -> AlignOf ((fst $3) args)),

                           (fun e -> match e with
                             AlignOf t' -> (snd $3) t' | _ -> None))
                        } 

|		PLUS expression
		        { $2 }
|		MINUS expression
		        { doUnop Neg $2 }

|		EXCLAM expression
		        { doUnop LNot $2 }

|		TILDE expression
		        { doUnop BNot $2 }

|               argu expression %prec ARG_u
                        { ((fun args -> 
                             let e = (fst $2) args in
                             UnOp((fst $1) args, e, typeOf e)),

                           (fun e -> match e with 
                             UnOp(uo, e', _) -> begin
                               match (snd $1) uo, (snd $2) e' with 
                                 Some m1, Some m2 -> Some (m1 @ m2)
                               | _ -> None
                             end
                           | _ -> None))
                        } 
                             
                          
|		AND expression				%prec ADDROF
		        { ((fun args -> 
                             match (fst $2) args with
                                Lval l -> mkAddrOf l
                              | _ -> E.s (bug "AddrOf applied to a non lval")),
                          (fun e -> match e with 
                            AddrOf l -> (snd $2) (Lval l)
                          | e -> (snd $2) (Lval (mkMem e NoOffset))))
                         }

|               LPAREN expression RPAREN 
                        { $2 }

|		expression PLUS expression
			{ ((fun args -> buildPlus ((fst $1) args) 
                                                  ((fst $3) args)), 
                          (fun e -> match e with 
                            BinOp((PlusPI|PlusA), e1, e2, _) -> begin
                              match (snd $1) e1, (snd $3) e2 with
                                Some m1, Some m2 -> Some (m1 @ m2)
                              | _, _ -> None
                            end
                          | _ -> None))
                        } 

|		expression MINUS expression
                        { ((fun args -> buildMinus ((fst $1) args)
                                                   ((fst $3) args)),

                           (fun e -> match e with 
                             BinOp((MinusPP|MinusPI|MinusA), e1, e2, _) -> 
                               begin
                                 match (snd $1) e1, (snd $3) e2 with
                                   Some m1, Some m2 -> Some (m1 @ m2)
                                 | _, _ -> None
                               end
                           | _ -> None))
                        } 
|               expression argb expression %prec ARG_b
                        { ((fun args -> 
                               let e1 = (fst $1) args in 
                               let bop = (fst $2) args in
                               let e2 = (fst $3) args in 
                               let t1 = typeOf e1 in
                               BinOp(bop, e1, e2, t1)),
                           
                           (fun e -> match e with 
                             BinOp(bop, e1, e2, _) -> begin
                               match (snd $1) e1,(snd $2) bop,(snd $3) e2 with
                                 Some m1, Some m2, Some m3 -> 
                                   Some (m1 @ m2 @ m3)
                               | _, _, _ -> None
                             end
                           | _ -> None))
                        } 

|		expression STAR expression
			{ doBinop Mult $1 $3 }
|		expression SLASH expression
			{ doBinop Div $1 $3 }
|		expression PERCENT expression
			{ doBinop Mod $1 $3 }
|		expression  INF_INF expression
			{ doBinop Shiftlt $1 $3 }
|		expression  SUP_SUP expression
			{ doBinop Shiftrt $1 $3 }
|		expression AND expression
			{ doBinop BAnd $1 $3 }
|		expression PIPE expression
			{ doBinop BOr $1 $3 }
|		expression CIRC expression
			{ doBinop BXor $1 $3 }
|		expression EQ_EQ expression
			{ doBinop Eq $1 $3 }
|		expression EXCLAM_EQ expression
			{ doBinop Ne $1 $3 }
|		expression INF expression
			{ doBinop Lt $1 $3 }
|		expression SUP expression
			{ doBinop Gt $1 $3 }
|		expression INF_EQ expression
			{ doBinop Le $1 $3 }
|		expression SUP_EQ expression
			{ doBinop Ge $1 $3 }

|		LPAREN typename RPAREN expression
		         { ((fun args -> 
                              let t = (fst $2) args in
                              let e = (fst $4) args in
                              mkCast e t),
                            
                            (fun e -> 
                              let t', e' = 
                                match e with 
                                  CastE (t', e') -> t', e'
                                | _ -> typeOf e, e
                              in
                              match (snd $2) t', (snd $4 e') with
                                Some m1, Some m2 -> Some (m1 @ m2)
                              | _, _ -> None))
                         } 
;

/*(* Separate the ARG_ to ensure that the counting of arguments is right *)*/
argu :
|   ARG_u              { let currentArg = $1 in
                         ((fun args ->
                           match getArg currentArg args with
                             Fu uo -> uo
                           | a -> wrongArgType currentArg "unnop" a),

                          fun uo -> Some [ Fu uo ])
                       } 
;

argb :
|   ARG_b              { let currentArg = $1 in
                         ((fun args ->
                           match getArg currentArg args with
                             Fb bo -> bo
                           | a -> wrongArgType currentArg "binop" a),

                          fun bo -> Some [ Fb bo ])
                       } 
;

constant:
|   ARG_d              { let currentArg = $1 in
                           ((fun args ->
                             match getArg currentArg args with
                               Fd n -> integer n
                              | a -> wrongArgType currentArg "integer" a),

                            fun e -> match e with 
                              Const(CInt64(n, _, _)) -> 
                                Some [ Fd (Int64.to_int n) ]
                            | _ -> None) 
                         } 

|   ARG_g             { let currentArg = $1 in
                        ((fun args ->
                             match getArg currentArg args with
                               Fg s -> Const(CStr s)
                              | a -> wrongArgType currentArg "string" a),

                            fun e -> match e with 
                              Const(CStr s) ->
                                Some [ Fg s ]
                            | _ -> None) 
                         } 
|   CST_INT              { let n = parseInt $1 in
                           ((fun args -> n),

                            (fun e -> match e, n with 
                              Const(CInt64(e', _, _)), 
                              Const(CInt64(n', _, _)) when e' = n' -> Some []
                            | _ -> None))
                         }
;


/*(***************** LVALUES *******************)*/
lval: 
|   ARG_l             { let currentArg = $1 in
                           ((fun args -> 
                                match getArg currentArg args with 
                                  Fl l -> l
                                | Fv v -> Var v, NoOffset
                                | a -> wrongArgType currentArg "lval" a),

                            fun l -> Some [ Fl l ])
                         }

|   argv offset       %prec ARG_v
                         { ((fun args -> 
                              let v = (fst $1) args in
                               (Var v, (fst $2) v.vtype args)),

                            (fun l -> match l with 
                              Var vi, off -> begin
                                match (snd $1) vi, (snd $2) off with 
                                  Some m1, Some m2 -> Some (m1 @ m2)
                                | _ -> None
                              end
                            | _ -> None))
                         }

|   STAR expression      { ((fun args -> mkMem ((fst $2) args) NoOffset),

                           (fun l -> match l with 
                              Mem e, NoOffset -> (snd $2) e
                           | _, _ -> None))
                         }

|   expression ARROW IDENT offset 
             { ((fun args -> 
                   let e = (fst $1) args in
                   let baset = 
                     match unrollTypeDeep (typeOf e) with 
                       TPtr (t, _) -> t
                     | _ -> E.s (bug "Expecting a pointer for field %s\n" $3)
                   in
                   let fi = getField baset $3 in
                   mkMem e (Field(fi, (fst $4) fi.ftype args))),

                (fun l -> match l with 
                   Mem e, Field(fi, off) when fi.fname = $3 -> begin
                     match (snd $1) e, (snd $4) off with 
                       Some m1, Some m2 -> Some (m1 @ m2)
                     | _, _ -> None
                   end
                | _, _ -> None))
             }

|   LPAREN STAR expression RPAREN offset
             { ((fun args -> 
                 let e = (fst $3) args in
                 let baset = 
                   match unrollTypeDeep (typeOf e) with 
                     TPtr (t, _) -> t
                   | _ -> E.s (bug "Expecting a pointer\n")
                 in
                 mkMem e ((fst $5) baset args)),

                (fun l -> match l with 
                  Mem e, off -> begin
                    match (snd $3) e, (snd $5 off) with 
                      Some m1, Some m2 -> Some (m1 @ m2)
                    | _, _ -> None
                  end
                | _, _ -> None))
              }
    ;

argv :
|   ARG_v              { let currentArg = $1 in
                         ((fun args ->
                           match getArg currentArg args with
                             Fv v -> v
                           | a -> wrongArgType currentArg "varinfo" a),

                          fun v -> Some [ Fv v ])
                       } 
|  IDENT               { let currentArg = $1 in
                         ((fun args -> 
                           match getArg currentArg args with 
                             Fv v -> v
                           | a -> wrongArgType currentArg "varinfo" a),
                         (fun v -> 
                             E.s (bug "identifiers (%s) are not supported for deconstruction" currentArg)))
                       } 
;

  
/*(********** OFFSETS *************)*/
offset: 
|  ARG_o             { let currentArg = $1 in
                            ((fun t args -> 
                                match getArg currentArg args with 
                                  Fo o -> o
                                | a -> wrongArgType currentArg "offset" a),

                              (fun off -> Some [ Fo off ]))
                          }

|  /* empty */            { ((fun t args -> NoOffset),

                             (fun off -> match off with 
                                NoOffset -> Some []
                              | _ -> None))
                          }

|  DOT IDENT offset       { ((fun t args -> 
                                let fi = getField t $2 in
                                Field (fi, (fst $3) fi.ftype args)),

                            (fun off -> match off with 
                               Field (fi, off') when fi.fname = $2 -> 
                                 (snd $3) off'
                            | _ -> None))
                          }

|  LBRACKET expression RBRACKET offset
                   { ((fun t args -> 
                     let bt = 
                       match unrollType t with 
                         TArray(bt, _, _) -> bt 
                       | _ -> E.s (error "Formatcil: expecting an array for index")
                     in
                     let e = (fst $2) args in 
                     Index(e, (fst $4) bt args)),

                    (fun off -> match off with 
                      Index (e, off') -> begin
                        match (snd $2) e, (snd $4) off with 
                          Some m1, Some m2 -> Some (m1 @ m2)
                        | _, _ -> None
                      end
                    | _ -> None))
                    }
;


/*(************ TYPES **************)*/
typename: one_formal  { ((fun args -> 
                            let (_, ft, _) = (fst $1) args in
                            ft),

                         (fun t -> (snd $1) ("", t, [])))
                      } 
;

one_formal: 
/*(* Do not allow attributes for the name *)*/
| type_spec attributes decl
                   { ((fun args -> 
                        let tal = (fst $2) args in
                        let ts = (fst $1) tal args in
                        let (fn, ft, _) = (fst $3) ts args in
                        (fn, ft, [])),

                      (fun (fn, ft, fa) -> 
                         match (snd $3) (fn, ft) with 
                           Some (restt, m3) -> begin
                             match (snd $1) restt, 
                                   (snd $2) (typeAttrs restt)with
                               Some m1, Some m2 -> 
                                 Some (m1 @ m2 @ m3)
                             | _, _ -> None
                           end
                         | _ -> None))
                   } 

| ARG_f 
                   { let currentArg = $1 in
                     ((fun args -> 
                         match getArg currentArg args with
                          Ff (fn, ft, fa) -> (fn, ft, fa)
                         | a  -> wrongArgType currentArg "formal" a),

                      (fun (fn, ft, fa) -> Some [ Ff (fn, ft, fa) ]))
                   } 
;

type_spec:  
|   ARG_t       { let currentArg = $1 in
                     ((fun al args -> 
                       match getArg currentArg args with 
                          Ft t -> typeAddAttributes al t
                       | a -> wrongArgType currentArg "type" a),
                      
                      (fun t -> Some [ Ft t ]))
                      }

|   VOID            { ((fun al args -> TVoid al),

                       (fun t -> match unrollType t with 
                           TVoid _ -> Some []
                         | _ -> None)) }

|   ARG_k           { let currentArg = $1 in
                      ((fun al args -> 
                        match getArg currentArg args with 
                          Fk ik -> TInt(ik, al)
                        | a -> wrongArgType currentArg "ikind" a),

                       (fun t -> match unrollType t with 
                         TInt(ik, _) -> Some [ Fk ik ]
                       | _ -> None))
                    } 

|   CHAR            { ((fun al args -> TInt(IChar, al)),
                       (matchIntType IChar)) }
|   UNSIGNED CHAR   { ((fun al args -> TInt(IUChar, al)), 
                       matchIntType IUChar) }

|   SHORT           { ((fun al args -> TInt(IShort, al)), 
                       matchIntType IShort) }
|   UNSIGNED SHORT  { ((fun al args -> TInt(IUShort, al)), 
                       matchIntType IUShort) }

|   INT             { ((fun al args -> TInt(IInt, al)), 
                       matchIntType IInt) }
|   UNSIGNED INT    { ((fun al args -> TInt(IUInt, al)), matchIntType IUInt) }

|   LONG             { ((fun al args -> TInt(ILong, al)), 
                        matchIntType ILong) }
|   UNSIGNED LONG    { ((fun al args -> TInt(IULong, al)), 
                        matchIntType IULong) }

|   LONG LONG          { ((fun al args -> TInt(ILongLong, al)), 
                          
                          matchIntType ILongLong)
                        }
|   UNSIGNED LONG LONG    { ((fun al args -> TInt(IULongLong, al)),

                             matchIntType IULongLong)
                           }

|   FLOAT           { ((fun al args -> TFloat(FFloat, al)),
                       matchFloatType FFloat) 
                    }
|   DOUBLE          { ((fun al args -> TFloat(FDouble, al)),
                       matchFloatType FDouble) }

|   STRUCT ARG_c { let currentArg = $2 in
                      ((fun al args -> 
                         match getArg currentArg args with 
                           Fc ci -> TComp(ci, al)
                         | a -> wrongArgType currentArg "compinfo" a),

                        (fun t -> match unrollType t with 
                            TComp(ci, _) -> Some [ Fc ci ]
                          | _ -> None))
                    }
|   UNION ARG_c { let currentArg = $2 in
                     ((fun al args -> 
                         match getArg currentArg args with 
                           Fc ci -> TComp(ci, al)
                         | a -> wrongArgType currentArg "compinfo" a),

                        (fun t -> match unrollType t with 
                            TComp(ci, _) -> Some [ Fc ci ]
                          | _ -> None))

                   }

|   TYPEOF LPAREN expression RPAREN     
                   { ((fun al args -> typeAddAttributes al 
                                        (typeOf ((fst $3) args))),
                    
                      (fun t -> E.s (bug "Cannot match typeof(e)\n")))
                   } 
;

decl: 
|  STAR attributes decl  
                    { ((fun ts args -> 
                         let al = (fst $2) args in
                         (fst $3) (TPtr(ts, al)) args),

                       (fun (fn, ft) -> 
                         match (snd $3) (fn, ft) with 
                           Some (TPtr(bt, al), m2) -> begin
                             match (snd $2) al with 
                               Some m1 -> Some (bt, m1 @ m2)
                             | _ -> None
                           end
                         | _ -> None))
                    } 

|  direct_decl  { $1 }
;

direct_decl: 
|  /* empty */     { ((fun ts args -> ("", ts, [])),

                      (* Match any name in this case *)
                      (fun (fn, ft) -> 
                         Some (unrollType ft, [])))
                   }

|  IDENT           { ((fun ts args -> ($1, ts, [])),

                      (fun (fn, ft) -> 
                        if fn = "" || fn = $1 then 
                          Some (unrollType ft, []) 
                        else 
                          None))
                   }

|  LPAREN attributes decl RPAREN 
                   { ((fun ts args -> 
                          let al = (fst $2) args in
                          (fst $3) (typeAddAttributes al ts) args),

                      (fun (fn, ft) -> begin
                        match (snd $3) (fn, ft) with
                          Some (restt, m2) -> begin
                            match (snd $2) (typeAttrs restt) with 
                              Some m1 -> Some (restt, m1 @ m2)
                            | _ -> None
                          end
                        | _ -> None
                      end))
                   } 

|  direct_decl LBRACKET exp_opt RBRACKET
                   { ((fun ts args -> 
                        (fst $1) (TArray(ts, (fst $3) args, [])) args),

                     (fun (fn, ft) -> 
                       match (snd $1) (fn, ft) with 
                         Some (TArray(bt, lo, _), m1) -> begin
                           match (snd $3) lo with 
                             Some m2 -> Some (unrollType bt, m1 @ m2)
                           | _ -> None
                         end 
                       | _ -> None))
                   }


/*(* We use parentheses around the function to avoid conflicts *)*/
|  LPAREN attributes decl RPAREN LPAREN parameters RPAREN 
                   { ((fun ts args -> 
                        let al = (fst $2) args in
                        let pars, isva = (fst $6) args in
                        (fst $3) (TFun(ts, pars, isva, al)) args),

                      (fun (fn, ft) -> 
                         match (snd $3) (fn, ft) with 
                           Some (TFun(rt, args, isva, al), m1) -> begin
                             match (snd $2) al, (snd $6) (args, isva) with 
                               Some m2, Some m6 
                               -> Some (unrollType rt, m1 @ m2 @ m6)
                             | _ -> None
                           end
                         | _ -> None))
                   }
;

parameters: 
| /* empty */      { ((fun args -> (None, false)),

                     (* Match any formals *)
                      (fun (pars, isva) -> 
                        match pars, isva with 
                          (_, false) -> Some [] 
                        | _ -> None))
                   } 

| parameters_ne    { ((fun args -> 
                        let (pars : (string * typ * attributes) list), 
                            (isva : bool) = (fst $1) args in
                        (Some pars), isva),

                     (function 
                         ((Some pars), isva) -> (snd $1) (pars, isva)
                       |  _ -> None))
                   } 
;
parameters_ne: 
| ELLIPSIS  
                   { ((fun args -> ([], true)),

                      (function 
                          ([], true) -> Some [] 
                        | _ -> None))
                   }

| ARG_va           { let currentArg = $1 in
                     ((fun args -> 
                       match getArg currentArg args with
                         Fva isva -> ([], isva)
                       | a -> wrongArgType currentArg "vararg" a),

                     (function 
                         ([], isva) -> Some [ Fva isva ] 
                       | _ -> None))
                   } 

| ARG_F            { let currentArg = $1 in
                     ((fun args -> 
                       match getArg currentArg args with
                        FF fl -> ( fl, false)
                       | a  -> wrongArgType currentArg "formals" a),

                      (function 
                          (pars, false) -> Some [ FF pars ] 
                        | _ -> None))
                   } 

| one_formal       { ((fun args -> ([(fst $1) args], false)),

                     (function 
                         ([ f ], false) -> (snd $1) f 
                       | _ -> None))
                   }


| one_formal COMMA parameters_ne
                   { ((fun args -> 
                        let this = (fst $1) args in
                        let (rest, isva) = (fst $3) args in
                        (this :: rest, isva)),

                      (function 
                          ((f::rest, isva)) -> begin
                            match (snd $1) f, (snd $3) (rest, isva) with 
                              Some m1, Some m2 -> Some (m1 @ m2)
                            | _, _ -> None
                          end
                        | _ -> None))
                   } 
;





exp_opt: 
   /* empty */     { ((fun args -> None),
                      (* Match anything if the pattern does not have a len *)
                      (fun _ -> Some [])) }

|  expression      { ((fun args -> Some ((fst $1) args)),

                      (fun lo -> match lo with
                        Some e -> (snd $1) e
                      | _ -> None))
                   } 
|  ARG_eo          { let currentArg = $1 in
                     ((fun args ->
                       match getArg currentArg args with
                         Feo lo -> lo
                       | a -> wrongArgType currentArg "exp_opt" a),

                      fun lo -> Some [ Feo lo ])
                   } 
;



attributes: 
  /*(* Ignore other attributes *)*/
  /* empty */     { ((fun args -> []), 
                     (fun attrs -> Some [])) }
          
| ARG_A           { let currentArg = $1 in
                    ((fun args -> 
                        match getArg currentArg args with
                          FA al -> al
                        | a -> wrongArgType currentArg "attributes" a),

                     (fun al -> Some [ FA al ]))
                  } 
                       
| attribute attributes
                  { ((fun args ->
                       addAttribute ((fst $1) args) ((fst $2) args)),
                     (* Pass all the attributes down *)
                     (fun attrs ->
                       match (snd $1) attrs, (snd $2) attrs with
                         Some m1, Some m2 -> Some (m1 @ m2)
                       | _, _ -> None))
                  } 
;

attribute:
|   CONST                               { doAttr "const" None }
|   RESTRICT                            { doAttr "restrict" None }
|   VOLATILE                            { doAttr "volatile" None }
|   ATTRIBUTE LPAREN LPAREN attr RPAREN RPAREN	
                                        { $4 }

;

  
attr: 
|   IDENT                                
                          { doAttr $1 None }
                                 
|   IDENT LPAREN attr_args_ne RPAREN     
                          { doAttr $1 (Some $3) }
;

attr_args_ne: 
    attr_arg                     { ((fun args -> [ (fst $1) args ]),

                                    (fun aargs -> match aargs with 
                                      [ arg ] -> (snd $1) arg
                                    | _ -> None))
                                 } 
|   attr_arg COMMA attr_args_ne  { ((fun args -> 
                                      let this = (fst $1) args in
                                      this :: ((fst $3) args)),

                                    (fun aargs -> match aargs with 
                                      h :: rest -> begin
                                        match (snd $1) h, (snd $3) rest with
                                          Some m1, Some m2 -> Some (m1 @ m2)
                                        | _, _ -> None
                                      end
                                    | _ -> None))
                                  } 
|   ARG_P               { let currentArg = $1 in
                          ((fun args -> 
                            match getArg currentArg args with
                              FP al -> al
                            | a -> wrongArgType currentArg "attrparams" a),

                           (fun al -> Some [ FP al ]))
                        } 
;

attr_arg: 
|   IDENT            { ((fun args -> ACons($1, [])),

                        (fun aarg -> match aarg with 
                            ACons(id, []) when id = $1 -> Some []
                        | _ -> None))
                     } 
|   IDENT LPAREN attr_args_ne RPAREN   
                     { ((fun args -> ACons($1, (fst $3) args)),

                        (fun aarg -> match aarg with 
                            ACons(id, args) when id = $1 -> 
                              (snd $3) args
                        | _ -> None))
                     } 
|   ARG_p            { let currentArg = $1 in
                       ((fun args -> 
                          match getArg currentArg args with
                            Fp p -> p
                          | a -> wrongArgType currentArg "attrparam" a),

                        (fun ap -> Some [ Fp ap]))
                     } 
                          
;

/* (********** INSTRUCTIONS ***********) */
instr: 
|               ARG_i SEMICOLON
                        { let currentArg = $1 in
                          ((fun loc args -> 
                                match getArg currentArg args with 
                                  Fi i -> i
                                | a -> wrongArgType currentArg "instr" a),

                           (fun i -> Some [ Fi i]))
                        }

|		lval EQ expression SEMICOLON
			{ ((fun loc args -> 
                              Set((fst $1) args, (fst $3) args, loc)),

                           (fun i -> match i with
                             Set (lv, e, l) -> begin
                               match (snd $1) lv, (snd $3) e with
                                 Some m1, Some m2 -> Some (m1 @ m2)
                               | _, _ -> None
                             end
                           | _ -> None))
                        } 

|		lval PLUS_EQ expression SEMICOLON
			{ ((fun loc args -> 
                              let l = (fst $1) args in
                              Set(l, buildPlus (Lval l) ((fst $3) args), loc)),

                           matchBinopEq 
                             (fun bop -> bop = PlusPI || bop = PlusA)
                             (snd $1) (snd $3)) 
                        }

|		lval MINUS_EQ expression SEMICOLON
			{ ((fun loc args -> 
                              let l = (fst $1) args in
                              Set(l, 
                                  buildMinus (Lval l) ((fst $3) args), loc)),

                           matchBinopEq (fun bop -> bop = MinusA 
                                               || bop = MinusPP 
                                               || bop = MinusPI) 
                                      (snd $1)  (snd $3)) 
                        }
|		lval STAR_EQ expression SEMICOLON
			{ doBinopEq Mult $1 $3 }

|		lval SLASH_EQ expression SEMICOLON
			{ doBinopEq Div $1 $3 }

|		lval PERCENT_EQ expression SEMICOLON
			{ doBinopEq Mod $1 $3 }

|		lval AND_EQ expression SEMICOLON
			{ doBinopEq BAnd $1 $3 }

|		lval PIPE_EQ expression SEMICOLON
			{ doBinopEq BOr $1 $3 }

|		lval CIRC_EQ expression SEMICOLON
			{ doBinopEq BXor $1 $3 }

|		lval INF_INF_EQ expression SEMICOLON
			{ doBinopEq Shiftlt $1 $3 }

|		lval SUP_SUP_EQ expression SEMICOLON
			{ doBinopEq Shiftrt $1 $3 }

/* (* Would be nice to be able to condense the next three rules but we get 
 * into conflicts *)*/
|		lval EQ lval LPAREN arguments RPAREN  SEMICOLON
			{ ((fun loc args -> 
                              Call(Some ((fst $1) args), Lval ((fst $3) args), 
                                     (fst $5) args, loc)),

                           (fun i -> match i with 
                             Call(Some l, Lval f, args, loc) -> begin
                               match (snd $1) l, (snd $3) f, (snd $5) args with
                                 Some m1, Some m2, Some m3 -> 
                                   Some (m1 @ m2 @ m3)
                               | _, _, _ -> None
                             end
                           | _ -> None))
                        }

|		        lval LPAREN arguments RPAREN  SEMICOLON
			{ ((fun loc args -> 
                              Call(None, Lval ((fst $1) args), 
                                     (fst $3) args, loc)), 

                           (fun i -> match i with 
                             Call(None, Lval f, args, loc) -> begin
                               match (snd $1) f, (snd $3) args with
                                 Some m1, Some m2 -> Some (m1 @ m2)
                               | _, _ -> None
                             end
                           | _ -> None))
                         }

|                 arglo lval LPAREN arguments RPAREN  SEMICOLON
		     { ((fun loc args -> 
                       Call((fst $1) args, Lval ((fst $2) args), 
                            (fst $4) args, loc)), 
                        
                        (fun i -> match i with 
                          Call(lo, Lval f, args, loc) -> begin
                            match (snd $1) lo, (snd $2) f, (snd $4) args with
                              Some m1, Some m2, Some m3 -> 
                                Some (m1 @ m2 @ m3)
                            | _, _, _ -> None
                          end
                        | _ -> None))
                     }
;

/* (* Separate this out to ensure that the counting or arguments is right *)*/
arglo: 
    ARG_lo               { let currentArg = $1 in
                           ((fun args -> 
                             let res = 
                               match getArg currentArg args with
                                 Flo x -> x
                               | a -> wrongArgType currentArg "lval option" a
                             in
                             res),

                            (fun lo -> Some [ Flo lo ]))
                         } 
;                              
arguments: 
    /* empty */   { ((fun args -> []), 

                     (fun actuals -> match actuals with 
                          [] -> Some []
                         | _ -> None))
                  }

| arguments_ne    { $1 }
;

arguments_ne:
  expression      { ((fun args -> [ (fst $1) args ]),

                     (fun actuals -> match actuals with 
                        [ h ] -> (snd $1) h
                       | _ -> None))
                  }

| ARG_E           {  let currentArg = $1 in
                     ((fun args -> 
                         match getArg currentArg args with
                           FE el -> el
                          | a -> wrongArgType currentArg "arguments" a),

                      (fun actuals -> Some [ FE actuals ]))
                  } 

| expression COMMA arguments_ne
                  { ((fun args -> ((fst $1) args) :: ((fst $3) args)),

                     (fun actuals -> match actuals with 
                         h :: rest -> begin
                           match (snd $1) h, (snd $3) rest with 
                             Some m1, Some m2 -> Some (m1 @ m2)
                           | _, _ -> None
                         end
                       | _ -> None))
                  }
;


/*(******** STATEMENTS *********)*/
stmt: 
    IF LPAREN expression RPAREN stmt           %prec IF
                  { (fun mkTemp loc args -> 
                         mkStmt (If((fst $3) args, 
                                    mkBlock [ $5 mkTemp loc args ],
                                    mkBlock [], loc)))
                  }
|   IF LPAREN expression RPAREN stmt ELSE stmt 
                  { (fun mkTemp loc args -> 
                         mkStmt (If((fst $3) args, 
                                    mkBlock [ $5 mkTemp loc args ],
                                    mkBlock [ $7 mkTemp loc args], loc)))
                  }
|   RETURN exp_opt SEMICOLON  
                  { (fun mkTemp loc args -> 
                         mkStmt (Return((fst $2) args, loc))) 
                  }
|   BREAK SEMICOLON  
                  { (fun mkTemp loc args -> 
                         mkStmt (Break loc))
                  }
|   CONTINUE SEMICOLON 
                  { (fun mkTemp loc args -> 
                         mkStmt (Continue loc))
                  }
|   LBRACE stmt_list RBRACE  
                  { (fun mkTemp loc args -> 
                         let stmts = $2 mkTemp loc args in
                         mkStmt (Block (mkBlock (stmts))))
                  }
|   WHILE LPAREN expression RPAREN stmt  
                  { (fun mkTemp loc args -> 
                        let e = (fst $3) args in
                        let e = 
                          if isPointerType(typeOf e) then 
                            mkCast e !upointType
                          else e
                        in
(*
                        mkStmt 
                          (Loop (mkBlock [ mkStmt 
                                             (If(e,
                                                 mkBlock [],
                                                 mkBlock [ mkStmt 
                                                             (Break loc) ],
                                                 loc));
                                           $5 mkTemp loc args ],
                                 loc, None, None))
*)
			mkStmt
			  (While (e, mkBlock [ $5 mkTemp loc args ], loc)))
                   } 
|   instr_list    { (fun mkTemp loc args -> 
                       mkStmt (Instr ($1 loc args)))
                  }
|   ARG_s         { let currentArg = $1 in
                    (fun mkTemp loc args -> 
                       match getArg currentArg args with
                         Fs s -> s
                       | a -> wrongArgType currentArg "stmt" a) }
;

stmt_list: 
    /* empty */  { (fun mkTemp loc args -> []) }

|   ARG_S        { let currentArg = $1 in
                   (fun mkTemp loc args -> 
                       match getArg currentArg args with 
                       | FS sl -> sl 
                       | a -> wrongArgType currentArg "stmts" a)
                 }
|   stmt stmt_list  
                 { (fun mkTemp loc args -> 
                      let this = $1 mkTemp loc args in
                      this :: ($2 mkTemp loc args))
                 }
/* (* We can also have a declaration *) */
|   type_spec attributes decl maybe_init SEMICOLON stmt_list 
                { (fun mkTemp loc args -> 
                     let tal = (fst $2) args in
                     let ts  = (fst $1) tal args in
                     let (n, t, _) = (fst $3) ts args in
                     let init = $4 args in
                     (* Before we proceed we must create the variable *)
                     let v = mkTemp n t in
                     (* Now we parse the rest *)
                     let rest = $6 mkTemp loc ((n, Fv v) :: args) in
                     (* Now we add the initialization instruction to the 
                      * front *)
                     match init with 
                       NoInit -> rest
                     | InitExp e -> 
                         mkStmtOneInstr (Set((Var v, NoOffset), e, loc)) 
                         :: rest
                     | InitCall (f, args) ->
                         mkStmtOneInstr (Call(Some (Var v, NoOffset), 
                                              Lval f, args, loc))
                         :: rest

                                                           )
                 } 
;

instr_list:
     /*(* Set this rule to very low precedence to ensure that we shift as 
          many instructions as possible *)*/
    instr   %prec COMMA 
                 { (fun loc args -> [ ((fst $1) loc args) ]) }
|   ARG_I        { let currentArg = $1 in
                   (fun loc args -> 
                       match getArg currentArg args with 
                       | FI il -> il 
                       | a -> wrongArgType currentArg "instrs" a)
                 }
|   instr instr_list 
                 { (fun loc args -> 
                      let this = (fst $1) loc args in
                      this :: ($2 loc args))
                 }
;


maybe_init:
|                               { (fun args -> NoInit) }
| EQ expression                 { (fun args -> InitExp ((fst $2) args)) }
| EQ lval LPAREN arguments RPAREN 
                                { (fun args -> 
                                    InitCall((fst $2) args, (fst $4) args)) }
;
%%







