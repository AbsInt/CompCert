/* $Id: CMparser.mly,v 1.2 2005/03/21 15:53:00 xleroy Exp $ */

%{
open Datatypes
open List
open Camlcoq
open BinPos
open BinInt
open Integers
open AST
open Op
open Cminor

let intconst n =
  Eop(Ointconst(coqint_of_camlint n), Enil)

let andbool e1 e2 =
  Cmconstr.conditionalexpr e1 e2 (intconst 0l)
let orbool e1 e2 =
  Cmconstr.conditionalexpr e1 (intconst 1l) e2

%}

%token ABSF
%token AMPERSAND
%token AMPERSANDAMPERSAND
%token BANG
%token BANGEQUAL
%token BANGEQUALF
%token BANGEQUALU
%token BAR
%token BARBAR
%token CARET
%token COLON
%token COMMA
%token DOLLAR
%token ELSE
%token EQUAL
%token EQUALEQUAL
%token EQUALEQUALF
%token EQUALEQUALU
%token EOF
%token EXIT
%token FLOAT
%token FLOAT32
%token FLOAT64
%token <float> FLOATLIT
%token FLOATOFINT
%token FLOATOFINTU
%token GREATER
%token GREATERF
%token GREATERU
%token GREATEREQUAL
%token GREATEREQUALF
%token GREATEREQUALU
%token GREATERGREATER
%token GREATERGREATERU
%token <AST.ident> IDENT
%token IF
%token IN
%token INT
%token INT16S
%token INT16U
%token INT32
%token INT8S
%token INT8U
%token <int32> INTLIT
%token INTOFFLOAT
%token LBRACE
%token LBRACELBRACE
%token LBRACKET
%token LESS
%token LESSU
%token LESSF
%token LESSEQUAL
%token LESSEQUALU
%token LESSEQUALF
%token LESSLESS
%token LET
%token LOOP
%token LPAREN
%token MINUS
%token MINUSF
%token MINUSGREATER
%token PERCENT
%token PERCENTU
%token PLUS
%token PLUSF
%token QUESTION
%token RBRACE
%token RBRACERBRACE
%token RBRACKET
%token RETURN
%token RPAREN
%token SEMICOLON
%token SLASH
%token SLASHF
%token SLASHU
%token STACK
%token STAR
%token STARF
%token <AST.ident> STRINGLIT
%token SWITCH
%token TILDE
%token VAR
%token VOID

/* Precedences from low to high */

%left COMMA
%left p_let
%right EQUAL
%right QUESTION COLON
%left BARBAR
%left AMPERSANDAMPERSAND
%left BAR
%left CARET
%left AMPERSAND
%left EQUALEQUAL BANGEQUAL LESS LESSEQUAL GREATER GREATEREQUAL EQUALEQUALU BANGEQUALU LESSU LESSEQUALU GREATERU GREATEREQUALU EQUALEQUALF BANGEQUALF LESSF LESSEQUALF GREATERF GREATEREQUALF 
%left LESSLESS GREATERGREATER GREATERGREATERU
%left PLUS PLUSF MINUS MINUSF
%left STAR SLASH PERCENT STARF SLASHF SLASHU PERCENTU
%nonassoc BANG TILDE p_uminus ABSF INTOFFLOAT FLOATOFINT FLOATOFINTU INT8S INT8U INT16S INT16U FLOAT32
%left LPAREN

/* Entry point */

%start prog
%type <Cminor.program> prog

%%

/* Programs */

prog:
    global_declarations proc_list EOF
      { { prog_funct = List.rev $2;
          prog_main = intern_string "main";
          prog_vars = List.rev $1; } }
;

global_declarations:
    /* empty */                                 { Coq_nil }
  | global_declarations global_declaration      { Coq_cons($2, $1) }
;

global_declaration:
    VAR STRINGLIT LBRACKET INTLIT RBRACKET      { Coq_pair($2, z_of_camlint $4) }
;

proc_list:
    /* empty */                                 { Coq_nil }
  | proc_list proc                              { Coq_cons($2, $1) }
;

/* Procedures */

proc:
    STRINGLIT LPAREN parameters RPAREN COLON signature
    LBRACE
      stack_declaration
      var_declarations
      stmt_list
    RBRACE
      { Coq_pair($1,
         { fn_sig = $6;
           fn_params = List.rev $3;
           fn_vars = List.rev $9;
           fn_stackspace = $8;
           fn_body = $10 }) }
;

signature:
    type_ 
               { {sig_args = Coq_nil; sig_res = Some $1} }
  | VOID
               { {sig_args = Coq_nil; sig_res = None} }
  | type_ MINUSGREATER signature
               { let s = $3 in {s with sig_args = Coq_cons($1, s.sig_args)} }
;

parameters:
    /* empty */                                 { Coq_nil }
  | parameter_list                              { $1 }
;

parameter_list:
    IDENT                                       { Coq_cons($1, Coq_nil) }
  | parameter_list COMMA IDENT                  { Coq_cons($3, $1) }
;

stack_declaration:
    /* empty */                                 { Z0 }
  | STACK INTLIT                                { z_of_camlint $2 }
;

var_declarations:
    /* empty */                                 { Coq_nil }
  | var_declarations var_declaration            { List.app $2 $1 }
;

var_declaration:
    VAR parameter_list SEMICOLON                { $2 }
;

/* Statements */

stmt:
    expr SEMICOLON                              { Sexpr $1 }
  | IF LPAREN expr RPAREN stmts ELSE stmts      { Cmconstr.ifthenelse $3 $5 $7 }
  | IF LPAREN expr RPAREN stmts                 { Cmconstr.ifthenelse $3 $5 Snil }
  | LOOP stmts                                  { Sloop($2) }
  | LBRACELBRACE stmts RBRACERBRACE             { Sblock($2) }
  | EXIT SEMICOLON                              { Sexit O }
  | EXIT INTLIT SEMICOLON                       { Sexit (nat_of_camlint(Int32.pred $2)) }
  | RETURN SEMICOLON                            { Sreturn None }
  | RETURN expr SEMICOLON                       { Sreturn (Some $2) }
;

stmts:
    LBRACE stmt_list RBRACE                     { $2 }
  | stmt                                        { Scons($1, Snil) }
;

stmt_list:
    /* empty */                                 { Snil }
  | stmt stmt_list                              { Scons($1, $2) }
;

/* Expressions */

expr:
    LPAREN expr RPAREN                          { $2 }
  | IDENT                                       { Evar $1 }
  | IDENT EQUAL expr                            { Eassign($1, $3) }
  | INTLIT                                      { intconst $1 }
  | FLOATLIT                                    { Eop(Ofloatconst $1, Enil) }
  | STRINGLIT                                   { Eop(Oaddrsymbol($1, Int.zero), Enil) }
  | AMPERSAND INTLIT                            { Eop(Oaddrstack(coqint_of_camlint $2), Enil) }
  | MINUS expr    %prec p_uminus                { Cmconstr.negint $2 }
  | MINUSF expr   %prec p_uminus                { Cmconstr.negfloat $2 }
  | ABSF expr                                   { Cmconstr.absfloat $2 }
  | INTOFFLOAT expr                             { Cmconstr.intoffloat $2 }
  | FLOATOFINT expr                             { Cmconstr.floatofint $2 }
  | FLOATOFINTU expr                            { Cmconstr.floatofintu $2 }
  | TILDE expr                                  { Cmconstr.notint $2 }
  | BANG expr                                   { Cmconstr.notbool $2 }
  | INT8S expr                                  { Cmconstr.cast8signed $2 }
  | INT8U expr                                  { Cmconstr.cast8unsigned $2 }
  | INT16S expr                                 { Cmconstr.cast16signed $2 }
  | INT16U expr                                 { Cmconstr.cast16unsigned $2 }
  | FLOAT32 expr                                { Cmconstr.singleoffloat $2 }
  | expr PLUS expr                              { Cmconstr.add $1 $3 }
  | expr MINUS expr                             { Cmconstr.sub $1 $3 }
  | expr STAR expr                              { Cmconstr.mul $1 $3 }
  | expr SLASH expr                             { Cmconstr.divs $1 $3 }
  | expr PERCENT expr                           { Cmconstr.mods $1 $3 }
  | expr SLASHU expr                            { Cmconstr.divu $1 $3 }
  | expr PERCENTU expr                          { Cmconstr.modu $1 $3 }
  | expr AMPERSAND expr                         { Cmconstr.coq_and $1 $3 }
  | expr BAR expr                               { Cmconstr.coq_or $1 $3 }
  | expr CARET expr                             { Cmconstr.xor $1 $3 }
  | expr LESSLESS expr                          { Cmconstr.shl $1 $3 }
  | expr GREATERGREATER expr                    { Cmconstr.shr $1 $3 }
  | expr GREATERGREATERU expr                   { Cmconstr.shru $1 $3 }
  | expr PLUSF expr                             { Cmconstr.addf $1 $3 }
  | expr MINUSF expr                            { Cmconstr.subf $1 $3 }
  | expr STARF expr                             { Cmconstr.mulf $1 $3 }
  | expr SLASHF expr                            { Cmconstr.divf $1 $3 }
  | expr EQUALEQUAL expr                        { Cmconstr.cmp Ceq $1 $3 }
  | expr BANGEQUAL expr                         { Cmconstr.cmp Cne $1 $3 }
  | expr LESS expr                              { Cmconstr.cmp Clt $1 $3 }
  | expr LESSEQUAL expr                         { Cmconstr.cmp Cle $1 $3 }
  | expr GREATER expr                           { Cmconstr.cmp Cgt $1 $3 }
  | expr GREATEREQUAL expr                      { Cmconstr.cmp Cge $1 $3 }
  | expr EQUALEQUALU expr                       { Cmconstr.cmpu Ceq $1 $3 }
  | expr BANGEQUALU expr                        { Cmconstr.cmpu Cne $1 $3 }
  | expr LESSU expr                             { Cmconstr.cmpu Clt $1 $3 }
  | expr LESSEQUALU expr                        { Cmconstr.cmpu Cle $1 $3 }
  | expr GREATERU expr                          { Cmconstr.cmpu Cgt $1 $3 }
  | expr GREATEREQUALU expr                     { Cmconstr.cmpu Cge $1 $3 }
  | expr EQUALEQUALF expr                       { Cmconstr.cmpf Ceq $1 $3 }
  | expr BANGEQUALF expr                        { Cmconstr.cmpf Cne $1 $3 }
  | expr LESSF expr                             { Cmconstr.cmpf Clt $1 $3 }
  | expr LESSEQUALF expr                        { Cmconstr.cmpf Cle $1 $3 }
  | expr GREATERF expr                          { Cmconstr.cmpf Cgt $1 $3 }
  | expr GREATEREQUALF expr                     { Cmconstr.cmpf Cge $1 $3 }
  | memory_chunk LBRACKET expr RBRACKET         { Cmconstr.load $1 $3 }
  | memory_chunk LBRACKET expr RBRACKET EQUAL expr
                                                { Cmconstr.store $1 $3 $6 }
  | expr LPAREN expr_list RPAREN COLON signature
                                                { Ecall($6, $1, $3) }
  | expr AMPERSANDAMPERSAND expr                { andbool $1 $3 }
  | expr BARBAR expr                            { orbool $1 $3 }
  | expr QUESTION expr COLON expr               { Cmconstr.conditionalexpr $1 $3 $5 }
  | LET expr IN expr %prec p_let                { Elet($2, $4) }
  | DOLLAR INTLIT                               { Eletvar (nat_of_camlint $2) }
;

expr_list:
    /* empty */                                 { Enil }
  | expr_list_1                                 { $1 }
;

expr_list_1:
    expr                     %prec COMMA        { Econs($1, Enil) }
  | expr COMMA expr_list_1                      { Econs($1, $3) }
;

memory_chunk:
    INT8S                                       { Mint8signed }
  | INT8U                                       { Mint8unsigned }
  | INT16S                                      { Mint16signed }
  | INT16U                                      { Mint16unsigned }
  | INT32                                       { Mint32 }
  | INT                                         { Mint32 }
  | FLOAT32                                     { Mfloat32 }
  | FLOAT64                                     { Mfloat64 }
  | FLOAT                                       { Mfloat64 }
;

/* Types */

type_:
    INT                                         { Tint }
  | FLOAT                                       { Tfloat }
;
