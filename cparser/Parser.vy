/* *********************************************************************/
/*                                                                     */
/*              The Compcert verified compiler                         */
/*                                                                     */
/*          Jacques-Henri Jourdan, INRIA Paris-Rocquencourt            */
/*                                                                     */
/*  Copyright Institut National de Recherche en Informatique et en     */
/*  Automatique.  All rights reserved.  This file is distributed       */
/*  under the terms of the GNU General Public License as published by  */
/*  the Free Software Foundation, either version 2 of the License, or  */
/*  (at your option) any later version.  This file is also distributed */
/*  under the terms of the INRIA Non-Commercial License Agreement.     */
/*                                                                     */
/* *********************************************************************/

%{

Require Import List.
Require Cabs.

%}

%token<Cabs.string * Cabs.loc> VAR_NAME TYPEDEF_NAME OTHER_NAME
%token<Cabs.string * Cabs.loc> PRAGMA
%token<bool * list Cabs.char_code * Cabs.loc> STRING_LITERAL
%token<Cabs.constant * Cabs.loc> CONSTANT
%token<Cabs.loc> SIZEOF PTR INC DEC LEFT RIGHT LEQ GEQ EQEQ EQ NEQ LT GT
  ANDAND BARBAR PLUS MINUS STAR TILDE BANG SLASH PERCENT HAT BAR QUESTION
  COLON AND ALIGNOF

%token<Cabs.loc> MUL_ASSIGN DIV_ASSIGN MOD_ASSIGN ADD_ASSIGN SUB_ASSIGN
  LEFT_ASSIGN RIGHT_ASSIGN AND_ASSIGN XOR_ASSIGN OR_ASSIGN

%token<Cabs.loc> LPAREN RPAREN LBRACK RBRACK LBRACE RBRACE DOT COMMA
  SEMICOLON ELLIPSIS TYPEDEF EXTERN STATIC RESTRICT AUTO REGISTER INLINE
  NORETURN CHAR SHORT INT LONG SIGNED UNSIGNED FLOAT DOUBLE CONST VOLATILE VOID
  STRUCT UNION ENUM UNDERSCORE_BOOL PACKED ALIGNAS ATTRIBUTE ASM

%token<Cabs.loc> CASE DEFAULT IF_ ELSE SWITCH WHILE DO FOR GOTO CONTINUE BREAK
  RETURN BUILTIN_VA_ARG BUILTIN_OFFSETOF

%token EOF

%type<Cabs.expression * Cabs.loc> primary_expression postfix_expression
  unary_expression cast_expression multiplicative_expression additive_expression
  shift_expression relational_expression equality_expression AND_expression
  exclusive_OR_expression inclusive_OR_expression logical_AND_expression
  logical_OR_expression conditional_expression assignment_expression
  constant_expression expression
%type<Cabs.unary_operator * Cabs.loc> unary_operator
%type<Cabs.binary_operator> assignment_operator
%type<list Cabs.expression (* Reverse order *)> argument_expression_list
%type<Cabs.definition> declaration
%type<list Cabs.spec_elem * Cabs.loc> declaration_specifiers
%type<list Cabs.spec_elem> declaration_specifiers_typespec_opt
%type<list Cabs.init_name (* Reverse order *)> init_declarator_list
%type<Cabs.init_name> init_declarator
%type<Cabs.storage * Cabs.loc> storage_class_specifier
%type<Cabs.typeSpecifier * Cabs.loc> type_specifier struct_or_union_specifier enum_specifier
%type<Cabs.structOrUnion * Cabs.loc> struct_or_union
%type<list Cabs.field_group (* Reverse order *)> struct_declaration_list
%type<Cabs.field_group> struct_declaration
%type<list Cabs.spec_elem * Cabs.loc> specifier_qualifier_list
%type<list (option Cabs.name * option Cabs.expression) (* Reverse order *)>
  struct_declarator_list
%type<option Cabs.name * option Cabs.expression> struct_declarator
%type<list (Cabs.string * option Cabs.expression * Cabs.loc) (* Reverse order *)>
  enumerator_list
%type<Cabs.string * option Cabs.expression * Cabs.loc> enumerator
%type<Cabs.string * Cabs.loc> enumeration_constant
%type<Cabs.cvspec * Cabs.loc> type_qualifier type_qualifier_noattr
%type<Cabs.funspec * Cabs.loc> function_specifier
%type<Cabs.name> declarator declarator_noattrend direct_declarator
%type<(Cabs.decl_type -> Cabs.decl_type) * Cabs.loc> pointer
%type<list Cabs.cvspec (* Reverse order *)> type_qualifier_list
%type<list Cabs.parameter * bool> parameter_type_list
%type<list Cabs.parameter (* Reverse order *)> parameter_list
%type<Cabs.parameter> parameter_declaration
%type<list Cabs.spec_elem * Cabs.decl_type> type_name
%type<Cabs.decl_type> abstract_declarator direct_abstract_declarator
%type<Cabs.init_expression> c_initializer
%type<list (list Cabs.initwhat * Cabs.init_expression) (* Reverse order *)>
  initializer_list
%type<list Cabs.initwhat> designation
%type<list Cabs.initwhat (* Reverse order *)> designator_list
%type<Cabs.initwhat> designator
%type<Cabs.statement> statement_dangerous statement_safe
  labeled_statement(statement_safe) labeled_statement(statement_dangerous)
  iteration_statement(statement_safe) iteration_statement(statement_dangerous)
  compound_statement
%type<list Cabs.statement (* Reverse order *)> block_item_list
%type<Cabs.statement> block_item expression_statement selection_statement_dangerous
  selection_statement_safe jump_statement asm_statement
%type<list Cabs.definition (* Reverse order *)> translation_unit
%type<Cabs.definition> external_declaration function_definition
%type<list Cabs.definition> declaration_list
%type<Cabs.attribute * Cabs.loc> attribute_specifier
%type<list Cabs.attribute> attribute_specifier_list
%type<Cabs.gcc_attribute> gcc_attribute
%type<list Cabs.gcc_attribute> gcc_attribute_list
%type<Cabs.gcc_attribute_word> gcc_attribute_word
%type<list Cabs.string (* Reverse order *)> identifier_list
%type<list Cabs.asm_flag> asm_flags
%type<option Cabs.string> asm_op_name
%type<Cabs.asm_operand> asm_operand
%type<list Cabs.asm_operand> asm_operands asm_operands_ne
%type<list Cabs.asm_operand * list Cabs.asm_operand * list Cabs.asm_flag> asm_arguments
%type<list Cabs.cvspec> asm_attributes

%start<list Cabs.definition> translation_unit_file
%%

(* Actual grammar *)

(* 6.5.1 *)
primary_expression:
| var = VAR_NAME
    { (Cabs.VARIABLE (fst var), snd var) }
| cst = CONSTANT
    { (Cabs.CONSTANT (fst cst), snd cst) }
| str = STRING_LITERAL
    { let '((wide, chars), loc) := str in
      (Cabs.CONSTANT (Cabs.CONST_STRING wide chars), loc) }
| loc = LPAREN expr = expression RPAREN
    { (fst expr, loc)}

(* 6.5.2 *)
postfix_expression:
| expr = primary_expression
    { expr }
| expr = postfix_expression LBRACK index = expression RBRACK
    { (Cabs.INDEX (fst expr) (fst index), snd expr) }
| expr = postfix_expression LPAREN args = argument_expression_list RPAREN
    { (Cabs.CALL (fst expr) (rev' args), snd expr) }
| expr = postfix_expression LPAREN RPAREN
    { (Cabs.CALL (fst expr) [], snd expr) }
| loc = BUILTIN_VA_ARG LPAREN expr = assignment_expression COMMA ty = type_name RPAREN
    { (Cabs.BUILTIN_VA_ARG (fst expr) ty, loc) }
| expr = postfix_expression DOT mem = OTHER_NAME
    { (Cabs.MEMBEROF (fst expr) (fst mem), snd expr) }
| expr = postfix_expression PTR mem = OTHER_NAME
    { (Cabs.MEMBEROFPTR (fst expr) (fst mem), snd expr) }
| expr = postfix_expression INC
    { (Cabs.UNARY Cabs.POSINCR (fst expr), snd expr) }
| expr = postfix_expression DEC
    { (Cabs.UNARY Cabs.POSDECR (fst expr), snd expr) }
| loc = LPAREN typ = type_name RPAREN LBRACE init = initializer_list RBRACE
    { (Cabs.CAST typ (Cabs.COMPOUND_INIT (rev' init)), loc) }
| loc = LPAREN typ = type_name RPAREN LBRACE init = initializer_list COMMA RBRACE
    { (Cabs.CAST typ (Cabs.COMPOUND_INIT (rev' init)), loc) }
| loc = BUILTIN_OFFSETOF LPAREN typ = type_name COMMA id = OTHER_NAME
  mems = designator_list RPAREN
    { (Cabs.BUILTIN_OFFSETOF typ ((Cabs.INFIELD_INIT (fst id))::(rev mems)), loc) }
| loc = BUILTIN_OFFSETOF LPAREN typ = type_name COMMA mem = OTHER_NAME RPAREN
    { (Cabs.BUILTIN_OFFSETOF typ [Cabs.INFIELD_INIT (fst mem)], loc) }

(* Semantic value is in reverse order. *)
argument_expression_list:
| expr = assignment_expression
    { [fst expr] }
| exprq = argument_expression_list COMMA exprt = assignment_expression
    { fst exprt::exprq }

(* 6.5.3 *)
unary_expression:
| expr = postfix_expression
    { expr }
| loc = INC expr = unary_expression
    { (Cabs.UNARY Cabs.PREINCR (fst expr), loc) }
| loc = DEC expr = unary_expression
    { (Cabs.UNARY Cabs.PREDECR (fst expr), loc) }
| op = unary_operator expr = cast_expression
    { (Cabs.UNARY (fst op) (fst expr), snd op) }
| loc = SIZEOF expr = unary_expression
    { (Cabs.EXPR_SIZEOF (fst expr), loc) }
| loc = SIZEOF LPAREN typ = type_name RPAREN
    { (Cabs.TYPE_SIZEOF typ, loc) }
(* Non-standard *)
| loc = ALIGNOF LPAREN typ = type_name RPAREN
    { (Cabs.ALIGNOF typ, loc) }

unary_operator:
| loc = AND
    { (Cabs.ADDROF, loc) }
| loc = STAR
    { (Cabs.MEMOF, loc) }
| loc = PLUS
    { (Cabs.PLUS, loc) }
| loc = MINUS
    { (Cabs.MINUS, loc) }
| loc = TILDE
    { (Cabs.BNOT, loc) }
| loc = BANG
    { (Cabs.NOT, loc) }

(* 6.5.4 *)
cast_expression:
| expr = unary_expression
    { expr }
| loc = LPAREN typ = type_name RPAREN expr = cast_expression
    { (Cabs.CAST typ (Cabs.SINGLE_INIT (fst expr)), loc) }

(* 6.5.5 *)
multiplicative_expression:
| expr = cast_expression
    { expr }
| expr1 = multiplicative_expression STAR expr2 = cast_expression
    { (Cabs.BINARY Cabs.MUL (fst expr1) (fst expr2), snd expr1) }
| expr1 = multiplicative_expression SLASH expr2 = cast_expression
    { (Cabs.BINARY Cabs.DIV (fst expr1) (fst expr2), snd expr1) }
| expr1 = multiplicative_expression PERCENT expr2 = cast_expression
    { (Cabs.BINARY Cabs.MOD (fst expr1) (fst expr2), snd expr1) }

(* 6.5.6 *)
additive_expression:
| expr = multiplicative_expression
    { expr }
| expr1 = additive_expression PLUS expr2 = multiplicative_expression
    { (Cabs.BINARY Cabs.ADD (fst expr1) (fst expr2), snd expr1) }
| expr1 = additive_expression MINUS expr2 = multiplicative_expression
    { (Cabs.BINARY Cabs.SUB (fst expr1) (fst expr2), snd expr1) }

(* 6.5.7 *)
shift_expression:
| expr = additive_expression
    { expr }
| expr1 = shift_expression LEFT expr2 = additive_expression
    { (Cabs.BINARY Cabs.SHL (fst expr1) (fst expr2), snd expr1) }
| expr1 = shift_expression RIGHT expr2 = additive_expression
    { (Cabs.BINARY Cabs.SHR (fst expr1) (fst expr2), snd expr1) }

(* 6.5.8 *)
relational_expression:
| expr = shift_expression
    { expr }
| expr1 = relational_expression LT expr2 = shift_expression
    { (Cabs.BINARY Cabs.LT (fst expr1) (fst expr2), snd expr1) }
| expr1 = relational_expression GT expr2 = shift_expression
    { (Cabs.BINARY Cabs.GT (fst expr1) (fst expr2), snd expr1) }
| expr1 = relational_expression LEQ expr2 = shift_expression
    { (Cabs.BINARY Cabs.LE (fst expr1) (fst expr2), snd expr1) }
| expr1 = relational_expression GEQ expr2 = shift_expression
    { (Cabs.BINARY Cabs.GE (fst expr1) (fst expr2), snd expr1) }

(* 6.5.9 *)
equality_expression:
| expr = relational_expression
    { expr }
| expr1 = equality_expression EQEQ expr2 = relational_expression
    { (Cabs.BINARY Cabs.EQ (fst expr1) (fst expr2), snd expr1) }
| expr1 = equality_expression NEQ expr2 = relational_expression
    { (Cabs.BINARY Cabs.NE (fst expr1) (fst expr2), snd expr1) }

(* 6.5.10 *)
AND_expression:
| expr = equality_expression
    { expr }
| expr1 = AND_expression AND expr2 = equality_expression
    { (Cabs.BINARY Cabs.BAND (fst expr1) (fst expr2), snd expr1) }

(* 6.5.11 *)
exclusive_OR_expression:
| expr = AND_expression
    { expr }
| expr1 = exclusive_OR_expression HAT expr2 = AND_expression
    { (Cabs.BINARY Cabs.XOR (fst expr1) (fst expr2), snd expr1) }

(* 6.5.12 *)
inclusive_OR_expression:
| expr = exclusive_OR_expression
    { expr }
| expr1 = inclusive_OR_expression BAR expr2 = exclusive_OR_expression
    { (Cabs.BINARY Cabs.BOR (fst expr1) (fst expr2), snd expr1) }

(* 6.5.13 *)
logical_AND_expression:
| expr = inclusive_OR_expression
    { expr }
| expr1 = logical_AND_expression ANDAND expr2 = inclusive_OR_expression
    { (Cabs.BINARY Cabs.AND (fst expr1) (fst expr2), snd expr1) }

(* 6.5.14 *)
logical_OR_expression:
| expr = logical_AND_expression
    { expr }
| expr1 = logical_OR_expression BARBAR expr2 = logical_AND_expression
    { (Cabs.BINARY Cabs.OR (fst expr1) (fst expr2), snd expr1) }

(* 6.5.15 *)
conditional_expression:
| expr = logical_OR_expression
    { expr }
| expr1 = logical_OR_expression QUESTION expr2 = expression COLON
  expr3 = conditional_expression
    { (Cabs.QUESTION (fst expr1) (fst expr2) (fst expr3), snd expr1) }

(* 6.5.16 *)
assignment_expression:
| expr = conditional_expression
    { expr }
| expr1 = unary_expression op = assignment_operator expr2 = assignment_expression
    { (Cabs.BINARY op (fst expr1) (fst expr2), snd expr1) }

assignment_operator:
| EQ
    { Cabs.ASSIGN  }
| MUL_ASSIGN
    { Cabs.MUL_ASSIGN }
| DIV_ASSIGN
    { Cabs.DIV_ASSIGN }
| MOD_ASSIGN
    { Cabs.MOD_ASSIGN }
| ADD_ASSIGN
    { Cabs.ADD_ASSIGN }
| SUB_ASSIGN
    { Cabs.SUB_ASSIGN }
| LEFT_ASSIGN
    { Cabs.SHL_ASSIGN }
| RIGHT_ASSIGN
    { Cabs.SHR_ASSIGN }
| XOR_ASSIGN
    { Cabs.XOR_ASSIGN }
| OR_ASSIGN
    { Cabs.BOR_ASSIGN }
| AND_ASSIGN
    { Cabs.BAND_ASSIGN }

(* 6.5.17 *)
expression:
| expr = assignment_expression
    { expr }
| expr1 = expression COMMA expr2 = assignment_expression
    { (Cabs.BINARY Cabs.COMMA (fst expr1) (fst expr2), snd expr1) }

(* 6.6 *)
constant_expression:
| expr = conditional_expression
    { expr }

(* 6.7 *)
declaration:
| decspec = declaration_specifiers decls = init_declarator_list SEMICOLON
    { Cabs.DECDEF (fst decspec, rev' decls) (snd decspec) }
| decspec = declaration_specifiers SEMICOLON
    { Cabs.DECDEF (fst decspec, []) (snd decspec) }

declaration_specifiers_typespec_opt:
| storage = storage_class_specifier rest = declaration_specifiers_typespec_opt
    { Cabs.SpecStorage (fst storage)::rest }
| typ = type_specifier rest = declaration_specifiers_typespec_opt
    { Cabs.SpecType (fst typ)::rest }
| qual = type_qualifier rest = declaration_specifiers_typespec_opt
    { Cabs.SpecCV (fst qual)::rest }
| func = function_specifier rest = declaration_specifiers_typespec_opt
    { Cabs.SpecFunction (fst func)::rest }
| /* empty */
    { [] }


(* We impose a lighter constraint on declaration specifiers than in the
   pre_parser: declaration specifiers should have at least one type
   specifier. *)
declaration_specifiers:
| storage = storage_class_specifier rest = declaration_specifiers
    { (Cabs.SpecStorage (fst storage)::fst rest, snd storage) }
| typ = type_specifier rest = declaration_specifiers_typespec_opt
    { (Cabs.SpecType (fst typ)::rest, snd typ) }
(* We have to inline type_qualifier in order to avoid a conflict. *)
| qual = type_qualifier_noattr rest = declaration_specifiers
    { (Cabs.SpecCV (fst qual)::fst rest, snd qual) }
| attr = attribute_specifier rest = declaration_specifiers
    { (Cabs.SpecCV (Cabs.CV_ATTR (fst attr))::fst rest, snd attr) }
| func = function_specifier rest = declaration_specifiers
    { (Cabs.SpecFunction (fst func)::fst rest, snd func) }

init_declarator_list:
| init = init_declarator
    { [init] }
| initq = init_declarator_list COMMA initt = init_declarator
    { initt::initq }

init_declarator:
| name = declarator
    { Cabs.Init_name name Cabs.NO_INIT }
| name = declarator EQ init = c_initializer
    { Cabs.Init_name name init }

(* 6.7.1 *)
storage_class_specifier:
| loc = TYPEDEF
    { (Cabs.TYPEDEF, loc) }
| loc = EXTERN
    { (Cabs.EXTERN, loc) }
| loc = STATIC
    { (Cabs.STATIC, loc) }
| loc = AUTO
    { (Cabs.AUTO, loc) }
| loc = REGISTER
    { (Cabs.REGISTER, loc) }

(* 6.7.2 *)
type_specifier:
| loc = VOID
    { (Cabs.Tvoid, loc) }
| loc = CHAR
    { (Cabs.Tchar, loc) }
| loc = SHORT
    { (Cabs.Tshort, loc) }
| loc = INT
    { (Cabs.Tint, loc) }
| loc = LONG
    { (Cabs.Tlong, loc) }
| loc = FLOAT
    { (Cabs.Tfloat, loc) }
| loc = DOUBLE
    { (Cabs.Tdouble, loc) }
| loc = SIGNED
    { (Cabs.Tsigned, loc) }
| loc = UNSIGNED
    { (Cabs.Tunsigned, loc) }
| loc = UNDERSCORE_BOOL
    { (Cabs.T_Bool, loc) }
| spec = struct_or_union_specifier
    { spec }
| spec = enum_specifier
    { spec }
| id = TYPEDEF_NAME
    { (Cabs.Tnamed (fst id), snd id) }

(* 6.7.2.1 *)
struct_or_union_specifier:
| str_uni = struct_or_union attrs = attribute_specifier_list id = OTHER_NAME
  LBRACE decls = struct_declaration_list RBRACE
    { (Cabs.Tstruct_union (fst str_uni) (Some (fst id)) (Some (rev' decls)) attrs,
       snd str_uni) }
| str_uni = struct_or_union attrs = attribute_specifier_list
  LBRACE decls = struct_declaration_list RBRACE
    { (Cabs.Tstruct_union (fst str_uni) None (Some (rev' decls)) attrs,
       snd str_uni) }
| str_uni = struct_or_union attrs = attribute_specifier_list id = OTHER_NAME
    { (Cabs.Tstruct_union (fst str_uni) (Some (fst id)) None attrs,
       snd str_uni) }

struct_or_union:
| loc = STRUCT
    { (Cabs.STRUCT, loc) }
| loc = UNION
    { (Cabs.UNION, loc) }

struct_declaration_list:
| (* empty *)
    { nil }
| qdecls = struct_declaration_list tdecls = struct_declaration
    { tdecls::qdecls }

struct_declaration:
| decspec = specifier_qualifier_list decls = struct_declarator_list SEMICOLON
    { Cabs.Field_group (fst decspec) (rev' decls) (snd decspec) }
(* Extension to C99 grammar needed to parse some GNU header files. *)
| decspec = specifier_qualifier_list SEMICOLON
    { Cabs.Field_group (fst decspec) [(None,None)] (snd decspec) }

specifier_qualifier_list:
| typ = type_specifier rest = specifier_qualifier_list
    { (Cabs.SpecType (fst typ)::fst rest, snd typ) }
| typ = type_specifier
    { ([Cabs.SpecType (fst typ)], snd typ) }
| qual = type_qualifier rest = specifier_qualifier_list
    { (Cabs.SpecCV (fst qual)::fst rest, snd qual) }
| qual = type_qualifier
    { ([Cabs.SpecCV (fst qual)], snd qual) }

struct_declarator_list:
| decl = struct_declarator
    { [decl] }
| declq = struct_declarator_list COMMA declt = struct_declarator
    { declt::declq }

struct_declarator:
| decl = declarator
    { (Some decl, None) }
| decl = declarator COLON expr = constant_expression
    { (Some decl, Some (fst expr)) }
| COLON expr = constant_expression
    { (None, Some (fst expr)) }

(* 6.7.2.2 *)
enum_specifier:
| loc = ENUM attrs = attribute_specifier_list name = OTHER_NAME
  LBRACE enum_list = enumerator_list RBRACE
    { (Cabs.Tenum (Some (fst name)) (Some (rev' enum_list)) attrs, loc) }
| loc = ENUM attrs = attribute_specifier_list
  LBRACE enum_list = enumerator_list RBRACE
    { (Cabs.Tenum None (Some (rev' enum_list)) attrs, loc) }
| loc = ENUM attrs = attribute_specifier_list name = OTHER_NAME
  LBRACE enum_list = enumerator_list COMMA RBRACE
    { (Cabs.Tenum (Some (fst name)) (Some (rev' enum_list)) attrs, loc) }
| loc = ENUM attrs = attribute_specifier_list
  LBRACE enum_list = enumerator_list COMMA RBRACE
    { (Cabs.Tenum None (Some (rev' enum_list)) attrs, loc) }
| loc = ENUM attrs = attribute_specifier_list name = OTHER_NAME
    { (Cabs.Tenum (Some (fst name)) None attrs, loc) }

enumerator_list:
| enum = enumerator
    { [enum] }
| enumsq = enumerator_list COMMA enumst = enumerator
    { enumst::enumsq }

enumerator:
| cst = enumeration_constant
    { (fst cst, None, snd cst) }
| cst = enumeration_constant EQ expr = constant_expression
    { (fst cst, Some (fst expr), snd cst) }

enumeration_constant:
| cst = VAR_NAME
    { cst }

(* 6.7.3 *)
type_qualifier_noattr:
| loc = CONST
    { (Cabs.CV_CONST, loc) }
| loc = RESTRICT
    { (Cabs.CV_RESTRICT, loc) }
| loc = VOLATILE
    { (Cabs.CV_VOLATILE, loc) }

type_qualifier:
| qual = type_qualifier_noattr
    { qual }
(* Non-standard *)
| attr = attribute_specifier
    { (Cabs.CV_ATTR (fst attr), snd attr) }

(* Non-standard *)

attribute_specifier_list:
| /* empty */
    { [] }
|  attr = attribute_specifier attrs = attribute_specifier_list
   { fst attr :: attrs }

attribute_specifier:
| loc = ATTRIBUTE LPAREN LPAREN attr = gcc_attribute_list RPAREN RPAREN
    { (Cabs.GCC_ATTR (rev' attr) loc, loc) }
| loc = PACKED LPAREN args = argument_expression_list RPAREN
    { (Cabs.PACKED_ATTR (rev' args) loc, loc) }
| loc = ALIGNAS LPAREN args = argument_expression_list RPAREN
    { (Cabs.ALIGNAS_ATTR (rev' args) loc, loc) }
| loc = ALIGNAS LPAREN typ = type_name RPAREN
    { (Cabs.ALIGNAS_ATTR [Cabs.ALIGNOF typ] loc, loc) }

gcc_attribute_list:
| a = gcc_attribute
    { [a] }
| q = gcc_attribute_list COMMA t = gcc_attribute
    { t::q }

gcc_attribute:
| /* empty */
    { Cabs.GCC_ATTR_EMPTY }
| w = gcc_attribute_word
    { Cabs.GCC_ATTR_NOARGS w }
| w = gcc_attribute_word LPAREN RPAREN
    { Cabs.GCC_ATTR_ARGS w [] }
| w = gcc_attribute_word LPAREN args = argument_expression_list RPAREN
    { Cabs.GCC_ATTR_ARGS w (rev' args) }

gcc_attribute_word:
| i = OTHER_NAME
    { Cabs.GCC_ATTR_IDENT (fst i) }
| CONST
    { Cabs.GCC_ATTR_CONST }
| PACKED
    { Cabs.GCC_ATTR_PACKED }

(* 6.7.4 *)
function_specifier:
| loc = INLINE
   { (Cabs.INLINE, loc) }
| loc = NORETURN
  { (Cabs.NORETURN, loc)}

(* 6.7.5 *)
declarator:
| decl = declarator_noattrend attrs = attribute_specifier_list
    { let 'Cabs.Name name typ attr loc := decl in
      Cabs.Name name typ (List.app attr attrs) loc }

declarator_noattrend:
| decl = direct_declarator
    { decl }
| pt = pointer decl = direct_declarator
    { let 'Cabs.Name name typ attr _ := decl in
      Cabs.Name name ((fst pt) typ) attr (snd pt) }

direct_declarator:
| id = VAR_NAME
    { Cabs.Name (fst id) Cabs.JUSTBASE [] (snd id) }
| LPAREN decl = declarator RPAREN
    { decl }
| decl = direct_declarator LBRACK quallst = type_qualifier_list
  expr = assignment_expression RBRACK
    { let 'Cabs.Name name typ attr loc := decl in
      Cabs.Name name (Cabs.ARRAY typ (rev' quallst) (Some (fst expr))) attr loc }
| decl = direct_declarator LBRACK expr = assignment_expression RBRACK
    { let 'Cabs.Name name typ attr loc := decl in
      Cabs.Name name (Cabs.ARRAY typ [] (Some (fst expr))) attr loc }
| decl = direct_declarator LBRACK quallst = type_qualifier_list RBRACK
    { let 'Cabs.Name name typ attr loc := decl in
      Cabs.Name name (Cabs.ARRAY typ (rev' quallst) None) attr loc }
| decl = direct_declarator LBRACK RBRACK
    { let 'Cabs.Name name typ attr loc := decl in
      Cabs.Name name (Cabs.ARRAY typ [] None) attr loc }
(*| direct_declarator LBRACK ... STATIC ... RBRACK
| direct_declarator LBRACK STAR RBRACK*)
| decl = direct_declarator LPAREN params = parameter_type_list RPAREN
    { let 'Cabs.Name name typ attr loc := decl in
      Cabs.Name name (Cabs.PROTO typ params) attr loc }
| decl = direct_declarator LPAREN RPAREN
    { let 'Cabs.Name name typ attr loc := decl in
      Cabs.Name name (Cabs.PROTO_OLD typ []) attr loc }
| decl = direct_declarator LPAREN params = identifier_list RPAREN
    { let 'Cabs.Name name typ attr loc := decl in
      Cabs.Name name (Cabs.PROTO_OLD typ (rev' params)) attr loc }

pointer:
| loc = STAR
    { (fun typ => Cabs.PTR [] typ, loc) }
| loc = STAR quallst = type_qualifier_list
    { (fun typ => Cabs.PTR (rev' quallst) typ, loc) }
| loc = STAR pt = pointer
    { (fun typ => Cabs.PTR [] ((fst pt) typ), loc) }
| loc = STAR quallst = type_qualifier_list pt = pointer
    { (fun typ => Cabs.PTR (rev' quallst) ((fst pt) typ), loc) }

type_qualifier_list:
| qual = type_qualifier
    { [fst qual] }
| qualq = type_qualifier_list qualt = type_qualifier
    { fst qualt::qualq }

parameter_type_list:
| lst = parameter_list
    { (rev' lst, false) }
| lst = parameter_list COMMA ELLIPSIS
    { (rev' lst, true) }

parameter_list:
| param = parameter_declaration
    { [param] }
| paramq = parameter_list COMMA paramt = parameter_declaration
    { paramt::paramq }

parameter_declaration:
| specs = declaration_specifiers decl = declarator
    { match decl with Cabs.Name name typ attr _ =>
        Cabs.PARAM (fst specs) (Some name) typ attr (snd specs) end }
| specs = declaration_specifiers decl = abstract_declarator
    { Cabs.PARAM (fst specs) None decl [] (snd specs) }
| specs = declaration_specifiers
    { Cabs.PARAM (fst specs) None Cabs.JUSTBASE [] (snd specs) }

identifier_list:
| id = VAR_NAME
    { [fst id] }
| idl = identifier_list COMMA id = VAR_NAME
    { fst id :: idl }

(* 6.7.6 *)
type_name:
| specqual = specifier_qualifier_list
    { (fst specqual, Cabs.JUSTBASE) }
| specqual = specifier_qualifier_list typ = abstract_declarator
    { (fst specqual, typ) }

abstract_declarator:
| pt = pointer
    { (fst pt) Cabs.JUSTBASE }
| pt = pointer typ = direct_abstract_declarator
    { (fst pt) typ }
| typ = direct_abstract_declarator
    { typ }

direct_abstract_declarator:
| LPAREN typ = abstract_declarator RPAREN
    { typ }
| typ = direct_abstract_declarator LBRACK cvspec = type_qualifier_list
  expr = assignment_expression RBRACK
    { Cabs.ARRAY typ cvspec (Some (fst expr)) }
| LBRACK cvspec = type_qualifier_list expr = assignment_expression RBRACK
    { Cabs.ARRAY Cabs.JUSTBASE cvspec (Some (fst expr)) }
| typ = direct_abstract_declarator LBRACK expr = assignment_expression RBRACK
    { Cabs.ARRAY typ [] (Some (fst expr)) }
| LBRACK expr = assignment_expression RBRACK
    { Cabs.ARRAY Cabs.JUSTBASE [] (Some (fst expr)) }
| typ = direct_abstract_declarator LBRACK cvspec = type_qualifier_list RBRACK
    { Cabs.ARRAY typ cvspec None }
| LBRACK cvspec = type_qualifier_list RBRACK
    { Cabs.ARRAY Cabs.JUSTBASE cvspec None }
| typ = direct_abstract_declarator LBRACK RBRACK
    { Cabs.ARRAY typ [] None }
| LBRACK RBRACK
    { Cabs.ARRAY Cabs.JUSTBASE [] None }
(*| direct_abstract_declarator? LBRACK STAR RBRACK*)
(*| direct_abstract_declarator? LBRACK ... STATIC ... RBRACK*)
| typ = direct_abstract_declarator LPAREN params = parameter_type_list RPAREN
    { Cabs.PROTO typ params }
| LPAREN params = parameter_type_list RPAREN
    { Cabs.PROTO Cabs.JUSTBASE params }
| typ = direct_abstract_declarator LPAREN RPAREN
    { Cabs.PROTO typ ([], false) }
| LPAREN RPAREN
    { Cabs.PROTO Cabs.JUSTBASE ([], false) }

(* 6.7.8 *)
c_initializer:
| expr = assignment_expression
    { Cabs.SINGLE_INIT (fst expr) }
| LBRACE init = initializer_list RBRACE
    { Cabs.COMPOUND_INIT (rev' init) }
| LBRACE init = initializer_list COMMA RBRACE
    { Cabs.COMPOUND_INIT (rev' init) }

initializer_list:
| design = designation init = c_initializer
    { [(design, init)] }
| init = c_initializer
    { [([], init)] }
| initq = initializer_list COMMA design = designation init = c_initializer
    { (design, init)::initq }
| initq = initializer_list COMMA init = c_initializer
    { ([], init)::initq }

designation:
| design = designator_list EQ
    { rev' design }

designator_list:
| design = designator
    { [design] }
| designq = designator_list designt = designator
    { designt::designq }

designator:
| LBRACK expr = constant_expression RBRACK
    { Cabs.ATINDEX_INIT (fst expr) }
| DOT id = OTHER_NAME
    { Cabs.INFIELD_INIT (fst id) }

(* 6.8 *)
statement_dangerous:
| stmt = labeled_statement(statement_dangerous)
| stmt = compound_statement
| stmt = expression_statement
| stmt = selection_statement_dangerous
| stmt = iteration_statement(statement_dangerous)
| stmt = jump_statement
(* Non-standard *)
| stmt = asm_statement
    { stmt }

statement_safe:
| stmt = labeled_statement(statement_safe)
| stmt = compound_statement
| stmt = expression_statement
| stmt = selection_statement_safe
| stmt = iteration_statement(statement_safe)
| stmt = jump_statement
(* Non-standard *)
| stmt = asm_statement
    { stmt }

(* 6.8.1 *)
labeled_statement(last_statement):
| lbl = OTHER_NAME COLON stmt = last_statement
    { Cabs.LABEL (fst lbl) stmt (snd lbl) }
| loc = CASE expr = constant_expression COLON stmt = last_statement
    { Cabs.CASE (fst expr) stmt loc }
| loc = DEFAULT COLON stmt = last_statement
    { Cabs.DEFAULT stmt loc }

(* 6.8.2 *)
compound_statement:
| loc = LBRACE lst = block_item_list RBRACE
    { Cabs.BLOCK (rev' lst) loc }
| loc = LBRACE RBRACE
    { Cabs.BLOCK [] loc }

block_item_list:
| stmt = block_item
    { [stmt] }
| stmtq = block_item_list stmtt = block_item
    { stmtt::stmtq }

block_item:
| decl = declaration
    { Cabs.DEFINITION decl }
| stmt = statement_dangerous
    { stmt }
(* Non-standard *)
| p = PRAGMA
    { Cabs.DEFINITION (Cabs.PRAGMA (fst p) (snd p)) }

(* 6.8.3 *)
expression_statement:
| expr = expression SEMICOLON
    { Cabs.COMPUTATION (fst expr) (snd expr) }
| loc = SEMICOLON
    { Cabs.NOP loc }

(* 6.8.4 *)
selection_statement_dangerous:
| loc = IF_ LPAREN expr = expression RPAREN stmt = statement_dangerous
    { Cabs.If (fst expr) stmt None loc }
| loc = IF_ LPAREN expr = expression RPAREN stmt1 = statement_safe ELSE
  stmt2 = statement_dangerous
    { Cabs.If (fst expr) stmt1 (Some stmt2) loc }
| loc = SWITCH LPAREN expr = expression RPAREN stmt = statement_dangerous
    { Cabs.SWITCH (fst expr) stmt loc }

selection_statement_safe:
| loc = IF_ LPAREN expr = expression RPAREN stmt1 = statement_safe ELSE
  stmt2 = statement_safe
    { Cabs.If (fst expr) stmt1 (Some stmt2) loc }
| loc = SWITCH LPAREN expr = expression RPAREN stmt = statement_safe
    { Cabs.SWITCH (fst expr) stmt loc }

(* 6.8.5 *)
iteration_statement(last_statement):
| loc = WHILE LPAREN expr = expression RPAREN stmt = last_statement
    { Cabs.WHILE (fst expr) stmt loc }
| loc = DO stmt = statement_dangerous WHILE LPAREN expr = expression RPAREN SEMICOLON
    { Cabs.DOWHILE (fst expr) stmt loc }
| loc = FOR LPAREN expr1 = expression SEMICOLON expr2 = expression SEMICOLON
  expr3 = expression RPAREN stmt = last_statement
    { Cabs.FOR (Some (Cabs.FC_EXP (fst expr1))) (Some (fst expr2)) (Some (fst expr3)) stmt loc }
| loc = FOR LPAREN decl1 = declaration expr2 = expression SEMICOLON
  expr3 = expression RPAREN stmt = last_statement
    { Cabs.FOR (Some (Cabs.FC_DECL decl1)) (Some (fst expr2)) (Some (fst expr3)) stmt loc }
| loc = FOR LPAREN SEMICOLON expr2 = expression SEMICOLON expr3 = expression RPAREN 
  stmt = last_statement
    { Cabs.FOR None (Some (fst expr2)) (Some (fst expr3)) stmt loc }
| loc = FOR LPAREN expr1 = expression SEMICOLON SEMICOLON expr3 = expression RPAREN
  stmt = last_statement
    { Cabs.FOR (Some (Cabs.FC_EXP (fst expr1))) None (Some (fst expr3)) stmt loc }
| loc = FOR LPAREN decl1 = declaration SEMICOLON expr3 = expression RPAREN
  stmt = last_statement
    { Cabs.FOR (Some (Cabs.FC_DECL decl1)) None (Some (fst expr3)) stmt loc }
| loc = FOR LPAREN SEMICOLON SEMICOLON expr3 = expression RPAREN stmt = last_statement
    { Cabs.FOR None None (Some (fst expr3)) stmt loc }
| loc = FOR LPAREN expr1 = expression SEMICOLON expr2 = expression SEMICOLON RPAREN
  stmt = last_statement
    { Cabs.FOR (Some (Cabs.FC_EXP (fst expr1))) (Some (fst expr2)) None stmt loc }
| loc = FOR LPAREN decl1 = declaration expr2 = expression SEMICOLON RPAREN
  stmt = last_statement
    { Cabs.FOR (Some (Cabs.FC_DECL decl1)) (Some (fst expr2)) None stmt loc }
| loc = FOR LPAREN SEMICOLON expr2 = expression SEMICOLON RPAREN stmt = last_statement
    { Cabs.FOR None (Some (fst expr2)) None stmt loc }
| loc = FOR LPAREN expr1 = expression SEMICOLON SEMICOLON RPAREN stmt = last_statement
    { Cabs.FOR (Some (Cabs.FC_EXP (fst expr1))) None None stmt loc }
| loc = FOR LPAREN decl1 = declaration SEMICOLON RPAREN stmt = last_statement
    { Cabs.FOR (Some (Cabs.FC_DECL decl1)) None None stmt loc }
| loc = FOR LPAREN SEMICOLON SEMICOLON RPAREN stmt = last_statement
    { Cabs.FOR None None None stmt loc }

(* 6.8.6 *)
jump_statement:
| loc = GOTO id = OTHER_NAME SEMICOLON
    { Cabs.GOTO (fst id) loc }
| loc = CONTINUE SEMICOLON
    { Cabs.CONTINUE loc }
| loc = BREAK SEMICOLON
    { Cabs.BREAK loc }
| loc = RETURN expr = expression SEMICOLON
    { Cabs.RETURN (Some (fst expr)) loc }
| loc = RETURN SEMICOLON
    { Cabs.RETURN None loc }

(* Non-standard *)
asm_statement:
| loc = ASM attr = asm_attributes LPAREN template = STRING_LITERAL args = asm_arguments
  RPAREN SEMICOLON
    { let '(wide, chars, _) := template in
      let '(outputs, inputs, flags) := args in
      Cabs.ASM attr wide chars outputs inputs flags loc }

asm_attributes:
| /* empty */
     { [] }
| CONST attr = asm_attributes
     { Cabs.CV_CONST :: attr }
| VOLATILE attr = asm_attributes
     { Cabs.CV_VOLATILE :: attr }

asm_arguments:
| /* empty */
     { ([], [], []) }
| COLON o = asm_operands
     { (o, [], []) }
| COLON o = asm_operands COLON i = asm_operands
     { (o, i, []) }
| COLON o = asm_operands COLON i = asm_operands COLON f = asm_flags
     { (o, i, f) }

asm_operands:
| /* empty */                                   { [] }
| ol = asm_operands_ne                          { rev' ol }

asm_operands_ne:
| ol = asm_operands_ne COMMA o = asm_operand    { o :: ol }
| o = asm_operand                               { [o] }

asm_operand:
| n = asm_op_name cstr = STRING_LITERAL LPAREN e = expression RPAREN
    { let '(wide, s, loc) := cstr in Cabs.ASMOPERAND n wide s (fst e) }

asm_op_name:
| /* empty */                         { None }
| LBRACK n = OTHER_NAME RBRACK        { Some (fst n) }

asm_flags:
| f = STRING_LITERAL
    { let '(wide, s, loc) := f in (wide, s) :: nil }
| f = STRING_LITERAL COMMA fl = asm_flags
    { let '(wide, s, loc) := f in (wide, s) :: fl }

(* 6.9 *)
translation_unit_file:
| lst = translation_unit EOF
    { rev' lst }
(* Non-standard *)
| EOF
    { [] }

translation_unit:
| def = external_declaration
    { [def] }
| defq = translation_unit deft = external_declaration
    { deft::defq }
(* Non-standard : empty declaration *)
| tu = translation_unit SEMICOLON
    { tu }
| SEMICOLON
    { [] }

external_declaration:
| def = function_definition
| def = declaration
    { def }
(* Non-standard *)
| p = PRAGMA
    { Cabs.PRAGMA (fst p) (snd p) }


(* 6.9.1 *)
function_definition:
| specs = declaration_specifiers
  decl = declarator_noattrend
  dlist = declaration_list
  stmt = compound_statement
   { Cabs.FUNDEF (fst specs) decl (List.rev' dlist) stmt (snd specs) }
| specs = declaration_specifiers
  decl = declarator
  stmt = compound_statement
    { Cabs.FUNDEF (fst specs) decl [] stmt (snd specs) }

declaration_list:
| d = declaration
    { [d] }
| dl = declaration_list d = declaration
    { d :: dl }
