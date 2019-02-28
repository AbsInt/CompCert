/* *********************************************************************/
/*                                                                     */
/*              The Compcert verified compiler                         */
/*                                                                     */
/*          Jacques-Henri Jourdan, INRIA Paris-Rocquencourt            */
/*             François Pottier, INRIA Paris-Rocquencourt              */
/*                                                                     */
/*  Copyright Institut National de Recherche en Informatique et en     */
/*  Automatique.  All rights reserved.  This file is distributed       */
/*  under the terms of the GNU General Public License as published by  */
/*  the Free Software Foundation, either version 2 of the License, or  */
/*  (at your option) any later version.  This file is also distributed */
/*  under the terms of the INRIA Non-Commercial License Agreement.     */
/*                                                                     */
/* *********************************************************************/

(*
   WARNING: The precedence declarations tend to silently solve
   conflicts. So, if you change the grammar (especially for
   statements), you should check that when you run "make correct"
   in the cparser/ directory, Menhir should say:
     2 shift/reduce conflicts were silently solved.
*)

%{
  open Pre_parser_aux

  let set_id_type (_,r,_) t =
    r := t

  let declare_varname (i,_,_) =
    !declare_varname i

  let declare_typename (i,_,_) =
    !declare_typename i

  type 'id fun_declarator_ctx =
  | Decl_ident
  | Decl_other
  | Decl_fun of (unit -> unit)
  | Decl_krfun of 'id

%}

%token<string> PRE_NAME
%token<string * Pre_parser_aux.identifier_type ref * Cabs.cabsloc>
  VAR_NAME TYPEDEF_NAME
%token<Cabs.constant * Cabs.cabsloc> CONSTANT
%token<bool * int64 list * Cabs.cabsloc> STRING_LITERAL
%token<string * Cabs.cabsloc> PRAGMA

%token<Cabs.cabsloc> SIZEOF PTR INC DEC LEFT RIGHT LEQ GEQ EQEQ EQ NEQ LT GT
  ANDAND BARBAR PLUS MINUS STAR TILDE BANG SLASH PERCENT HAT BAR QUESTION
  COLON AND MUL_ASSIGN DIV_ASSIGN MOD_ASSIGN ADD_ASSIGN SUB_ASSIGN LEFT_ASSIGN
  RIGHT_ASSIGN AND_ASSIGN XOR_ASSIGN OR_ASSIGN LPAREN RPAREN LBRACK RBRACK
  LBRACE RBRACE DOT COMMA SEMICOLON ELLIPSIS TYPEDEF EXTERN STATIC RESTRICT
  AUTO REGISTER INLINE NORETURN CHAR SHORT INT LONG SIGNED UNSIGNED FLOAT DOUBLE
  UNDERSCORE_BOOL CONST VOLATILE VOID STRUCT UNION ENUM CASE DEFAULT IF ELSE
  SWITCH WHILE DO FOR GOTO CONTINUE BREAK RETURN BUILTIN_VA_ARG ALIGNOF
  ATTRIBUTE ALIGNAS PACKED ASM BUILTIN_OFFSETOF

%token EOF

(* These precedence declarations solve the conflict in the following
   declaration:

   int f(int (a));

   when a is a TYPEDEF_NAME. It is specified by 6.7.5.3 11: 'a' should
   be taken as the type of parameter of the anonymous function.

   See below comment on [low_prec]
*)
%nonassoc lowPrec1
%nonassoc TYPEDEF_NAME

(* These precedence declarations solve the dangling else conflict. *)
%nonassoc lowPrec2
%nonassoc ELSE

%start<unit> translation_unit_file

(* The following declarations cause certain nonterminal symbols to be
   reduced when an error is detected. This replaces error actions in
   the automaton with reduction actions. So, if the input is correct,
   this makes no difference, and if the input is incorrect, this only
   forces a few more reductions to take place before the error is
   detected and reported. If used properly, this facilitates error
   reports. *)

%on_error_reduce
  primary_expression
  postfix_expression
  unary_expression
  cast_expression
  multiplicative_expression
  additive_expression
  shift_expression
  relational_expression
  equality_expression
  and_expression
  exclusive_or_expression
  inclusive_or_expression
  logical_and_expression
  logical_or_expression
  conditional_expression
  assignment_expression
  expression
  attribute_specifier_list
  declarator
  declarator_noattrend
  selection_statement
  enum_specifier
  struct_or_union_specifier
  specifier_qualifier_list(struct_declaration)
  specifier_qualifier_list(type_name)
  option(abstract_declarator(type_name))
  abstract_declarator(type_name)
  abstract_declarator(parameter_declaration)
  asm_flags
  asm_operands
  init_declarator
  rlist(declaration_specifier_no_type)

%%

(* Helpers *)

(* Note that, by convention, [X?] is syntactic sugar for [option(X)],
   so this definition of [option] is actually used, even though the
   word [option] does not appear in the rest of this file. *)

(* [ioption(X)] is equivalent to [option(X)], but is marked [%inline],
   so its definition is expanded. In the absence of conflicts, the two
   are equivalent. Using [ioption] instead of [option] in well-chosen
   places can help avoid conflicts. Conversely, using [option] instead
   of [ioption] in well-chosen places can help reduce the number of
   states of the automaton. *)

(* Defining the non-%inline version in terms of the %inline version is
   a standard idiom. It obviates the need to duplicate the definition.
   The same idiom is used elsewhere below. *)

%inline ioption(X):
| /* nothing */
    { None }
| x = X
    { Some x }

option(X):
  o = ioption(X)
    { o }

(* [optional(X, Y)] is equivalent to [X? Y]. However, by inlining
   the two possibilies -- either [X Y] or just [Y] -- we are able
   to give more meaningful syntax error messages. [optional(X, Y)]
   itself is usually NOT inlined, as that would cause a useless
   explosion of cases. *)
optional(X, Y):
  ioption(X) Y {}

(* This is a standard left-recursive, possibly empty list, without
   separators. Note that, by convention, [X*] is syntactic sugar for
   [list(X)]. *)

(* [ilist(X)] is equivalent to [list(X)], but is marked [%inline],
   so its definition is expanded (only one level deep, of course). *)

%inline ilist(X):
| (* empty *) {}
| list(X) X   {}

list(X):
| ilist(X)    {}

(* [rlist(X)] is right-recursive non-empty list. *)

rlist(X):
| X           {}
| X rlist(X)  {}

(* The kind of an identifier should not be determined when looking
   ahead, because the context may not be up to date. For this reason,
   when reading an identifier, the lexer emits two tokens: the first
   one (PRE_NAME) is eaten as a lookahead token, the second one is the
   actual identifier.
*)
(* For [var_name] we need more context on error reporting, so we use
   %inline. Not using %inline for typedef_name helps foctorizing many
   similar error messages. *)

typedef_name:
| PRE_NAME i = TYPEDEF_NAME
    { i }

%inline var_name:
| PRE_NAME i = VAR_NAME
    { i }

general_identifier:
| i = typedef_name
| i = var_name
    { i }

(* [other_identifier] is equivalent to [general_identifier], but adds
   an instruction that re-classifies this identifier as an [OtherId].
   Because this definition is marked %inline, the function call takes
   place when the host production is reduced. *)

%inline other_identifier:
  i = general_identifier
    { set_id_type i OtherId }

string_literals_list:
| STRING_LITERAL
| string_literals_list STRING_LITERAL
    {}

save_context:
  (* empty *) { !save_context () }

declare_varname(nt):
  i = nt { declare_varname (fst i); i }
declare_typename(nt):
  i = nt { declare_typename (fst i); i }

(* A note about phantom parameters. The definition of a non-terminal symbol
   [nt] is sometimes parameterized with a parameter that is unused in the
   right-hand side. This parameter disappears when macro-expansion takes
   place. Thus, the presence of this parameter does not influence the language
   that is accepted by the parser. Yet, it carries information about the
   context, since different call sites can supply different values of this
   parameter. This forces the creation of two (or more) identical copies of
   the definition of [nt], which leads to a larger automaton, where some
   states have been duplicated. In these states, more information about the
   context is available, which allows better syntax error messages to be
   given.

   By convention, a formal phantom parameter is named [phantom], so as to be
   easily recognizable. For clarity, we usually explicitly document which
   actual values it can take. *)

(* Actual grammar *)

primary_expression:
| var_name
| CONSTANT
| string_literals_list
| LPAREN expression RPAREN
    {}

postfix_expression:
| primary_expression
| postfix_expression LBRACK expression RBRACK
| postfix_expression LPAREN argument_expression_list? RPAREN
| BUILTIN_VA_ARG LPAREN assignment_expression COMMA type_name RPAREN
| BUILTIN_OFFSETOF LPAREN type_name COMMA other_identifier RPAREN
| BUILTIN_OFFSETOF LPAREN type_name COMMA other_identifier designator_list RPAREN
| postfix_expression DOT other_identifier
| postfix_expression PTR other_identifier
| postfix_expression INC
| postfix_expression DEC
| LPAREN type_name RPAREN LBRACE initializer_list COMMA? RBRACE
    {}

argument_expression_list:
| assignment_expression
| argument_expression_list COMMA assignment_expression
    {}

unary_expression:
| postfix_expression
| INC unary_expression
| DEC unary_expression
| unary_operator cast_expression
| SIZEOF unary_expression
| SIZEOF LPAREN type_name RPAREN
| ALIGNOF LPAREN type_name RPAREN
    {}

unary_operator:
| AND
| STAR
| PLUS
| MINUS
| TILDE
| BANG
    {}

cast_expression:
| unary_expression
| LPAREN type_name RPAREN cast_expression
    {}

multiplicative_operator:
  STAR | SLASH | PERCENT {}

multiplicative_expression:
| cast_expression
| multiplicative_expression multiplicative_operator cast_expression
    {}

additive_operator:
  PLUS | MINUS {}

additive_expression:
| multiplicative_expression
| additive_expression additive_operator multiplicative_expression
    {}

shift_operator:
  LEFT | RIGHT {}

shift_expression:
| additive_expression
| shift_expression shift_operator additive_expression
    {}

relational_operator:
  LT | GT | LEQ | GEQ {}

relational_expression:
| shift_expression
| relational_expression relational_operator shift_expression
    {}

equality_operator:
  EQEQ | NEQ {}

equality_expression:
| relational_expression
| equality_expression equality_operator relational_expression
    {}

and_expression:
| equality_expression
| and_expression AND equality_expression
    {}

exclusive_or_expression:
| and_expression
| exclusive_or_expression HAT and_expression
    {}

inclusive_or_expression:
| exclusive_or_expression
| inclusive_or_expression BAR exclusive_or_expression
    {}

logical_and_expression:
| inclusive_or_expression
| logical_and_expression ANDAND inclusive_or_expression
    {}

logical_or_expression:
| logical_and_expression
| logical_or_expression BARBAR logical_and_expression
    {}

conditional_expression:
| logical_or_expression
| logical_or_expression QUESTION expression COLON conditional_expression
    {}

assignment_expression:
| conditional_expression
| unary_expression assignment_operator assignment_expression
    {}

assignment_operator:
| EQ
| MUL_ASSIGN
| DIV_ASSIGN
| MOD_ASSIGN
| ADD_ASSIGN
| SUB_ASSIGN
| LEFT_ASSIGN
| RIGHT_ASSIGN
| AND_ASSIGN
| XOR_ASSIGN
| OR_ASSIGN
    {}

expression:
| assignment_expression
| expression COMMA assignment_expression
    {}

%inline constant_expression:
| conditional_expression
    {}

(* We separate two kinds of declarations: the typedef declaration and
   the normal declarations. This makes possible to distinguish /in the
   grammar/ whether a declaration should add a typename or a varname
   in the context.  There is an other difference between
   [init_declarator_list] and [typedef_declarator_list]: the later
   cannot contain an initialization (this is an error to initialize a
   typedef). *)

(* The phantom parameter is either [block_item], which means we are
   definitely reading a declaration, or [external_declaration], which
   means we could also be reading the beginning of a function definition. *)
declaration(phantom):
| declaration_specifiers(declaration(phantom)) init_declarator_list?    SEMICOLON
| declaration_specifiers_typedef               typedef_declarator_list? SEMICOLON
    {}

init_declarator_list:
| init_declarator
| init_declarator_list COMMA init_declarator
    {}

init_declarator:
| declare_varname(declarator_noattrend) save_context attribute_specifier_list
| declare_varname(declarator_noattrend) save_context attribute_specifier_list EQ c_initializer
    {}

typedef_declarator_list:
| typedef_declarator
| typedef_declarator_list COMMA typedef_declarator
    {}

typedef_declarator:
| declare_typename(declarator)
    {}

storage_class_specifier_no_typedef:
| EXTERN
| STATIC
| AUTO
| REGISTER
    {}

(* [declaration_specifier_no_type] matches declaration specifiers
   that do not contain either "typedef" nor type specifiers. *)
%inline declaration_specifier_no_type:
| storage_class_specifier_no_typedef
| type_qualifier_noattr
| function_specifier
| attribute_specifier
    {}

(* [declaration_specifier_no_typedef_name] matches declaration
   specifiers that contain neither "typedef" nor a typedef name
   (i.e. type specifier declared using a previous "typedef
   keyword"). *)
declaration_specifier_no_typedef_name:
| storage_class_specifier_no_typedef
| type_qualifier
| function_specifier
| type_specifier_no_typedef_name
    {}

(* [declaration_specifiers] makes sure one type specifier is given, and,
   if a typedef_name is given, then no other type specifier is given.

   This is a weaker condition than 6.7.2 2. It is necessary to enforce
   this in the grammar to disambiguate the example in 6.7.7 6:

   typedef signed int t;
   struct tag {
     unsigned t:4;
     const t:5;
   };

   The first field is a named t, while the second is unnamed of type t.
*)
(* The phantom parameter is either [declaration(_)], which means that
   this is the beginning of a declaration or a function definition, or
   [parameter_declaration], which means that this is the beginning of a
   parameter declaration. *)
declaration_specifiers(phantom):
| ioption(rlist(declaration_specifier_no_type)) typedef_name                   declaration_specifier_no_type*
| ioption(rlist(declaration_specifier_no_type)) type_specifier_no_typedef_name declaration_specifier_no_typedef_name*
    {}

(* This matches declaration_specifiers that do contains once the
   "typedef" keyword. To avoid conflicts, we also encode the
   constraint described in the comment for [declaration_specifiers]. *)
declaration_specifiers_typedef:
| ioption(rlist(declaration_specifier_no_type)) TYPEDEF                        declaration_specifier_no_type*         typedef_name                   declaration_specifier_no_type*
| ioption(rlist(declaration_specifier_no_type)) typedef_name                   declaration_specifier_no_type*         TYPEDEF                        declaration_specifier_no_type*
| ioption(rlist(declaration_specifier_no_type)) TYPEDEF                        declaration_specifier_no_type*         type_specifier_no_typedef_name declaration_specifier_no_typedef_name*
| ioption(rlist(declaration_specifier_no_type)) type_specifier_no_typedef_name declaration_specifier_no_typedef_name* TYPEDEF                        declaration_specifier_no_typedef_name*
    {}

(* A type specifier which is not a typedef name. *)
type_specifier_no_typedef_name:
| VOID
| CHAR
| SHORT
| INT
| LONG
| FLOAT
| DOUBLE
| SIGNED
| UNSIGNED
| UNDERSCORE_BOOL
| struct_or_union_specifier
| enum_specifier
    {}

struct_or_union_specifier:
| struct_or_union attribute_specifier_list other_identifier? LBRACE struct_declaration_list RBRACE
| struct_or_union attribute_specifier_list other_identifier
    {}

struct_or_union:
| STRUCT
| UNION
    {}

struct_declaration_list:
| (* empty *)
| struct_declaration_list struct_declaration
    {}

struct_declaration:
| specifier_qualifier_list(struct_declaration) struct_declarator_list? SEMICOLON
    {}

(* As in the standard, except it also encodes the constraint described
   in the comment above [declaration_specifiers]. *)
(* The phantom parameter can be [struct_declaration] or [type_name]. *)
specifier_qualifier_list(phantom):
| ioption(type_qualifier_list) typedef_name                   type_qualifier_list?
| ioption(type_qualifier_list) type_specifier_no_typedef_name specifier_qualifier_no_typedef_name*
    {}

specifier_qualifier_no_typedef_name:
| type_specifier_no_typedef_name
| type_qualifier
    {}

struct_declarator_list:
| struct_declarator
| struct_declarator_list COMMA struct_declarator
    {}

struct_declarator:
| declarator
| declarator? COLON constant_expression
    {}

enum_specifier:
| ENUM attribute_specifier_list other_identifier? LBRACE enumerator_list COMMA? RBRACE
| ENUM attribute_specifier_list other_identifier
    {}

enumerator_list:
| declare_varname(enumerator)
| enumerator_list COMMA declare_varname(enumerator)
    {}

enumerator:
| i = enumeration_constant
| i = enumeration_constant EQ constant_expression
    { (i, ()) }

enumeration_constant:
| i = general_identifier
    { set_id_type i VarId; i }

type_qualifier_noattr:
| CONST
| RESTRICT
| VOLATILE
    {}

%inline type_qualifier:
| type_qualifier_noattr
| attribute_specifier
    {}

attribute_specifier_list:
| /* empty */
| attribute_specifier attribute_specifier_list
    {}

attribute_specifier:
| ATTRIBUTE LPAREN LPAREN gcc_attribute_list RPAREN RPAREN
| PACKED LPAREN argument_expression_list RPAREN
| ALIGNAS LPAREN argument_expression_list RPAREN
| ALIGNAS LPAREN type_name RPAREN
    {}

gcc_attribute_list:
| gcc_attribute
| gcc_attribute_list COMMA gcc_attribute
    {}

gcc_attribute:
| /* empty */
| gcc_attribute_word
| gcc_attribute_word LPAREN argument_expression_list? RPAREN
    {}
| gcc_attribute_word LPAREN i = typedef_name COMMA argument_expression_list RPAREN
    (* This is to emulate GCC's attribute syntax : we make this identifier
       a var name identifier, so that the parser will see it as a variable
       reference *)
    { set_id_type i VarId }

gcc_attribute_word:
| other_identifier
| CONST
| PACKED
    {}

function_specifier:
| INLINE
| NORETURN
    {}

(* We add this non-terminal here to force the resolution of the
   conflict at the point of shifting the TYPEDEF_NAME. If we had
   already shifted it, a reduce/reduce conflict appears, and menhir is
   not able to solve them.

   The conflict in question is when parsing :
     int f(int (t
   With lookahead ')', in a context where 't' is a type name.
   In this case, we are able to reduce the two productions:
     (1) "declarator_identifier -> PRE_NAME TYPEDEF_NAME"
           followed by "direct_declarator -> declarator_identifier"
       meaning that 't' is the parameter of function 'f'
     (2) "list(declaration_specifier_no_type) -> "
           followed by "list(declaration_specifier_no_type) -> PRE_NAME TYPEDEF_NAME list(declaration_specifier_no_type)"
           followed by "declaration_specifiers(...) -> ..."
           followed by "parameter_declaration -> ..."
       meaning that 't' is the type of the parameter of a function
       passed as parameter to 'f'

  By adding this non-terminal at this point, we force this conflict to
  be solved earlier: once we have seen "f(int (", followed by PRE_NAME
  and with TYPEDEF_NAME in lookahead position, we know (1) can safely
  be ignored (if (1) is still possible after reading the next token,
  (2) will also be possible, and the conflict has to be solved in
  favor of (2)). We add low_prec in declaration_identifier, but not in
  typedef_name, so that it has to be reduced in (1) but not in (2).
  This is a shift/reduce conflict that can be solved using
  precedences.
 *)
low_prec : %prec lowPrec1 {}
declarator_identifier:
| PRE_NAME low_prec i = TYPEDEF_NAME
| i = var_name
    { i }

(* The semantic action returned by [declarator] is a pair of the
   identifier being defined and a value containing the context stack
   that has to be restored if entering the body of the function being
   defined, if so. *)
declarator:
| x = declarator_noattrend attribute_specifier_list
    { x }

declarator_noattrend:
| x = direct_declarator
    { x }
| pointer x = direct_declarator
    { match snd x with
      | Decl_ident -> (fst x, Decl_other)
      | _ -> x }

direct_declarator:
| i = declarator_identifier
    { set_id_type i VarId; (i, Decl_ident) }
| LPAREN save_context x = declarator RPAREN
    { x }
| x = direct_declarator LBRACK type_qualifier_list? optional(assignment_expression, RBRACK)
    { match snd x with
      | Decl_ident -> (fst x, Decl_other)
      | _ -> x }
| x = direct_declarator LPAREN ctx = context_parameter_type_list RPAREN
    { match snd x with
      | Decl_ident -> (fst x, Decl_fun ctx)
      | _ -> x }
| x = direct_declarator LPAREN save_context il=identifier_list? RPAREN
    { match snd x, il with
      | Decl_ident, Some il -> (fst x, Decl_krfun il)
      | Decl_ident, None -> (fst x, Decl_krfun [])
      | _ -> x }

(* The C standard defines [pointer] as a right-recursive list. We prefer to
   define it as a left-recursive list, because this provides better static
   context (that is, this changes the automaton in such a way that it is
   easier to give good error messages, in at least 2 states).

   The non-terminal symbol [pointer1] represents one list element.

   [pointer], which represents a non-empty list of [pointer1]'s, is defined
   as [pointer1* pointer1].

   When the C standard writes [pointer?], which represents a possibly empty
   list of [pointer1]'s, we write [pointer1*]. *)

%inline pointer1:
  STAR type_qualifier_list?
    {}

%inline pointer:
  pointer1* pointer1
    {}

type_qualifier_list:
| type_qualifier_list? type_qualifier
    {}

context_parameter_type_list:
| ctx1 = save_context parameter_type_list ctx2 = save_context
    { ctx1 (); ctx2 }

parameter_type_list:
| parameter_list
| parameter_list COMMA ELLIPSIS
    {}

parameter_list:
| parameter_declaration
| parameter_list COMMA parameter_declaration
    {}

parameter_declaration:
| declaration_specifiers(parameter_declaration) declare_varname(declarator)
| declaration_specifiers(parameter_declaration) abstract_declarator(parameter_declaration)?
    {}

type_name:
| specifier_qualifier_list(type_name) abstract_declarator(type_name)?
    {}

(* The phantom parameter can be [parameter_declaration] or [type_name].
   We take the latter to mean [type_or_name] or [direct_abstract_declarator].
   We need not distinguish these two cases: in both cases, a closing parenthesis
   is permitted (and we do not wish to keep track of why it is permitted). *)
abstract_declarator(phantom):
| pointer
| ioption(pointer) direct_abstract_declarator
    {}

direct_abstract_declarator:
| LPAREN save_context abstract_declarator(type_name) RPAREN
| direct_abstract_declarator? LBRACK type_qualifier_list? optional(assignment_expression, RBRACK)
| ioption(direct_abstract_declarator) LPAREN context_parameter_type_list? RPAREN
    {}

c_initializer:
| assignment_expression
| LBRACE initializer_list COMMA? RBRACE
    {}

initializer_list:
| designation? c_initializer
| initializer_list COMMA designation? c_initializer
    {}

designation:
| designator_list EQ
    {}

designator_list:
| designator_list? designator
    {}

designator:
| LBRACK constant_expression RBRACK
| DOT other_identifier
    {}

statement:
| labeled_statement
| compound_statement
| expression_statement
| selection_statement
| iteration_statement
| jump_statement
| asm_statement
    {}

labeled_statement:
| other_identifier COLON statement
| CASE constant_expression COLON statement
| DEFAULT COLON statement
    {}

compound_statement:
| ctx = save_context LBRACE block_item_list? RBRACE
    { ctx() }

block_item_list:
| block_item_list? block_item
    {}

block_item:
| declaration(block_item)
| statement
| PRAGMA
    {}

expression_statement:
| expression? SEMICOLON
    {}

jump_statement:
| GOTO other_identifier SEMICOLON
| CONTINUE SEMICOLON
| BREAK SEMICOLON
| RETURN expression? SEMICOLON
    {}

asm_statement:
| ASM asm_attributes LPAREN string_literals_list asm_arguments RPAREN SEMICOLON
    {}

ifelse_statement1:
| IF LPAREN expression RPAREN ctx = save_context statement ELSE
    { ctx() }

selection_statement:
| ctx = save_context ifelse_statement1 statement
| ctx = save_context IF LPAREN expression RPAREN save_context statement %prec lowPrec2
| ctx = save_context SWITCH LPAREN expression RPAREN statement
    { ctx() }

do_statement1:
| ctx = save_context DO statement
    { ctx () }

iteration_statement:
| ctx = save_context WHILE LPAREN expression RPAREN statement
| ctx = save_context do_statement1 WHILE LPAREN expression RPAREN SEMICOLON
| ctx = save_context FOR LPAREN for_statement_header optional(expression, SEMICOLON) optional(expression, RPAREN) statement
    { ctx() }

for_statement_header:
| optional(expression, SEMICOLON)
| declaration(block_item)
    {}

asm_attributes:
| /* empty */
| CONST asm_attributes
| VOLATILE asm_attributes
    {}

asm_arguments:
| /* empty */
| COLON asm_operands
| COLON asm_operands COLON asm_operands
| COLON asm_operands COLON asm_operands COLON asm_flags
    {}

asm_operands:
| /* empty */
| asm_operands_ne
    {}

asm_operands_ne:
| asm_operands_ne COMMA asm_operand
| asm_operand
    {}

asm_operand:
| asm_op_name string_literals_list LPAREN expression RPAREN
    {}

asm_op_name:
| /*empty*/
| LBRACK other_identifier RBRACK
    {}

asm_flags:
| string_literals_list
| asm_flags COMMA string_literals_list
    {}

translation_unit_file:
| translation_item* EOF
    {}

translation_item:
| external_declaration
| SEMICOLON
    {}

%inline external_declaration:
| function_definition
| declaration(external_declaration)
| PRAGMA
    {}

identifier_list:
| x = var_name
    { [x] }
| l = identifier_list COMMA x = var_name
    { x::l }

kr_param_declaration:
| declaration_specifiers(declaration(block_item)) init_declarator_list? SEMICOLON
    {}

declaration_list:
| kr_param_declaration
| declaration_list kr_param_declaration
    {}

function_definition1:
| declaration_specifiers(declaration(external_declaration))
    func = declare_varname(declarator_noattrend)
    save_context attribute_specifier_list ctx = save_context
| declaration_specifiers(declaration(external_declaration))
    func = declare_varname(declarator_noattrend)
    ctx = save_context declaration_list
    { begin match snd func with
      | Decl_fun ctx -> ctx (); declare_varname (fst func)
      | Decl_krfun il -> List.iter declare_varname il
      | _ -> ()
      end;
      ctx }

function_definition:
| ctx = function_definition1 compound_statement
    { ctx () }
