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
  open Pre_parser_aux

  let set_id_type (_,r,_) t =
    r := t

  let declare_varname (i,_,_) =
    !declare_varname i

  let declare_typename (i,_,_) =
    !declare_typename i

  let syntax_error pos =
    Cerrors.fatal_error "%s:%d: syntax error"
        pos.Lexing.pos_fname pos.Lexing.pos_lnum

  let unclosed opening closing pos1 pos2 =
    Cerrors.info "%s:%d: syntax error: expecting '%s'"
        pos2.Lexing.pos_fname pos2.Lexing.pos_lnum closing;
    Cerrors.fatal_error "%s:%d: this is the location of the unclosed '%s'"
        pos1.Lexing.pos_fname pos1.Lexing.pos_lnum opening

%}

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
  AUTO REGISTER INLINE CHAR SHORT INT LONG SIGNED UNSIGNED FLOAT DOUBLE
  UNDERSCORE_BOOL CONST VOLATILE VOID STRUCT UNION ENUM CASE DEFAULT IF ELSE
  SWITCH WHILE DO FOR GOTO CONTINUE BREAK RETURN BUILTIN_VA_ARG ALIGNOF
  ATTRIBUTE ALIGNAS PACKED ASM

%token EOF

(* These precedences declarations solve the conflict in the following declaration :

   int f(int (a));

   when a is a TYPEDEF_NAME. It is specified by 6.7.5.3 11.

   WARNING: These precedence declarations tend to silently solve other
   conflicts. So, if you change the grammar (especially or
   statements), you should check that without these declarations, it
   has ONLY ONE CONFLICT.
*)
%nonassoc TYPEDEF_NAME
%nonassoc highPrec

%start<unit> translation_unit_file
%%

(* Helpers *)

%inline option(X):
| /* nothing */
    { None }
| x = X
    { Some x }

%inline fst(X):
| x = X
    { fst x }

general_identifier:
| i = VAR_NAME
| i = TYPEDEF_NAME
    { i }

string_literals_list:
| STRING_LITERAL
| string_literals_list STRING_LITERAL
    {}

(* WARNING : because of the lookahead token, the context might be
   opened or closed one token after the position of this non-terminal !

   Opening too late is not dangerous for us, because this does not
   change the token stream. However, we have to make sure the
   lookahead token present just after closing/declaring/restoring is
   not an identifier. An easy way to check that is to look at the
   follow set of the non-terminal in question. The follow sets are
   given by menhir with option -lg 3. *)

%inline nop: (* empty *) { }

open_context:
  (* empty *)%prec highPrec { !open_context () }
close_context:
  (* empty *) { !close_context () }
in_context(nt):
  open_context x = nt close_context { x }

save_contexts_stk:
  (* empty *) { !save_contexts_stk () }

declare_varname(nt):
  i = nt { declare_varname i; i }
declare_typename(nt):
  i = nt { declare_typename i; i }

(* Actual grammar *)

primary_expression:
| i = VAR_NAME
    { set_id_type i VarId }
| CONSTANT
| string_literals_list
| LPAREN expression RPAREN
    {}
| LPAREN expression error
    { unclosed "(" ")" $startpos($1) $endpos }

postfix_expression:
| primary_expression
| postfix_expression LBRACK expression RBRACK
| postfix_expression LPAREN argument_expression_list? RPAREN
    {}
| postfix_expression LPAREN argument_expression_list? error
    { unclosed "(" ")" $startpos($2) $endpos }
| BUILTIN_VA_ARG LPAREN assignment_expression COMMA type_name RPAREN
    {}
| BUILTIN_VA_ARG LPAREN assignment_expression COMMA type_name error
    { unclosed "(" ")" $startpos($2) $endpos }
| postfix_expression DOT i = general_identifier
| postfix_expression PTR i = general_identifier
    { set_id_type i OtherId }
| postfix_expression INC
| postfix_expression DEC
| LPAREN type_name RPAREN LBRACE initializer_list COMMA? RBRACE
    {}
| LPAREN type_name error
    { unclosed "(" ")" $startpos($1) $endpos }
| LPAREN type_name RPAREN LBRACE initializer_list COMMA? error
    { unclosed "{" "}" $startpos($4) $endpos }

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
| ALIGNOF unary_expression
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

multiplicative_expression:
| cast_expression
| multiplicative_expression STAR cast_expression
| multiplicative_expression SLASH cast_expression
| multiplicative_expression PERCENT cast_expression
    {}

additive_expression:
| multiplicative_expression
| additive_expression PLUS multiplicative_expression
| additive_expression MINUS multiplicative_expression
    {}

shift_expression:
| additive_expression
| shift_expression LEFT additive_expression
| shift_expression RIGHT additive_expression
    {}

relational_expression:
| shift_expression
| relational_expression LT shift_expression
| relational_expression GT shift_expression
| relational_expression LEQ shift_expression
| relational_expression GEQ shift_expression
    {}

equality_expression:
| relational_expression
| equality_expression EQEQ relational_expression
| equality_expression NEQ relational_expression
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

constant_expression:
| conditional_expression
    {}

(* We separate two kinds of declarations: the typedef declaration and
   the normal declarations. This makes possible to distinguish /in the
   grammar/ whether a declaration should add a typename or a varname
   in the context.  There is an other difference between
   [init_declarator_list] and [typedef_declarator_list]: the later
   cannot contain an initialization (this is an error to initialize a
   typedef). *)

declaration:
| declaration_specifiers         init_declarator_list?    SEMICOLON
    {}
| declaration_specifiers_typedef typedef_declarator_list? SEMICOLON
    {}

init_declarator_list:
| init_declarator
| init_declarator_list COMMA init_declarator
    {}

init_declarator:
| declare_varname(fst(declarator))
| declare_varname(fst(declarator)) EQ c_initializer
    { }

typedef_declarator_list:
| typedef_declarator
| typedef_declarator_list COMMA typedef_declarator
    {}

typedef_declarator:
| declare_typename(fst(declarator))
    { }

storage_class_specifier_no_typedef:
| EXTERN
| STATIC
| AUTO
| REGISTER
    {}

(* [declaration_specifiers_no_type] matches declaration specifiers
   that do not contain either "typedef" nor type specifiers. *)
declaration_specifiers_no_type:
| storage_class_specifier_no_typedef declaration_specifiers_no_type?
| type_qualifier                     declaration_specifiers_no_type?
| function_specifier                 declaration_specifiers_no_type?
    {}

(* [declaration_specifiers_no_typedef_name] matches declaration
   specifiers that contain neither "typedef" nor a typedef name
   (i.e. type specifier declared using a previous "typedef
   keyword"). *)
declaration_specifiers_no_typedef_name:
| storage_class_specifier_no_typedef declaration_specifiers_no_typedef_name?
| type_qualifier                     declaration_specifiers_no_typedef_name?
| function_specifier                 declaration_specifiers_no_typedef_name?
| type_specifier_no_typedef_name     declaration_specifiers_no_typedef_name?
    {}

(* [declaration_specifiers_no_type] matches declaration_specifiers
   that do not contains "typedef". Moreover, it makes sure that it
   contains either one typename and not other type specifier or no
   typename.

   This is a weaker condition than 6.7.2 2. It is necessary to enforce
   this in the grammar to disambiguate the example in 6.7.7 6:

   typedef signed int t;
   struct tag {
     unsigned t:4;
     const t:5;
   };

   The first field is a named t, while the second is unnamed of type t.
*)
declaration_specifiers:
| declaration_specifiers_no_type? i = TYPEDEF_NAME               declaration_specifiers_no_type?
    { set_id_type i TypedefId }
| declaration_specifiers_no_type? type_specifier_no_typedef_name declaration_specifiers_no_typedef_name?
    {}

(* This matches declaration_specifiers that do contains once the
   "typedef" keyword. To avoid conflicts, we also encode the
   constraint described in the comment for [declaration_specifiers]. *)
declaration_specifiers_typedef:
| declaration_specifiers_no_type? TYPEDEF                        declaration_specifiers_no_type?         i = TYPEDEF_NAME               declaration_specifiers_no_type?
| declaration_specifiers_no_type? i = TYPEDEF_NAME               declaration_specifiers_no_type?         TYPEDEF                        declaration_specifiers_no_type?
    { set_id_type i TypedefId }
| declaration_specifiers_no_type? TYPEDEF                        declaration_specifiers_no_type?         type_specifier_no_typedef_name declaration_specifiers_no_typedef_name?
| declaration_specifiers_no_type? type_specifier_no_typedef_name declaration_specifiers_no_typedef_name? TYPEDEF                        declaration_specifiers_no_typedef_name?
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
| struct_or_union attribute_specifier_list LBRACE struct_declaration_list RBRACE
    {}
| struct_or_union attribute_specifier_list i = general_identifier LBRACE struct_declaration_list RBRACE
| struct_or_union attribute_specifier_list i = general_identifier
    { set_id_type i OtherId }
| struct_or_union attribute_specifier_list LBRACE struct_declaration_list error
    { unclosed "{" "}" $startpos($3) $endpos }
| struct_or_union attribute_specifier_list general_identifier LBRACE struct_declaration_list error
    { unclosed "{" "}" $startpos($4) $endpos }

struct_or_union:
| STRUCT
| UNION
    {}

struct_declaration_list:
| (* empty *)
| struct_declaration_list struct_declaration
    {}

struct_declaration:
| specifier_qualifier_list struct_declarator_list? SEMICOLON
    {}

(* As in the standard, except it also encodes the constraint described
   in the comment above [declaration_specifiers]. *)
specifier_qualifier_list:
| type_qualifier_list? i = TYPEDEF_NAME               type_qualifier_list?
    { set_id_type i TypedefId }
| type_qualifier_list? type_specifier_no_typedef_name specifier_qualifier_list_no_typedef_name?
    {}

specifier_qualifier_list_no_typedef_name:
| type_specifier_no_typedef_name specifier_qualifier_list_no_typedef_name?
| type_qualifier                 specifier_qualifier_list_no_typedef_name?
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
| ENUM attribute_specifier_list LBRACE enumerator_list COMMA? RBRACE
    {}
| ENUM attribute_specifier_list i = general_identifier LBRACE enumerator_list COMMA? RBRACE
| ENUM attribute_specifier_list i = general_identifier
    { set_id_type i OtherId }
| ENUM attribute_specifier_list LBRACE enumerator_list COMMA? error
    { unclosed "{" "}" $startpos($3) $endpos }
| ENUM attribute_specifier_list general_identifier LBRACE enumerator_list COMMA? error
    { unclosed "{" "}" $startpos($4) $endpos }

enumerator_list:
| declare_varname(enumerator)
| enumerator_list COMMA declare_varname(enumerator)
    {}

enumerator:
| i = enumeration_constant
| i = enumeration_constant EQ constant_expression
    { i }

enumeration_constant:
| i = general_identifier
    { set_id_type i VarId; i }

type_qualifier:
| CONST
| RESTRICT
| VOLATILE
| attribute_specifier
    {}

attribute_specifier_list:
| /* empty */
| attribute_specifier_list attribute_specifier
    {}

attribute_specifier:
| ATTRIBUTE LPAREN LPAREN gcc_attribute_list RPAREN RPAREN
| PACKED LPAREN argument_expression_list RPAREN
(* TODO: slove conflict *)
(* | PACKED *)
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
| gcc_attribute_word LPAREN i = TYPEDEF_NAME COMMA argument_expression_list RPAREN
    (* This is to emulate GCC's attribute syntax : we make this identifier
       a var name identifier, so that the parser will see it as a variable
       reference *)
    { set_id_type i VarId }

gcc_attribute_word:
| i = general_identifier
    { set_id_type i OtherId }
| CONST
| PACKED
    {}

function_specifier:
| INLINE
    {}

(* The semantic action returned by [declarator] is a pair of the
   identifier being defined and an option of the context stack that
   has to be restored if entering the body of the function being
   defined, if so. *)
declarator:
| pointer? x = direct_declarator attribute_specifier_list
    { x }

direct_declarator:
| i = general_identifier
    { set_id_type i VarId; (i, None) }
| LPAREN x = declarator RPAREN
| x = direct_declarator LBRACK type_qualifier_list? assignment_expression? RBRACK
    { x }
| x = direct_declarator LPAREN
    open_context parameter_type_list? restore_fun = save_contexts_stk
    close_context RPAREN
    { match snd x with
      | None -> (fst x, Some restore_fun)
      | Some _ -> x }

pointer:
| STAR type_qualifier_list?
| STAR type_qualifier_list? pointer
    {}

type_qualifier_list:
| type_qualifier_list? type_qualifier
    {}

parameter_type_list:
| l=parameter_list
| l=parameter_list COMMA ELLIPSIS
    { l }

parameter_list:
| i=parameter_declaration
    { [i] }
| l=parameter_list COMMA i=parameter_declaration
    { i::l }

parameter_declaration:
| declaration_specifiers id=declare_varname(fst(declarator))
    { Some id }
| declaration_specifiers abstract_declarator?
    { None }

type_name:
| specifier_qualifier_list abstract_declarator?
    {}

abstract_declarator:
| pointer
| pointer? direct_abstract_declarator
    {}

direct_abstract_declarator:
| LPAREN abstract_declarator RPAREN
| direct_abstract_declarator? LBRACK type_qualifier_list? assignment_expression? RBRACK
| direct_abstract_declarator? LPAREN in_context(parameter_type_list?) RPAREN
    {}

c_initializer:
| assignment_expression
| LBRACE initializer_list COMMA? RBRACE
    {}
| LBRACE initializer_list COMMA? error
    { unclosed "{" "}" $startpos($1) $endpos }

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
    {}
| DOT i = general_identifier
    { set_id_type i OtherId }

(* The grammar of statements is replicated three times.

   [statement_finish_close] should close the current context just
   before its last token.

   [statement_finish_noclose] should not close the current context. It
   should modify it only if this modification actually changes the
   context of the current block.

   [statement_intern_close] is like [statement_finish_close], except
   it cannot reduce to a single-branch if statement.
*)

statement_finish_close:
| labeled_statement(statement_finish_close)
| compound_statement(nop)
| expression_statement(close_context)
| selection_statement_finish(nop)
| iteration_statement(nop,statement_finish_close)
| jump_statement(close_context)
| asm_statement(close_context)
    {}

statement_finish_noclose:
| labeled_statement(statement_finish_noclose)
| compound_statement(open_context)
| expression_statement(nop)
| selection_statement_finish(open_context)
| iteration_statement(open_context,statement_finish_close)
| jump_statement(nop)
| asm_statement(nop)
    {}

statement_intern_close:
| labeled_statement(statement_intern_close)
| compound_statement(nop)
| expression_statement(close_context)
| selection_statement_intern_close
| iteration_statement(nop,statement_intern_close)
| jump_statement(close_context)
| asm_statement(close_context)
    {}

(* [labeled_statement(last_statement)] has the same effect on contexts
   as [last_statement]. *)
labeled_statement(last_statement):
| i = general_identifier COLON last_statement
    { set_id_type i OtherId }
| CASE constant_expression COLON last_statement
| DEFAULT COLON last_statement
    {}

(* [compound_statement] uses a local context and closes it before its
   last token. It uses [openc] to open this local context if needed.
   That is, if a local context has already been opened, [openc] = [nop],
   otherwise, [openc] = [open_context]. *)
compound_statement(openc):
| LBRACE openc block_item_list? close_context RBRACE
    {}
| LBRACE openc block_item_list? close_context error
    { unclosed "{" "}" $startpos($1) $endpos }

block_item_list:
| block_item_list? block_item
    {}

block_item:
| declaration
| statement_finish_noclose
| PRAGMA
    {}

(* [expression_statement], [jump_statement] and [asm_statement] close
   the local context if needed, depending of the close parameter. If
   there is no local context, [close] = [nop]. Otherwise,
   [close] = [close_context]. *)
expression_statement(close):
| expression? close SEMICOLON
    {}

jump_statement(close):
| GOTO i = general_identifier close SEMICOLON
    { set_id_type i OtherId }
| CONTINUE close SEMICOLON
| BREAK close SEMICOLON
| RETURN expression? close SEMICOLON
    {}

asm_statement(close):
| ASM asm_attributes LPAREN string_literals_list asm_arguments RPAREN close SEMICOLON
    {}

(* [selection_statement_finish] and [selection_statement_intern] use a
   local context and close it before their last token.

   [selection_statement_finish(openc)] uses [openc] to open this local
   context if needed. That is, if a local context has already been
   opened, [openc] = [nop], otherwise, [openc] = [open_context].

   [selection_statement_intern_close] is always called with a local
   context openned. It closes it before its last token.  *)

(* It should be noted that the token [ELSE] should be lookaheaded
   /outside/ of the local context because if the lookaheaded token is
   not [ELSE], then this is the end of the statement.

   This is especially important to parse correctly the following
   example:

     typedef int a;

     int f() {
       for(int a; ;)
         if(1);
       a * x;
     }

   However, if the lookahead token is [ELSE], we should parse the
   second branch in the same context as the first branch, so we have
   to reopen the previously closed context. This is the reason for the
   save/restore system.
*)

if_else_statement_begin(openc):
| IF openc LPAREN expression RPAREN restore_fun = save_contexts_stk
  statement_intern_close
    { restore_fun () }

selection_statement_finish(openc):
| IF openc LPAREN expression RPAREN save_contexts_stk statement_finish_close
| if_else_statement_begin(openc) ELSE statement_finish_close
| SWITCH openc LPAREN expression RPAREN statement_finish_close
    {}

selection_statement_intern_close:
| if_else_statement_begin(nop) ELSE statement_intern_close
| SWITCH LPAREN expression RPAREN statement_intern_close
    {}

(* [iteration_statement] uses a local context and closes it before
   their last token.

   [iteration_statement] uses [openc] to open this local context if
   needed. That is, if a local context has already been opened,
   [openc] = [nop], otherwise, [openc] = [open_context].

   [last_statement] is either [statement_intern_close] or
   [statement_finish_close]. That is, it should /always/ close the
   local context. *)

iteration_statement(openc,last_statement):
| WHILE openc LPAREN expression RPAREN last_statement
| DO open_context statement_finish_close WHILE
    openc LPAREN expression RPAREN close_context SEMICOLON
| FOR openc LPAREN expression? SEMICOLON expression? SEMICOLON expression? RPAREN last_statement
| FOR openc LPAREN declaration expression? SEMICOLON expression? RPAREN last_statement
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
| /*empty*/                             {}
| LBRACK i = general_identifier RBRACK  { set_id_type i OtherId }

asm_flags:
| string_literals_list
| string_literals_list COMMA asm_flags
    {}

translation_unit_file:
| translation_unit EOF
| EOF
    {}
| error
    { syntax_error $endpos }

translation_unit:
| external_declaration
| translation_unit external_declaration
| translation_unit SEMICOLON
| SEMICOLON
    {}

external_declaration:
| function_definition
| declaration
| PRAGMA
    {}

function_definition_begin:
| declaration_specifiers pointer? x=direct_declarator
    { match x with
      | (_, None) -> $syntaxerror
      | (i, Some restore_fun) -> restore_fun ()
    }
| declaration_specifiers pointer? x=direct_declarator
  LPAREN params=identifier_list RPAREN open_context declaration_list
    { match x with
      | (_, Some _) -> $syntaxerror
      | (i, None) ->
	declare_varname i;
	List.iter declare_varname params
    }

identifier_list:
| id = VAR_NAME
    { [id] }
| idl = identifier_list COMMA id = VAR_NAME
    { id :: idl }

declaration_list:
| /*empty*/
    { }
| declaration_list declaration
    { }

function_definition:
| function_definition_begin LBRACE block_item_list? close_context RBRACE
    { }
| function_definition_begin LBRACE block_item_list? close_context error
    { unclosed "{" "}" $startpos($2) $endpos }
