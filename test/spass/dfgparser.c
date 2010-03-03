/* A Bison parser, made from dfgparser.y, by GNU bison 1.75.  */

/* Skeleton parser for Yacc-like parsing with Bison,
   Copyright (C) 1984, 1989, 1990, 2000, 2001, 2002 Free Software Foundation, Inc.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2, or (at your option)
   any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place - Suite 330,
   Boston, MA 02111-1307, USA.  */

/* As a special exception, when this file is copied by Bison into a
   Bison output file, you may use that output file without restriction.
   This special exception was added by the Free Software Foundation
   in version 1.24 of Bison.  */

/* Written by Richard Stallman by simplifying the original so called
   ``semantic'' parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON	1

/* Pure parsers.  */
#define YYPURE	0

/* Using locations.  */
#define YYLSP_NEEDED 0

/* If NAME_PREFIX is specified substitute the variables and functions
   names.  */
#define yyparse dfg_parse
#define yylex   dfg_lex
#define yyerror dfg_error
#define yylval  dfg_lval
#define yychar  dfg_char
#define yydebug dfg_debug
#define yynerrs dfg_nerrs


/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
     DFG_AND = 258,
     DFG_AUTHOR = 259,
     DFG_AXIOMS = 260,
     DFG_BEGPROB = 261,
     DFG_BY = 262,
     DFG_CLAUSE = 263,
     DFG_CLOSEBRACE = 264,
     DFG_CLSLIST = 265,
     DFG_CNF = 266,
     DFG_CONJECS = 267,
     DFG_DATE = 268,
     DFG_DECLLIST = 269,
     DFG_DESC = 270,
     DFG_DESCLIST = 271,
     DFG_DNF = 272,
     DFG_DOMPRED = 273,
     DFG_ENDLIST = 274,
     DFG_ENDPROB = 275,
     DFG_EQUAL = 276,
     DFG_EQUIV = 277,
     DFG_EXISTS = 278,
     DFG_FALSE = 279,
     DFG_FORMLIST = 280,
     DFG_FORMULA = 281,
     DFG_FORALL = 282,
     DFG_FREELY = 283,
     DFG_FUNC = 284,
     DFG_GENERATED = 285,
     DFG_GENSET = 286,
     DFG_HYPOTH = 287,
     DFG_IMPLIED = 288,
     DFG_IMPLIES = 289,
     DFG_LOGIC = 290,
     DFG_NAME = 291,
     DFG_NOT = 292,
     DFG_OPENBRACE = 293,
     DFG_OPERAT = 294,
     DFG_OR = 295,
     DFG_PREC = 296,
     DFG_PRED = 297,
     DFG_PRDICAT = 298,
     DFG_PRFLIST = 299,
     DFG_QUANTIF = 300,
     DFG_SATIS = 301,
     DFG_SETFLAG = 302,
     DFG_SETTINGS = 303,
     DFG_SYMLIST = 304,
     DFG_SORT = 305,
     DFG_SORTS = 306,
     DFG_STATUS = 307,
     DFG_STEP = 308,
     DFG_SUBSORT = 309,
     DFG_TERMLIST = 310,
     DFG_TRUE = 311,
     DFG_UNKNOWN = 312,
     DFG_UNSATIS = 313,
     DFG_VERSION = 314,
     DFG_NUM = 315,
     DFG_MINUS1 = 316,
     DFG_ID = 317,
     DFG_TEXT = 318
   };
#endif
#define DFG_AND 258
#define DFG_AUTHOR 259
#define DFG_AXIOMS 260
#define DFG_BEGPROB 261
#define DFG_BY 262
#define DFG_CLAUSE 263
#define DFG_CLOSEBRACE 264
#define DFG_CLSLIST 265
#define DFG_CNF 266
#define DFG_CONJECS 267
#define DFG_DATE 268
#define DFG_DECLLIST 269
#define DFG_DESC 270
#define DFG_DESCLIST 271
#define DFG_DNF 272
#define DFG_DOMPRED 273
#define DFG_ENDLIST 274
#define DFG_ENDPROB 275
#define DFG_EQUAL 276
#define DFG_EQUIV 277
#define DFG_EXISTS 278
#define DFG_FALSE 279
#define DFG_FORMLIST 280
#define DFG_FORMULA 281
#define DFG_FORALL 282
#define DFG_FREELY 283
#define DFG_FUNC 284
#define DFG_GENERATED 285
#define DFG_GENSET 286
#define DFG_HYPOTH 287
#define DFG_IMPLIED 288
#define DFG_IMPLIES 289
#define DFG_LOGIC 290
#define DFG_NAME 291
#define DFG_NOT 292
#define DFG_OPENBRACE 293
#define DFG_OPERAT 294
#define DFG_OR 295
#define DFG_PREC 296
#define DFG_PRED 297
#define DFG_PRDICAT 298
#define DFG_PRFLIST 299
#define DFG_QUANTIF 300
#define DFG_SATIS 301
#define DFG_SETFLAG 302
#define DFG_SETTINGS 303
#define DFG_SYMLIST 304
#define DFG_SORT 305
#define DFG_SORTS 306
#define DFG_STATUS 307
#define DFG_STEP 308
#define DFG_SUBSORT 309
#define DFG_TERMLIST 310
#define DFG_TRUE 311
#define DFG_UNKNOWN 312
#define DFG_UNSATIS 313
#define DFG_VERSION 314
#define DFG_NUM 315
#define DFG_MINUS1 316
#define DFG_ID 317
#define DFG_TEXT 318




/* Copy the first part of user declarations.  */
#line 48 "dfgparser.y"


#include <ctype.h>
#include "dfg.h"
#include "symbol.h"
#include "term.h"
#include "foldfg.h"
#include "stringsx.h"

/* Used for the texts from description section. */
typedef struct {
  char*     name;
  char*     author;
  char*     version;
  char*     logic;
  DFG_STATE status;
  char*     description;
  char*     date;
} DFG_DESCRIPTIONTYPE;

static DFG_DESCRIPTIONTYPE dfg_DESC;
static LIST                dfg_AXIOMLIST;
static LIST                dfg_CONJECLIST;
static LIST                dfg_SORTDECLLIST;
/* symbol precedence explicitly defined by user */
static LIST                dfg_USERPRECEDENCE;
static LIST                dfg_AXCLAUSES;
static LIST                dfg_CONCLAUSES;
static LIST                dfg_PROOFLIST;     /* list_of_proofs */
static LIST                dfg_TERMLIST;      /* list_of_terms  */
static BOOL                dfg_IGNORE;      /* tokens are ignored while TRUE */
static FLAGSTORE           dfg_FLAGS;
static PRECEDENCE          dfg_PRECEDENCE;

/* used also in the scanner */
NAT                        dfg_LINENUMBER;
BOOL			   dfg_IGNORETEXT;

void yyerror(const char*);
int  yylex(void);		/* Defined in dfgscanner.l */

static void   dfg_SymbolDecl(int, char*, int);
static SYMBOL dfg_Symbol(char*, NAT);
static void   dfg_SubSort(char*, char*);
static void   dfg_SymbolGenerated(SYMBOL, BOOL, LIST);

static __inline__ TERM dfg_TermCreate(char* Name, LIST Arguments)
/* Look up the symbol, check its arity and create the term */
{
  SYMBOL s;
  NAT    arity;
  arity = list_Length(Arguments);
  s = dfg_Symbol(Name, arity); /* Frees the string */
  if (!symbol_IsVariable(s) && !symbol_IsFunction(s)) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n Line %d: is not a function.\n", dfg_LINENUMBER);
    misc_FinishUserErrorReport();
  }
  return term_Create(s, Arguments);
}

static __inline__ TERM dfg_AtomCreate(char* Name, LIST Arguments)
/* Look up the symbol, check its arity and create the atom term */
{
  SYMBOL s;
  s = dfg_Symbol(Name, list_Length(Arguments)); /* Frees the string */
  if (symbol_IsVariable(s) || !symbol_IsPredicate(s)) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n Line %d: Symbol is not a predicate.\n", dfg_LINENUMBER);
    misc_FinishUserErrorReport();
  }
  return term_Create(s, Arguments);
}

static __inline__ void dfg_DeleteStringList(LIST List)
{
  list_DeleteWithElement(List, (void (*)(POINTER)) string_StringFree);
}

/**************************************************************/
/* Functions that handle symbols with unspecified arity       */
/**************************************************************/

/* The symbol list holds all symbols whose arity wasn't       */
/* specified in the symbol declaration section.               */
/* If the arity of a symbol was not specified in this section */
/* it is first set to 0. If the symbol occurs with always the */
/* same arity 'A' the arity of this symbol is set to 'A'.     */
static LIST   dfg_SYMBOLLIST;

static void dfg_SymAdd(SYMBOL);
static void dfg_SymCheck(SYMBOL, NAT);
static void dfg_SymCleanUp(void);

/**************************************************************/
/* Functions that handle variable names                       */
/**************************************************************/

/* List of quantified variables in the current input formula. */
/* This list is used to find symbols that by mistake weren't  */
/* declared in the symbol declaration section                 */
/* --> free variables                                         */
/* This is a list of lists, since each time a quantifier is   */
/* reached, a new list is added to the global list.           */
static LIST dfg_VARLIST;
static BOOL dfg_VARDECL;

static void   dfg_VarStart(void);
static void   dfg_VarStop(void);
static void   dfg_VarBacktrack(void);
static void   dfg_VarCheck(void);
static SYMBOL dfg_VarLookup(char*);

#define YYERROR_VERBOSE



/* Enabling traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 0
#endif

#ifndef YYSTYPE
#line 165 "dfgparser.y"
typedef union {
  int       number;
  char*     string;
  SYMBOL    symbol;
  SPROPERTY property;
  TERM      term;
  LIST      list;
  DFG_STATE state;
  BOOL      bool;
} yystype;
/* Line 193 of /opt/gnu//share/bison/yacc.c.  */
#line 336 "dfgparser.c"
# define YYSTYPE yystype
# define YYSTYPE_IS_TRIVIAL 1
#endif

#ifndef YYLTYPE
typedef struct yyltype
{
  int first_line;
  int first_column;
  int last_line;
  int last_column;
} yyltype;
# define YYLTYPE yyltype
# define YYLTYPE_IS_TRIVIAL 1
#endif

/* Copy the second part of user declarations.  */


/* Line 213 of /opt/gnu//share/bison/yacc.c.  */
#line 357 "dfgparser.c"

#if ! defined (yyoverflow) || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# if YYSTACK_USE_ALLOCA
#  define YYSTACK_ALLOC alloca
# else
#  ifndef YYSTACK_USE_ALLOCA
#   if defined (alloca) || defined (_ALLOCA_H)
#    define YYSTACK_ALLOC alloca
#   else
#    ifdef __GNUC__
#     define YYSTACK_ALLOC __builtin_alloca
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's `empty if-body' warning. */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
# else
#  if defined (__STDC__) || defined (__cplusplus)
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   define YYSIZE_T size_t
#  endif
#  define YYSTACK_ALLOC malloc
#  define YYSTACK_FREE free
# endif
#endif /* ! defined (yyoverflow) || YYERROR_VERBOSE */


#if (! defined (yyoverflow) \
     && (! defined (__cplusplus) \
	 || (YYLTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  short yyss;
  YYSTYPE yyvs;
  };

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAX (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (short) + sizeof (YYSTYPE))				\
      + YYSTACK_GAP_MAX)

/* Copy COUNT objects from FROM to TO.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if 1 < __GNUC__
#   define YYCOPY(To, From, Count) \
      __builtin_memcpy (To, From, (Count) * sizeof (*(From)))
#  else
#   define YYCOPY(To, From, Count)		\
      do					\
	{					\
	  register YYSIZE_T yyi;		\
	  for (yyi = 0; yyi < (Count); yyi++)	\
	    (To)[yyi] = (From)[yyi];	\
	}					\
      while (0)
#  endif
# endif

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack)					\
    do									\
      {									\
	YYSIZE_T yynewbytes;						\
	YYCOPY (&yyptr->Stack, Stack, yysize);				\
	Stack = &yyptr->Stack;						\
	yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAX;	\
	yyptr += yynewbytes / sizeof (*yyptr);				\
      }									\
    while (0)

#endif

#if defined (__STDC__) || defined (__cplusplus)
   typedef signed char yysigned_char;
#else
   typedef short yysigned_char;
#endif

/* YYFINAL -- State number of the termination state. */
#define YYFINAL  4
#define YYLAST   506

/* YYNTOKENS -- Number of terminals. */
#define YYNTOKENS  71
/* YYNNTS -- Number of nonterminals. */
#define YYNNTS  100
/* YYNRULES -- Number of rules. */
#define YYNRULES  196
/* YYNRULES -- Number of states. */
#define YYNSTATES  477

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   318

#define YYTRANSLATE(X) \
  ((unsigned)(X) <= YYMAXUTOK ? yytranslate[X] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const unsigned char yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
      64,    65,     2,     2,    69,     2,    66,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,    70,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,    67,     2,    68,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63
};

#if YYDEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const unsigned short yyprhs[] =
{
       0,     0,     3,    14,    26,    32,    38,    44,    50,    51,
      57,    58,    64,    65,    71,    73,    75,    77,    84,    85,
      95,    96,   102,   104,   108,   110,   116,   117,   123,   125,
     129,   131,   137,   138,   144,   146,   150,   151,   157,   159,
     163,   165,   171,   172,   178,   180,   184,   186,   192,   194,
     196,   197,   203,   204,   207,   209,   217,   220,   228,   229,
     230,   242,   252,   253,   255,   257,   261,   263,   267,   276,
     278,   280,   281,   284,   285,   293,   294,   297,   299,   304,
     311,   316,   317,   318,   329,   330,   332,   334,   338,   340,
     342,   344,   346,   348,   350,   352,   354,   356,   358,   360,
     362,   364,   368,   370,   375,   376,   379,   390,   391,   403,
     404,   412,   413,   415,   417,   418,   419,   430,   435,   437,
     441,   443,   448,   450,   454,   456,   458,   460,   467,   472,
     473,   481,   482,   484,   486,   495,   500,   502,   507,   509,
     513,   514,   517,   518,   528,   529,   545,   547,   551,   552,
     557,   561,   567,   568,   572,   574,   576,   578,   580,   582,
     584,   586,   588,   590,   591,   595,   603,   605,   607,   608,
     611,   612,   619,   620,   624,   625,   628,   634,   635,   645,
     647,   651,   652,   656,   661,   666,   673,   675,   679,   681,
     688,   689,   692,   694,   697,   703,   705
};

/* YYRHS -- A `-1'-separated list of the rules' RHS. */
static const short yyrhs[] =
{
      72,     0,    -1,     6,    64,   121,    65,    66,    73,    82,
     159,    20,    66,    -1,    16,    66,    74,    75,    78,    79,
      76,    77,    80,    19,    66,    -1,    36,    64,    63,    65,
      66,    -1,     4,    64,    63,    65,    66,    -1,    52,    64,
      81,    65,    66,    -1,    15,    64,    63,    65,    66,    -1,
      -1,    59,    64,    63,    65,    66,    -1,    -1,    35,    64,
      63,    65,    66,    -1,    -1,    13,    64,    63,    65,    66,
      -1,    46,    -1,    58,    -1,    57,    -1,    83,    99,   110,
     124,   143,   155,    -1,    -1,    49,    66,    84,    87,    90,
      92,    95,    19,    66,    -1,    -1,    29,    67,    85,    68,
      66,    -1,    86,    -1,    85,    69,    86,    -1,   121,    -1,
      64,   121,    69,    98,    65,    -1,    -1,    43,    67,    88,
      68,    66,    -1,    89,    -1,    88,    69,    89,    -1,   121,
      -1,    64,   121,    69,    98,    65,    -1,    -1,    51,    67,
      91,    68,    66,    -1,   121,    -1,    91,    69,   121,    -1,
      -1,    39,    67,    93,    68,    66,    -1,    94,    -1,    93,
      69,    94,    -1,   121,    -1,    64,   121,    69,    98,    65,
      -1,    -1,    45,    67,    96,    68,    66,    -1,    97,    -1,
      96,    69,    97,    -1,   121,    -1,    64,   121,    69,    98,
      65,    -1,    61,    -1,    60,    -1,    -1,    14,    66,   100,
      19,    66,    -1,    -1,   100,   101,    -1,   104,    -1,    54,
      64,   121,    69,   121,    65,    66,    -1,   136,    66,    -1,
      42,    64,   121,    69,   107,    65,    66,    -1,    -1,    -1,
      27,    64,    67,   102,   122,   103,    68,    69,   136,    65,
      66,    -1,    50,   121,   105,    30,     7,    67,   106,    68,
      66,    -1,    -1,    28,    -1,   121,    -1,   106,    69,   121,
      -1,   121,    -1,   107,    69,   121,    -1,    25,    64,   109,
      65,    66,   111,    19,    66,    -1,     5,    -1,    12,    -1,
      -1,   110,   108,    -1,    -1,   111,    26,    64,   116,   112,
      65,    66,    -1,    -1,    69,   121,    -1,   136,    -1,    37,
      64,   113,    65,    -1,   118,    64,   113,    69,   113,    65,
      -1,   119,    64,   117,    65,    -1,    -1,    -1,   120,    64,
      67,   114,   122,   115,    68,    69,   113,    65,    -1,    -1,
     113,    -1,   113,    -1,   117,    69,   113,    -1,    22,    -1,
      33,    -1,    34,    -1,     3,    -1,    40,    -1,    23,    -1,
      27,    -1,    62,    -1,    60,    -1,    47,    -1,    18,    -1,
      41,    -1,   123,    -1,   122,    69,   123,    -1,   121,    -1,
     121,    64,   121,    65,    -1,    -1,   124,   125,    -1,    10,
      64,   109,    69,    11,    65,    66,   127,    19,    66,    -1,
      -1,    10,    64,   109,    69,    17,    65,    66,   126,   137,
      19,    66,    -1,    -1,   127,     8,    64,   128,   112,    65,
      66,    -1,    -1,   129,    -1,   132,    -1,    -1,    -1,    27,
      64,    67,   130,   122,   131,    68,    69,   132,    65,    -1,
      40,    64,   133,    65,    -1,   134,    -1,   133,    69,   134,
      -1,   136,    -1,    37,    64,   136,    65,    -1,   136,    -1,
     135,    69,   136,    -1,   121,    -1,    56,    -1,    24,    -1,
      21,    64,   141,    69,   141,    65,    -1,   121,    64,   142,
      65,    -1,    -1,   137,     8,    64,   138,   112,    65,    66,
      -1,    -1,   139,    -1,   140,    -1,    23,    64,    67,   135,
      68,    69,   140,    65,    -1,     3,    64,   133,    65,    -1,
     121,    -1,   121,    64,   142,    65,    -1,   141,    -1,   142,
      69,   141,    -1,    -1,   143,   144,    -1,    -1,    44,    64,
     121,    65,    66,   145,   146,    19,    66,    -1,    -1,   146,
      53,    64,   150,    69,   154,    69,   121,    69,    67,   147,
      68,   148,    65,    66,    -1,   150,    -1,   147,    69,   150,
      -1,    -1,    69,    67,   149,    68,    -1,   150,    70,   150,
      -1,   149,    69,   150,    70,   150,    -1,    -1,   152,   151,
     153,    -1,   121,    -1,    37,    -1,    22,    -1,    33,    -1,
      34,    -1,     3,    -1,    40,    -1,    27,    -1,    23,    -1,
      -1,    64,   117,    65,    -1,    64,    67,   122,    68,    69,
     113,    65,    -1,   129,    -1,   139,    -1,    -1,   155,   156,
      -1,    -1,    55,    66,   157,   158,    19,    66,    -1,    -1,
     158,   141,    66,    -1,    -1,   159,   160,    -1,    31,    66,
     168,    19,    66,    -1,    -1,    48,    64,   121,   161,    65,
      66,   162,    19,    66,    -1,    63,    -1,    38,   163,     9,
      -1,    -1,   163,   164,    66,    -1,    41,    64,   165,    65,
      -1,    18,    64,   170,    65,    -1,    47,    64,    62,    69,
      98,    65,    -1,   166,    -1,   165,    69,   166,    -1,   121,
      -1,    64,   121,    69,    60,   167,    65,    -1,    -1,    69,
      62,    -1,   169,    -1,   168,   169,    -1,    32,    67,   170,
      68,    66,    -1,   121,    -1,   170,    69,   121,    -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const unsigned short yyrline[] =
{
       0,   206,   206,   218,   229,   233,   237,   241,   245,   246,
     250,   251,   255,   256,   260,   261,   262,   269,   281,   282,
     291,   292,   295,   296,   299,   300,   304,   305,   308,   309,
     312,   313,   316,   317,   320,   321,   324,   325,   328,   329,
     332,   333,   336,   337,   340,   341,   344,   345,   348,   349,
     356,   357,   362,   363,   366,   367,   369,   370,   372,   373,
     372,   382,   386,   387,   390,   391,   394,   395,   402,   412,
     413,   416,   417,   420,   421,   435,   436,   439,   440,   442,
     444,   446,   447,   446,   454,   455,   458,   460,   464,   465,
     466,   469,   470,   473,   474,   477,   483,   485,   487,   489,
     493,   495,   499,   510,   534,   535,   538,   548,   547,   554,
     555,   569,   570,   573,   574,   575,   574,   582,   586,   588,
     592,   593,   597,   598,   601,   603,   605,   607,   609,   616,
     617,   620,   621,   624,   625,   628,   635,   637,   641,   643,
     651,   652,   656,   655,   669,   670,   691,   693,   698,   699,
     702,   710,   721,   720,   732,   733,   734,   735,   736,   737,
     738,   739,   740,   743,   744,   745,   748,   749,   757,   758,
     761,   761,   768,   769,   776,   777,   780,   781,   781,   789,
     792,   795,   796,   799,   800,   820,   832,   833,   836,   848,
     865,   866,   883,   884,   887,   891,   892
};
#endif

#if YYDEBUG || YYERROR_VERBOSE
/* YYTNME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals. */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "DFG_AND", "DFG_AUTHOR", "DFG_AXIOMS", 
  "DFG_BEGPROB", "DFG_BY", "DFG_CLAUSE", "DFG_CLOSEBRACE", "DFG_CLSLIST", 
  "DFG_CNF", "DFG_CONJECS", "DFG_DATE", "DFG_DECLLIST", "DFG_DESC", 
  "DFG_DESCLIST", "DFG_DNF", "DFG_DOMPRED", "DFG_ENDLIST", "DFG_ENDPROB", 
  "DFG_EQUAL", "DFG_EQUIV", "DFG_EXISTS", "DFG_FALSE", "DFG_FORMLIST", 
  "DFG_FORMULA", "DFG_FORALL", "DFG_FREELY", "DFG_FUNC", "DFG_GENERATED", 
  "DFG_GENSET", "DFG_HYPOTH", "DFG_IMPLIED", "DFG_IMPLIES", "DFG_LOGIC", 
  "DFG_NAME", "DFG_NOT", "DFG_OPENBRACE", "DFG_OPERAT", "DFG_OR", 
  "DFG_PREC", "DFG_PRED", "DFG_PRDICAT", "DFG_PRFLIST", "DFG_QUANTIF", 
  "DFG_SATIS", "DFG_SETFLAG", "DFG_SETTINGS", "DFG_SYMLIST", "DFG_SORT", 
  "DFG_SORTS", "DFG_STATUS", "DFG_STEP", "DFG_SUBSORT", "DFG_TERMLIST", 
  "DFG_TRUE", "DFG_UNKNOWN", "DFG_UNSATIS", "DFG_VERSION", "DFG_NUM", 
  "DFG_MINUS1", "DFG_ID", "DFG_TEXT", "'('", "')'", "'.'", "'['", "']'", 
  "','", "':'", "$accept", "problem", "description", "name", "author", 
  "status", "desctext", "versionopt", "logicopt", "dateopt", "log_state", 
  "logicalpart", "symbollistopt", "functionsopt", "functionlist", "func", 
  "predicatesopt", "predicatelist", "pred", "sortsopt", "sortlist", 
  "operatorsopt", "operatorlist", "op", "quantifiersopt", 
  "quantifierlist", "quant", "number", "declarationlistopt", 
  "decllistopt", "decl", "@1", "@2", "gendecl", "freelyopt", "funclist", 
  "sortdecl", "formulalist", "origin", "formulalistsopt", 
  "formulalistopt", "labelopt", "formula", "@3", "@4", "formulaopt", 
  "arglist", "binsymbol", "nsymbol", "quantsymbol", "id", "qtermlist", 
  "qterm", "clauselistsopt", "clauselist", "@5", "cnfclausesopt", 
  "cnfclauseopt", "cnfclause", "@6", "@7", "cnfclausebody", "litlist", 
  "lit", "atomlist", "atom", "dnfclausesopt", "dnfclauseopt", "dnfclause", 
  "dnfclausebody", "term", "termlist", "prooflistsopt", "prooflist", "@8", 
  "prooflistopt", "parentlist", "assoclistopt", "assoclist", 
  "id_or_formula", "@9", "anysymbol", "optargs", "clause", 
  "listOfTermsopt", "listOfTerms", "@10", "terms", "settinglistsopt", 
  "settinglist", "@11", "flags", "spassflags", "spassflag", "preclist", 
  "precitem", "statopt", "gsettings", "gsetting", "labellist", 0
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[YYLEX-NUM] -- Internal token number corresponding to
   token YYLEX-NUM.  */
static const unsigned short yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,   302,   303,   304,
     305,   306,   307,   308,   309,   310,   311,   312,   313,   314,
     315,   316,   317,   318,    40,    41,    46,    91,    93,    44,
      58
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const unsigned char yyr1[] =
{
       0,    71,    72,    73,    74,    75,    76,    77,    78,    78,
      79,    79,    80,    80,    81,    81,    81,    82,    83,    83,
      84,    84,    85,    85,    86,    86,    87,    87,    88,    88,
      89,    89,    90,    90,    91,    91,    92,    92,    93,    93,
      94,    94,    95,    95,    96,    96,    97,    97,    98,    98,
      99,    99,   100,   100,   101,   101,   101,   101,   102,   103,
     101,   104,   105,   105,   106,   106,   107,   107,   108,   109,
     109,   110,   110,   111,   111,   112,   112,   113,   113,   113,
     113,   114,   115,   113,   116,   116,   117,   117,   118,   118,
     118,   119,   119,   120,   120,   121,   121,   121,   121,   121,
     122,   122,   123,   123,   124,   124,   125,   126,   125,   127,
     127,   128,   128,   129,   130,   131,   129,   132,   133,   133,
     134,   134,   135,   135,   136,   136,   136,   136,   136,   137,
     137,   138,   138,   139,   139,   140,   141,   141,   142,   142,
     143,   143,   145,   144,   146,   146,   147,   147,   148,   148,
     149,   149,   151,   150,   152,   152,   152,   152,   152,   152,
     152,   152,   152,   153,   153,   153,   154,   154,   155,   155,
     157,   156,   158,   158,   159,   159,   160,   161,   160,   162,
     162,   163,   163,   164,   164,   164,   165,   165,   166,   166,
     167,   167,   168,   168,   169,   170,   170
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const unsigned char yyr2[] =
{
       0,     2,    10,    11,     5,     5,     5,     5,     0,     5,
       0,     5,     0,     5,     1,     1,     1,     6,     0,     9,
       0,     5,     1,     3,     1,     5,     0,     5,     1,     3,
       1,     5,     0,     5,     1,     3,     0,     5,     1,     3,
       1,     5,     0,     5,     1,     3,     1,     5,     1,     1,
       0,     5,     0,     2,     1,     7,     2,     7,     0,     0,
      11,     9,     0,     1,     1,     3,     1,     3,     8,     1,
       1,     0,     2,     0,     7,     0,     2,     1,     4,     6,
       4,     0,     0,    10,     0,     1,     1,     3,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     3,     1,     4,     0,     2,    10,     0,    11,     0,
       7,     0,     1,     1,     0,     0,    10,     4,     1,     3,
       1,     4,     1,     3,     1,     1,     1,     6,     4,     0,
       7,     0,     1,     1,     8,     4,     1,     4,     1,     3,
       0,     2,     0,     9,     0,    15,     1,     3,     0,     4,
       3,     5,     0,     3,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     0,     3,     7,     1,     1,     0,     2,
       0,     6,     0,     3,     0,     2,     5,     0,     9,     1,
       3,     0,     3,     4,     4,     6,     1,     3,     1,     6,
       0,     2,     1,     2,     5,     1,     3
};

/* YYDEFACT[STATE-NAME] -- Default rule to reduce with in state
   STATE-NUM when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const unsigned char yydefact[] =
{
       0,     0,     0,     0,     1,    98,    99,    97,    96,    95,
       0,     0,     0,     0,    18,     0,     0,   174,    50,     0,
       0,    20,     0,     0,    71,     0,     0,     8,     0,    26,
       0,     0,     0,   175,    52,   104,     0,     0,     0,    10,
       0,     0,    32,     2,     0,     0,     0,     0,    72,   140,
       0,     0,     0,     0,     0,     0,     0,    22,    24,     0,
       0,    36,     0,     0,   192,   177,     0,     0,   126,     0,
       0,     0,     0,   125,    53,    54,   124,     0,     0,     0,
     105,   168,     4,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    28,    30,     0,     0,    42,     0,     0,
     193,     0,    51,     0,     0,     0,    62,     0,     0,    56,
      69,    70,     0,     0,     0,   141,    17,     5,     0,     0,
       0,     0,    12,     0,    21,    23,     0,     0,     0,     0,
      34,     0,     0,     0,   195,     0,   176,     0,   136,     0,
      58,     0,    63,     0,     0,   138,     0,     0,     0,     0,
       0,   169,     9,     0,    14,    16,    15,     0,     0,     0,
       0,    49,    48,     0,     0,    27,    29,     0,     0,     0,
       0,    38,    40,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   128,     0,    73,     0,     0,   170,
      11,     0,     0,     0,     0,    25,     0,    33,    35,     0,
       0,     0,     0,     0,    44,    46,    19,   194,   196,   181,
     179,     0,     0,     0,   102,    59,   100,     0,    66,     0,
       0,   139,     0,     0,     0,     0,   172,     6,     0,     0,
       3,    31,     0,    37,    39,     0,     0,     0,     0,     0,
     137,   127,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   142,     0,     7,     0,     0,     0,    43,
      45,   180,     0,     0,     0,     0,   178,     0,   101,     0,
      57,    67,     0,    64,    55,    68,    84,   109,   107,   144,
       0,     0,    13,    41,     0,     0,     0,     0,   182,   103,
       0,     0,     0,    91,    88,    93,    94,    89,    90,     0,
      92,    85,    75,     0,     0,     0,    77,     0,   129,     0,
     171,   173,    47,     0,     0,   188,     0,   186,     0,     0,
      61,    65,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   184,     0,   183,     0,     0,     0,     0,
      76,     0,     0,    86,     0,    81,   111,   106,     0,     0,
     143,     0,     0,   187,     0,    60,    78,    74,     0,    80,
       0,     0,     0,     0,    75,   112,   113,   131,   108,   159,
     156,   162,   161,   157,   158,   155,   160,   154,     0,   152,
     190,   185,     0,    87,    82,     0,     0,     0,     0,     0,
      75,   132,   133,     0,   163,     0,     0,    79,     0,   114,
       0,     0,   118,   120,     0,     0,     0,     0,   166,   167,
       0,     0,   153,   191,   189,     0,     0,     0,   117,     0,
     110,     0,     0,     0,     0,     0,     0,     0,   115,     0,
     119,   135,     0,   122,   130,     0,     0,   164,     0,     0,
     121,     0,     0,     0,     0,    83,     0,     0,   123,     0,
       0,     0,     0,     0,   146,     0,     0,   134,   148,     0,
     165,   116,     0,     0,   147,     0,     0,     0,     0,   145,
     149,     0,     0,     0,   150,     0,   151
};

/* YYDEFGOTO[NTERM-NUM]. */
static const short yydefgoto[] =
{
      -1,     2,    14,    20,    27,    87,   122,    39,    54,   160,
     157,    17,    18,    29,    56,    57,    42,    92,    93,    61,
     129,    97,   170,   171,   133,   203,   204,   163,    24,    46,
      74,   180,   244,    75,   143,   272,   217,    48,   112,    35,
     222,   324,   343,   361,   398,   302,   344,   303,   304,   305,
      76,   215,   216,    49,    80,   308,   307,   364,   365,   416,
     439,   366,   401,   402,   432,   306,   330,   390,   391,   392,
     145,   146,    81,   115,   279,   309,   453,   463,   467,   378,
     394,   379,   412,   410,   116,   151,   226,   254,    22,    33,
     101,   211,   238,   265,   316,   317,   396,    63,    64,   135
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -356
static const short yypact[] =
{
       9,   -32,    35,   232,  -356,  -356,  -356,  -356,  -356,  -356,
      -6,    13,    67,    20,    45,    53,    30,  -356,   110,    46,
     118,   121,   -12,    73,  -356,    91,    84,   113,   112,   141,
     123,   128,   132,  -356,  -356,   175,   152,   161,   155,   191,
       2,   162,   180,  -356,   204,   232,   214,   173,  -356,   252,
     176,   206,   209,   213,   226,   232,    47,  -356,  -356,    80,
     218,   254,   224,   -14,  -356,  -356,   230,   233,  -356,   234,
     241,   232,   242,  -356,  -356,  -356,   243,   237,    21,   244,
    -356,   260,  -356,   246,   245,   250,   251,   294,   247,   248,
       2,   232,    93,  -356,  -356,   232,   255,   272,   232,   253,
    -356,   256,  -356,   232,   257,   232,   290,   232,   232,  -356,
    -356,  -356,   258,    21,   261,  -356,   271,  -356,   262,   264,
      14,   263,   317,   108,  -356,  -356,   265,   266,    80,   119,
    -356,    85,   268,   312,  -356,   124,  -356,   270,   273,   269,
    -356,   274,  -356,   309,   275,  -356,   -52,   276,   277,   232,
     279,  -356,  -356,   281,  -356,  -356,  -356,   284,   287,   288,
     321,  -356,  -356,   286,   108,  -356,  -356,   289,   232,   232,
     138,  -356,  -356,   156,   291,   293,   232,   -17,   232,   232,
     232,   232,   346,   232,  -356,   232,  -356,    40,   296,  -356,
    -356,   297,   299,   302,   300,  -356,   303,  -356,  -356,   285,
     301,    85,   232,   143,  -356,  -356,  -356,  -356,  -356,  -356,
    -356,   337,    16,   304,   298,   306,  -356,    32,  -356,   311,
     305,  -356,    56,   308,   314,   310,  -356,  -356,   315,   318,
    -356,  -356,   108,  -356,  -356,   313,   319,   156,    -2,   320,
    -356,  -356,   232,   232,   316,   322,   232,   232,   323,   324,
     307,   325,   326,  -356,   240,  -356,   327,   329,   108,  -356,
    -356,  -356,   331,   332,   334,   333,  -356,   335,  -356,   336,
    -356,  -356,   145,  -356,  -356,  -356,    96,  -356,  -356,  -356,
     338,   340,  -356,  -356,   342,   232,   163,   339,  -356,  -356,
     239,   343,   232,  -356,  -356,  -356,  -356,  -356,  -356,   344,
    -356,  -356,   341,   347,   348,   350,  -356,     3,  -356,   -15,
    -356,  -356,  -356,    42,   232,  -356,    43,  -356,   349,   351,
    -356,  -356,    96,   232,   352,    96,    96,   353,   355,   357,
      57,   358,   361,  -356,   359,  -356,   163,   108,   360,   362,
    -356,   363,   364,  -356,    44,  -356,   -13,  -356,   366,   365,
    -356,   168,   372,  -356,   369,  -356,  -356,  -356,    96,  -356,
      96,   232,   371,   373,   341,  -356,  -356,     0,  -356,  -356,
    -356,  -356,  -356,  -356,  -356,  -356,  -356,  -356,   367,  -356,
     370,  -356,   375,  -356,   306,   374,   228,   377,   379,   380,
     341,  -356,  -356,    50,   381,   376,   382,  -356,   383,  -356,
     384,    66,  -356,  -356,   386,   228,   387,   385,  -356,  -356,
     388,     7,  -356,  -356,  -356,   389,   232,   239,  -356,   228,
    -356,    69,   239,   393,   232,   232,    90,    96,   306,   390,
    -356,  -356,   153,  -356,  -356,   391,   179,  -356,   396,   395,
    -356,   397,   239,   398,   401,  -356,   402,   399,  -356,   168,
      96,   409,   408,   185,  -356,   410,   411,  -356,   405,   168,
    -356,  -356,   400,   412,  -356,   168,   413,   198,   345,  -356,
    -356,   168,   168,   394,  -356,   168,  -356
};

/* YYPGOTO[NTERM-NUM].  */
static const short yypgoto[] =
{
    -356,  -356,  -356,  -356,  -356,  -356,  -356,  -356,  -356,  -356,
    -356,  -356,  -356,  -356,  -356,   392,  -356,  -356,   259,  -356,
    -356,  -356,  -356,   202,  -356,  -356,   216,  -152,  -356,  -356,
    -356,  -356,  -356,  -356,  -356,  -356,  -356,  -356,   267,  -356,
    -356,  -340,  -267,  -356,  -356,  -356,    70,  -356,  -356,  -356,
      -3,  -355,   235,  -356,  -356,  -356,  -356,  -356,    87,  -356,
    -356,    33,    78,    68,  -356,   -45,  -356,  -356,    92,    39,
    -101,   328,  -356,  -356,  -356,  -356,  -356,  -356,  -356,  -308,
    -356,  -356,  -356,  -356,  -356,  -356,  -356,  -356,  -356,  -356,
    -356,  -356,  -356,  -356,  -356,   154,  -356,  -356,   425,   207
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If zero, do what YYDEFACT says.
   If YYTABLE_NINF, parse error.  */
#define YYTABLE_NINF -1
static const unsigned short yytable[] =
{
      10,    77,   139,   388,   331,    99,   384,   261,    30,   301,
     293,   328,   196,   184,   362,     1,   262,   185,    62,    31,
       5,   209,   329,   389,   387,     5,   110,   363,    67,   294,
     295,    68,     3,   111,   296,     4,    32,    58,   332,   263,
     297,   298,    65,     6,   299,   264,   210,   300,     6,     7,
     407,   223,    88,   388,     7,   339,    94,   224,   342,    11,
     154,   428,     8,    73,     9,   348,    55,     8,   106,     9,
     436,   155,   156,   389,   425,   249,   349,   362,   213,    12,
     257,   240,   250,    13,   221,   185,    15,    58,   126,    19,
     363,   382,   130,   383,    16,   134,    21,   245,     5,   293,
     138,   246,   141,     5,   144,   138,   284,   333,   335,   359,
      25,   176,   336,   360,     5,    89,    90,    67,   294,   295,
      68,     6,    26,   296,    23,    94,     6,     7,   172,   297,
     298,   418,     7,   299,   431,   419,   300,     6,   419,    34,
       8,   454,     9,     7,    91,     8,   188,     9,    37,   169,
      28,   464,    73,   281,    36,   437,     8,   468,     9,   360,
     438,   127,   128,   473,   474,   198,   199,   476,   161,   162,
     205,   369,    38,   208,     5,   138,   138,   214,   218,    40,
     220,     5,   138,   455,    41,   354,     5,   167,   168,    43,
     370,   371,   175,   176,    44,   372,    45,     6,   172,   235,
      47,   373,   374,     7,     6,   375,   200,   201,   376,     6,
       7,   236,   237,   291,   292,     7,     8,    50,     9,    52,
     202,   441,   442,     8,    51,     9,    53,   314,     8,    59,
       9,    60,     5,    66,   205,    67,    62,    78,    68,   267,
     214,    69,    82,   271,   273,   319,     5,   444,   243,    67,
       5,   138,    68,   458,   459,     6,    70,     5,     5,   280,
      67,     7,    79,    68,    71,   400,   470,   471,    72,     6,
      73,    83,    84,     6,     8,     7,     9,    85,    86,     7,
       6,     6,   134,   315,    73,    95,     7,     7,     8,   321,
       9,    98,     8,    96,     9,    73,   102,   103,   104,     8,
       8,     9,     9,   109,   114,   105,   107,   108,   113,   121,
     118,   334,   117,   119,   124,   120,   123,   132,   142,   136,
     340,   137,   131,   147,   140,   149,   150,   158,   152,   153,
     159,   174,   165,   315,   164,   173,   177,   178,   179,   182,
     194,   403,   186,   181,   183,   189,   187,   190,   377,   191,
     192,   195,   193,   219,   232,   197,   239,   206,   214,   207,
     403,   225,   242,   227,   228,   229,   230,   233,   231,   241,
     248,   276,   429,   251,   403,   243,   253,   433,   247,   252,
     148,   255,   258,   256,   269,   259,   266,   166,   270,   274,
     275,   277,   278,   282,   283,   285,   286,   448,   287,   288,
     289,   318,   388,   234,   310,   290,   311,   312,   322,   320,
     323,   325,   326,   214,   327,   472,   338,   341,   337,   346,
     345,   435,   214,   347,   350,   351,   355,   356,   352,   357,
     367,   368,   380,   358,   381,   385,   393,   386,   413,   395,
     397,   399,   404,   405,   406,   411,   377,   414,   417,   363,
     423,   415,   420,   260,   422,   440,   377,   424,   427,   434,
     443,   445,   377,   446,   475,   449,   447,   465,   377,   377,
     450,   451,   377,   457,   462,   460,   461,   466,   268,   469,
     408,   426,   125,   421,   456,   409,   452,   430,   100,     0,
     353,     0,   313,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   212
};

static const short yycheck[] =
{
       3,    46,   103,     3,    19,    19,   361,     9,    20,   276,
       3,     8,   164,    65,    27,     6,    18,    69,    32,    31,
      18,    38,    19,    23,   364,    18,     5,    40,    21,    22,
      23,    24,    64,    12,    27,     0,    48,    40,    53,    41,
      33,    34,    45,    41,    37,    47,    63,    40,    41,    47,
     390,    11,    55,     3,    47,   322,    59,    17,   325,    65,
      46,   416,    60,    56,    62,     8,    64,    60,    71,    62,
     425,    57,    58,    23,    67,    19,    19,    27,   179,    66,
     232,    65,    26,    16,   185,    69,    66,    90,    91,    36,
      40,   358,    95,   360,    49,    98,    66,    65,    18,     3,
     103,    69,   105,    18,   107,   108,   258,    65,    65,    65,
      64,    69,    69,    69,    18,    68,    69,    21,    22,    23,
      24,    41,     4,    27,    14,   128,    41,    47,   131,    33,
      34,    65,    47,    37,    65,    69,    40,    41,    69,    66,
      60,   449,    62,    47,    64,    60,   149,    62,    64,    64,
      29,   459,    56,   254,    63,    65,    60,   465,    62,    69,
     427,    68,    69,   471,   472,   168,   169,   475,    60,    61,
     173,     3,    59,   176,    18,   178,   179,   180,   181,    67,
     183,    18,   185,   450,    43,   337,    18,    68,    69,    66,
      22,    23,    68,    69,    66,    27,    64,    41,   201,   202,
      25,    33,    34,    47,    41,    37,    68,    69,    40,    41,
      47,    68,    69,    68,    69,    47,    60,    65,    62,    64,
      64,    68,    69,    60,    63,    62,    35,    64,    60,    67,
      62,    51,    18,    19,   237,    21,    32,    64,    24,   242,
     243,    27,    66,   246,   247,   290,    18,    68,    69,    21,
      18,   254,    24,    68,    69,    41,    42,    18,    18,    19,
      21,    47,    10,    24,    50,    37,    68,    69,    54,    41,
      56,    65,    63,    41,    60,    47,    62,    64,    52,    47,
      41,    41,   285,   286,    56,    67,    47,    47,    60,   292,
      62,    67,    60,    39,    62,    56,    66,    64,    64,    60,
      60,    62,    62,    66,    44,    64,    64,    64,    64,    15,
      65,   314,    66,    63,    66,    64,    69,    45,    28,    66,
     323,    65,    67,    65,    67,    64,    55,    64,    66,    65,
      13,    19,    66,   336,    69,    67,    66,    64,    69,    30,
      19,   386,    66,    69,    69,    66,    69,    66,   351,    65,
      63,    65,    64,     7,    69,    66,    19,    66,   361,    66,
     405,    65,    64,    66,    65,    63,    66,    66,    65,    65,
      65,    64,   417,    65,   419,    69,    66,   422,    67,    65,
     113,    66,    69,    65,    68,    66,    66,   128,    66,    66,
      66,    66,    66,    66,    65,    64,    64,   442,    64,    66,
      65,    62,     3,   201,    66,    69,    66,    65,    64,    66,
      69,    64,    64,   416,    64,    70,    65,    65,    69,    64,
      67,   424,   425,    66,    66,    64,    66,    65,    69,    66,
      64,    66,    60,    69,    65,    64,    69,    64,    62,    69,
      65,    67,    65,    64,    64,    64,   449,    65,    64,    40,
      65,    68,    66,   237,    67,    65,   459,    69,    69,    66,
      69,    65,   465,    68,    70,    67,    69,    67,   471,   472,
      69,    69,   475,    65,    69,    65,    65,    65,   243,    66,
     393,   411,    90,   405,   451,   393,   447,   419,    63,    -1,
     336,    -1,   285,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   178
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const unsigned char yystos[] =
{
       0,     6,    72,    64,     0,    18,    41,    47,    60,    62,
     121,    65,    66,    16,    73,    66,    49,    82,    83,    36,
      74,    66,   159,    14,    99,    64,     4,    75,    29,    84,
      20,    31,    48,   160,    66,   110,    63,    64,    59,    78,
      67,    43,    87,    66,    66,    64,   100,    25,   108,   124,
      65,    63,    64,    35,    79,    64,    85,    86,   121,    67,
      51,    90,    32,   168,   169,   121,    19,    21,    24,    27,
      42,    50,    54,    56,   101,   104,   121,   136,    64,    10,
     125,   143,    66,    65,    63,    64,    52,    76,   121,    68,
      69,    64,    88,    89,   121,    67,    39,    92,    67,    19,
     169,   161,    66,    64,    64,    64,   121,    64,    64,    66,
       5,    12,   109,    64,    44,   144,   155,    66,    65,    63,
      64,    15,    77,    69,    66,    86,   121,    68,    69,    91,
     121,    67,    45,    95,   121,   170,    66,    65,   121,   141,
      67,   121,    28,   105,   121,   141,   142,    65,   109,    64,
      55,   156,    66,    65,    46,    57,    58,    81,    64,    13,
      80,    60,    61,    98,    69,    66,    89,    68,    69,    64,
      93,    94,   121,    67,    19,    68,    69,    66,    64,    69,
     102,    69,    30,    69,    65,    69,    66,    69,   121,    66,
      66,    65,    63,    64,    19,    65,    98,    66,   121,   121,
      68,    69,    64,    96,    97,   121,    66,    66,   121,    38,
      63,   162,   142,   141,   121,   122,   123,   107,   121,     7,
     121,   141,   111,    11,    17,    65,   157,    66,    65,    63,
      66,    65,    69,    66,    94,   121,    68,    69,   163,    19,
      65,    65,    64,    69,   103,    65,    69,    67,    65,    19,
      26,    65,    65,    66,   158,    66,    65,    98,    69,    66,
      97,     9,    18,    41,    47,   164,    66,   121,   123,    68,
      66,   121,   106,   121,    66,    66,    64,    66,    66,   145,
      19,   141,    66,    65,    98,    64,    64,    64,    66,    65,
      69,    68,    69,     3,    22,    23,    27,    33,    34,    37,
      40,   113,   116,   118,   119,   120,   136,   127,   126,   146,
      66,    66,    65,   170,    64,   121,   165,   166,    62,   136,
      66,   121,    64,    69,   112,    64,    64,    64,     8,    19,
     137,    19,    53,    65,   121,    65,    69,    69,    65,   113,
     121,    65,   113,   113,   117,    67,    64,    66,     8,    19,
      66,    64,    69,   166,    98,    66,    65,    66,    69,    65,
      69,   114,    27,    40,   128,   129,   132,    64,    66,     3,
      22,    23,    27,    33,    34,    37,    40,   121,   150,   152,
      60,    65,   113,   113,   122,    64,    64,   112,     3,    23,
     138,   139,   140,    69,   151,    69,   167,    65,   115,    67,
      37,   133,   134,   136,    65,    64,    64,   112,   129,   139,
     154,    64,   153,    62,    65,    68,   130,    64,    65,    69,
      66,   133,    67,    65,    69,    67,   117,    69,   122,   136,
     134,    65,   135,   136,    66,   121,   122,    65,   113,   131,
      65,    68,    69,    69,    68,    65,    68,    69,   136,    67,
      69,    69,   140,   147,   150,   113,   132,    65,    68,    69,
      65,    65,    69,   148,   150,    67,    65,   149,   150,    66,
      68,    69,    70,   150,   150,    70,   150
};

#if ! defined (YYSIZE_T) && defined (__SIZE_TYPE__)
# define YYSIZE_T __SIZE_TYPE__
#endif
#if ! defined (YYSIZE_T) && defined (size_t)
# define YYSIZE_T size_t
#endif
#if ! defined (YYSIZE_T)
# if defined (__STDC__) || defined (__cplusplus)
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# endif
#endif
#if ! defined (YYSIZE_T)
# define YYSIZE_T unsigned int
#endif

#define yyerrok		(yyerrstatus = 0)
#define yyclearin	(yychar = YYEMPTY)
#define YYEMPTY		-2
#define YYEOF		0

#define YYACCEPT	goto yyacceptlab
#define YYABORT		goto yyabortlab
#define YYERROR		goto yyerrlab1

/* Like YYERROR except do call yyerror.  This remains here temporarily
   to ease the transition to the new meaning of YYERROR, for GCC.
   Once GCC version 2 has supplanted version 1, this can go.  */

#define YYFAIL		goto yyerrlab

#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)					\
do								\
  if (yychar == YYEMPTY && yylen == 1)				\
    {								\
      yychar = (Token);						\
      yylval = (Value);						\
      yychar1 = YYTRANSLATE (yychar);				\
      YYPOPSTACK;						\
      goto yybackup;						\
    }								\
  else								\
    { 								\
      yyerror ("syntax error: cannot back up");			\
      YYERROR;							\
    }								\
while (0)

#define YYTERROR	1
#define YYERRCODE	256

/* YYLLOC_DEFAULT -- Compute the default location (before the actions
   are run).  */

#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)           \
  Current.first_line   = Rhs[1].first_line;      \
  Current.first_column = Rhs[1].first_column;    \
  Current.last_line    = Rhs[N].last_line;       \
  Current.last_column  = Rhs[N].last_column;
#endif

/* YYLEX -- calling `yylex' with the right arguments.  */

#define YYLEX	yylex ()

/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)			\
do {						\
  if (yydebug)					\
    YYFPRINTF Args;				\
} while (0)
# define YYDSYMPRINT(Args)			\
do {						\
  if (yydebug)					\
    yysymprint Args;				\
} while (0)
/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YYDSYMPRINT(Args)
#endif /* !YYDEBUG */

/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef	YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   SIZE_MAX < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#if YYMAXDEPTH == 0
# undef YYMAXDEPTH
#endif

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif



#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined (__GLIBC__) && defined (_STRING_H)
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
static YYSIZE_T
#   if defined (__STDC__) || defined (__cplusplus)
yystrlen (const char *yystr)
#   else
yystrlen (yystr)
     const char *yystr;
#   endif
{
  register const char *yys = yystr;

  while (*yys++ != '\0')
    continue;

  return yys - yystr - 1;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined (__GLIBC__) && defined (_STRING_H) && defined (_GNU_SOURCE)
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
#   if defined (__STDC__) || defined (__cplusplus)
yystpcpy (char *yydest, const char *yysrc)
#   else
yystpcpy (yydest, yysrc)
     char *yydest;
     const char *yysrc;
#   endif
{
  register char *yyd = yydest;
  register const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

#endif /* !YYERROR_VERBOSE */



#if YYDEBUG
/*-----------------------------.
| Print this symbol on YYOUT.  |
`-----------------------------*/

static void
#if defined (__STDC__) || defined (__cplusplus)
yysymprint (FILE* yyout, int yytype, YYSTYPE yyvalue)
#else
yysymprint (yyout, yytype, yyvalue)
    FILE* yyout;
    int yytype;
    YYSTYPE yyvalue;
#endif
{
  /* Pacify ``unused variable'' warnings.  */
  (void) yyvalue;

  if (yytype < YYNTOKENS)
    {
      YYFPRINTF (yyout, "token %s (", yytname[yytype]);
# ifdef YYPRINT
      YYPRINT (yyout, yytoknum[yytype], yyvalue);
# endif
    }
  else
    YYFPRINTF (yyout, "nterm %s (", yytname[yytype]);

  switch (yytype)
    {
      default:
        break;
    }
  YYFPRINTF (yyout, ")");
}
#endif /* YYDEBUG. */


/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
#if defined (__STDC__) || defined (__cplusplus)
yydestruct (int yytype, YYSTYPE yyvalue)
#else
yydestruct (yytype, yyvalue)
    int yytype;
    YYSTYPE yyvalue;
#endif
{
  /* Pacify ``unused variable'' warnings.  */
  (void) yyvalue;

  switch (yytype)
    {
      default:
        break;
    }
}



/* The user can define YYPARSE_PARAM as the name of an argument to be passed
   into yyparse.  The argument should have type void *.
   It should actually point to an object.
   Grammar actions can access the variable by casting it
   to the proper pointer type.  */

#ifdef YYPARSE_PARAM
# if defined (__STDC__) || defined (__cplusplus)
#  define YYPARSE_PARAM_ARG void *YYPARSE_PARAM
#  define YYPARSE_PARAM_DECL
# else
#  define YYPARSE_PARAM_ARG YYPARSE_PARAM
#  define YYPARSE_PARAM_DECL void *YYPARSE_PARAM;
# endif
#else /* !YYPARSE_PARAM */
# define YYPARSE_PARAM_ARG
# define YYPARSE_PARAM_DECL
#endif /* !YYPARSE_PARAM */

/* Prevent warning if -Wstrict-prototypes.  */
#ifdef __GNUC__
# ifdef YYPARSE_PARAM
int yyparse (void *);
# else
int yyparse (void);
# endif
#endif


/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;

/* Number of parse errors so far.  */
int yynerrs;


int
yyparse (YYPARSE_PARAM_ARG)
     YYPARSE_PARAM_DECL
{
  
  register int yystate;
  register int yyn;
  int yyresult;
  /* Number of tokens to shift before error messages enabled.  */
  int yyerrstatus;
  /* Lookahead token as an internal (translated) token number.  */
  int yychar1 = 0;

  /* Three stacks and their tools:
     `yyss': related to states,
     `yyvs': related to semantic values,
     `yyls': related to locations.

     Refer to the stacks thru separate pointers, to allow yyoverflow
     to reallocate them elsewhere.  */

  /* The state stack.  */
  short	yyssa[YYINITDEPTH];
  short *yyss = yyssa;
  register short *yyssp;

  /* The semantic value stack.  */
  YYSTYPE yyvsa[YYINITDEPTH];
  YYSTYPE *yyvs = yyvsa;
  register YYSTYPE *yyvsp;



#define YYPOPSTACK   (yyvsp--, yyssp--)

  YYSIZE_T yystacksize = YYINITDEPTH;

  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;


  /* When reducing, the number of symbols on the RHS of the reduced
     rule.  */
  int yylen;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY;		/* Cause a token to be read.  */

  /* Initialize stack pointers.
     Waste one element of value and location stack
     so that they stay on the same level as the state stack.
     The wasted elements are never initialized.  */

  yyssp = yyss;
  yyvsp = yyvs;

  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed. so pushing a state here evens the stacks.
     */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyssp >= yyss + yystacksize - 1)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
	/* Give user a chance to reallocate the stack. Use copies of
	   these so that the &'s don't force the real ones into
	   memory.  */
	YYSTYPE *yyvs1 = yyvs;
	short *yyss1 = yyss;


	/* Each stack pointer address is followed by the size of the
	   data in use in that stack, in bytes.  This used to be a
	   conditional around just the two extra args, but that might
	   be undefined if yyoverflow is a macro.  */
	yyoverflow ("parser stack overflow",
		    &yyss1, yysize * sizeof (*yyssp),
		    &yyvs1, yysize * sizeof (*yyvsp),

		    &yystacksize);

	yyss = yyss1;
	yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyoverflowlab;
# else
      /* Extend the stack our own way.  */
      if (yystacksize >= YYMAXDEPTH)
	goto yyoverflowlab;
      yystacksize *= 2;
      if (yystacksize > YYMAXDEPTH)
	yystacksize = YYMAXDEPTH;

      {
	short *yyss1 = yyss;
	union yyalloc *yyptr =
	  (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
	if (! yyptr)
	  goto yyoverflowlab;
	YYSTACK_RELOCATE (yyss);
	YYSTACK_RELOCATE (yyvs);

#  undef YYSTACK_RELOCATE
	if (yyss1 != yyssa)
	  YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;


      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
		  (unsigned long int) yystacksize));

      if (yyssp >= yyss + yystacksize - 1)
	YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

/* Do appropriate processing given the current state.  */
/* Read a lookahead token if we need one and don't already have one.  */
/* yyresume: */

  /* First try to decide what to do without reference to lookahead token.  */

  yyn = yypact[yystate];
  if (yyn == YYPACT_NINF)
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* yychar is either YYEMPTY or YYEOF
     or a valid token in external form.  */

  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = YYLEX;
    }

  /* Convert token to internal form (in yychar1) for indexing tables with.  */

  if (yychar <= 0)		/* This means end of input.  */
    {
      yychar1 = 0;
      yychar = YYEOF;		/* Don't call YYLEX any more.  */

      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yychar1 = YYTRANSLATE (yychar);

      /* We have to keep this `#if YYDEBUG', since we use variables
	 which are defined only if `YYDEBUG' is set.  */
      YYDPRINTF ((stderr, "Next token is "));
      YYDSYMPRINT ((stderr, yychar1, yylval));
      YYDPRINTF ((stderr, "\n"));
    }

  /* If the proper action on seeing token YYCHAR1 is to reduce or to
     detect an error, take that action.  */
  yyn += yychar1;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yychar1)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yyn == 0 || yyn == YYTABLE_NINF)
	goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  if (yyn == YYFINAL)
    YYACCEPT;

  /* Shift the lookahead token.  */
  YYDPRINTF ((stderr, "Shifting token %d (%s), ",
	      yychar, yytname[yychar1]));

  /* Discard the token being shifted unless it is eof.  */
  if (yychar != YYEOF)
    yychar = YYEMPTY;

  *++yyvsp = yylval;


  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  yystate = yyn;
  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     `$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];



#if YYDEBUG
  /* We have to keep this `#if YYDEBUG', since we use variables which
     are defined only if `YYDEBUG' is set.  */
  if (yydebug)
    {
      int yyi;

      YYFPRINTF (stderr, "Reducing via rule %d (line %d), ",
		 yyn - 1, yyrline[yyn]);

      /* Print the symbols being reduced, and their result.  */
      for (yyi = yyprhs[yyn]; yyrhs[yyi] >= 0; yyi++)
	YYFPRINTF (stderr, "%s ", yytname[yyrhs[yyi]]);
      YYFPRINTF (stderr, " -> %s\n", yytname[yyr1[yyn]]);
    }
#endif
  switch (yyn)
    {
        case 2:
#line 210 "dfgparser.y"
    { string_StringFree(yyvsp[-7].string);
					  YYACCEPT; /* Stop immediately */ }
    break;

  case 4:
#line 230 "dfgparser.y"
    { dfg_DESC.name = yyvsp[-2].string; }
    break;

  case 5:
#line 234 "dfgparser.y"
    { dfg_DESC.author = yyvsp[-2].string; }
    break;

  case 6:
#line 238 "dfgparser.y"
    { dfg_DESC.status = yyvsp[-2].state; }
    break;

  case 7:
#line 242 "dfgparser.y"
    { dfg_DESC.description = yyvsp[-2].string; }
    break;

  case 9:
#line 247 "dfgparser.y"
    { dfg_DESC.version = yyvsp[-2].string; }
    break;

  case 11:
#line 252 "dfgparser.y"
    { dfg_DESC.logic = yyvsp[-2].string; }
    break;

  case 13:
#line 257 "dfgparser.y"
    { dfg_DESC.date = yyvsp[-2].string; }
    break;

  case 14:
#line 260 "dfgparser.y"
    { yyval.state = DFG_SATISFIABLE; }
    break;

  case 15:
#line 261 "dfgparser.y"
    { yyval.state = DFG_UNSATISFIABLE; }
    break;

  case 16:
#line 262 "dfgparser.y"
    { yyval.state = DFG_UNKNOWNSTATE; }
    break;

  case 24:
#line 299 "dfgparser.y"
    { dfg_SymbolDecl(DFG_FUNC, yyvsp[0].string, -2); }
    break;

  case 25:
#line 301 "dfgparser.y"
    { dfg_SymbolDecl(DFG_FUNC, yyvsp[-3].string, yyvsp[-1].number); }
    break;

  case 30:
#line 312 "dfgparser.y"
    { dfg_SymbolDecl(DFG_PRDICAT, yyvsp[0].string, -2); }
    break;

  case 31:
#line 313 "dfgparser.y"
    { dfg_SymbolDecl(DFG_PRDICAT, yyvsp[-3].string, yyvsp[-1].number); }
    break;

  case 34:
#line 320 "dfgparser.y"
    { dfg_SymbolDecl(DFG_PRDICAT, yyvsp[0].string, 1); }
    break;

  case 35:
#line 321 "dfgparser.y"
    { dfg_SymbolDecl(DFG_PRDICAT, yyvsp[0].string, 1); }
    break;

  case 40:
#line 332 "dfgparser.y"
    { dfg_SymbolDecl(DFG_OPERAT, yyvsp[0].string, -2); }
    break;

  case 41:
#line 333 "dfgparser.y"
    { dfg_SymbolDecl(DFG_OPERAT, yyvsp[-3].string, yyvsp[-1].number); }
    break;

  case 46:
#line 344 "dfgparser.y"
    { dfg_SymbolDecl(DFG_QUANTIF, yyvsp[0].string, -2); }
    break;

  case 47:
#line 345 "dfgparser.y"
    { dfg_SymbolDecl(DFG_QUANTIF, yyvsp[-3].string, yyvsp[-1].number); }
    break;

  case 48:
#line 348 "dfgparser.y"
    { yyval.number = -1; }
    break;

  case 49:
#line 349 "dfgparser.y"
    { yyval.number = yyvsp[0].number; }
    break;

  case 55:
#line 368 "dfgparser.y"
    { dfg_SubSort(yyvsp[-4].string,yyvsp[-2].string); }
    break;

  case 56:
#line 369 "dfgparser.y"
    { dfg_SORTDECLLIST = list_Nconc(dfg_SORTDECLLIST,list_List(list_PairCreate(NULL,yyvsp[-1].term))); }
    break;

  case 57:
#line 371 "dfgparser.y"
    { string_StringFree(yyvsp[-4].string); }
    break;

  case 58:
#line 372 "dfgparser.y"
    { dfg_VarStart(); }
    break;

  case 59:
#line 373 "dfgparser.y"
    { dfg_VarStop();  }
    break;

  case 60:
#line 374 "dfgparser.y"
    { TERM term;
					  dfg_VarBacktrack();
					  dfg_VarCheck();
					  term = dfg_CreateQuantifier(fol_All(),yyvsp[-6].list,yyvsp[-2].term);
					  dfg_SORTDECLLIST = list_Nconc(dfg_SORTDECLLIST,list_List(list_PairCreate(NULL,term)));
					}
    break;

  case 61:
#line 383 "dfgparser.y"
    { dfg_SymbolGenerated(dfg_Symbol(yyvsp[-7].string,1), yyvsp[-6].bool, yyvsp[-2].list); }
    break;

  case 62:
#line 386 "dfgparser.y"
    { yyval.bool = FALSE; }
    break;

  case 63:
#line 387 "dfgparser.y"
    { yyval.bool = TRUE; }
    break;

  case 64:
#line 390 "dfgparser.y"
    { yyval.list = list_List(yyvsp[0].string); }
    break;

  case 65:
#line 391 "dfgparser.y"
    { yyval.list = list_Cons(yyvsp[0].string, yyvsp[-2].list); }
    break;

  case 66:
#line 394 "dfgparser.y"
    { string_StringFree(yyvsp[0].string); }
    break;

  case 67:
#line 395 "dfgparser.y"
    { string_StringFree(yyvsp[0].string); }
    break;

  case 68:
#line 404 "dfgparser.y"
    { list_NReverse(yyvsp[-2].list);
                                  if (yyvsp[-5].bool) /* Axioms */
				    dfg_AXIOMLIST = list_Nconc(dfg_AXIOMLIST, yyvsp[-2].list);
				  else
				    dfg_CONJECLIST = list_Nconc(dfg_CONJECLIST, yyvsp[-2].list);
				}
    break;

  case 69:
#line 412 "dfgparser.y"
    { yyval.bool = TRUE;  }
    break;

  case 70:
#line 413 "dfgparser.y"
    { yyval.bool = FALSE; }
    break;

  case 73:
#line 420 "dfgparser.y"
    { yyval.list = list_Nil(); }
    break;

  case 74:
#line 422 "dfgparser.y"
    { LIST pair;
					  if (yyvsp[-3].term == NULL) { /* No term */
					    if (yyvsp[-2].string != NULL)
					      string_StringFree(yyvsp[-2].string);
					    yyval.list = yyvsp[-6].list;
					  } else {
					    pair = list_PairCreate(yyvsp[-2].string, yyvsp[-3].term);
					    yyval.list = list_Cons(pair, yyvsp[-6].list);
					  }
					  dfg_VarCheck();
					}
    break;

  case 75:
#line 435 "dfgparser.y"
    { yyval.string = NULL; }
    break;

  case 76:
#line 436 "dfgparser.y"
    { yyval.string = yyvsp[0].string;   }
    break;

  case 77:
#line 439 "dfgparser.y"
    { yyval.term = yyvsp[0].term; }
    break;

  case 78:
#line 441 "dfgparser.y"
    { yyval.term = dfg_IGNORE ? NULL : term_Create(fol_Not(),list_List(yyvsp[-1].term)); }
    break;

  case 79:
#line 443 "dfgparser.y"
    { yyval.term = dfg_IGNORE ? NULL : term_Create(yyvsp[-5].symbol, list_Cons(yyvsp[-3].term, list_List(yyvsp[-1].term))); }
    break;

  case 80:
#line 445 "dfgparser.y"
    { yyval.term = dfg_IGNORE ? NULL : term_Create(yyvsp[-3].symbol, yyvsp[-1].list); }
    break;

  case 81:
#line 446 "dfgparser.y"
    { dfg_VarStart(); }
    break;

  case 82:
#line 447 "dfgparser.y"
    { dfg_VarStop(); }
    break;

  case 83:
#line 449 "dfgparser.y"
    { dfg_VarBacktrack();
		    yyval.term = dfg_IGNORE ? NULL : dfg_CreateQuantifier(yyvsp[-9].symbol,yyvsp[-5].list,yyvsp[-1].term);
		  }
    break;

  case 84:
#line 454 "dfgparser.y"
    { yyval.term = NULL; }
    break;

  case 85:
#line 455 "dfgparser.y"
    { yyval.term = yyvsp[0].term; }
    break;

  case 86:
#line 459 "dfgparser.y"
    { yyval.list = dfg_IGNORE ? list_Nil() : list_List(yyvsp[0].term); }
    break;

  case 87:
#line 461 "dfgparser.y"
    { yyval.list = dfg_IGNORE ? yyvsp[-2].list : list_Nconc(yyvsp[-2].list, list_List(yyvsp[0].term)); }
    break;

  case 88:
#line 464 "dfgparser.y"
    { yyval.symbol = fol_Equiv();    }
    break;

  case 89:
#line 465 "dfgparser.y"
    { yyval.symbol = fol_Implied();  }
    break;

  case 90:
#line 466 "dfgparser.y"
    { yyval.symbol = fol_Implies();  }
    break;

  case 91:
#line 469 "dfgparser.y"
    { yyval.symbol = fol_And(); }
    break;

  case 92:
#line 470 "dfgparser.y"
    { yyval.symbol = fol_Or();  }
    break;

  case 93:
#line 473 "dfgparser.y"
    { yyval.symbol = fol_Exist(); }
    break;

  case 94:
#line 474 "dfgparser.y"
    { yyval.symbol = fol_All(); }
    break;

  case 95:
#line 477 "dfgparser.y"
    { if (dfg_IGNORE) {
  					    string_StringFree(yyvsp[0].string);
					    yyval.string = NULL;
					  } else
					    yyval.string = yyvsp[0].string;
					}
    break;

  case 96:
#line 484 "dfgparser.y"
    { yyval.string = dfg_IGNORE ? NULL : string_IntToString(yyvsp[0].number); }
    break;

  case 97:
#line 486 "dfgparser.y"
    { yyval.string = dfg_IGNORE ? NULL : string_StringCopy("set_flag"); }
    break;

  case 98:
#line 488 "dfgparser.y"
    { yyval.string = dfg_IGNORE ? NULL : string_StringCopy("set_DomPred"); }
    break;

  case 99:
#line 490 "dfgparser.y"
    { yyval.string = dfg_IGNORE ? NULL : string_StringCopy("set_precedence"); }
    break;

  case 100:
#line 494 "dfgparser.y"
    { yyval.list = dfg_IGNORE ? list_Nil() : list_List(yyvsp[0].term); }
    break;

  case 101:
#line 496 "dfgparser.y"
    { yyval.list = dfg_IGNORE ? yyvsp[-2].list : list_Nconc(yyvsp[-2].list, list_List(yyvsp[0].term)); }
    break;

  case 102:
#line 500 "dfgparser.y"
    { if (!dfg_IGNORE) {
		      SYMBOL s = dfg_Symbol(yyvsp[0].string,0);
		      if (!symbol_IsVariable(s)) {
			misc_StartUserErrorReport();
			misc_UserErrorReport("\n Line %d: Symbol is not a variable.\n",dfg_LINENUMBER);
			misc_FinishUserErrorReport();
		      }
		      yyval.term = term_Create(s, list_Nil());
		    }
		  }
    break;

  case 103:
#line 511 "dfgparser.y"
    { if (!dfg_IGNORE) {
		      SYMBOL p, v;
		      p = dfg_Symbol(yyvsp[-3].string, 1);
		      if (!symbol_IsPredicate(p)) {
			misc_StartUserErrorReport();
			misc_UserErrorReport("\n Line %d: Symbol is not a predicate.\n",dfg_LINENUMBER);
			misc_FinishUserErrorReport();
		      }
		      v = dfg_Symbol(yyvsp[-1].string, 0);
		      if (!symbol_IsVariable(v)) {
			misc_StartUserErrorReport();
			misc_UserErrorReport("\n Line %d: Symbol is not a variable.\n",dfg_LINENUMBER);
			misc_FinishUserErrorReport();
		      }
		      yyval.term = term_Create(p, list_List(term_Create(v,list_Nil())));
		    }
		  }
    break;

  case 106:
#line 541 "dfgparser.y"
    { list_NReverse(yyvsp[-2].list);
                    if (yyvsp[-7].bool) /* Axioms */
		      dfg_AXCLAUSES = list_Nconc(dfg_AXCLAUSES, yyvsp[-2].list);
		    else
		      dfg_CONCLAUSES = list_Nconc(dfg_CONCLAUSES, yyvsp[-2].list);
		  }
    break;

  case 107:
#line 548 "dfgparser.y"
    { stack_Push((POINTER)dfg_IGNORE); dfg_IGNORE = TRUE; }
    break;

  case 108:
#line 551 "dfgparser.y"
    { dfg_IGNORE = (BOOL)stack_PopResult(); }
    break;

  case 109:
#line 554 "dfgparser.y"
    { yyval.list = list_Nil(); }
    break;

  case 110:
#line 556 "dfgparser.y"
    { LIST pair;
		    if (yyvsp[-3].term == NULL) { /* No clause */
		      if (yyvsp[-2].string != NULL)
			string_StringFree(yyvsp[-2].string);
		      yyval.list = yyvsp[-6].list;
		    } else {
		      pair = list_PairCreate(yyvsp[-2].string, yyvsp[-3].term);
		      yyval.list = list_Cons(pair, yyvsp[-6].list);
		    }
		    dfg_VarCheck();
		  }
    break;

  case 111:
#line 569 "dfgparser.y"
    { yyval.term = NULL; }
    break;

  case 112:
#line 570 "dfgparser.y"
    { yyval.term = yyvsp[0].term; }
    break;

  case 113:
#line 573 "dfgparser.y"
    { yyval.term = yyvsp[0].term; }
    break;

  case 114:
#line 574 "dfgparser.y"
    { dfg_VarStart(); }
    break;

  case 115:
#line 575 "dfgparser.y"
    { dfg_VarStop();  }
    break;

  case 116:
#line 577 "dfgparser.y"
    { dfg_VarBacktrack();
		    yyval.term = dfg_IGNORE ? NULL : dfg_CreateQuantifier(fol_All(),yyvsp[-5].list,yyvsp[-1].term);
		  }
    break;

  case 117:
#line 583 "dfgparser.y"
    { yyval.term = dfg_IGNORE ? NULL : term_Create(fol_Or(), yyvsp[-1].list); }
    break;

  case 118:
#line 587 "dfgparser.y"
    { yyval.list = dfg_IGNORE ? list_Nil() : list_List(yyvsp[0].term); }
    break;

  case 119:
#line 589 "dfgparser.y"
    { yyval.list = dfg_IGNORE ? yyvsp[-2].list : list_Nconc(yyvsp[-2].list, list_List(yyvsp[0].term)); }
    break;

  case 120:
#line 592 "dfgparser.y"
    { yyval.term = yyvsp[0].term; }
    break;

  case 121:
#line 594 "dfgparser.y"
    { yyval.term = dfg_IGNORE ? yyvsp[-1].term : term_Create(fol_Not(),list_List(yyvsp[-1].term)); }
    break;

  case 122:
#line 597 "dfgparser.y"
    { yyval.list = list_List(yyvsp[0].term); }
    break;

  case 123:
#line 598 "dfgparser.y"
    { yyval.list = list_Nconc(yyvsp[-2].list, list_List(yyvsp[0].term)); }
    break;

  case 124:
#line 602 "dfgparser.y"
    { yyval.term = dfg_IGNORE ? NULL : dfg_AtomCreate(yyvsp[0].string,list_Nil()); }
    break;

  case 125:
#line 604 "dfgparser.y"
    { yyval.term = dfg_IGNORE ? NULL : term_Create(fol_True(),list_Nil()); }
    break;

  case 126:
#line 606 "dfgparser.y"
    { yyval.term = dfg_IGNORE ? NULL : term_Create(fol_False(),list_Nil()); }
    break;

  case 127:
#line 608 "dfgparser.y"
    { yyval.term = dfg_IGNORE ? NULL : term_Create(fol_Equality(),list_Cons(yyvsp[-3].term,list_List(yyvsp[-1].term))); }
    break;

  case 128:
#line 610 "dfgparser.y"
    { yyval.term = dfg_IGNORE ? NULL : dfg_AtomCreate(yyvsp[-3].string, yyvsp[-1].list); }
    break;

  case 136:
#line 636 "dfgparser.y"
    { yyval.term = dfg_IGNORE ? NULL : dfg_TermCreate(yyvsp[0].string,list_Nil()); }
    break;

  case 137:
#line 638 "dfgparser.y"
    { yyval.term = dfg_IGNORE ? NULL : dfg_TermCreate(yyvsp[-3].string, yyvsp[-1].list); }
    break;

  case 138:
#line 642 "dfgparser.y"
    { yyval.list = dfg_IGNORE ? list_Nil() : list_List(yyvsp[0].term); }
    break;

  case 139:
#line 644 "dfgparser.y"
    { yyval.list = dfg_IGNORE ? yyvsp[-2].list : list_Nconc(yyvsp[-2].list,list_List(yyvsp[0].term)); }
    break;

  case 142:
#line 656 "dfgparser.y"
    { if (!string_Equal(yyvsp[-2].string,"SPASS")) {
		      stack_Push((POINTER)dfg_IGNORE);
		      dfg_IGNORE = TRUE;
		    }
		  }
    break;

  case 143:
#line 663 "dfgparser.y"
    { if (!string_Equal(yyvsp[-6].string,"SPASS"))
		      dfg_IGNORE = (BOOL)stack_PopResult();
		    string_StringFree(yyvsp[-6].string);
		  }
    break;

  case 145:
#line 672 "dfgparser.y"
    { if (!dfg_IGNORE && yyvsp[-11].string!=NULL && yyvsp[-9].term!=NULL && !list_Empty(yyvsp[-4].list)) {
		    LIST tupel;
		    RULE Rule = clause_GetOriginFromString(yyvsp[-7].string);
		    string_StringFree(yyvsp[-7].string);
		    /* Build a tuple (label,clause,parentlist,split level,origin) */
		    tupel = list_Cons((POINTER)yyvsp[-2].number,list_List((POINTER)Rule));
		    tupel = list_Cons(yyvsp[-11].string,list_Cons(yyvsp[-9].term,list_Cons(yyvsp[-4].list,tupel)));
		    dfg_PROOFLIST = list_Cons(tupel, dfg_PROOFLIST);
		  } else {
		    /* ignore DNF clauses and clauses with incomplete data */
		    if (yyvsp[-11].string != NULL) string_StringFree(yyvsp[-11].string);
		    if (yyvsp[-9].term != NULL) term_Delete(yyvsp[-9].term);
		    if (yyvsp[-7].string != NULL) string_StringFree(yyvsp[-7].string);
		    dfg_DeleteStringList(yyvsp[-4].list);
		  }
		  dfg_VarCheck();
		}
    break;

  case 146:
#line 692 "dfgparser.y"
    { yyval.list = (dfg_IGNORE||yyvsp[0].string==NULL) ? list_Nil() : list_List(yyvsp[0].string); }
    break;

  case 147:
#line 694 "dfgparser.y"
    { yyval.list = (dfg_IGNORE||yyvsp[0].string==NULL) ? yyvsp[-2].list : list_Nconc(yyvsp[-2].list, list_List(yyvsp[0].string)); }
    break;

  case 148:
#line 698 "dfgparser.y"
    { yyval.number = 0; }
    break;

  case 149:
#line 699 "dfgparser.y"
    { yyval.number = yyvsp[-1].number; }
    break;

  case 150:
#line 703 "dfgparser.y"
    { if (!dfg_IGNORE && yyvsp[-2].string!=NULL && yyvsp[0].string!=NULL && string_Equal(yyvsp[-2].string,"splitlevel"))
		      string_StringToInt(yyvsp[0].string, TRUE, &yyval.number);
		    else
		      yyval.number = 0;
		    if (yyvsp[-2].string != NULL) string_StringFree(yyvsp[-2].string);
		    if (yyvsp[0].string != NULL) string_StringFree(yyvsp[0].string);
		  }
    break;

  case 151:
#line 711 "dfgparser.y"
    { if (!dfg_IGNORE && yyvsp[-2].string!=NULL && yyvsp[0].string!=NULL && string_Equal(yyvsp[-2].string,"splitlevel"))
		      string_StringToInt(yyvsp[0].string, TRUE, &yyval.number);
		    else
		      yyval.number = yyvsp[-4].number;
		    if (yyvsp[-2].string != NULL) string_StringFree(yyvsp[-2].string);
		    if (yyvsp[0].string != NULL) string_StringFree(yyvsp[0].string);
		  }
    break;

  case 152:
#line 721 "dfgparser.y"
    { stack_Push((POINTER) dfg_IGNORE); dfg_IGNORE = TRUE; }
    break;

  case 153:
#line 723 "dfgparser.y"
    { dfg_IGNORE = (BOOL) stack_PopResult();
		    if (yyvsp[0].bool) {
		      if (yyvsp[-2].string != NULL) string_StringFree(yyvsp[-2].string);
		      yyval.string = NULL;
		    } else
		      yyval.string = yyvsp[-2].string;
		  }
    break;

  case 154:
#line 732 "dfgparser.y"
    { yyval.string = yyvsp[0].string; }
    break;

  case 155:
#line 733 "dfgparser.y"
    { yyval.string = NULL; }
    break;

  case 156:
#line 734 "dfgparser.y"
    { yyval.string = NULL; }
    break;

  case 157:
#line 735 "dfgparser.y"
    { yyval.string = NULL; }
    break;

  case 158:
#line 736 "dfgparser.y"
    { yyval.string = NULL; }
    break;

  case 159:
#line 737 "dfgparser.y"
    { yyval.string = NULL; }
    break;

  case 160:
#line 738 "dfgparser.y"
    { yyval.string = NULL; }
    break;

  case 161:
#line 739 "dfgparser.y"
    { yyval.string = NULL; }
    break;

  case 162:
#line 740 "dfgparser.y"
    { yyval.string = NULL; }
    break;

  case 163:
#line 743 "dfgparser.y"
    { yyval.bool = FALSE; }
    break;

  case 164:
#line 744 "dfgparser.y"
    { yyval.bool = TRUE; }
    break;

  case 165:
#line 745 "dfgparser.y"
    { yyval.bool = TRUE; }
    break;

  case 166:
#line 748 "dfgparser.y"
    { yyval.term = yyvsp[0].term;   }
    break;

  case 167:
#line 749 "dfgparser.y"
    { yyval.term = NULL; }
    break;

  case 170:
#line 761 "dfgparser.y"
    { dfg_VarStart(); }
    break;

  case 171:
#line 762 "dfgparser.y"
    {
                                          dfg_VarStop();
                                          dfg_VarBacktrack();
                                          dfg_VarCheck(); }
    break;

  case 173:
#line 769 "dfgparser.y"
    { dfg_TERMLIST = list_Nconc(dfg_TERMLIST, list_List(yyvsp[-1].term)); }
    break;

  case 177:
#line 781 "dfgparser.y"
    { if (string_Equal(yyvsp[0].string,"SPASS"))
					    dfg_IGNORETEXT = FALSE;
					  string_StringFree(yyvsp[0].string);
					}
    break;

  case 178:
#line 786 "dfgparser.y"
    { dfg_IGNORETEXT = TRUE; }
    break;

  case 179:
#line 789 "dfgparser.y"
    { /* no SPASS flags */
				  string_StringFree(yyvsp[0].string);
				}
    break;

  case 184:
#line 801 "dfgparser.y"
    { SYMBOL s;
		    for ( ; !list_Empty(yyvsp[-1].list); yyvsp[-1].list = list_Pop(yyvsp[-1].list)) {
		      s = symbol_Lookup(list_Car(yyvsp[-1].list));
		      if (s == 0) {
		        misc_StartUserErrorReport();
		        misc_UserErrorReport("\n Undefined symbol %s", list_Car(yyvsp[-1].list));
			misc_UserErrorReport(" in DomPred list.\n"); 
			misc_FinishUserErrorReport(); 
		      }
		      if (!symbol_IsPredicate(s)) {
			misc_StartUserErrorReport();
			misc_UserErrorReport("\n Symbol %s isn't a predicate", list_Car(yyvsp[-1].list));
			misc_UserErrorReport(" in DomPred list.\n");
			misc_FinishUserErrorReport();
		      }
		      string_StringFree(list_Car(yyvsp[-1].list)); 
		      symbol_AddProperty(s, DOMPRED);
		    }
		  }
    break;

  case 185:
#line 821 "dfgparser.y"
    { int flag = flag_Id(yyvsp[-3].string);
		    if (flag == -1) {
		      misc_StartUserErrorReport();
		      misc_UserErrorReport("\n Found unknown flag %s", yyvsp[-3].string);
		      misc_FinishUserErrorReport();
		    }
		    string_StringFree(yyvsp[-3].string);
		    flag_SetFlagValue(dfg_FLAGS, flag, yyvsp[-1].number);
		  }
    break;

  case 188:
#line 837 "dfgparser.y"
    { SYMBOL s = symbol_Lookup(yyvsp[0].string);
		      if (s == 0) {
			misc_StartUserErrorReport();
			misc_UserErrorReport("\n Undefined symbol %s ", yyvsp[0].string);
			misc_UserErrorReport(" in precedence list.\n"); 
			misc_FinishUserErrorReport(); 
		      }
		      string_StringFree(yyvsp[0].string);
		      symbol_SetIncreasedOrdering(dfg_PRECEDENCE, s);
                      dfg_USERPRECEDENCE = list_Cons((POINTER)s, dfg_USERPRECEDENCE);
		    }
    break;

  case 189:
#line 849 "dfgparser.y"
    { SYMBOL s = symbol_Lookup(yyvsp[-4].string);
		      if (s == 0) {
			misc_StartUserErrorReport();
			misc_UserErrorReport("\n Undefined symbol %s", yyvsp[-4].string);
			misc_UserErrorReport("in precedence list.\n");
			misc_FinishUserErrorReport(); 
		      }
		      string_StringFree(yyvsp[-4].string);
		      symbol_SetIncreasedOrdering(dfg_PRECEDENCE, s);
                      dfg_USERPRECEDENCE = list_Cons((POINTER)s, dfg_USERPRECEDENCE);
		      symbol_SetWeight(s, yyvsp[-2].number);
		      if (yyvsp[-1].property != 0)
			symbol_AddProperty(s, yyvsp[-1].property);
		    }
    break;

  case 190:
#line 865 "dfgparser.y"
    { yyval.property = 0; /* left */ }
    break;

  case 191:
#line 867 "dfgparser.y"
    { if (yyvsp[0].string[1] != '\0' ||
			  (yyvsp[0].string[0]!='l' && yyvsp[0].string[0]!='m' && yyvsp[0].string[0]!='r')) {
		         misc_StartUserErrorReport();
			 misc_UserErrorReport("\n Invalid symbol status %s", yyvsp[0].string);
			 misc_UserErrorReport(" in precedence list.");
			 misc_FinishUserErrorReport();
		      }
		      switch (yyvsp[0].string[0]) {
		      case 'm': yyval.property = ORDMUL;   break;
		      case 'r': yyval.property = ORDRIGHT; break;
		      default:  yyval.property = 0;
		      }
		      string_StringFree(yyvsp[0].string);
		    }
    break;

  case 194:
#line 888 "dfgparser.y"
    { dfg_DeleteStringList(yyvsp[-2].list); }
    break;

  case 195:
#line 891 "dfgparser.y"
    { yyval.list = list_List(yyvsp[0].string); }
    break;

  case 196:
#line 892 "dfgparser.y"
    { yyval.list = list_Nconc(yyvsp[-2].list, list_List(yyvsp[0].string)); }
    break;


    }

/* Line 1016 of /opt/gnu//share/bison/yacc.c.  */
#line 2471 "dfgparser.c"

  yyvsp -= yylen;
  yyssp -= yylen;


#if YYDEBUG
  if (yydebug)
    {
      short *yyssp1 = yyss - 1;
      YYFPRINTF (stderr, "state stack now");
      while (yyssp1 != yyssp)
	YYFPRINTF (stderr, " %d", *++yyssp1);
      YYFPRINTF (stderr, "\n");
    }
#endif

  *++yyvsp = yyval;


  /* Now `shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*------------------------------------.
| yyerrlab -- here on detecting error |
`------------------------------------*/
yyerrlab:
  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if YYERROR_VERBOSE
      yyn = yypact[yystate];

      if (YYPACT_NINF < yyn && yyn < YYLAST)
	{
	  YYSIZE_T yysize = 0;
	  int yytype = YYTRANSLATE (yychar);
	  char *yymsg;
	  int yyx, yycount;

	  yycount = 0;
	  /* Start YYX at -YYN if negative to avoid negative indexes in
	     YYCHECK.  */
	  for (yyx = yyn < 0 ? -yyn : 0;
	       yyx < (int) (sizeof (yytname) / sizeof (char *)); yyx++)
	    if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR)
	      yysize += yystrlen (yytname[yyx]) + 15, yycount++;
	  yysize += yystrlen ("parse error, unexpected ") + 1;
	  yysize += yystrlen (yytname[yytype]);
	  yymsg = (char *) YYSTACK_ALLOC (yysize);
	  if (yymsg != 0)
	    {
	      char *yyp = yystpcpy (yymsg, "parse error, unexpected ");
	      yyp = yystpcpy (yyp, yytname[yytype]);

	      if (yycount < 5)
		{
		  yycount = 0;
		  for (yyx = yyn < 0 ? -yyn : 0;
		       yyx < (int) (sizeof (yytname) / sizeof (char *));
		       yyx++)
		    if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR)
		      {
			const char *yyq = ! yycount ? ", expecting " : " or ";
			yyp = yystpcpy (yyp, yyq);
			yyp = yystpcpy (yyp, yytname[yyx]);
			yycount++;
		      }
		}
	      yyerror (yymsg);
	      YYSTACK_FREE (yymsg);
	    }
	  else
	    yyerror ("parse error; also virtual memory exhausted");
	}
      else
#endif /* YYERROR_VERBOSE */
	yyerror ("parse error");
    }
  goto yyerrlab1;


/*----------------------------------------------------.
| yyerrlab1 -- error raised explicitly by an action.  |
`----------------------------------------------------*/
yyerrlab1:
  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
	 error, discard it.  */

      /* Return failure if at end of input.  */
      if (yychar == YYEOF)
        {
	  /* Pop the error token.  */
          YYPOPSTACK;
	  /* Pop the rest of the stack.  */
	  while (yyssp > yyss)
	    {
	      YYDPRINTF ((stderr, "Error: popping "));
	      YYDSYMPRINT ((stderr,
			    yystos[*yyssp],
			    *yyvsp));
	      YYDPRINTF ((stderr, "\n"));
	      yydestruct (yystos[*yyssp], *yyvsp);
	      YYPOPSTACK;
	    }
	  YYABORT;
        }

      YYDPRINTF ((stderr, "Discarding token %d (%s).\n",
		  yychar, yytname[yychar1]));
      yydestruct (yychar1, yylval);
      yychar = YYEMPTY;
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */

  yyerrstatus = 3;	/* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (yyn != YYPACT_NINF)
	{
	  yyn += YYTERROR;
	  if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
	    {
	      yyn = yytable[yyn];
	      if (0 < yyn)
		break;
	    }
	}

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
	YYABORT;

      YYDPRINTF ((stderr, "Error: popping "));
      YYDSYMPRINT ((stderr,
		    yystos[*yyssp], *yyvsp));
      YYDPRINTF ((stderr, "\n"));

      yydestruct (yystos[yystate], *yyvsp);
      yyvsp--;
      yystate = *--yyssp;


#if YYDEBUG
      if (yydebug)
	{
	  short *yyssp1 = yyss - 1;
	  YYFPRINTF (stderr, "Error: state stack now");
	  while (yyssp1 != yyssp)
	    YYFPRINTF (stderr, " %d", *++yyssp1);
	  YYFPRINTF (stderr, "\n");
	}
#endif
    }

  if (yyn == YYFINAL)
    YYACCEPT;

  YYDPRINTF ((stderr, "Shifting error token, "));

  *++yyvsp = yylval;


  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#ifndef yyoverflow
/*----------------------------------------------.
| yyoverflowlab -- parser overflow comes here.  |
`----------------------------------------------*/
yyoverflowlab:
  yyerror ("parser stack overflow");
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
  return yyresult;
}


#line 895 "dfgparser.y"


void yyerror(const char *s)
{
  misc_StartUserErrorReport();
  misc_UserErrorReport("\n Line %i: %s\n", dfg_LINENUMBER, s);
  misc_FinishUserErrorReport();
}

static void dfg_Init(FILE* Input, FLAGSTORE Flags, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   The input file stream for the parser, a flag store and
           a precedence.
  RETURNS: Nothing.
  EFFECT:  The parser and scanner are initialized.
           The parser will use the flag store and the precedence
	   to memorize the settings from the input file.
***************************************************************/
{
  extern FILE* dfg_in;  /* declared in dfgscanner */

  dfg_in               = Input;
  dfg_LINENUMBER       = 1;
  dfg_IGNORETEXT       = TRUE;
  dfg_AXIOMLIST        = list_Nil();
  dfg_CONJECLIST       = list_Nil();
  dfg_SORTDECLLIST     = list_Nil();
  dfg_USERPRECEDENCE   = list_Nil();
  dfg_AXCLAUSES        = list_Nil();
  dfg_CONCLAUSES       = list_Nil();
  dfg_PROOFLIST        = list_Nil();
  dfg_TERMLIST         = list_Nil();
  dfg_SYMBOLLIST       = list_Nil();
  dfg_VARLIST          = list_Nil();
  dfg_VARDECL          = FALSE;
  dfg_IGNORE           = FALSE;
  dfg_FLAGS            = Flags;
  dfg_PRECEDENCE       = Precedence;
  dfg_DESC.name        = (char*) NULL;
  dfg_DESC.author      = (char*) NULL;
  dfg_DESC.version     = (char*) NULL;
  dfg_DESC.logic       = (char*) NULL;
  dfg_DESC.status      = DFG_UNKNOWNSTATE;
  dfg_DESC.description = (char*) NULL;
  dfg_DESC.date        = (char*) NULL;
}


void dfg_Free(void)
/**************************************************************
  INPUT:   None.
  RETURNS: Nothing.
  EFFECT:  Frees memory used by the problem description.
***************************************************************/
{
  if (dfg_DESC.name != NULL)
    string_StringFree(dfg_DESC.name);
  if (dfg_DESC.author != NULL)
    string_StringFree(dfg_DESC.author);
  if (dfg_DESC.version != NULL)
    string_StringFree(dfg_DESC.version);
  if (dfg_DESC.logic != NULL)
    string_StringFree(dfg_DESC.logic);
  if (dfg_DESC.description != NULL)
    string_StringFree(dfg_DESC.description);
  if(dfg_DESC.date != NULL)
    string_StringFree(dfg_DESC.date);
}

const char* dfg_ProblemName(void)
/**************************************************************
  INPUT:   None.
  RETURNS: The problem's name from the description section.
***************************************************************/
{
  return dfg_DESC.name;
}

const char* dfg_ProblemAuthor(void)
/**************************************************************
  INPUT:   None.
  RETURNS: The problem's author from the description section.
***************************************************************/
{
  return dfg_DESC.author;
}

const char* dfg_ProblemVersion(void)
/**************************************************************
  INPUT:   None.
  RETURNS: The problem's version from the description section.
***************************************************************/
{
  return dfg_DESC.version;
}

const char* dfg_ProblemLogic(void)
/**************************************************************
  INPUT:   None.
  RETURNS: The problem's logic from the description section.
***************************************************************/
{
  return dfg_DESC.logic;
}

DFG_STATE dfg_ProblemStatus(void)
/**************************************************************
  INPUT:   None.
  RETURNS: The problem's status from the description section.
***************************************************************/
{
  return dfg_DESC.status;
}

const char* dfg_ProblemStatusString(void)
/**************************************************************
  INPUT:   None.
  RETURNS: The string representation of the problem's status.
***************************************************************/
{
  const char* result = "";

  switch (dfg_DESC.status) {
  case DFG_SATISFIABLE:
    result = "satisfiable"; break;
  case DFG_UNSATISFIABLE:
    result = "unsatisfiable"; break;
  case DFG_UNKNOWNSTATE:
    result = "unknown"; break;
  default:
    misc_StartErrorReport();
    misc_ErrorReport("\n In dfg_ProblemStatusString: Invalid status.\n");
    misc_FinishErrorReport();
  }
  return result;
}

const char* dfg_ProblemDescription(void)
/**************************************************************
  INPUT:   None.
  RETURNS: The problem's description from the description section.
***************************************************************/
{
  return dfg_DESC.description;
}

const char* dfg_ProblemDate(void)
/**************************************************************
  INPUT:   None.
  RETURNS: The problem's date from the description section.
***************************************************************/
{
  return dfg_DESC.date;
}

void dfg_FPrintDescription(FILE* File)
/**************************************************************
  INPUT:   A file stream.
  RETURNS: Nothing.
  EFFECT:  The description section from the input file
           is printed to 'File'. You must call the parser first
           before calling this function.
***************************************************************/
{
  fputs("list_of_descriptions.\n  name(", File);
  if (dfg_DESC.name != NULL)
    fputs(dfg_DESC.name, File);
  else
    fputs("{* *}", File);
  fputs(").\n  author(", File);
  if (dfg_DESC.author != NULL)
    fputs(dfg_DESC.author, File);
  else
    fputs("{* *}", File);
  fputs(").\n", File);
  if (dfg_DESC.version != NULL) {
    fputs("  version(", File);
    fputs(dfg_DESC.version, File);
    fputs(").\n", File);
  }
  if (dfg_DESC.logic != NULL) {
    fputs("  logic(", File);
    fputs(dfg_DESC.logic, File);
    fputs(").\n", File);
  }
  fputs("  status(", File);
  fputs(dfg_ProblemStatusString(), File);
  fputs(").\n  description(", File);
  if (dfg_DESC.description != NULL)
    fputs(dfg_DESC.description, File);
  else
    fputs("{* *}", File);
  fputs(").\n", File);
  if (dfg_DESC.date != NULL) {
    fputs("  date(", File);
    fputs(dfg_DESC.date, File);
    fputs(").\n", File);
  }
  fputs("end_of_list.", File);
}


LIST dfg_DFGParser(FILE* File, FLAGSTORE Flags, PRECEDENCE Precedence,
		   LIST* Axioms, LIST* Conjectures, LIST* SortDecl,
		   LIST* UserDefinedPrecedence)
/**************************************************************
  INPUT:   The input file containing clauses or formulae in DFG syntax,
           a flag store and a precedence used to memorize settings
	   from the file.
           Axioms, Conjectures, SortDecl and UserDefinedPrecedence are
	   pointers to lists used as return values.
  RETURNS: The list of clauses from File.
  EFFECT:  Reads formulae and clauses from the input file.
           The axioms, conjectures, sort declarations and user-defined
	   precedences are appended to the respective lists, the lists
	   are not deleted!
	   All lists except the clause list contain pairs
	   (label, term), where <label> may be NULL, if no
	   label was specified for that term.
	   <UserDefinedPrecedence> contains symbols sorted by decreasing
	   precedence. This list will only be changed, if the precedence
	   is explicitly defined in the input file. This can be done
	   by the 'set_precedence' flag in the SPASS settings list in
	   the DFG input file.
  CAUTION: The weight of the clauses is not correct and the literals
           are not oriented!
***************************************************************/
{
  LIST  scan, tupel;
  TERM  clauseTerm;
  NAT   bottom;

  dfg_Init(File, Flags, Precedence);  /* Initialize the parser and scanner */
  bottom = stack_Bottom();
  dfg_parse();          /* Invoke the parser */
#ifdef CHECK 
  if (!stack_Empty(bottom)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In dfg_DFGParser: Stack not empty!\n");
    misc_FinishErrorReport();
  }
#endif
  dfg_SymCleanUp();

  /* Remove clause labels and create clauses from the terms */
  for (scan = dfg_AXCLAUSES; !list_Empty(scan); scan = list_Cdr(scan)) {
    tupel = list_Car(scan);
    clauseTerm = list_PairSecond(tupel);
    list_Rplaca(scan, dfg_CreateClauseFromTerm(clauseTerm,TRUE, Flags, Precedence));
    if (list_PairFirst(tupel) != NULL)        /* Label is defined */
      string_StringFree(list_PairFirst(tupel));  /* Delete the label */
    list_PairFree(tupel);
  }
  /* Since dfg_CreateClauseFromTerm() returns NULL for trivial tautologies */
  /* we now delete those NULL pointers from the clause list.               */
  dfg_AXCLAUSES = list_PointerDeleteElement(dfg_AXCLAUSES, NULL);
  for (scan = dfg_CONCLAUSES; !list_Empty(scan); scan = list_Cdr(scan)) {
    tupel = list_Car(scan);
    clauseTerm = list_PairSecond(tupel);
    list_Rplaca(scan, dfg_CreateClauseFromTerm(clauseTerm,FALSE, Flags, Precedence));
    if (list_PairFirst(tupel) != NULL)        /* Label is defined */
      string_StringFree(list_PairFirst(tupel));  /* Delete the label */
    list_PairFree(tupel);
  }
  /* Since dfg_CreateClauseFromTerm() returns NULL for trivial tautologies */
  /* we now delete those NULL pointers from the clause list.               */
  dfg_CONCLAUSES = list_PointerDeleteElement(dfg_CONCLAUSES, NULL);

  /* Delete the proof list */
  dfg_DeleteProofList(dfg_PROOFLIST);

  /* Delete the list_of_terms, since it'll be ignored */
  term_DeleteTermList(dfg_TERMLIST);

  scan = list_Nconc(dfg_AXCLAUSES, dfg_CONCLAUSES);

  *Axioms      = list_Nconc(*Axioms, dfg_AXIOMLIST);
  *Conjectures = list_Nconc(*Conjectures, dfg_CONJECLIST);
  *SortDecl    = list_Nconc(*SortDecl, dfg_SORTDECLLIST);
  list_NReverse(dfg_USERPRECEDENCE);
  *UserDefinedPrecedence = list_Nconc(*UserDefinedPrecedence, dfg_USERPRECEDENCE);

  return scan;
}


LIST dfg_ProofParser(FILE* File, FLAGSTORE Flags, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   The input file containing clauses in DFG syntax,
           a flag store and a precedence used to memorize settings
           from the file.
  RETURNS: A list of tuples (label,clause,justificationlist,splitlevel,origin)
           representing a proof.
  EFFECT:  Reads inputs clauses with labels and the proof lists
           from the input file.
           The elements of the list are lists with five items.
	   1. the label (a string) of a clause,
	   2. the clause in TERM format,
           3. the list of justification labels (strings, too),
           4. the split level of the clause,
           5. the origin of the clause (RULE struct from clause.h).
	   Note that the justification list is empty for input
	   clauses.
***************************************************************/
{
  LIST  scan, tupel;
  TERM  term;
  NAT   bottom;

  dfg_Init(File, Flags, Precedence);  /* Initialize the parser and scanner */
  bottom = stack_Bottom();
  dfg_parse();          /* Invoke the parser */
#ifdef CHECK 
  if (!stack_Empty(bottom)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In dfg_ProofParser: Stack not empty!\n");
    misc_FinishErrorReport();
  }
#endif

  dfg_SymCleanUp();

  /* Build the union of axiom and conjecture clauses */
  dfg_AXCLAUSES  = list_Nconc(dfg_AXCLAUSES, dfg_CONCLAUSES);
  dfg_CONCLAUSES = list_Nil();
  for (scan = dfg_AXCLAUSES; !list_Empty(scan); scan = list_Cdr(scan)) {
    tupel = list_Car(scan);
    term  = list_PairSecond(tupel);
    if (list_PairFirst(tupel) == NULL) {
      /* Ignore input clauses without label */
      term_Delete(term);
      list_PairFree(tupel);
      list_Rplaca(scan, NULL);
    } else
      /* Expand the pair to a tuple                            */
      /* (label,clause,justificationlist, split level, origin) */
      /* For input clauses the justificationlist is empty.     */
      /* Input clauses have split level 0.                     */
      list_Rplacd(tupel, list_Cons(term,list_Cons(list_Nil(),list_Cons(0, list_List((POINTER)INPUT)))));
  }
  /* Now delete the list items without labels */
  dfg_AXCLAUSES = list_PointerDeleteElement(dfg_AXCLAUSES, NULL);

  /* Delete the formula lists */
  dfg_DeleteFormulaPairList(dfg_AXIOMLIST);
  dfg_DeleteFormulaPairList(dfg_CONJECLIST);
  /* Delete the list of sort declarations */
  dfg_DeleteFormulaPairList(dfg_SORTDECLLIST);
  /* Delete the list_of_terms, since it'll be ignored */
  term_DeleteTermList(dfg_TERMLIST);

  /* Finally append the proof list to the list of input clauses with labels */
  dfg_PROOFLIST = list_NReverse(dfg_PROOFLIST);
  dfg_AXCLAUSES = list_Nconc(dfg_AXCLAUSES, dfg_PROOFLIST);

  return dfg_AXCLAUSES;
}


LIST dfg_TermParser(FILE* File, FLAGSTORE Flags, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   The input file containing a list of terms in DFG syntax,
           a flag store and a precedence used to memorize settings
	   from the file.
  RETURNS: The list of terms from <File>.
  EFFECT:  Reads terms from the list_of_terms from the input file.
***************************************************************/
{
  NAT bottom;
  
  dfg_Init(File, Flags, Precedence);   /* Initialize the parser and scanner */
  bottom = stack_Bottom();
  dfg_parse();          /* Invoke the parser */
#ifdef CHECK 
  if (!stack_Empty(bottom)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In dfg_TermParser: Stack not empty!\n");
    misc_FinishErrorReport();
  }
#endif

  dfg_SymCleanUp();

  /* Delete the clause lists */
  dfg_DeleteFormulaPairList(dfg_AXCLAUSES);
  dfg_DeleteFormulaPairList(dfg_CONCLAUSES);
  /* Delete the formula lists */
  dfg_DeleteFormulaPairList(dfg_AXIOMLIST);
  dfg_DeleteFormulaPairList(dfg_CONJECLIST);
  /* Delete the proof list */
  dfg_DeleteProofList(dfg_PROOFLIST);
  /* Delete the list of sort declarations */
  dfg_DeleteFormulaPairList(dfg_SORTDECLLIST);

  return dfg_TERMLIST;
}


void dfg_DeleteFormulaPairList(LIST FormulaPairs)
/**************************************************************
  INPUT:   A list of pairs (label, formula).
  RETURNS: Nothing.
  EFFECT:  The list and the pairs with their strings and terms
           are completely deleted.
***************************************************************/
{
  LIST pair;

  for ( ; !list_Empty(FormulaPairs); FormulaPairs = list_Pop(FormulaPairs)) {
    pair = list_Car(FormulaPairs);  /* (label, term) */
    term_Delete(list_PairSecond(pair));
    if (list_PairFirst(pair) != NULL)
      string_StringFree(list_PairFirst(pair));  /* Free the label */
    list_PairFree(pair);
  }
}

void dfg_StripLabelsFromList(LIST FormulaPairs)
/**************************************************************
  INPUT:   A list of pairs (label, formula).
  RETURNS: Nothing.
  EFFECT:  The pairs are replaced by the respective formula
           and the pairs with their label strings are deleted.
***************************************************************/
{
  LIST pair, scan;

  for (scan = FormulaPairs; !list_Empty(scan); scan = list_Cdr(scan)) {
    pair = list_Car(scan);  /* (label, term) */
    list_Rplaca(scan, list_PairSecond(pair));
    if (list_PairFirst(pair) != NULL)
      string_StringFree(list_PairFirst(pair));  /* Free the label */
    list_PairFree(pair);
  }
}

void dfg_DeleteProofList(LIST Proof)
/**************************************************************
  INPUT:   A list of tuples (label, term, justificationlist, split level).
  RETURNS: Nothing.
  EFFECT:  All memory used by the proof list is freed.
           The labels must NOT be NULL entries!
***************************************************************/
{
  /* Delete the proof list */
  for ( ; !list_Empty(Proof); Proof = list_Pop(Proof)) {
    LIST tupel = list_Car(Proof);
    string_StringFree(list_First(tupel));
    term_Delete(list_Second(tupel));
    dfg_DeleteStringList(list_Third(tupel));
    list_Delete(tupel);
  }
}

/**************************************************************/
/* Static Functions                                           */
/**************************************************************/

static void dfg_SymbolDecl(int SymbolType, char* Name, int Arity)
/**************************************************************
  INPUT:   The type of a symbol, the name, and the arity.
  RETURNS: Nothing.
  EFFECT:  This function handles the declaration of symbols.
           If <Arity> is -2, it means that the arity of the symbol
	   was not specified, if it is -1 the symbol is declared
	   with arbitrary arity. User defined symbols with arbitrary
           arity are not allowed.
	   The <Name> is deleted.
***************************************************************/
{
  NAT    arity, length;
  SYMBOL symbol;

  switch (Arity) {
  case -2: /* not specified */
    arity = 0;
    break;
  case -1:
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n Line %u: symbols with arbitrary arity are not allowed.\n",
	    dfg_LINENUMBER);
    misc_FinishUserErrorReport();
  default:
    arity = Arity;
}

  /* Pay attention to the maximum symbol name length */
  length = strlen(Name);
  if (length >= symbol__SYMBOLMAXLEN)
    Name[symbol__SYMBOLMAXLEN-1] = '\0';

  /* Check if this symbol was declared earlier */
  symbol = symbol_Lookup(Name);
  if (symbol != 0) {
    /* Symbol was declared before */
    /* Check if the old and new symbol type are equal */
    if ((SymbolType == DFG_FUNC && !symbol_IsFunction(symbol)) ||
	(SymbolType == DFG_PRDICAT && !symbol_IsPredicate(symbol)) ||
	((SymbolType == DFG_OPERAT || SymbolType == DFG_QUANTIF) && 
	 !symbol_IsJunctor(symbol))) {
      misc_StartUserErrorReport();
      misc_UserErrorReport("\n Line %u: symbol %s was already declared as ",
	      dfg_LINENUMBER, Name);
      switch (symbol_Type(symbol)) {
      case symbol_CONSTANT:
      case symbol_FUNCTION:
	misc_UserErrorReport("function.\n"); break;
      case symbol_PREDICATE:
	misc_UserErrorReport("predicate.\n"); break;
      case symbol_JUNCTOR:
	misc_UserErrorReport("junctor.\n"); break;
      default:
	misc_UserErrorReport("unknown type.\n");
      }
      misc_FinishUserErrorReport();
    }
    /* Now check the old and new arity if specified */
    if (Arity != -2 && Arity != symbol_Arity(symbol)) {
      misc_StartUserErrorReport();
      misc_UserErrorReport("\n Line %u: symbol %s was already declared with arity %d\n",
			   dfg_LINENUMBER, Name, symbol_Arity(symbol));
      misc_FinishUserErrorReport();
    }
  } else {
    /* Symbol was not declared before */
    switch (SymbolType) {
    case DFG_FUNC:
      symbol = symbol_CreateFunction(Name, arity, symbol_STATLEX,dfg_PRECEDENCE);
      break;
    case DFG_PRDICAT:
      symbol = symbol_CreatePredicate(Name, arity,symbol_STATLEX,dfg_PRECEDENCE);
      break;
    default:
      symbol = symbol_CreateJunctor(Name, arity, symbol_STATLEX, dfg_PRECEDENCE);
    }
    if (Arity == -2)
      /* Arity wasn't specified so check the arity for each occurrence */
      dfg_SymAdd(symbol);
  }

  if (length >= symbol__SYMBOLMAXLEN) {
    /* To avoid a memory error restore the old string length */
    Name[symbol__SYMBOLMAXLEN-1] = ' ';  /* Something != '\0' */
  }
  string_StringFree(Name);  /* Name was copied */
}


static SYMBOL dfg_Symbol(char* Name, NAT Arity)
/**************************************************************
  INPUT:   The name of a symbol and the actual arity of the symbol.
  RETURNS: The corresponding SYMBOL.
  EFFECT:  This function checks if the <Name> was declared as
           symbol or variable. If not, an error message is printed
	   to stderr.
	   The <Name> is deleted.
***************************************************************/
{
  SYMBOL symbol;
  char   old;
  NAT    length;

  old = ' ';  /* Just to avoid a compiler warning */
  /* Pay attention to the maximum symbol name length */
  length = strlen(Name);
  if (length >= symbol__SYMBOLMAXLEN) {
    old = Name[symbol__SYMBOLMAXLEN-1];
    Name[symbol__SYMBOLMAXLEN-1] = '\0';
  }

  symbol = symbol_Lookup(Name);
  if (length >= symbol__SYMBOLMAXLEN) {
    /* To avoid a memory error restore the old string */
    Name[symbol__SYMBOLMAXLEN-1] = old;
  }
  if (symbol != 0) {
    string_StringFree(Name);
    dfg_SymCheck(symbol, Arity); /* Check the arity */
  } else {
    /* Variable */
    if (Arity > 0) {
      misc_StartUserErrorReport();
      misc_UserErrorReport("\n Line %d: Undefined symbol %s.\n",dfg_LINENUMBER,Name);
      misc_FinishUserErrorReport();
    }
    symbol = dfg_VarLookup(Name);
  }
  return symbol;
}


TERM dfg_CreateQuantifier(SYMBOL Symbol, LIST VarTermList, TERM Term)
/**************************************************************
  INPUT:   A quantifier symbol, a list possibly containing sorts,
           and a term.
  RETURNS: The created quantifier term..
***************************************************************/
{
  LIST varlist, sortlist, scan;
  TERM helpterm;

  /* First collect the variable symbols in varlist and the sorts in sortlist */
  varlist = sortlist = list_Nil();
  for ( ; !list_Empty(VarTermList); VarTermList = list_Pop(VarTermList)) {
    helpterm = list_Car(VarTermList);
    if (term_IsVariable(helpterm)) {
      varlist = list_Nconc(varlist, list_List((POINTER)term_TopSymbol(helpterm)));
      term_Delete(helpterm);
    } else {
      SYMBOL var = term_TopSymbol(term_FirstArgument(helpterm));
      varlist  = list_Nconc(varlist, list_List((POINTER)var));
      sortlist = list_Nconc(sortlist, list_List(helpterm));
    }
  }

  varlist = list_PointerDeleteDuplicates(varlist);
  /* Now create terms from the variables */
  for (scan = varlist; !list_Empty(scan); scan = list_Cdr(scan))
    list_Rplaca(scan, term_Create((SYMBOL)list_Car(scan), list_Nil()));

  if (!list_Empty(sortlist)) {
    if (symbol_Equal(fol_All(), Symbol)) {
      /* The conjunction of all sortterms implies the Term */
      if (symbol_Equal(fol_Or(), term_TopSymbol(Term))) {
	/* Special treatment if <Term> is a term with "or" like */
	/* in clauses: add all sort terms negated to the args    */
	/* of the "or" */
	for (scan = sortlist; !list_Empty(scan); scan = list_Cdr(scan))
	  /* Negate the sort terms */
	  list_Rplaca(scan, term_Create(fol_Not(), list_List(list_Car(scan))));
	sortlist = list_Nconc(sortlist, term_ArgumentList(Term));
	term_RplacArgumentList(Term, sortlist);
      } else {
	/* No "or" term, so build the implication term */
	if (list_Empty(list_Cdr(sortlist))) {
	  /* Only one sort term */
	  list_Rplacd(sortlist, list_List(Term));
	  Term = term_Create(fol_Implies(), sortlist);
	} else {
	  /* More than one sort term */
	  helpterm = term_Create(fol_And(), sortlist);
	  Term = term_Create(fol_Implies(), list_Cons(helpterm, list_List(Term)));
	}
      }
    } else if (symbol_Equal(fol_Exist(), Symbol)) {
      /* Quantify the conjunction of all sort terms and <Term> */
      if (symbol_Equal(fol_And(), term_TopSymbol(Term))) {
	/* Special treatment if <Term> has an "and" as top symbol: */
	/* just add the sort terms to the args of the "and".       */
	sortlist = list_Nconc(sortlist, term_ArgumentList(Term));
	term_RplacArgumentList(Term, sortlist);
      } else {
	sortlist = list_Nconc(sortlist, list_List(Term));
	Term = term_Create(fol_And(), sortlist);
      }
    }
  }
  helpterm = fol_CreateQuantifier(Symbol, varlist, list_List(Term));
  return helpterm;
}


CLAUSE dfg_CreateClauseFromTerm(TERM Clause, BOOL IsAxiom, FLAGSTORE Flags,
				PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause term, a boolean value, a flag store and a precedence.
  RETURNS: The clause term converted to a CLAUSE or NULL if the
           clause is a trivial tautology (the clause contains
	   the literal "true" or "not(false)" ).
  EFFECT:  This function converts a clause stored as term into an
           EARL clause structure.
	   If 'IsAxiom' is TRUE the clause is treated as axiom
	   clause else as conjecture clause.
           The function deletes the literals "false" and "not(true)"
           if they occur in <Clause>.
	   The contents of the flag store and the precedence are changed
	   because the parser read flag and precedence settings from
	   
  MEMORY:  The clause term is deleted.
***************************************************************/
{
  LIST   literals, scan;
  TERM   literal;
  CLAUSE result;
  
  if (term_TopSymbol(Clause) == fol_All()) {
    /* Remove and free the quantifier and the OR term */
    literals = term_ArgumentList(term_SecondArgument(Clause));
    term_RplacArgumentList(term_SecondArgument(Clause), list_Nil());
  } else {
    /* Remove and free the OR term */
    literals = term_ArgumentList(Clause);
    term_RplacArgumentList(Clause, list_Nil());
  }
  term_Delete(Clause);

  for (scan = literals; !list_Empty(scan); scan = list_Cdr(scan)) {
    literal = (TERM) list_Car(scan);
    if (symbol_IsPredicate(term_TopSymbol(literal))) {  /* Positive literal */
      if (fol_IsTrue(literal)) {
	/* Clause is a tautology */
	list_PointerDeleteElement(literals, NULL);
	/* Remove possible NULL elements to avoid a crash in term_Delete */
	term_DeleteTermList(literals);
	return (CLAUSE) NULL;
      } else if (fol_IsFalse(literal)) {
	/* Ignore this literal */
	term_Delete(literal);
	list_Rplaca(scan, NULL); /* Mark the actual list element */
      }
    } else {
      /* Found a negative literal */
      TERM atom = term_FirstArgument(literal);
      if (fol_IsFalse(atom)) {
	/* Clause is a tautology */
	list_PointerDeleteElement(literals, NULL);
	/* Remove possible NULL elements to avoid a crash in term_Delete */
	term_DeleteTermList(literals);
	return (CLAUSE) NULL;
      } else if (fol_IsTrue(atom)) {
	/* Ignore this literal */
	term_Delete(literal);
	list_Rplaca(literals, NULL); /* Mark the actual list element */
      }
    }
  }

  literals = list_PointerDeleteElement(literals, NULL);
  /* Remove the special literals treated above from the list */
  result = clause_CreateFromLiterals(literals, FALSE, !IsAxiom, FALSE, Flags, Precedence);
  /* Don't create sorts! */
  list_Delete(literals);

  return result;
}


static void dfg_SubSort(char* Name1, char* Name2)
/**************************************************************
  INPUT:   Two sort symbol names.
  RETURNS: Nothing.
  EFFECT:  This functions adds the formula
           forall([U], implies(Name1(U), Name2(U)))
	   to the list of axiom formulas. Both <Name1> and <Name2>
	   are deleted.
***************************************************************/
{
  SYMBOL s1, s2;
  TERM   varterm, t1, t2, term;

  s1 = dfg_Symbol(Name1, 1);   /* Should be unary predicates */
  s2 = dfg_Symbol(Name2, 1);
  if (!symbol_IsPredicate(s1)) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n Line %d: Symbol is not a sort predicate.\n", dfg_LINENUMBER);
    misc_FinishUserErrorReport();
  }
  if (!symbol_IsPredicate(s2)) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n Line %d: Symbol is not a sort predicate.\n", dfg_LINENUMBER);
    misc_FinishUserErrorReport();
  }

  varterm = term_Create(symbol_CreateStandardVariable(), list_Nil());
  symbol_ResetStandardVarCounter();
  
  t1   = term_Create(s1, list_List(varterm));
  t2   = term_Create(s2, list_List(term_Copy(varterm)));
  term = term_Create(fol_Implies(), list_Cons(t1, list_List(t2)));
  term = fol_CreateQuantifier(fol_All(), list_List(term_Copy(varterm)),
			      list_List(term));
  dfg_SORTDECLLIST = list_Nconc(dfg_SORTDECLLIST, list_List(list_PairCreate(NULL,term)));
}


static void dfg_SymbolGenerated(SYMBOL SortPredicate, BOOL FreelyGenerated,
				LIST GeneratedBy)
/**************************************************************
  INPUT:   A sort predicate, a boolean flag, and a list of function
           symbol names.
  RETURNS: Nothing.
  EFFECT:  This function stores the information that the <SortPredicate>
           is generated by the function symbols from the <GeneratedBy>
           list. The list contains only symbol names!
	   The <SortPredicate> AND the symbols from the list get
           the property GENERATED. Additionally the symbols get
	   the property FREELY, if the flag <FreelyGenerated> is TRUE.
***************************************************************/
{
  SYMBOL symbol;
  LIST   scan;

  if (!symbol_IsPredicate(SortPredicate)) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n Line %d: Symbol is not a sort predicate.\n", dfg_LINENUMBER);
    misc_FinishUserErrorReport();
  }
  /* First reset the old information */
  symbol_RemoveProperty(SortPredicate, GENERATED);
  symbol_RemoveProperty(SortPredicate, FREELY);
  list_Delete(symbol_GeneratedBy(SortPredicate));
  /* Now set the new information */
  symbol_AddProperty(SortPredicate, GENERATED);
  if (FreelyGenerated)
    symbol_AddProperty(SortPredicate, FREELY);
  for (scan = GeneratedBy; !list_Empty(scan); scan = list_Cdr(scan)) {
    symbol = symbol_Lookup(list_Car(scan));
    if (symbol == 0) {
      misc_StartUserErrorReport();
      misc_UserErrorReport("\n Line %d: undefined symbol %s.\n", dfg_LINENUMBER,
			   (char*)list_Car(scan));
      misc_FinishUserErrorReport();
    } else if (!symbol_IsFunction(symbol)) { /* must be function or constant */
      misc_StartUserErrorReport();
      misc_UserErrorReport("\n Line %d: Symbol is not a function.\n", dfg_LINENUMBER);
      misc_FinishUserErrorReport();
    }
    string_StringFree(list_Car(scan));
    list_Rplaca(scan, (POINTER)symbol);  /* change the name list to a symbol list */
    /* Set GENERATED properties for generating symbols */
    symbol_AddProperty(symbol, GENERATED);
    if (FreelyGenerated)
      symbol_AddProperty(symbol, FREELY);
  }
  symbol_SetGeneratedBy(SortPredicate, GeneratedBy);
}


/**************************************************************/
/* Functions for the Symbol Table                             */
/**************************************************************/

typedef struct {
  SYMBOL symbol;
  BOOL   valid;
  int    arity;
} DFG_SYMENTRY, *DFG_SYM;

static __inline__ DFG_SYM dfg_SymCreate(void)
{
  return (DFG_SYM) memory_Malloc(sizeof(DFG_SYMENTRY));
}

static __inline__ void dfg_SymFree(DFG_SYM Entry)
{
  memory_Free(Entry, sizeof(DFG_SYMENTRY));
}


static void dfg_SymAdd(SYMBOL Symbol)
/**************************************************************
  INPUT:   A symbol.
  RETURNS: Nothing.
  EFFECT:  This function adds 'Symbol' to the symbol list.
           The arity of these symbols will be checked every time
	   the symbol occurs.
***************************************************************/
{
  DFG_SYM newEntry = dfg_SymCreate();
  newEntry->symbol = Symbol;
  newEntry->valid  = FALSE;
  newEntry->arity  = 0;
  dfg_SYMBOLLIST = list_Cons(newEntry, dfg_SYMBOLLIST);
}


static void dfg_SymCheck(SYMBOL Symbol, NAT Arity)
/**************************************************************
  INPUT:   A symbol and the current arity of this symbol.
  RETURNS: Nothing.
  EFFECT:  This function compares the previous arity of 'Symbol'
           with the actual 'Arity'. If these values differ
	   the symbol's arity is set to arbitrary.
	   The arity of symbols whose arity was specified in
	   the symbol declaration section is checked and a warning
	   is printed to stderr in case of differences.
***************************************************************/
{
  LIST scan = dfg_SYMBOLLIST;
  while (!list_Empty(scan)) {
    DFG_SYM actEntry = (DFG_SYM) list_Car(scan);
    if (actEntry->symbol == Symbol) {
      if (actEntry->valid) {
	if (actEntry->arity != Arity) {
	  misc_StartUserErrorReport();
	  misc_UserErrorReport("\n Line %u:", dfg_LINENUMBER);
	  misc_UserErrorReport(" The actual arity %u", Arity);
	  misc_UserErrorReport(" of symbol %s differs", symbol_Name(Symbol));
	  misc_UserErrorReport(" from the previous arity %u.\n", actEntry->arity);
	  misc_FinishUserErrorReport();
	}
      } else {
	/* Not valid => first time */
	actEntry->arity = Arity;
	actEntry->valid = TRUE;
      }
      return;
    }
    scan = list_Cdr(scan);
  }

  /* Symbol isn't in SymbolList, so its arity was specified.        */
  /* Check if the specified arity corresponds with the actual arity */
  if (symbol_Arity(Symbol) != Arity) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n Line %u: Symbol %s was declared with arity %u.\n",
			 dfg_LINENUMBER, symbol_Name(Symbol), symbol_Arity(Symbol));
    misc_FinishUserErrorReport();
  }
}


static void dfg_SymCleanUp(void)
/**************************************************************
  INPUT:   None.
  RETURNS: Nothing.
  EFFECT:  This function corrects all symbols whose arity wasn't
           specified in the symbol declaration section but seem
	   to occur with always the same arity.
	   The memory for the symbol list is freed.
***************************************************************/
{
  while (!list_Empty(dfg_SYMBOLLIST)) {
    DFG_SYM actEntry  = (DFG_SYM) list_Car(dfg_SYMBOLLIST);
    SYMBOL  actSymbol = actEntry->symbol;

    if (actEntry->arity != symbol_Arity(actSymbol))
      symbol_SetArity(actSymbol, actEntry->arity);

    dfg_SymFree(actEntry);
    dfg_SYMBOLLIST = list_Pop(dfg_SYMBOLLIST);
  }
}


/**************************************************************/
/* Functions for the Variable Table                           */
/**************************************************************/
  
typedef struct {
  char*  name;
  SYMBOL symbol;
} DFG_VARENTRY, *DFG_VAR;

static __inline__ char* dfg_VarName(DFG_VAR Entry)
{
  return Entry->name;
}

static __inline__ SYMBOL dfg_VarSymbol(DFG_VAR Entry)
{
  return Entry->symbol;
}

static __inline__ DFG_VAR dfg_VarCreate(void)
{
  return (DFG_VAR) memory_Malloc(sizeof(DFG_VARENTRY));
}

static void dfg_VarFree(DFG_VAR Entry)
{
  string_StringFree(Entry->name);
  memory_Free(Entry, sizeof(DFG_VARENTRY));
}

static void dfg_VarStart(void)
{
  dfg_VARLIST = list_Push(list_Nil(), dfg_VARLIST);
  dfg_VARDECL = TRUE;
}

static void dfg_VarStop(void)
{
  dfg_VARDECL = FALSE;
}

static void dfg_VarBacktrack(void)
{
  list_DeleteWithElement(list_Top(dfg_VARLIST), (void (*)(POINTER)) dfg_VarFree);
  dfg_VARLIST = list_Pop(dfg_VARLIST);
}

static void dfg_VarCheck(void)
/* Should be called after a complete clause or formula was parsed */
{
  if (!list_Empty(dfg_VARLIST)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In dfg_VarCheck: List of variables should be empty!\n");
    misc_FinishErrorReport();
  }
  symbol_ResetStandardVarCounter();
}

static SYMBOL dfg_VarLookup(char* Name)
/**************************************************************
  INPUT:   A variable name.
  RETURNS: The corresponding variable symbol.
  EFFECT:  If the variable name was quantified before, the
           corresponding symbol is returned and the <Name> is freed.
	   If the variable name was not quantified, and <dfg_VARDECL>
	   is TRUE, a new variable is created, else an error
	   message is printed and the program exits.
***************************************************************/
{
  LIST   scan, scan2;
  SYMBOL symbol = symbol_Null();

  scan  = dfg_VARLIST;
  scan2 = list_Nil();
  while (!list_Empty(scan) && list_Empty(scan2)) {
    scan2 = list_Car(scan);
    while (!list_Empty(scan2) &&
	   (!string_Equal(dfg_VarName(list_Car(scan2)), Name)))
      scan2 = list_Cdr(scan2);
    scan = list_Cdr(scan);
  }

  if (!list_Empty(scan2)) {
    /* Found variable */
    string_StringFree(Name);
    symbol = dfg_VarSymbol(list_Car(scan2));
  } else {
    /* Variable not found */
    if (dfg_VARDECL) {
      DFG_VAR newEntry = dfg_VarCreate();
      newEntry->name   = Name;
      newEntry->symbol = symbol_CreateStandardVariable();
      /* Add <newentry> to the first list in dfg_VARLIST */
      list_Rplaca(dfg_VARLIST, list_Cons(newEntry,list_Car(dfg_VARLIST)));
      symbol = dfg_VarSymbol(newEntry);
    } else {
      misc_StartUserErrorReport();
      misc_UserErrorReport("\n Line %u: Free Variable %s.\n", dfg_LINENUMBER, Name);
      misc_FinishUserErrorReport();
    }
  }
  return symbol;
}

