/* A Bison parser, made from iaparser.y, by GNU bison 1.75.  */

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
#define yyparse ia_parse
#define yylex   ia_lex
#define yyerror ia_error
#define yylval  ia_lval
#define yychar  ia_char
#define yydebug ia_debug
#define yynerrs ia_nerrs


/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
     IA_AND = 258,
     IA_EQUAL = 259,
     IA_EQUIV = 260,
     IA_EXISTS = 261,
     IA_FALSE = 262,
     IA_FORALL = 263,
     IA_IMPLIED = 264,
     IA_IMPLIES = 265,
     IA_NOT = 266,
     IA_OR = 267,
     IA_PROVE = 268,
     IA_TRUE = 269,
     IA_NUM = 270,
     IA_ID = 271
   };
#endif
#define IA_AND 258
#define IA_EQUAL 259
#define IA_EQUIV 260
#define IA_EXISTS 261
#define IA_FALSE 262
#define IA_FORALL 263
#define IA_IMPLIED 264
#define IA_IMPLIES 265
#define IA_NOT 266
#define IA_OR 267
#define IA_PROVE 268
#define IA_TRUE 269
#define IA_NUM 270
#define IA_ID 271




/* Copy the first part of user declarations.  */
#line 48 "iaparser.y"


#include "flags.h"
#include "ia.h"
#include "symbol.h"
#include "term.h"
#include "foldfg.h"
#include "clause.h"

extern NAT dfg_LINENUMBER;    /* Defined in dfgparser.y */
LIST       ia_PROOFREQUEST;   /* A pair! */
FLAGSTORE  ia_FLAGS;

void yyerror(const char*);
int  yylex(void);		/* Defined in iascanner.l */

static SYMBOL ia_Symbol(char*, NAT);
static TERM   ia_CreateQuantifier(SYMBOL, LIST, TERM);

static __inline__ void  ia_StringFree(char* String)
{
  memory_Free(String, sizeof(char)*(strlen(String)+1));
}

static __inline__ TERM ia_TermCreate(char* Name, LIST Arguments)
/* Look up the symbol, check its arity and create the term */
{
  return term_Create(ia_Symbol(Name,list_Length(Arguments)), Arguments);
}

/**************************************************************/
/* Functions to check the arity of symbols                    */
/**************************************************************/

static void ia_SymCheck(SYMBOL, NAT);

/**************************************************************/
/* Functions that handle variable names                       */
/**************************************************************/

/* List of quantified variables in the current input formula. */
/* This list is used to find symbols that by mistake weren't  */
/* declared in the symbol declaration section                 */
/* --> free variables                                         */
/* This is a list of lists, since each time a quantifier is   */
/* reached, a new list is added to the global list.           */
static LIST ia_VARLIST;
static BOOL ia_VARDECL;

static void   ia_VarStart(void);
static void   ia_VarStop(void);
static void   ia_VarBacktrack(void);
static void   ia_VarCheck(void);
static SYMBOL ia_VarLookup(char*);

#define YY_INPUT(buf,result,max_size) \
{ \
  int c = getc(ia_in); \
  result = (c == EOF) ? YY_NULL : (buf[0] = c, 1); \
}

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
#line 113 "iaparser.y"
typedef union {
  int       number;
  char*     string;
  SYMBOL    symbol;
  TERM      term;
  LIST      list;
} yystype;
/* Line 193 of /opt/gnu//share/bison/yacc.c.  */
#line 187 "iaparser.c"
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
#line 208 "iaparser.c"

#if ! defined (yyoverflow) || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

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
#define YYLAST   83

/* YYNTOKENS -- Number of terminals. */
#define YYNTOKENS  23
/* YYNNTS -- Number of nonterminals. */
#define YYNNTS  16
/* YYNRULES -- Number of rules. */
#define YYNRULES  36
/* YYNRULES -- Number of states. */
#define YYNSTATES  77

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   271

#define YYTRANSLATE(X) \
  ((unsigned)(X) <= YYMAXUTOK ? yytranslate[X] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const unsigned char yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
      17,    19,     2,     2,    18,     2,    20,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,    21,     2,    22,     2,     2,     2,     2,     2,     2,
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
      15,    16
};

#if YYDEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const unsigned char yyprhs[] =
{
       0,     0,     3,     4,    14,    16,    20,    22,    24,    26,
      31,    38,    43,    48,    49,    50,    61,    62,    63,    74,
      76,    78,    80,    82,    84,    86,    88,    90,    92,    94,
      96,   100,   102,   107,   110,   114,   116
};

/* YYRHS -- A `-1'-separated list of the rules' RHS. */
static const yysigned_char yyrhs[] =
{
      24,     0,    -1,    -1,    13,    17,    26,    18,    37,    18,
      15,    19,    20,    -1,    26,    -1,    25,    18,    26,    -1,
      34,    -1,    14,    -1,     7,    -1,    11,    17,    26,    19,
      -1,    31,    17,    26,    18,    26,    19,    -1,    32,    17,
      25,    19,    -1,    34,    17,    25,    19,    -1,    -1,    -1,
      33,    17,    21,    27,    35,    28,    22,    18,    26,    19,
      -1,    -1,    -1,    34,    17,    21,    29,    35,    30,    22,
      18,    26,    19,    -1,     4,    -1,     5,    -1,     9,    -1,
      10,    -1,     3,    -1,    12,    -1,     6,    -1,     8,    -1,
      16,    -1,    15,    -1,    36,    -1,    35,    18,    36,    -1,
      34,    -1,    34,    17,    34,    19,    -1,    21,    22,    -1,
      21,    38,    22,    -1,    34,    -1,    38,    18,    34,    -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const unsigned char yyrline[] =
{
       0,   136,   136,   137,   149,   150,   153,   154,   155,   156,
     158,   160,   162,   164,   165,   164,   170,   171,   170,   179,
     180,   181,   182,   185,   186,   189,   190,   193,   194,   197,
     198,   201,   211,   232,   233,   236,   237
};
#endif

#if YYDEBUG || YYERROR_VERBOSE
/* YYTNME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals. */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "IA_AND", "IA_EQUAL", "IA_EQUIV", 
  "IA_EXISTS", "IA_FALSE", "IA_FORALL", "IA_IMPLIED", "IA_IMPLIES", 
  "IA_NOT", "IA_OR", "IA_PROVE", "IA_TRUE", "IA_NUM", "IA_ID", "'('", 
  "','", "')'", "'.'", "'['", "']'", "$accept", "proofrequest", 
  "termlist", "term", "@1", "@2", "@3", "@4", "binsymbol", "nsymbol", 
  "quantsymbol", "id", "qtermlist", "qterm", "labellistopt", "labellist", 0
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[YYLEX-NUM] -- Internal token number corresponding to
   token YYLEX-NUM.  */
static const unsigned short yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,    40,    44,    41,
      46,    91,    93
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const unsigned char yyr1[] =
{
       0,    23,    24,    24,    25,    25,    26,    26,    26,    26,
      26,    26,    26,    27,    28,    26,    29,    30,    26,    31,
      31,    31,    31,    32,    32,    33,    33,    34,    34,    35,
      35,    36,    36,    37,    37,    38,    38
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const unsigned char yyr2[] =
{
       0,     2,     0,     9,     1,     3,     1,     1,     1,     4,
       6,     4,     4,     0,     0,    10,     0,     0,    10,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       3,     1,     4,     2,     3,     1,     3
};

/* YYDEFACT[STATE-NAME] -- Default rule to reduce with in state
   STATE-NUM when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const unsigned char yydefact[] =
{
       2,     0,     0,     0,     1,    23,    19,    20,    25,     8,
      26,    21,    22,     0,    24,     7,    28,    27,     0,     0,
       0,     0,     6,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     4,    13,    16,     0,     9,    33,
      35,     0,     0,     0,     0,    11,     0,     0,    12,     0,
      34,     0,     0,     5,    31,    14,    29,    17,    36,     0,
      10,     0,     0,     0,     0,     3,     0,    30,     0,     0,
      32,     0,     0,     0,     0,    15,    18
};

/* YYDEFGOTO[NTERM-NUM]. */
static const yysigned_char yydefgoto[] =
{
      -1,     2,    33,    34,    46,    63,    47,    64,    19,    20,
      21,    22,    55,    56,    31,    41
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -29
static const yysigned_char yypact[] =
{
     -12,    12,    35,     0,   -29,   -29,   -29,   -29,   -29,   -29,
     -29,   -29,   -29,    19,   -29,   -29,   -29,   -29,    20,    22,
      40,    41,    42,     0,    31,     0,     0,    43,    39,    18,
       8,    38,    44,     7,   -29,   -29,   -29,     9,   -29,   -29,
     -29,    -5,    46,     0,     0,   -29,    16,    16,   -29,    16,
     -29,    47,    48,   -29,    53,    45,   -29,    45,   -29,    51,
     -29,    16,    16,    50,    52,   -29,    54,   -29,    57,    58,
     -29,     0,     0,    59,    60,   -29,   -29
};

/* YYPGOTO[NTERM-NUM].  */
static const yysigned_char yypgoto[] =
{
     -29,   -29,    37,    -3,   -29,   -29,   -29,   -29,   -29,   -29,
     -29,   -28,    30,    21,   -29,   -29
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If zero, do what YYDEFACT says.
   If YYTABLE_NINF, parse error.  */
#define YYTABLE_NINF -1
static const unsigned char yytable[] =
{
      18,     1,    40,     5,     6,     7,     8,     9,    10,    11,
      12,    13,    14,    49,    15,    16,    17,    50,    54,    54,
      29,    58,    32,    16,    17,    44,    45,    44,    48,     3,
      39,    16,    17,    66,    54,     4,    23,    38,    24,    25,
      52,    53,     5,     6,     7,     8,     9,    10,    11,    12,
      13,    14,    30,    15,    16,    17,    42,    26,    27,    28,
      36,    51,    43,    62,    35,    37,    59,    60,    73,    74,
      61,    65,    68,    70,    69,    71,    72,    57,    75,    76,
       0,     0,     0,    67
};

static const yysigned_char yycheck[] =
{
       3,    13,    30,     3,     4,     5,     6,     7,     8,     9,
      10,    11,    12,    18,    14,    15,    16,    22,    46,    47,
      23,    49,    25,    15,    16,    18,    19,    18,    19,    17,
      22,    15,    16,    61,    62,     0,    17,    19,    18,    17,
      43,    44,     3,     4,     5,     6,     7,     8,     9,    10,
      11,    12,    21,    14,    15,    16,    18,    17,    17,    17,
      21,    15,    18,    18,    21,    28,    19,    19,    71,    72,
      17,    20,    22,    19,    22,    18,    18,    47,    19,    19,
      -1,    -1,    -1,    62
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const unsigned char yystos[] =
{
       0,    13,    24,    17,     0,     3,     4,     5,     6,     7,
       8,     9,    10,    11,    12,    14,    15,    16,    26,    31,
      32,    33,    34,    17,    18,    17,    17,    17,    17,    26,
      21,    37,    26,    25,    26,    21,    21,    25,    19,    22,
      34,    38,    18,    18,    18,    19,    27,    29,    19,    18,
      22,    15,    26,    26,    34,    35,    36,    35,    34,    19,
      19,    17,    18,    28,    30,    20,    34,    36,    22,    22,
      19,    18,    18,    26,    26,    19,    19
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
  /*(void) yyvalue;*/

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
#line 136 "iaparser.y"
    { YYABORT; }
    break;

  case 3:
#line 137 "iaparser.y"
    {
					  ia_VarCheck();
					  ia_PROOFREQUEST = list_PairCreate(yyvsp[-6].term,yyvsp[-4].list);
					  flag_SetFlagValue(ia_FLAGS,flag_TIMELIMIT,yyvsp[-2].number);
					  YYACCEPT;
                                        }
    break;

  case 4:
#line 149 "iaparser.y"
    { yyval.list = list_List(yyvsp[0].term); }
    break;

  case 5:
#line 150 "iaparser.y"
    { yyval.list = list_Nconc(yyvsp[-2].list, list_List(yyvsp[0].term)); }
    break;

  case 6:
#line 153 "iaparser.y"
    { yyval.term = ia_TermCreate(yyvsp[0].string, list_Nil()); }
    break;

  case 7:
#line 154 "iaparser.y"
    { yyval.term = term_Create(fol_True(),list_Nil()); }
    break;

  case 8:
#line 155 "iaparser.y"
    { yyval.term = term_Create(fol_False(),list_Nil()); }
    break;

  case 9:
#line 157 "iaparser.y"
    { yyval.term = term_Create(fol_Not(),list_List(yyvsp[-1].term)); }
    break;

  case 10:
#line 159 "iaparser.y"
    { yyval.term = term_Create(yyvsp[-5].symbol, list_Cons(yyvsp[-3].term, list_List(yyvsp[-1].term))); }
    break;

  case 11:
#line 161 "iaparser.y"
    { yyval.term = term_Create(yyvsp[-3].symbol, yyvsp[-1].list); }
    break;

  case 12:
#line 163 "iaparser.y"
    { yyval.term = ia_TermCreate(yyvsp[-3].string, yyvsp[-1].list); }
    break;

  case 13:
#line 164 "iaparser.y"
    { ia_VarStart(); }
    break;

  case 14:
#line 165 "iaparser.y"
    { ia_VarStop(); }
    break;

  case 15:
#line 167 "iaparser.y"
    { ia_VarBacktrack();
				  yyval.term = ia_CreateQuantifier(yyvsp[-9].symbol,yyvsp[-5].list,yyvsp[-1].term);
				}
    break;

  case 16:
#line 170 "iaparser.y"
    { ia_VarStart(); }
    break;

  case 17:
#line 171 "iaparser.y"
    { ia_VarStop(); }
    break;

  case 18:
#line 173 "iaparser.y"
    { misc_StartUserErrorReport();
				  misc_UserErrorReport("\n Line %d: SPASS can't handle the quantifier %s.\n", dfg_LINENUMBER, yyvsp[-9].string);
				  misc_FinishUserErrorReport();
				}
    break;

  case 19:
#line 179 "iaparser.y"
    { yyval.symbol = fol_Equality(); }
    break;

  case 20:
#line 180 "iaparser.y"
    { yyval.symbol = fol_Equiv();    }
    break;

  case 21:
#line 181 "iaparser.y"
    { yyval.symbol = fol_Implied();  }
    break;

  case 22:
#line 182 "iaparser.y"
    { yyval.symbol = fol_Implies();  }
    break;

  case 23:
#line 185 "iaparser.y"
    { yyval.symbol = fol_And(); }
    break;

  case 24:
#line 186 "iaparser.y"
    { yyval.symbol = fol_Or();  }
    break;

  case 25:
#line 189 "iaparser.y"
    { yyval.symbol = fol_Exist(); }
    break;

  case 26:
#line 190 "iaparser.y"
    { yyval.symbol = fol_All(); }
    break;

  case 27:
#line 193 "iaparser.y"
    { yyval.string = yyvsp[0].string; }
    break;

  case 28:
#line 194 "iaparser.y"
    { yyval.string = string_IntToString(yyvsp[0].number); }
    break;

  case 29:
#line 197 "iaparser.y"
    { yyval.list = list_List(yyvsp[0].term); }
    break;

  case 30:
#line 198 "iaparser.y"
    { yyval.list = list_Nconc(yyvsp[-2].list, list_List(yyvsp[0].term)); }
    break;

  case 31:
#line 201 "iaparser.y"
    { SYMBOL s = ia_Symbol(yyvsp[0].string,0);
					  if (!symbol_IsVariable(s)) {
					    misc_StartUserErrorReport();
					    misc_UserErrorReport("\n Line %d: %s",dfg_LINENUMBER,
								 symbol_Name(s));
					    misc_UserErrorReport(" is not a variable.\n");
					    misc_FinishUserErrorReport();
					  }
					  yyval.term = term_Create(s, list_Nil());
					}
    break;

  case 32:
#line 211 "iaparser.y"
    { SYMBOL p, v;
					  p = ia_Symbol(yyvsp[-3].string, 1);
					  if (!symbol_IsPredicate(p)) {
					    misc_StartUserErrorReport();
					    misc_UserErrorReport("\n Line %d: %s",dfg_LINENUMBER,
								 symbol_Name(p));
					    misc_UserErrorReport(" is not a predicate.\n");
					    misc_FinishUserErrorReport();
					  }
					  v = ia_Symbol(yyvsp[-1].string, 0);
					  if (!symbol_IsVariable(v)) {
					    misc_StartUserErrorReport();
					    misc_UserErrorReport("\n Line %d: %s",dfg_LINENUMBER,
								 symbol_Name(v));
					    misc_UserErrorReport(" is not a variable.\n");
					    misc_FinishUserErrorReport();
					  }
					  yyval.term = term_Create(p, list_List(term_Create(v,list_Nil())));
					}
    break;

  case 33:
#line 232 "iaparser.y"
    { yyval.list = list_Nil(); }
    break;

  case 34:
#line 233 "iaparser.y"
    { yyval.list = yyvsp[-1].list; }
    break;

  case 35:
#line 236 "iaparser.y"
    { yyval.list = list_List(yyvsp[0].string); }
    break;

  case 36:
#line 237 "iaparser.y"
    { yyval.list = list_Nconc(yyvsp[-2].list, list_List(yyvsp[0].string)); }
    break;


    }

/* Line 1016 of /opt/gnu//share/bison/yacc.c.  */
#line 1290 "iaparser.c"

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


#line 240 "iaparser.y"



void yyerror(const char *s)
{
  misc_StartUserErrorReport();
  misc_UserErrorReport("\n Line %i: %s\n", dfg_LINENUMBER, s);
  misc_FinishUserErrorReport();

}

LIST ia_GetNextRequest(FILE* Input, FLAGSTORE Flags)
/**************************************************************
  INPUT:   An input file containing one proof request from KIV.
  RETURNS: The proof request as pair (formula, labellist),
           list_Nil(), if EOF was reached.
  EFFECT:  Reads ONE proof request from the file.
           <Input> may also be a UNIX pipe.
***************************************************************/
{
  extern FILE* ia_in;  /* defined in kivscanner */

  ia_in           = Input;
  ia_PROOFREQUEST = list_Nil();
  ia_FLAGS        = Flags;
  ia_parse();
  
  return ia_PROOFREQUEST;
}


/**************************************************************/
/* Static Functions                                           */
/**************************************************************/

static SYMBOL ia_Symbol(char* Name, NAT Arity)
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

  symbol = symbol_Lookup(Name);
  if (symbol != 0) {
    ia_StringFree(Name);
    ia_SymCheck(symbol, Arity); /* Check the arity */
  } else {
    /* Variable */
    if (Arity > 0) {
      misc_StartUserErrorReport();
      misc_UserErrorReport("\n Line %d: Undefined symbol %s.\n",dfg_LINENUMBER,Name);
      misc_FinishUserErrorReport();
    }
    symbol = ia_VarLookup(Name);
  }
  return symbol;
}


static TERM ia_CreateQuantifier(SYMBOL Symbol, LIST VarTermList, TERM Term)
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


/**************************************************************/
/* Functions for the Symbol Table                             */
/**************************************************************/

static void ia_SymCheck(SYMBOL Symbol, NAT Arity)
/**************************************************************
  INPUT:   A symbol and the current arity of this symbol.
  RETURNS: Nothing.
  EFFECT:  This function compares the previous arity of 'Symbol'
           with the actual 'Arity'. If these values differ
	   a warning is printed to stderr and the program exits.
***************************************************************/
{
  /* Check if the specified arity corresponds with the actual arity */
  if (symbol_Arity(Symbol) != symbol_ArbitraryArity() &&
      symbol_Arity(Symbol) != Arity) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n Line %u: Symbol %s", dfg_LINENUMBER, symbol_Name(Symbol));
    misc_UserErrorReport(" was declared with arity %u.\n", symbol_Arity(Symbol));
    misc_FinishUserErrorReport();
  }
}


/**************************************************************/
/* Functions for the Variable Table                           */
/**************************************************************/
  
typedef struct {
  char*  name;
  SYMBOL symbol;
} IA_VARENTRY, *IA_VAR;

static __inline__ char* ia_VarName(IA_VAR Entry)
{
  return Entry->name;
}

static __inline__ SYMBOL ia_VarSymbol(IA_VAR Entry)
{
  return Entry->symbol;
}

static __inline__ IA_VAR ia_VarCreate(void)
{
  return (IA_VAR) memory_Malloc(sizeof(IA_VARENTRY));
}

static void ia_VarFree(IA_VAR Entry)
{
  ia_StringFree(Entry->name);
  memory_Free(Entry, sizeof(IA_VARENTRY));
}

static void ia_VarStart(void)
{
  ia_VARLIST = list_Push(list_Nil(), ia_VARLIST);
  ia_VARDECL = TRUE;
}

static void ia_VarStop(void)
{
  ia_VARDECL = FALSE;
}

static void ia_VarBacktrack(void)
{
  list_DeleteWithElement(list_Top(ia_VARLIST), (void (*)(POINTER)) ia_VarFree);
  ia_VARLIST = list_Pop(ia_VARLIST);
}

static void ia_VarCheck(void)
/* Should be called after a complete clause or formula was parsed */
{
  if (!list_Empty(ia_VARLIST)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In ia_VarCheck: List of variables should be empty!\n");
    misc_FinishErrorReport();
  }
  symbol_ResetStandardVarCounter();
}

static SYMBOL ia_VarLookup(char* Name)
/**************************************************************
  INPUT:   A variable name.
  RETURNS: The corresponding variable symbol.
  EFFECT:  If the variable name was quantified before, the
           corresponding symbol is returned and the <Name> is freed.
	   If the variable name was not quantified, and <ia_VARDECL>
	   is TRUE, a new variable is created, else an error
	   message is printed and the program exits.
***************************************************************/
{
  LIST   scan, scan2;
  SYMBOL symbol;

  symbol = symbol_Null();

  scan  = ia_VARLIST;
  scan2 = list_Nil();
  while (!list_Empty(scan) && list_Empty(scan2)) {
    scan2 = list_Car(scan);
    while (!list_Empty(scan2) &&
	   !string_Equal(ia_VarName(list_Car(scan2)), Name))
      scan2 = list_Cdr(scan2);
    scan = list_Cdr(scan);
  }

  if (!list_Empty(scan2)) {
    /* Found variable */
    ia_StringFree(Name);
    symbol = ia_VarSymbol(list_Car(scan2));
  } else {
    /* Variable not found */
    if (ia_VARDECL) {
      IA_VAR newEntry = ia_VarCreate();
      newEntry->name   = Name;
      newEntry->symbol = symbol_CreateStandardVariable();
      /* Add <newentry> to the first list in ia_VARLIST */
      list_Rplaca(ia_VARLIST, list_Cons(newEntry,list_Car(ia_VARLIST)));
      symbol = ia_VarSymbol(newEntry);
    } else {
      misc_StartUserErrorReport();
      misc_UserErrorReport("\n Line %u: Free Variable %s.\n", dfg_LINENUMBER, Name);
      misc_FinishUserErrorReport();
    }
  }
  return symbol;
}

