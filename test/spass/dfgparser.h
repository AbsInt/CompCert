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

#ifndef BISON_DFGPARSER_H
# define BISON_DFGPARSER_H

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
/* Line 1281 of /opt/gnu//share/bison/yacc.c.  */
#line 177 "dfgparser.h"
# define YYSTYPE yystype
#endif

extern YYSTYPE dfg_lval;


#endif /* not BISON_DFGPARSER_H */

