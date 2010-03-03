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

#ifndef BISON_IAPARSER_H
# define BISON_IAPARSER_H

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




#ifndef YYSTYPE
#line 113 "iaparser.y"
typedef union {
  int       number;
  char*     string;
  SYMBOL    symbol;
  TERM      term;
  LIST      list;
} yystype;
/* Line 1281 of /opt/gnu//share/bison/yacc.c.  */
#line 80 "iaparser.h"
# define YYSTYPE yystype
#endif

extern YYSTYPE ia_lval;


#endif /* not BISON_IAPARSER_H */

