/****************************************************************************/
/* STDINC.H: standard include file for C programs.                          */
/*                                                                          */
/* Copyright (c) 1993 by Joshua E. Barnes, Honolulu, HI.                    */
/* It's free because it's yours.                                            */
/****************************************************************************/

/*
 * If not already loaded, include stdio.h.
 */

#ifndef FILE
#  include <stdio.h>
#endif

/*
 * STREAM: a tasteful replacement for FILE *.
 */

typedef FILE *stream;

/*
 * NULL: denotes a pointer to nothing.
 */

#ifndef NULL
#  define NULL 0
#endif

/*
 * GLOBAL: make something global when declared at file level; a workaround
 * for the Strict-Ref/Def-initialization model in ANSI C.  Predefine with
 * something innocuous (like a comment) to actually allocate the data.
 */

#ifndef global
#  define global extern
#endif

/*
 * LOCAL: make something local when declared at file level.
 */

#define local static

/*
 * PERMANENT: make data declared within a function static.
 */

#define permanent static

/*
 * BOOL, TRUE and FALSE: standard names for logical values.
 */

#ifndef TRUE
   typedef short int bool;
#  define FALSE 0
#  define TRUE  1
#endif

/*
 * STRING: for null-terminated character strings.
 */

typedef char *string;
// sm: this isn't a performance change, it's a boxing crankiness change
#define NULLCHR 0

/*
 * PROC, IPROC: pointers to procedures and integer-valued functions.
 */

typedef void (*proc)();
typedef int (*iproc)();

/*
 *  PI, etc.  --  mathematical constants
 */

#define   PI         3.14159265358979323846
#define   TWO_PI     6.28318530717958647693
#define   FOUR_PI   12.56637061435917295385
#define   HALF_PI    1.57079632679489661923
#define   FRTHRD_PI  4.18879020478639098462

/*
 *  ABS: returns the absolute value of its argument
 *  MAX: returns the argument with the highest value
 *  MIN: returns the argument with the lowest value
 */

#define   ABS(x)       (((x) < 0) ? -(x) : (x))
#define   MAX(x,y)     (((x) > (y)) ? (x) : (y))
#define   MIN(x,y)     (((x) < (y)) ? (x) : (y))


