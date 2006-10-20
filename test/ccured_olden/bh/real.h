/****************************************************************************/
/* REAL.H: include file to support compile-time specification of precision  */
/* in floating-point calculations.  If the DOUBLEPREC symbol is defined to  */
/* the preprocessor, calculations are done in double precision; otherwise,  */
/* they may be done in single precision.                                    */
/*                                                                          */
/* Rationale: ANSI C enables programmers to write single-precision code,    */
/* but does not make it easy to change the precision of code at compile     */
/* time, since different functions names are used for floating and double   */
/* calculations.  This package introduces the keyword "real", which may be  */
/* either float or double, and defines functions which compute with         */
/* real-valued numbers.                                                     */
/*                                                                          */
/* Copyright (c) 1993 by Joshua E. Barnes, Honolulu, HI.                    */
/* It's free because it's yours.                                            */
/****************************************************************************/

/*
 * REAL, REALPTR: real-valued number, and pointer to same.
 */

#ifndef  DOUBLEPREC

typedef float real, *realptr;

#else

typedef double real, *realptr;

#endif

/*
 * RPROC: pointer to a real-valued function.  This prototype does
 * not specify the types of any arguments.
 */

typedef real (*rproc)();

/*
 * Include math.h to get prototypes for standard C math functions.
 */

#include <math.h>

/*
 * Real-valued library functions.  Most of these are actually supplied
 * by the standard C libraries.
 */

#ifndef  DOUBLEPREC

#  define rsqrt  sqrtf
#  define rsqr   fsqr
#  define rsin   sinf
#  define rcos   cosf
#  define rtan   tanf
#  define rasin  asinf
#  define racos  acosf
#  define ratan  atanf
#  define ratan2 atan2f
#  define rlog   logf
#  define rexp   expf
#  define rlog10 log10f
#  define rsinh  sinhf
#  define rcosh  coshf
#  define rtanh  tanhf
#  define rpow   powf
#  define rabs   fabsf
#  define rfloor floorf
#  define rceil  ceilf

/*
 * These functions are not part of the standard C libraries.
 */

float fsqr(float);			/* square function		    */

#else

#  define rsqrt  sqrt
#  define rsqr   sqr
#  define rsin   sin
#  define rcos   cos
#  define rtan   tan
#  define rasin  asin
#  define racos  acos
#  define ratan  atan
#  define ratan2 atan2
#  define rlog   log
#  define rexp   exp
#  define rlog10 log10
#  define rsinh  sinh
#  define rcosh  cosh
#  define rtanh  tanh
#  define rpow   pow
#  define rabs   fabs
#  define rfloor floor
#  define rceil  ceil

/*
 * These functions are not part of the standard C libraries.
 */

double sqr(double);			/* square function		    */

#endif
