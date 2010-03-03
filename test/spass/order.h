/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *         INTERFACE FOR ALL ORDERING IMPLEMENTATIONS     * */
/* *                                                        * */
/* *  $Module:   ORDER                                      * */ 
/* *                                                        * */
/* *  Copyright (C) 1997, 2000, 2001 MPI fuer Informatik    * */
/* *                                                        * */
/* *  This program is free software; you can redistribute   * */
/* *  it and/or modify it under the terms of the GNU        * */
/* *  General Public License as published by the Free       * */
/* *  Software Foundation; either version 2 of the License, * */
/* *  or (at your option) any later version.                * */
/* *                                                        * */
/* *  This program is distributed in the hope that it will  * */
/* *  be useful, but WITHOUT ANY WARRANTY; without even     * */
/* *  the implied warranty of MERCHANTABILITY or FITNESS    * */
/* *  FOR A PARTICULAR PURPOSE.  See the GNU General Public * */
/* *  License for more details.                             * */
/* *                                                        * */
/* *  You should have received a copy of the GNU General    * */
/* *  Public License along with this program; if not, write * */
/* *  to the Free Software Foundation, Inc., 59 Temple      * */
/* *  Place, Suite 330, Boston, MA  02111-1307  USA         * */
/* *                                                        * */
/* *                                                        * */
/* $Revision: 21527 $                                        * */
/* $State$                                            * */
/* $Date: 2005-04-24 21:10:28 -0700 (Sun, 24 Apr 2005) $                             * */
/* $Author: duraid $                                       * */
/* *                                                        * */
/* *             Contact:                                   * */
/* *             Christoph Weidenbach                       * */
/* *             MPI fuer Informatik                        * */
/* *             Stuhlsatzenhausweg 85                      * */
/* *             66123 Saarbruecken                         * */
/* *             Email: weidenb@mpi-sb.mpg.de               * */
/* *             Germany                                    * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/


/* $RCSfile$ */

#ifndef _ORDER_
#define _ORDER_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "term.h"
#include "context.h"
#include "flags.h"
#include "symbol.h"

/**************************************************************/
/* TYPES and GLOBAL VARIABLES                                 */
/**************************************************************/

typedef enum { ord_UNCOMPARABLE,
	       ord_SMALLER_THAN,
	       ord_EQUAL,
	       ord_GREATER_THAN } ord_RESULT;

/* This array is used to count variable occurrences in two terms. */
/* It may be used by any available ordering.                     */
extern NAT ord_VARCOUNT[symbol__MAXSTANDARDVAR][2];

/* A precedence is needed in almost every ordering function. */
/* For performance reasons it is stored in a global variable, */
/* instead of passing it to all those functions, which are   */
/* often recursive. Nevertheless this variable must not be   */
/* set externally!                                           */
extern PRECEDENCE ord_PRECEDENCE;

/**************************************************************/
/*  INLINE FUNCTIONS                                          */
/**************************************************************/

static __inline__ ord_RESULT ord_Uncomparable(void)
{
  return ord_UNCOMPARABLE;
}

static __inline__ ord_RESULT ord_Equal(void)
{
  return ord_EQUAL;
}

static __inline__ ord_RESULT ord_GreaterThan(void)
{
  return ord_GREATER_THAN;
}

static __inline__ ord_RESULT ord_SmallerThan(void)
{
  return ord_SMALLER_THAN;
}

static __inline__ BOOL ord_IsGreaterThan(ord_RESULT Res)
{
  return ord_GREATER_THAN == Res;
}

static __inline__ BOOL ord_IsNotGreaterThan(ord_RESULT Res)
{
  return ord_GREATER_THAN != Res;
}

static __inline__ BOOL ord_IsSmallerThan(ord_RESULT Res)
{
  return ord_SMALLER_THAN == Res;
}

static __inline__ BOOL ord_IsNotSmallerThan(ord_RESULT Res)
{
  return ord_SMALLER_THAN != Res;
}

static __inline__ BOOL ord_IsEqual(ord_RESULT Res)
{
  return ord_EQUAL == Res;
}

static __inline__ BOOL ord_IsUncomparable(ord_RESULT Res)
{
  return ord_UNCOMPARABLE == Res;
}



/**************************************************************/
/*  FUNCTIONS                                                 */
/**************************************************************/

ord_RESULT ord_Not(ord_RESULT);
ord_RESULT ord_Compare(TERM, TERM, FLAGSTORE, PRECEDENCE);
ord_RESULT ord_ContCompare(CONTEXT, TERM, CONTEXT, TERM, FLAGSTORE, PRECEDENCE);
BOOL       ord_CompareEqual(TERM, TERM, FLAGSTORE);
BOOL       ord_ContGreater(CONTEXT, TERM, CONTEXT, TERM, FLAGSTORE, PRECEDENCE);
ord_RESULT ord_LiteralCompare(TERM,BOOL,TERM,BOOL,BOOL, FLAGSTORE, PRECEDENCE);
void       ord_Print(ord_RESULT);

#endif
