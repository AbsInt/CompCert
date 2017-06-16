/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *         RECURSIVE PATH ORDERING WITH STATUS            * */
/* *                                                        * */
/* *  $Module:   RPOS                                       * */
/* *                                                        * */
/* *  Copyright (C) 1997, 1998 MPI fuer Informatik          * */
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

#ifndef _RPOS_
#define _RPOS_

#include "misc.h"
#include "term.h"
#include "order.h"
#include "context.h"

/**************************************************************/
/*  Function Prototypes                                       */
/**************************************************************/

BOOL       rpos_Equal(TERM, TERM);
ord_RESULT rpos_GreaterEqual(TERM, TERM);
ord_RESULT rpos_Compare(TERM, TERM);

BOOL       rpos_ContEqual(CONTEXT, TERM, CONTEXT, TERM);
ord_RESULT rpos_ContGreaterEqual(CONTEXT, TERM, CONTEXT, TERM);
ord_RESULT rpos_ContCompare(CONTEXT, TERM, CONTEXT, TERM);

/**************************************************************/
/*  Inline Functions                                          */
/**************************************************************/

static __inline__ BOOL rpos_Greater(TERM T1, TERM T2)
{
  return ord_IsGreaterThan(rpos_GreaterEqual(T1, T2));
}

static __inline__ BOOL rpos_ContGreater(CONTEXT C1, TERM T1,
					CONTEXT C2, TERM T2)
{
  return ord_IsGreaterThan(rpos_ContGreaterEqual(C1, T1, C2, T2));
}

#endif
