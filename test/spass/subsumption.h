/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                     SUBSUMPTION                        * */
/* *                                                        * */
/* *  $Module:   SUBSUMPTION                                * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1997, 1999, 2000                  * */
/* *  MPI fuer Informatik                                   * */
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


#ifndef _SUBSUMPTION_
#define _SUBSUMPTION_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "misc.h"
#include "unify.h"
#include "component.h"
#include "vector.h"
#include "clause.h"

/**************************************************************/
/* Functions                                                 */
/**************************************************************/

#define subs__MAXLITS 100

static __inline__ int subs_NoException(void)
{
  return -1;
}

void subs_Init(void);
BOOL subs_ST(int, int, CLAUSE, CLAUSE);
BOOL subs_STMulti(CLAUSE, CLAUSE);
BOOL subs_STMultiExcept(CLAUSE, CLAUSE, int, int);
BOOL subs_Subsumes(CLAUSE, CLAUSE, int, int);
BOOL subs_SubsumesBasic(CLAUSE, CLAUSE, int, int);
BOOL subs_SubsumesWithSignature(CLAUSE, CLAUSE, BOOL, LIST*);
BOOL subs_Idc(CLAUSE, CLAUSE);
BOOL subs_IdcRes(CLAUSE, int, int);
BOOL subs_IdcEq(CLAUSE, CLAUSE);
BOOL subs_IdcEqMatch(CLAUSE, CLAUSE, SUBST);
BOOL subs_IdcEqMatchExcept(CLAUSE, int, CLAUSE, int, SUBST);

#endif

