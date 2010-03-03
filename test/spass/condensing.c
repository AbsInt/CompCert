/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *               CONDENSATION OF CLAUSES                  * */
/* *                                                        * */
/* *  $Module:   CONDENSING                                 * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1997, 2001 MPI fuer Informatik    * */
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

#include "subsumption.h"
#include "misc.h"
#include "condensing.h"


LIST cond_CondFast(CLAUSE c)
/**********************************************************
  INPUT:   A clause c.
  RETURNS: A list with indexes with respect to c that can
           be deleted due to condensing.
  CAUTION: None.
***********************************************************/
{
  int    vec, i, j, k;
  LIST   indexlist;

  indexlist = list_Nil();
  vec       = vec_ActMax();
  
  for (i = 0; i < clause_Length(c); i++) {
    vec_Push((POINTER) i);
  }
  
  for (k = clause_Length(c) - 1; k >= 0; k--) {
    for (i = vec; i < vec_ActMax(); i++) {
      if ((int)vec_GetNth(i) != k) {
	cont_StartBinding();
	if (unify_Match(cont_LeftContext(),
			clause_GetLiteralTerm(c,k),
			clause_GetLiteralTerm(c,(int)vec_GetNth(i)))) {
	  cont_BackTrack();
	  for (j = vec; j < vec_ActMax(); j++) {
	    if (k == (int)vec_GetNth(j)) {
	      vec_Swap((vec_ActMax() -1) ,j);
	      j = vec_ActMax();
	    }
	  }
	  
	  if (subs_IdcRes(c,vec,(vec_ActMax() -1))) {
	    indexlist = list_Cons((POINTER)k,indexlist);
	    vec_Pop();
	  }
	  
	  i = vec_ActMax()+1;
	}
	else
	  cont_BackTrack();
      }
    }
  }
 
  vec_SetMax(vec);
  return indexlist;
}
