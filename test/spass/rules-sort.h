/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *           INFERENCE RULES FOR SORTS                    * */
/* *                                                        * */
/* *  $Module:   SORTRULES                                  * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1997, 1999, 2000, 2001            * */
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

#ifndef _SORTRULES_
#define _SORTRULES_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "sort.h"
#include "unify.h"
#include "clause.h"
#include "flags.h"

/**************************************************************/
/* Functions                                                  */
/**************************************************************/        

LIST inf_ForwardSortResolution(CLAUSE, st_INDEX, SORTTHEORY, BOOL, FLAGSTORE,
			       PRECEDENCE);
LIST inf_BackwardSortResolution(CLAUSE, st_INDEX, SORTTHEORY, BOOL, FLAGSTORE,
				PRECEDENCE);
LIST inf_ForwardEmptySort(CLAUSE, st_INDEX, SORTTHEORY, BOOL, FLAGSTORE,
			  PRECEDENCE);
LIST inf_BackwardEmptySort(CLAUSE, st_INDEX, SORTTHEORY, BOOL, FLAGSTORE,
			   PRECEDENCE);
LIST inf_ForwardWeakening(CLAUSE, st_INDEX, SORTTHEORY, FLAGSTORE, PRECEDENCE);
LIST inf_BackwardWeakening(CLAUSE, st_INDEX, SORTTHEORY, FLAGSTORE, PRECEDENCE);
LIST inf_ForwardEmptySortPlusPlus(CLAUSE, st_INDEX, SORTTHEORY, FLAGSTORE,
				  PRECEDENCE);
LIST inf_BackwardEmptySortPlusPlus(CLAUSE, st_INDEX, SORTTHEORY, FLAGSTORE,
				   PRECEDENCE);

#endif
