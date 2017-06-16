/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                INFERENCE RULES                         * */
/* *                                                        * */
/* *  $Module:   INFRULES                                   * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1997, 1998, 1999, 2000, 2001      * */
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

#ifndef _INFRULES_
#define _INFRULES_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "search.h"
#include "rules-split.h"
#include "rules-sort.h"
#include "rules-ur.h"
#include "subst.h"
#include "unify.h"
#include "st.h"
#include "defs.h"

/**************************************************************/
/* Functions                                                  */
/**************************************************************/        

LIST inf_DerivableClauses(PROOFSEARCH, CLAUSE);

LIST inf_EqualityResolution(CLAUSE, BOOL, FLAGSTORE, PRECEDENCE);
LIST inf_EqualityFactoring(CLAUSE, FLAGSTORE, PRECEDENCE);

LIST inf_MergingParamodulation(CLAUSE, SHARED_INDEX, FLAGSTORE, PRECEDENCE);

LIST inf_GenSuperpositionLeft(CLAUSE,SHARED_INDEX,BOOL,BOOL,BOOL,FLAGSTORE, PRECEDENCE);
LIST inf_GenSuperpositionRight(CLAUSE,SHARED_INDEX,BOOL,BOOL,BOOL,FLAGSTORE, PRECEDENCE);

LIST inf_BoundedDepthUnitResolution(CLAUSE, SHARED_INDEX, BOOL, FLAGSTORE, PRECEDENCE);
LIST inf_UnitResolution(CLAUSE, SHARED_INDEX, BOOL, FLAGSTORE, PRECEDENCE);
LIST inf_GeneralResolution(CLAUSE, SHARED_INDEX, BOOL, BOOL, FLAGSTORE, PRECEDENCE);

BOOL inf_HyperLiteralIsBetter(LITERAL, NAT, LITERAL, NAT);
LIST inf_GeneralHyperResolution(CLAUSE, SHARED_INDEX, BOOL, FLAGSTORE, PRECEDENCE);

LIST inf_GeneralFactoring(CLAUSE, BOOL, BOOL, BOOL, FLAGSTORE, PRECEDENCE);

LIST inf_ApplyDefinition(PROOFSEARCH, CLAUSE, FLAGSTORE, PRECEDENCE);

/**************************************************************/
/* Inline Functions                                           */
/**************************************************************/        

static __inline__ LIST inf_Paramodulation(CLAUSE GivenClause,
					  SHARED_INDEX ShIndex,
					  FLAGSTORE Flags,
					  PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause, an Index, usually the WorkedOffIndex, a 
           flag store and a precedence.
  RETURNS: A list of clauses derivable from the GivenClause by 
           paramodulation wrt. the Index. 
  MEMORY:  A list of clauses is produced, where memory for the list
           and the clauses is allocated.
***************************************************************/
{ 
  return list_Nconc(inf_GenSuperpositionLeft(GivenClause, ShIndex, FALSE,
					     FALSE, FALSE, Flags, Precedence),
		    inf_GenSuperpositionRight(GivenClause, ShIndex, FALSE,
					      FALSE, FALSE, Flags, Precedence));
}

static __inline__ LIST inf_OrderedParamodulation(CLAUSE GivenClause,
						 SHARED_INDEX ShIndex,
						 FLAGSTORE Flags,
						 PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause, an Index, usually the WorkedOffIndex, a 
           flag store and a precedence.
  RETURNS: A list of clauses derivable from the Givenclause by 
           ordered paramodulation wrt. the Index. 
  MEMORY:  A list of clauses is produced, where memory for the list
           and the clauses is allocated.
***************************************************************/
{
  return list_Nconc(inf_GenSuperpositionLeft(GivenClause, ShIndex, TRUE,
					     FALSE, FALSE, Flags, Precedence),
		    inf_GenSuperpositionRight(GivenClause, ShIndex, TRUE,
					      FALSE, FALSE, Flags, Precedence));
}

static __inline__ LIST inf_SuperpositionLeft(CLAUSE GivenClause,
					     SHARED_INDEX ShIndex,
					     FLAGSTORE Flags,
					     PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause, an Index, usually the WorkedOffIndex, a
           flag store, and a precedence.
  RETURNS: A list of clauses derivable from the Givenclause by 
           superposition left wrt. the Index. 
  MEMORY:  A list of clauses is produced, where memory for the list
           and the clauses is allocated.
***************************************************************/
{
  return inf_GenSuperpositionLeft(GivenClause,ShIndex,TRUE,TRUE,FALSE,Flags, Precedence);
}

static __inline__ LIST inf_SuperpositionRight(CLAUSE GivenClause,
					      SHARED_INDEX ShIndex,
					      FLAGSTORE Flags,
					      PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause, an Index, usually the WorkedOffIndex, a 
           flag store and a precedence.
  RETURNS: A list of clauses derivable from the Givenclause by 
           superposition right wrt. the Index. 
  MEMORY:  A list of clauses is produced, where memory for the list
           and the clauses is allocated.
***************************************************************/
{
  return inf_GenSuperpositionRight(GivenClause,ShIndex,TRUE,TRUE,FALSE,Flags, Precedence);
}


#endif

