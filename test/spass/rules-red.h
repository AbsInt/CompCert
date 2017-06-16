/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                REDUCTION RULES                         * */
/* *                                                        * */
/* *  $Module:   REDRULES                                   * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1997, 1998, 1999, 2000            * */
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

#ifndef _REDRULES_
#define _REDRULES_

#include "sort.h"
#include "subsumption.h"
#include "condensing.h"
#include "search.h"
#include "rules-split.h"
#include "rules-inf.h"
#include "doc-proof.h"
#include "clock.h"
#include "closure.h"

/**************************************************************/
/* Constants                                                  */
/**************************************************************/

extern const NAT red_USABLE;
extern const NAT red_WORKEDOFF;
extern const NAT red_ALL;


/**************************************************************/
/* Functions                                                  */
/**************************************************************/

static __inline__ BOOL red_WorkedOffMode(NAT Mode)
{
  return (Mode == red_WORKEDOFF || Mode == red_ALL);
}

static __inline__ BOOL red_OnlyWorkedOffMode(NAT Mode)
{
  return (Mode == red_WORKEDOFF);
}

static __inline__ BOOL red_UsableMode(NAT Mode)
{
  return (Mode == red_USABLE || Mode == red_ALL);
}

static __inline__ BOOL red_AllMode(NAT Mode)
{
  return (Mode == red_ALL);
}


void   red_Init(void);        


LIST   red_CompleteReductionOnDerivedClauses(PROOFSEARCH, LIST, NAT, int, NAT, int*);
CLAUSE red_ReductionOnDerivedClause(PROOFSEARCH, CLAUSE, NAT);
CLAUSE red_CompleteReductionOnDerivedClause(PROOFSEARCH, CLAUSE, NAT);
LIST   red_BackReduction(PROOFSEARCH, CLAUSE, NAT);
LIST   red_SatUnit(PROOFSEARCH, LIST);
LIST   red_SatInput(PROOFSEARCH);
LIST   red_ReduceInput(PROOFSEARCH, LIST);
BOOL   red_ClauseDeletion(SORTTHEORY, CLAUSE, FLAGSTORE, PRECEDENCE);


void   red_CheckSplitSubsumptionCondition(PROOFSEARCH);


#endif
