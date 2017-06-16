/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                     SUBSTITUTION                       * */
/* *                                                        * */
/* *  $Module:      SUBSTITUTION                            * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1997, 1998, 1999, 2001            * */
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

#ifndef _SUBST_
#define _SUBST_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "term.h"
#include "symbol.h"
#include "list.h"

/**************************************************************/
/* Data Structures                                            */
/**************************************************************/

typedef struct subst {
  struct subst *next;
  SYMBOL dom;
  TERM   codomain;
} SUBST_NODE, *SUBST;


static __inline__ SUBST subst_Get(void)
{
  return (SUBST) memory_Malloc(sizeof(SUBST_NODE));
}

static __inline__ void subst_FreeOneNode(SUBST SL)
{
  memory_Free(SL, sizeof(SUBST_NODE));
}

/**************************************************************/
/* Include 'unify.h' after SUBST declaration.                 */
/**************************************************************/

#include "unify.h"

/**************************************************************/
/* Functions on Substitutions                                 */
/**************************************************************/

static __inline__ SUBST subst_Nil(void)
{
  return (SUBST)NULL;
}

static __inline__ BOOL subst_Exist(SUBST S)
{
  return S != subst_Nil();
}

static __inline__ BOOL subst_Empty(SUBST S)
{
  return S == subst_Nil();
}

static __inline__ SUBST subst_Next(SUBST S)
{
  return S->next;
}

static __inline__ void subst_SetNext(SUBST S, SUBST N)
{
  S->next = N;
}

static __inline__ SYMBOL subst_Dom(SUBST S)
{
  return S->dom;
}

static __inline__ TERM subst_Cod(SUBST S)
{
  return S->codomain;
}

static __inline__ SUBST subst_NUnion(SUBST S1,SUBST S2)
{
  SUBST Result;

  if (S1 == (SUBST)NULL)  
    return S2;        

  if (S2 == (SUBST)NULL) 
    return S1;

  Result = S1;

  for (; S1->next != (SUBST)NULL; S1 = S1->next);
            
  S1->next = S2;

  return Result; 
}


/**************************************************************/
/* Functions for Creation and Deletion                        */
/**************************************************************/

SUBST subst_Add(SYMBOL, TERM, SUBST);
void  subst_Delete(SUBST);
void  subst_Free(SUBST);

/**************************************************************/
/* Functions for Applying and Copying                         */
/**************************************************************/

TERM  subst_Term(SYMBOL, SUBST);
TERM  subst_Apply(SUBST, TERM);
SUBST subst_Merge(SUBST, SUBST);
SUBST subst_Compose(SUBST, SUBST);
SUBST subst_Copy(SUBST);
BOOL  subst_MatchTops(const CONTEXT, SUBST);
BOOL  subst_BindVar(SYMBOL,SUBST);

/**************************************************************/
/* Functions for Search of Unifiers                           */
/**************************************************************/

BOOL subst_Unify(CONTEXT, SUBST);
BOOL subst_IsShallow(SUBST);

/**************************************************************/
/* Functions for Search of Generalizations                    */
/**************************************************************/

BOOL  subst_Match(const CONTEXT, SUBST);

/**************************************************************/
/* Functions for Search of Instances                          */
/**************************************************************/

BOOL  subst_MatchReverse(const CONTEXT, SUBST);

/**************************************************************/
/* Functions for Search of Variations                         */
/**************************************************************/

BOOL  subst_Variation(const CONTEXT, SUBST);

/**************************************************************/
/* Functions for Computation of MSCGs                         */
/**************************************************************/

SUBST subst_ComGen(const CONTEXT, SUBST, SUBST*, SUBST*);

/**************************************************************/
/* Functions for Closing Bindings                             */
/**************************************************************/

void  subst_CloseVariables(const CONTEXT, SUBST);
SUBST subst_CloseOpenVariables(SUBST);

/**************************************************************/
/* Functions for Extracting Substitutions from Bindings       */
/**************************************************************/

void      subst_ExtractUnifier(const CONTEXT, SUBST*, const CONTEXT, SUBST*);
void      subst_ExtractUnifierCom(const CONTEXT, SUBST*);
SUBST     subst_ExtractMatcher(void);

/**************************************************************/
/* Functions for Debugging                                    */
/**************************************************************/

void  subst_Print(SUBST);

#endif


