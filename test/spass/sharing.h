/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                  STRUCTURE SHARING                     * */
/* *                                                        * */
/* *  $Module:   SHARING                                    * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1997, 1998, 2000, 2001            * */
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

#ifndef _SHARING_
#define _SHARING_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "term.h"
#include "st.h"

/**************************************************************/
/* Data Structures and Constants                              */
/**************************************************************/

/* Symbol Tables; constants are just positive    */
/* integers and variables negative integers.     */
/* For constants and vars is a special symbol    */
/* table available, containing the  sharing      */
/* info, i.e. a POINTER to the term structure, if */
/* the symbol is already inserted in the sharing */
/* structure, a NULL Pointer else.               */
  
typedef TERM VARTABLE[symbol__MAXVARIABLES];

typedef TERM CONSTTABLE[symbol__MAXSIGNATURE];

typedef struct {
  st_INDEX   index;
  VARTABLE   vartable;
  CONSTTABLE consttable;
  NAT        stampId;
} SHARED_INDEX_NODE, *SHARED_INDEX;

/**************************************************************/
/* Inline Functions                                           */
/**************************************************************/

static __inline__ st_INDEX sharing_Index(SHARED_INDEX ShIndex)
{
  return ShIndex->index;
}

static __inline__ void sharing_SetIndex(SHARED_INDEX ShIndex, st_INDEX ST)
{
  ShIndex->index = ST;
}

static __inline__ const TERM* sharing_Vartable(SHARED_INDEX ShIndex)
{
  return ShIndex->vartable;
}

static __inline__ const TERM* sharing_Consttable(SHARED_INDEX ShIndex)
{
  return ShIndex->consttable;
}

static __inline__ NAT sharing_StampID(SHARED_INDEX ShIndex)
{
  return ShIndex->stampId;
}

static __inline__ void sharing_SetStampID(SHARED_INDEX ShIndex, NAT Stamp)
{
  ShIndex->stampId = Stamp;
}

static __inline__ TERM sharing_VartableEntry(SHARED_INDEX ShIndex, NAT Index)
{
  return ShIndex->vartable[Index];
}

static __inline__ void sharing_SetVartableEntry(SHARED_INDEX ShIndex,
						NAT Index, TERM Term)
{
  ShIndex->vartable[Index] = Term;
}

static __inline__ TERM sharing_ConsttableEntry(SHARED_INDEX ShIndex,
					       NAT Index)
{
  return ShIndex->consttable[Index];
}

static __inline__ void sharing_SetConsttableEntry(SHARED_INDEX ShIndex,
						 NAT Index, TERM Term)
{
  ShIndex->consttable[Index] = Term;
}

static __inline__ TERM sharing_GetVarFromSymbol(SYMBOL S, SHARED_INDEX ShIndex)
{
  return sharing_VartableEntry(ShIndex, symbol_VarIndex(S));
}

static __inline__ int sharing_VariableIndex(TERM Term)
{
  return symbol_VarIndex(term_TopSymbol(Term));
}

static __inline__ int sharing_ConstantIndex(TERM Term)
{
  return symbol_Index(term_TopSymbol(Term));
}

static __inline__ BOOL sharing_IsSharedVar(TERM T, SHARED_INDEX ShIndex)
/* RETURNS: True if there's already an entry for the variable T   */
/*          in the Vartable of the shared index ShIndex.          */
{
  return sharing_VartableEntry(ShIndex, sharing_VariableIndex(T)) != NULL;
}

static __inline__ BOOL sharing_IsSharedConst(TERM T, SHARED_INDEX ShIndex)
/* True if there's already an entry for the constant T   */
/* in the Consttable of the shared index ShIndex.        */
{
  return sharing_ConsttableEntry(ShIndex, sharing_ConstantIndex(T)) != NULL;
}

static __inline__ BOOL sharing_IsNotReallyShared(TERM Term)
/* Der einzige Superterm ist der in dem ich loesche */
{
  return list_Length(term_SupertermList(Term)) <= 1;
}

static __inline__ void sharing_RememberSharedTermCopy(TERM Term, TERM Copy)
/* The unshared term Term has now a link to its shared copy  */
{
  term_RplacSuperterm(Term, Copy);
}

static __inline__ TERM sharing_SharedTermCopy(TERM Term)
/* Return the shared copy of the unshared term Term */
{
  return term_Superterm(Term);
}


/**************************************************************/
/* Functions for Creation and Deletion of a SHARED_INDEX         */
/**************************************************************/

SHARED_INDEX sharing_IndexCreate(void); 
void         sharing_IndexDelete(SHARED_INDEX);

/**************************************************************/
/* Functions on term insertion and deletion.                  */
/**************************************************************/

TERM         sharing_Insert(POINTER, TERM, SHARED_INDEX);
void         sharing_Delete(POINTER, TERM, SHARED_INDEX);

void         sharing_PushOnStack(TERM);
void         sharing_PushReverseOnStack(TERM);
void         sharing_PushOnStackNoStamps(TERM);
void         sharing_PushListOnStack(LIST);
void         sharing_PushListReverseOnStack(LIST);
void         sharing_PushListReverseOnStackExcept(LIST, LIST);
void         sharing_PushListOnStackNoStamps(LIST);

/**************************************************************/
/* Functions to access unshared data by the shared terms.     */
/**************************************************************/

LIST         sharing_GetDataList(TERM, SHARED_INDEX);

void         sharing_StartDataIterator(TERM, SHARED_INDEX);
POINTER      sharing_GetNextData(void);
void         sharing_StopDataIterator(void);

LIST         sharing_NAtomDataList(TERM);
LIST         sharing_GetAllSuperTerms(SHARED_INDEX);

void         sharing_ResetAllTermStamps(SHARED_INDEX);

NAT          sharing_GetNumberOfOccurances(TERM);
NAT          sharing_GetNumberOfInstances(TERM, SHARED_INDEX);

/**************************************************************/
/* Output functions                                            */
/**************************************************************/

void         sharing_PrintVartable(SHARED_INDEX);
void         sharing_PrintConsttable(SHARED_INDEX);
void         sharing_PrintSharing(SHARED_INDEX);

/**************************************************************/
/* Debugging Functions                                        */
/**************************************************************/

void         sharing_PrintStack(void);
void         sharing_PrintSharingConstterms1(SHARED_INDEX);
void         sharing_PrintSharingVarterms1(SHARED_INDEX);
void         sharing_PrintSameLevelTerms(TERM);


#endif

