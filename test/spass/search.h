/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *          REPRESENTATION OF PROOF SEARCH                * */
/* *                                                        * */
/* *  $Module:   PROOF SEARCH                               * */ 
/* *                                                        * */
/* *  Copyright (C) 1997, 1998, 1999, 2000                  * */
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

#ifndef _PROOFSEARCH_
#define _PROOFSEARCH_

#include "clause.h"
#include "sort.h"

/**************************************************************/
/* Data Structures and Constants                              */
/**************************************************************/

/* <blockedClauses>: list of (unshared) clauses containing the   */
/*                   "remainder" of the clause splitted at this  */
/*                   level and the negation of the first branch  */
/*                   if this branch created a ground clause.     */ 
/*                   The right clause has clause number 0, and   */
/*                   the negation clauses have number -1.        */
/* <deletedClauses>: list of (unshared) clauses made redundant   */
/*                   by a clause of this level. The split level  */
/*                   of these clauses may be above or below the  */
/*                   current level, but not equal to the current */
/*                   level.                                      */
/* <father>:         the unshared clause that was splitted.      */
typedef struct {
  /* == 0 -> TOPLEVEL, 1,2,... */
  int     splitlevel;
  BOOL    used;
  LIST    blockedClauses, deletedClauses;
  CLAUSE  father;
} *SPLIT, SPLIT_NODE;


typedef struct PROOFSEARCH_HELP {
  LIST            definitions;
  LIST            emptyclauses;
  LIST            usedemptyclauses;
  LIST            finmonpreds;
  SHARED_INDEX    woindex;
  LIST            wolist;
  SHARED_INDEX    usindex;
  LIST            uslist;
  SORTTHEORY      astatic;
  SORTTHEORY      adynamic;
  SORTTHEORY      dynamic;
  SHARED_INDEX    dpindex;
  LIST            dplist;
  PRECEDENCE      precedence;
  FLAGSTORE       store;
  LIST            stack;
  int             validlevel;
  int             lastbacktrack;
  int             splitcounter;
  int             keptclauses;
  int             derivedclauses;
  int             loops;
  int             backtracked;
  NAT             nontrivclausenumber;
} PROOFSEARCH_NODE,*PROOFSEARCH;

/* There are two sets of clauses with their respective clause list: worked-off clauses   */
/* contained in <woindex>, <wolist> and usable clauses, contained in <usindex>,<uslist>. */
/* The assoc list <finitepreds> is a list of pairs (<pred>.(<gterm1>,...,<gtermn>))      */
/* where <pred> (monadic) has (at most) the extension <gterm1>,...,<gtermn>              */
/* Three sort theories: <astatic> is the static overall approximation, only available    */
/* in a non-equality setting, <adynamic> is the dynamic approximation only considering   */
/* maximal declarations, and <dynamic> is the (not approximated) dynamic sort theory of  */
/* all maximal declarations. Clauses that are no longer needed for the search, but for   */
/* proof documentation are stored in <dpindex>, <dplist>. If <dpindex> is NULL, then     */
/* this means that no proof documentation is required.                                   */
/* A search is also heavily influenced by the used <precedence> and flag values in       */
/* store.                                                                                */
/* The next components deal with splitting: the split stack, the current level           */
/* of splitting, the last backtrack level (for branch condensing) and the overall number */
/* of splittings stored in <splitcounter>.                                               */
/* Finally some statistics is stored: the number of kept, derived clauses ...            */
/* and the clause number of some clause that implies a non-trivial domain .               */

/**************************************************************/
/* Inline Functions                                           */
/**************************************************************/

static __inline__ LIST prfs_EmptyClauses(PROOFSEARCH Prf)
{
  return Prf->emptyclauses;
}

static __inline__ void prfs_SetEmptyClauses(PROOFSEARCH Prf, LIST Clauses)
{
  Prf->emptyclauses = Clauses;
}

static __inline__ LIST prfs_Definitions(PROOFSEARCH Prf)
{
  return Prf->definitions;
}

static __inline__ void prfs_SetDefinitions(PROOFSEARCH Prf, LIST Definitions)
{
  Prf->definitions = Definitions;
}

static __inline__ LIST prfs_UsedEmptyClauses(PROOFSEARCH Prf)
{
  return Prf->usedemptyclauses;
}

static __inline__ void prfs_SetUsedEmptyClauses(PROOFSEARCH Prf, LIST Clauses)
{
  Prf->usedemptyclauses = Clauses;
}


static __inline__ LIST prfs_WorkedOffClauses(PROOFSEARCH Prf)
{
  return Prf->wolist;
}

static __inline__ void prfs_SetWorkedOffClauses(PROOFSEARCH Prf, LIST Clauses)
{
  Prf->wolist = Clauses;
}

static __inline__ SHARED_INDEX prfs_WorkedOffSharingIndex(PROOFSEARCH Prf)
{
  return Prf->woindex;
}

static __inline__ LIST prfs_UsableClauses(PROOFSEARCH Prf)
{
  return Prf->uslist;
}

static __inline__ void prfs_SetUsableClauses(PROOFSEARCH Prf, LIST Clauses)
{
  Prf->uslist = Clauses;
}

static __inline__ SHARED_INDEX prfs_UsableSharingIndex(PROOFSEARCH Prf)
{
  return Prf->usindex;
}

static __inline__ LIST prfs_DocProofClauses(PROOFSEARCH Prf)
{
  return Prf->dplist;
}

static __inline__ void prfs_SetDocProofClauses(PROOFSEARCH Prf, LIST Clauses)
{
  Prf->dplist = Clauses;
}

static __inline__ SHARED_INDEX prfs_DocProofSharingIndex(PROOFSEARCH Prf)
{
  return Prf->dpindex;
}

static __inline__ void prfs_AddDocProofSharingIndex(PROOFSEARCH Prf)
{
  Prf->dpindex  = sharing_IndexCreate();
}

static __inline__ LIST prfs_GetFinMonPreds(PROOFSEARCH Prf)
{
  return Prf->finmonpreds;
}

static __inline__ void prfs_SetFinMonPreds(PROOFSEARCH Prf, LIST Preds)
{
  Prf->finmonpreds = Preds;
}

static __inline__ void prfs_DeleteFinMonPreds(PROOFSEARCH Prf)
{
  list_DeleteAssocListWithValues(Prf->finmonpreds,
				 (void (*)(POINTER)) term_DeleteTermList);
  prfs_SetFinMonPreds(Prf, list_Nil());
}

static __inline__ SORTTHEORY prfs_StaticSortTheory(PROOFSEARCH Prf)
{
  return Prf->astatic;
}

static __inline__ void prfs_SetStaticSortTheory(PROOFSEARCH Prf, SORTTHEORY Theory)
{
  Prf->astatic = Theory;
}

static __inline__ SORTTHEORY prfs_DynamicSortTheory(PROOFSEARCH Prf)
{
  return Prf->dynamic;
}

static __inline__ void prfs_SetDynamicSortTheory(PROOFSEARCH Prf, SORTTHEORY Theory)
{
  Prf->dynamic = Theory;
}

static __inline__ SORTTHEORY prfs_ApproximatedDynamicSortTheory(PROOFSEARCH Prf)
{
  return Prf->adynamic;
}

static __inline__ void prfs_SetApproximatedDynamicSortTheory(PROOFSEARCH Prf, SORTTHEORY Theory)
{
  Prf->adynamic = Theory;
}

static __inline__ PRECEDENCE prfs_Precedence(PROOFSEARCH Prf)
{
  return Prf->precedence;
}

static __inline__ FLAGSTORE prfs_Store(PROOFSEARCH Prf)
{
  return Prf->store;
}

static __inline__ BOOL prfs_SplitLevelCondition(NAT OriginLevel, NAT RedundantLevel, NAT BacktrackLevel)
{
  return (OriginLevel > RedundantLevel || OriginLevel > BacktrackLevel);
}

static __inline__ BOOL prfs_IsClauseValid(CLAUSE C, int Level)
{
  return clause_SplitLevel(C) <= Level;
}

static __inline__ SPLIT prfs_GetSplitOfLevel(int L, PROOFSEARCH Prf)
{
  LIST Scan;
  Scan = Prf->stack; 
  while (!list_Empty(Scan) &&
	 (((SPLIT)list_Car(Scan))->splitlevel != L))
    Scan = list_Cdr(Scan);  
  
  return (SPLIT) list_Car(Scan);
}

static __inline__ LIST prfs_SplitStack(PROOFSEARCH Prf)
{
  return Prf->stack;
}

static __inline__ SPLIT prfs_SplitStackTop(PROOFSEARCH Prf)
{
  return (SPLIT) list_Car(Prf->stack);
}

static __inline__ void prfs_SplitStackPop(PROOFSEARCH Prf)
{
  Prf->stack = list_Pop(Prf->stack);
}

static __inline__ void prfs_SplitStackPush(PROOFSEARCH Prf, SPLIT S)
{
  Prf->stack = list_Cons(S, Prf->stack);
}

static __inline__ BOOL prfs_SplitStackEmpty(PROOFSEARCH Prf)
{
  return list_StackEmpty(prfs_SplitStack(Prf));
}

static __inline__ int prfs_TopLevel(void) 
{
  return 0;
}

static __inline__ int prfs_ValidLevel(PROOFSEARCH Prf)
{
  return Prf->validlevel;
}

static __inline__ void prfs_SetValidLevel(PROOFSEARCH Prf, int Value)
{
  Prf->validlevel = Value;
}

static __inline__ void prfs_IncValidLevel(PROOFSEARCH Prf)
{
  (Prf->validlevel)++;
}

static __inline__ void prfs_DecValidLevel(PROOFSEARCH Prf)
{
  (Prf->validlevel)--;
}

static __inline__ int prfs_LastBacktrackLevel(PROOFSEARCH Prf)
{
  return Prf->lastbacktrack;
}

static __inline__ void prfs_SetLastBacktrackLevel(PROOFSEARCH Prf, int Value)
{
  Prf->lastbacktrack = Value;
}

static __inline__ int prfs_SplitCounter(PROOFSEARCH Prf)
{
  return Prf->splitcounter;
}

static __inline__ void prfs_SetSplitCounter(PROOFSEARCH Prf, int c)
{
  Prf->splitcounter = c;
}

static __inline__ void prfs_DecSplitCounter(PROOFSEARCH Prf)
{
  (Prf->splitcounter)--;
}

static __inline__ int prfs_KeptClauses(PROOFSEARCH Prf)
{
  return Prf->keptclauses;
}

static __inline__ void prfs_IncKeptClauses(PROOFSEARCH Prf)
{
  Prf->keptclauses++;
}

static __inline__ int prfs_DerivedClauses(PROOFSEARCH Prf)
{
  return Prf->derivedclauses;
}

static __inline__ void prfs_IncDerivedClauses(PROOFSEARCH Prf, int k)
{
  Prf->derivedclauses += k;
}

static __inline__ int prfs_Loops(PROOFSEARCH Prf)
{
  return Prf->loops;
}

static __inline__ void prfs_SetLoops(PROOFSEARCH Prf, int k)
{
  Prf->loops = k;
}

static __inline__ void prfs_DecLoops(PROOFSEARCH Prf)
{
  Prf->loops--;
}

static __inline__ int prfs_BacktrackedClauses(PROOFSEARCH Prf)
{
  return Prf->backtracked;
}

static __inline__ void prfs_SetBacktrackedClauses(PROOFSEARCH Prf, int k)
{
  Prf->backtracked = k;
}

static __inline__ void prfs_IncBacktrackedClauses(PROOFSEARCH Prf, int k)
{
  Prf->backtracked += k;
}

static __inline__ NAT prfs_NonTrivClauseNumber(PROOFSEARCH Prf)
{
  return Prf->nontrivclausenumber;
}

static __inline__ void prfs_SetNonTrivClauseNumber(PROOFSEARCH Prf, NAT Number)
{
  Prf->nontrivclausenumber = Number;
}


/**************************************************************/
/* Functions for accessing SPLIT objects                      */
/**************************************************************/

static __inline__ void prfs_SplitFree(SPLIT Sp)
{
  memory_Free(Sp, sizeof(SPLIT_NODE));
}

static __inline__ LIST prfs_SplitBlockedClauses(SPLIT S)
{
  return S->blockedClauses;
}

static __inline__ void prfs_SplitAddBlockedClause(SPLIT S, CLAUSE C)
{
  S->blockedClauses = list_Cons(C,S->blockedClauses);
}

static __inline__ void prfs_SplitSetBlockedClauses(SPLIT S, LIST L)
{
  S->blockedClauses = L;
}

static __inline__ LIST prfs_SplitDeletedClauses(SPLIT S)
{
  return S->deletedClauses;
}

static __inline__ void prfs_SplitSetDeletedClauses(SPLIT S, LIST L)
{
  S->deletedClauses = L;
}

static __inline__ int prfs_SplitSplitLevel(SPLIT S)
{
  return S->splitlevel;
}

static __inline__ BOOL prfs_SplitIsUsed(SPLIT S)
{
  return S->used;
}

static __inline__ BOOL prfs_SplitIsUnused(SPLIT S)
{
  return !S->used;
}

static __inline__ void prfs_SplitSetUsed(SPLIT S)
{
  S->used = TRUE;
}

static __inline__ CLAUSE prfs_SplitFatherClause(SPLIT S) 
{
  return S->father;
}

static __inline__ void prfs_SplitSetFatherClause(SPLIT S, CLAUSE C)
{
  S->father = C;
}


/**************************************************************/
/* Functions                                                  */
/**************************************************************/

PROOFSEARCH prfs_Create(void);
BOOL        prfs_Check(PROOFSEARCH);
void        prfs_CopyIndices(PROOFSEARCH, PROOFSEARCH);
void        prfs_Delete(PROOFSEARCH);
void        prfs_DeleteDocProof(PROOFSEARCH);
void        prfs_Clean(PROOFSEARCH);
void        prfs_Print(PROOFSEARCH);
void        prfs_PrintSplit(SPLIT);
void        prfs_PrintSplitStack(PROOFSEARCH);
void        prfs_InsertWorkedOffClause(PROOFSEARCH,CLAUSE);
void        prfs_InsertUsableClause(PROOFSEARCH,CLAUSE);
void        prfs_InsertDocProofClause(PROOFSEARCH,CLAUSE);
void        prfs_MoveUsableWorkedOff(PROOFSEARCH, CLAUSE);
void        prfs_MoveWorkedOffDocProof(PROOFSEARCH, CLAUSE);
void        prfs_MoveUsableDocProof(PROOFSEARCH, CLAUSE);
void        prfs_ExtractWorkedOff(PROOFSEARCH, CLAUSE);
void        prfs_DeleteWorkedOff(PROOFSEARCH, CLAUSE);
void        prfs_ExtractUsable(PROOFSEARCH, CLAUSE);
void        prfs_DeleteUsable(PROOFSEARCH, CLAUSE);
void        prfs_ExtractDocProof(PROOFSEARCH, CLAUSE);
void        prfs_MoveInvalidClausesDocProof(PROOFSEARCH);
void        prfs_SwapIndexes(PROOFSEARCH);

void        prfs_InstallFiniteMonadicPredicates(PROOFSEARCH, LIST, LIST);

CLAUSE      prfs_PerformSplitting(PROOFSEARCH, CLAUSE);
CLAUSE      prfs_DoSplitting(PROOFSEARCH, CLAUSE, LIST);
NAT         prfs_GetNumberOfInstances(PROOFSEARCH, LITERAL, BOOL);


#endif
