/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *          REPRESENTATION OF PROOF SEARCH                * */
/* *                                                        * */
/* *  $Module:   PROOF SEARCH                               * */ 
/* *                                                        * */
/* *  Copyright (C) 1997, 1998, 1999, 2000, 2001            * */
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


#include "search.h"
#include "defs.h"


/**************************************************************/
/* Functions                                                  */
/**************************************************************/

static SPLIT prfs_SplitCreate(PROOFSEARCH PS)
/**************************************************************
  INPUT:   A proofsearch object
  RETURNS: A new split object, which is initialized.
  MEMORY:  Allocates memory for the SPLIT_NODE.
  EFFECT:  Increases the split level of the proof search object.
***************************************************************/
{
  SPLIT Result;

  prfs_IncValidLevel(PS);

  Result                 = (SPLIT)memory_Malloc(sizeof(SPLIT_NODE));
  Result->splitlevel     = prfs_ValidLevel(PS);
  Result->used           = FALSE;
  Result->blockedClauses = list_Nil();
  Result->deletedClauses = list_Nil();
  Result->father         = (CLAUSE) NULL;
  return Result;
}


static void prfs_SplitDelete(SPLIT S)
/**************************************************************
  INPUT:   A split 
  RETURNS: Nothing.
  MEMORY:  Deletes blocked and deleted clauses. Frees the split.
***************************************************************/
{
  clause_DeleteClauseList(S->blockedClauses);
  clause_DeleteClauseList(S->deletedClauses);
  if (S->father != (CLAUSE)NULL)
    clause_Delete(S->father);
  prfs_SplitFree(S);
}


/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *		    DEBUGGING FUNCTIONS	         	    * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/

BOOL prfs_Check(PROOFSEARCH Search)
/**************************************************************
  INPUT:   A proof search object.
  EFFECT:  None.
  RETURNS: TRUE if all invariants about <Search> are valid.
***************************************************************/
{
  LIST   Scan,Clauses;
  SPLIT  Split;
  CLAUSE Clause;

  for (Scan=prfs_UsableClauses(Search);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
    Clause = (CLAUSE)list_Car(Scan);
    if (!clause_IsClause(Clause, prfs_Store(Search), prfs_Precedence(Search)) ||
	clause_GetFlag(Clause, WORKEDOFF) ||
	!prfs_IsClauseValid(Clause, prfs_ValidLevel(Search)))
      return FALSE;
  }

  for (Scan=prfs_WorkedOffClauses(Search);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
    Clause = (CLAUSE)list_Car(Scan);
    if (!clause_IsClause(Clause, prfs_Store(Search), prfs_Precedence(Search)) ||
	!clause_GetFlag(Clause,WORKEDOFF) ||
	!prfs_IsClauseValid(Clause, prfs_ValidLevel(Search)))
      return FALSE;
  }

  for (Scan=prfs_SplitStack(Search); !list_Empty(Scan); Scan=list_Cdr(Scan)) {
    Split = (SPLIT)list_Car(Scan);
    if (prfs_SplitIsUsed(Split)) {
      if (!list_Empty(prfs_SplitBlockedClauses(Split)) ||
	  !list_Empty(prfs_SplitDeletedClauses(Split))) {
	/*putchar('\n');prfs_PrintSplit(Split); putchar('\n');*/
	return FALSE;
      } else {
	for (Clauses=prfs_UsableClauses(Search);!list_Empty(Clauses);Clauses=list_Cdr(Clauses))
	  if (clause_SplitLevel(list_Car(Clauses)) == prfs_SplitSplitLevel(Split)) {
	    /*puts("\n");prfs_PrintSplit(Split); 
	      fputs("\n Clause must not exist: ",stdout);
	      clause_Print(list_Car(Clauses)); putchar('\n');*/
	    return FALSE;
	  }
	for (Clauses=prfs_WorkedOffClauses(Search);!list_Empty(Clauses);Clauses=list_Cdr(Clauses))
	  if (clause_SplitLevel(list_Car(Clauses)) == prfs_SplitSplitLevel(Split)) {
	    /*puts("\n");prfs_PrintSplit(Split);
	      fputs("\n Clause must not exist: ",stdout);
	      clause_Print(list_Car(Clauses)); putchar('\n');*/
	    return FALSE;
	  }
      }
    } 
  }
  
  if (prfs_ValidLevel(Search) == 0) {
    if (!prfs_SplitStackEmpty(Search))
      return FALSE;
  } else {
    if (prfs_ValidLevel(Search) != prfs_SplitSplitLevel(prfs_SplitStackTop(Search)))
      return FALSE;
  }

  if (prfs_ValidLevel(Search) < prfs_LastBacktrackLevel(Search))
    return FALSE;

  return TRUE;
}

/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *			HIGH LEVEL FUNCTIONS		    * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/

static void prfs_InsertInSortTheories(PROOFSEARCH Search, CLAUSE Clause)
/**************************************************************
  INPUT:   A proof search object and a clause.
  EFFECT:  If the clause is a declaration clause it is inserted
           into the dynamic and approximated dynamic sort theory.
  RETURNS: Nothing.
***************************************************************/
{
  if ((prfs_DynamicSortTheory(Search) != (SORTTHEORY)NULL ||
       prfs_ApproximatedDynamicSortTheory(Search) != (SORTTHEORY)NULL) &&
      clause_IsDeclarationClause(Clause)) {
    int     i,l;
    LITERAL lit;
    CLAUSE  copy;
    LIST    approx;
    l = clause_Length(Clause);
    for (i = clause_FirstSuccedentLitIndex(Clause); i < l; i++) {
      lit = clause_GetLiteral(Clause,i);
      if (clause_LiteralIsMaximal(lit) && 
	  symbol_IsBaseSort(term_TopSymbol(clause_LiteralSignedAtom(lit)))) {
	if (prfs_DynamicSortTheory(Search) != (SORTTHEORY)NULL) {
	  copy = clause_Copy(Clause);
	  list_Delete(clause_ParentClauses(copy));
	  clause_SetParentClauses(copy,list_Nil());
	  list_Delete(clause_ParentLiterals(copy));
	  clause_SetParentLiterals(copy,list_Nil());
	  clause_SetNumber(copy,clause_Number(Clause));
	  sort_TheoryInsertClause(prfs_DynamicSortTheory(Search),Clause,
				  copy,clause_GetLiteral(copy,i));
	}
	if (prfs_ApproximatedDynamicSortTheory(Search) != (SORTTHEORY)NULL) {
	  approx = sort_ApproxMaxDeclClauses(Clause, prfs_Store(Search),
					     prfs_Precedence(Search));
	  for ( ; !list_Empty(approx); approx = list_Pop(approx)) {
	    copy = (CLAUSE)list_Car(approx);
	    sort_TheoryInsertClause(prfs_ApproximatedDynamicSortTheory(Search),
				    Clause, copy, 
				    clause_GetLiteral(copy,clause_FirstSuccedentLitIndex(copy)));
	  }
	}
      }
    }
  }
}


static void prfs_DeleteFromSortTheories(PROOFSEARCH Search, CLAUSE Clause)
/**************************************************************
  INPUT:   A proof search object and a clause.
  RETURNS: Nothing.
  EFFECT:  If the clause is a declaration clause it is deleted
           from the dynamic and approximated dynamic sort theory.
***************************************************************/
{
  if (clause_IsDeclarationClause(Clause)) {
    if (prfs_DynamicSortTheory(Search) != (SORTTHEORY)NULL)
      sort_TheoryDeleteClause(prfs_DynamicSortTheory(Search), Clause);
    if (prfs_ApproximatedDynamicSortTheory(Search) != (SORTTHEORY)NULL)
      sort_TheoryDeleteClause(prfs_ApproximatedDynamicSortTheory(Search), Clause);
  }
}


void prfs_DeleteDocProof(PROOFSEARCH Search)
/**************************************************************
  INPUT:   A proof search object.
  RETURNS: Nothing.
  EFFECT:  The docproof structures are deleted.
***************************************************************/
{
  clause_DeleteSharedClauseList(prfs_DocProofClauses(Search),
				prfs_DocProofSharingIndex(Search),
				prfs_Store(Search), prfs_Precedence(Search));
  if (prfs_DocProofSharingIndex(Search))
    sharing_IndexDelete(prfs_DocProofSharingIndex(Search));
  Search->dpindex = NULL;
  Search->dplist  = list_Nil();
}


static void prfs_InternalDelete(PROOFSEARCH Search)
/**************************************************************
  INPUT:   A proof search object.
  RETURNS: Nothing.
  EFFECT:  Most of the proofsearch object is deleted.
           This function implements the common subset of
	   functionality of prfs_Clean and prfs_Delete.
***************************************************************/
{
  LIST Scan;

  clause_DeleteClauseList(prfs_EmptyClauses(Search));
  list_DeleteWithElement(prfs_Definitions(Search),
			 (void (*)(POINTER)) def_Delete);
  list_Delete(prfs_UsedEmptyClauses(Search));
  sort_TheoryDelete(prfs_StaticSortTheory(Search));
  sort_TheoryDelete(prfs_DynamicSortTheory(Search));
  sort_TheoryDelete(prfs_ApproximatedDynamicSortTheory(Search));
  clause_DeleteSharedClauseList(prfs_WorkedOffClauses(Search),
				prfs_WorkedOffSharingIndex(Search),
				prfs_Store(Search), prfs_Precedence(Search));
  clause_DeleteSharedClauseList(prfs_UsableClauses(Search),
				prfs_UsableSharingIndex(Search),
				prfs_Store(Search), prfs_Precedence(Search));
  clause_DeleteSharedClauseList(prfs_DocProofClauses(Search),
				prfs_DocProofSharingIndex(Search),
				prfs_Store(Search), prfs_Precedence(Search));
  prfs_DeleteFinMonPreds(Search);
  for (Scan=prfs_SplitStack(Search); !list_Empty(Scan); Scan=list_Cdr(Scan))
    prfs_SplitDelete(list_Car(Scan));
  list_Delete(prfs_SplitStack(Search));
}


void prfs_Delete(PROOFSEARCH Search)
/**************************************************************
  INPUT:   A proof search object.
  RETURNS: Nothing.
  EFFECT:  The whole structure including all its substructures 
           is deleted.
***************************************************************/
{
  prfs_InternalDelete(Search);

  sharing_IndexDelete(prfs_WorkedOffSharingIndex(Search));
  sharing_IndexDelete(prfs_UsableSharingIndex(Search));
  if (prfs_DocProofSharingIndex(Search))
    sharing_IndexDelete(prfs_DocProofSharingIndex(Search));
  flag_DeleteStore(prfs_Store(Search));
  symbol_DeletePrecedence(prfs_Precedence(Search));
  memory_Free(Search,sizeof(PROOFSEARCH_NODE));
}


void prfs_Clean(PROOFSEARCH Search)
/**************************************************************
  INPUT:   A proof search object.
  RETURNS: Nothing.
  EFFECT:  All clauses are deleted. The structure is cleaned
           and initialized.
***************************************************************/
{
  prfs_InternalDelete(Search);

  Search->emptyclauses     = list_Nil();
  Search->definitions      = list_Nil();
  Search->usedemptyclauses = list_Nil();
  Search->wolist           = list_Nil();
  Search->uslist           = list_Nil();
  Search->finmonpreds      = list_Nil();
  Search->astatic          = (SORTTHEORY)NULL;
  Search->adynamic         = (SORTTHEORY)NULL;
  Search->dynamic          = (SORTTHEORY)NULL;
  Search->dplist           = list_Nil();
  
  Search->stack               = list_StackBottom();
  Search->validlevel          = 0;
  Search->lastbacktrack       = 0;
  Search->splitcounter        = 0;
  Search->keptclauses         = 0;
  Search->derivedclauses      = 0;
  Search->loops               = 0;
  Search->backtracked         = 0;
  Search->nontrivclausenumber = 0;

  symbol_ClearPrecedence(prfs_Precedence(Search));
}


void prfs_SwapIndexes(PROOFSEARCH Search)
/**************************************************************
  INPUT:   A proof search object.
  RETURNS: Nothing.
  EFFECT:  The usable and worked-off indexes are exchanged.
***************************************************************/
{
  LIST         Scan;
  SHARED_INDEX Help;

  Help = prfs_WorkedOffSharingIndex(Search);
  Scan = prfs_WorkedOffClauses(Search);
  prfs_SetWorkedOffClauses(Search,prfs_UsableClauses(Search));
  Search->woindex = prfs_UsableSharingIndex(Search);
  prfs_SetUsableClauses(Search, Scan);
  Search->usindex = Help;

  for (Scan=prfs_UsableClauses(Search); !list_Empty(Scan); Scan=list_Cdr(Scan))
    clause_RemoveFlag(list_Car(Scan), WORKEDOFF);
  for (Scan=prfs_WorkedOffClauses(Search);!list_Empty(Scan);Scan=list_Cdr(Scan))
    clause_SetFlag(list_Car(Scan), WORKEDOFF);
}


PROOFSEARCH prfs_Create(void)
/**************************************************************
  INPUT:   None.
  RETURNS: A new proof search object. The worked off and usable
           indexes are created whilst the docproof index and the
	   sort theories are not created, since they are not
	   needed in general.
***************************************************************/
{
  PROOFSEARCH Result;

  Result = memory_Malloc(sizeof(PROOFSEARCH_NODE));

  Result->emptyclauses = list_Nil();
  Result->definitions  = list_Nil();
  Result->usedemptyclauses = list_Nil();
  Result->woindex      = sharing_IndexCreate();
  Result->wolist       = list_Nil();
  Result->usindex      = sharing_IndexCreate();
  Result->uslist       = list_Nil();
  Result->finmonpreds  = list_Nil();

  Result->astatic      = (SORTTHEORY)NULL;
  Result->adynamic     = (SORTTHEORY)NULL;
  Result->dynamic      = (SORTTHEORY)NULL;

  Result->precedence   = symbol_CreatePrecedence();

  Result->store        = flag_CreateStore();
  flag_InitStoreByDefaults(Result->store);
  
  Result->dpindex      = (SHARED_INDEX)NULL;
  Result->dplist       = list_Nil();
  
  Result->stack               = list_StackBottom();
  Result->validlevel          = 0;
  Result->lastbacktrack       = 0;
  Result->splitcounter        = 0;
  Result->keptclauses         = 0;
  Result->derivedclauses      = 0;
  Result->loops               = 0;
  Result->backtracked         = 0;
  Result->nontrivclausenumber = 0;
    
  return Result;  
}


void prfs_CopyIndices(PROOFSEARCH Search, PROOFSEARCH SearchCopy) 
/**************************************************************
  INPUT:   A proof search object and a clean proof search object.
  RETURNS: Nothing.
  EFFECT:  Copies the indices from Search to SearchCopy.
  CAUTION: Splitstack and theories are not copied!
***************************************************************/
{
  LIST Scan;

  /* If a DocProof index is required but not yet allocated in SearchCopy,
     do it now */
  if (prfs_DocProofSharingIndex(Search) != NULL &&
      prfs_DocProofSharingIndex(SearchCopy) == NULL)
    prfs_AddDocProofSharingIndex(SearchCopy);

  /* Copy usable, worked-off and docproof index */
  for (Scan = prfs_UsableClauses(Search); !list_Empty(Scan); Scan = list_Cdr(Scan))
    prfs_InsertUsableClause(SearchCopy, clause_Copy((CLAUSE) list_Car(Scan)));

  for (Scan = prfs_WorkedOffClauses(Search); !list_Empty(Scan); Scan = list_Cdr(Scan))
    prfs_InsertWorkedOffClause(SearchCopy, clause_Copy((CLAUSE) list_Car(Scan)));

  for (Scan = prfs_DocProofClauses(Search); !list_Empty(Scan); Scan = list_Cdr(Scan))
    prfs_InsertDocProofClause(SearchCopy, clause_Copy((CLAUSE) list_Car(Scan)));
}


void prfs_InsertWorkedOffClause(PROOFSEARCH Search, CLAUSE Clause)
/**************************************************************
  INPUT:   A proof search object and a clause.
  RETURNS: Nothing.
  MEMORY:  The clause is assumed to be unshared.
  EFFECT:  The clause is inserted into the worked off sharing index
           and list of <Search>. The unshared literals are deleted.
***************************************************************/
{
#ifdef CHECK
  if (!clause_IsClause(Clause,prfs_Store(Search), prfs_Precedence(Search))) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In prfs_InsertWorkedOffClause: Illegal input.");
    misc_FinishErrorReport();
  }
#endif 

  clause_SetFlag(Clause,WORKEDOFF);
  prfs_SetWorkedOffClauses(Search,list_Cons(Clause, prfs_WorkedOffClauses(Search)));
  clause_InsertIntoSharing(Clause, prfs_WorkedOffSharingIndex(Search),
			   prfs_Store(Search), prfs_Precedence(Search));
  prfs_InsertInSortTheories(Search, Clause);
}


void prfs_InsertUsableClause(PROOFSEARCH Search, CLAUSE Clause)
/**************************************************************
  INPUT:   A proof search object and a clause.
  RETURNS: Nothing.
  MEMORY:  The clause is assumed to be unshared.
  EFFECT:  The clause is inserted into the usable sharing index
           and list of <Search> sorted with respect to their weight. 
	   The unshared literals are deleted.
***************************************************************/
{

#ifdef CHECK
  if (!clause_IsClause(Clause, prfs_Store(Search), prfs_Precedence(Search)) ||
      clause_GetFlag(Clause, WORKEDOFF)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In prfs_InsertUsableClause: Illegal input.");
    misc_FinishErrorReport();
  }
  /* The invariant that no two clauses have the same clause number cannot  */
  /* be guaranteed as long as e.g. several directly subsequent reductions */
  /* are applied to a clause that eventually gets a greater split level.   */
#endif 
    
  prfs_SetUsableClauses(Search,clause_InsertWeighed(Clause,
						    prfs_UsableClauses(Search),
						    prfs_Store(Search),
						    prfs_Precedence(Search)));
  clause_InsertIntoSharing(Clause, prfs_UsableSharingIndex(Search),
			   prfs_Store(Search), prfs_Precedence(Search));
}


void prfs_InsertDocProofClause(PROOFSEARCH Search, CLAUSE Clause)
/**************************************************************
  INPUT:   A proof search object and a clause.
  RETURNS: Nothing.
  MEMORY:  The clause is assumed to be unshared.
  EFFECT:  The clause is inserted into the proof documentation sharing index.
	   The unshared literals are deleted.
***************************************************************/
{ 
#ifdef CHECK
  if (!clause_IsClause(Clause, prfs_Store(Search), prfs_Precedence(Search))) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In prfs_InsertDocProofClause: Illegal input.");
    misc_FinishErrorReport();
  }
#endif   
  
  if (prfs_DocProofSharingIndex(Search) == (SHARED_INDEX)NULL)
    clause_Delete(Clause);
  else {
    prfs_SetDocProofClauses(Search,list_Cons(Clause, prfs_DocProofClauses(Search)));
    clause_InsertIntoSharing(Clause, prfs_DocProofSharingIndex(Search),
			     prfs_Store(Search), prfs_Precedence(Search));
  }
}


void prfs_MoveUsableWorkedOff(PROOFSEARCH Search, CLAUSE Clause)
/**************************************************************
  INPUT:   A proof search object and a clause.
  RETURNS: Nothing.
  EFFECT:  The clause is inserted into the worked off sharing index
           and list and it is deleted from the usable index and list.
	   In particular, the WorkedOff flag is set and if <Clause> is a 
	   declaration clause, it is inserted into the respective sort theories.
***************************************************************/
{
#ifdef CHECK
  if (!clause_IsClause(Clause,prfs_Store(Search), prfs_Precedence(Search)) ||
      clause_GetFlag(Clause, WORKEDOFF)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In prfs_MoveUsableWorkedOff: Illegal input.");
    misc_FinishErrorReport();
  }
#endif 

  prfs_SetUsableClauses(Search,list_PointerDeleteElement(prfs_UsableClauses(Search),Clause));
  clause_SetFlag(Clause,WORKEDOFF);
  clause_MoveSharedClause(Clause, prfs_UsableSharingIndex(Search),
			  prfs_WorkedOffSharingIndex(Search), prfs_Store(Search),
			  prfs_Precedence(Search));
  prfs_SetWorkedOffClauses(Search,list_Cons(Clause, prfs_WorkedOffClauses(Search)));
  prfs_InsertInSortTheories(Search, Clause);
}


void prfs_MoveWorkedOffDocProof(PROOFSEARCH Search, CLAUSE Clause)
/**************************************************************
  INPUT:   A proof search object and a clause.
  RETURNS: Nothing.
  EFFECT:  The clause is inserted into the doc proof sharing index
           and list of <Search> and it is deleted from the worked off
	   index and list.
***************************************************************/
{
#ifdef CHECK
  if (!clause_IsClause(Clause, prfs_Store(Search), prfs_Precedence(Search)) ||
      !clause_GetFlag(Clause, WORKEDOFF)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In prfs_MoveWorkedOffDocProof: Illegal input.");
    misc_FinishErrorReport();
  }
#endif 

  prfs_DeleteFromSortTheories(Search, Clause);
  prfs_SetWorkedOffClauses(Search,list_PointerDeleteElement(prfs_WorkedOffClauses(Search),Clause));
  clause_RemoveFlag(Clause,WORKEDOFF);

  if (prfs_DocProofSharingIndex(Search) == (SHARED_INDEX)NULL)
    clause_DeleteFromSharing(Clause,prfs_WorkedOffSharingIndex(Search),
			     prfs_Store(Search), prfs_Precedence(Search));
  else {
    clause_MoveSharedClause(Clause, prfs_WorkedOffSharingIndex(Search),
			    prfs_DocProofSharingIndex(Search),prfs_Store(Search),
			    prfs_Precedence(Search));
    prfs_SetDocProofClauses(Search,list_Cons(Clause, prfs_DocProofClauses(Search)));
  }
}


void prfs_MoveUsableDocProof(PROOFSEARCH Search, CLAUSE Clause)
/**************************************************************
  INPUT:   A proof search object and a clause.
  RETURNS: Nothing.
  EFFECT:  The clause is inserted into the doc proof sharing index
           and list of <Search> and it is deleted from the usable
	   index and list.
***************************************************************/
{
#ifdef CHECK
  if (!clause_IsClause(Clause, prfs_Store(Search), prfs_Precedence(Search)) ||
      clause_GetFlag(Clause, WORKEDOFF)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In prfs_MoveUsableDocProof: Illegal input.");
    misc_FinishErrorReport();
  }
#endif 

  prfs_SetUsableClauses(Search,list_PointerDeleteElement(prfs_UsableClauses(Search),Clause));

  if (prfs_DocProofSharingIndex(Search) == (SHARED_INDEX)NULL)
    clause_DeleteFromSharing(Clause, prfs_UsableSharingIndex(Search),
			     prfs_Store(Search), prfs_Precedence(Search));
  else {
    clause_MoveSharedClause(Clause, prfs_UsableSharingIndex(Search),
			    prfs_DocProofSharingIndex(Search),prfs_Store(Search),
			    prfs_Precedence(Search));
    prfs_SetDocProofClauses(Search,list_Cons(Clause, prfs_DocProofClauses(Search)));
  }
}


void prfs_MoveInvalidClausesDocProof(PROOFSEARCH Search)
/**************************************************************
  INPUT:   A proof search object.
  RETURNS: Nothing.
  EFFECT:  All clauses that have a split level higher than the
           current split level of <Search> are moved to the
	   proof documentation index. If it does not exist, i.e.,
	   no proof documentation required, the clauses are
	   deleted.
***************************************************************/
{
  LIST   scan, invalid;
  CLAUSE clause;

  invalid = list_Nil();
  for (scan = prfs_WorkedOffClauses(Search); !list_Empty(scan);
       scan = list_Cdr(scan)) {
    clause = (CLAUSE)list_Car(scan);
    if (!prfs_IsClauseValid(clause, prfs_ValidLevel(Search)))
      invalid = list_Cons(clause,invalid);
  }
  /* WARNING: The following move operation changes the worked off */
  /* set of the proof search object destructively.                */
  /* So it's impossible to move those function calls into the     */
  /* loop above.                                                  */
  for ( ; !list_Empty(invalid); invalid = list_Pop(invalid))
    prfs_MoveWorkedOffDocProof(Search,list_Car(invalid));

  invalid = list_Nil();
  for (scan = prfs_UsableClauses(Search); !list_Empty(scan);
       scan = list_Cdr(scan)) {
    clause = (CLAUSE)list_Car(scan);
    if (!prfs_IsClauseValid(clause, prfs_ValidLevel(Search)))
      invalid = list_Cons(clause,invalid);
  }
  /* WARNING: The following move operation changes the usable     */
  /* set of the proof search object destructively.                */
  /* So it's impossible to move those function calls into the     */
  /* loop above.                                                  */
  for ( ; !list_Empty(invalid); invalid = list_Pop(invalid))
    prfs_MoveUsableDocProof(Search,list_Car(invalid));
}


void prfs_ExtractWorkedOff(PROOFSEARCH Search, CLAUSE Clause)
/**************************************************************
  INPUT:   A proof search object and a clause.
  RETURNS: Nothing.
  EFFECT:  The clause is removed from the worked off index and
           list and returned as an unshared clause.
	   Sort theories are updated accordingly.
***************************************************************/
{
#ifdef CHECK
  if (!clause_IsUnorderedClause(Clause) || !clause_GetFlag(Clause, WORKEDOFF)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In prfs_ExtractWorkedOff: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  prfs_DeleteFromSortTheories(Search, Clause);
  clause_RemoveFlag(Clause,WORKEDOFF);
  prfs_SetWorkedOffClauses(Search,list_PointerDeleteElement(prfs_WorkedOffClauses(Search),Clause));
  clause_MakeUnshared(Clause,prfs_WorkedOffSharingIndex(Search));
}


void prfs_ExtractUsable(PROOFSEARCH Search, CLAUSE Clause)
/**************************************************************
  INPUT:   A proof search object and a clause.
  RETURNS: Nothing.
  EFFECT:  The clause is removed from the usable off index and
           list and returned as an unshared clause.
***************************************************************/
{
#ifdef CHECK
  if (!clause_IsUnorderedClause(Clause) || clause_GetFlag(Clause, WORKEDOFF)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In prfs_ExtractUsable: Illegal input.");
    misc_FinishErrorReport();
  }
#endif 

  prfs_SetUsableClauses(Search,list_PointerDeleteElement(prfs_UsableClauses(Search),Clause));
  clause_MakeUnshared(Clause,prfs_UsableSharingIndex(Search));
}


void prfs_ExtractDocProof(PROOFSEARCH Search, CLAUSE Clause)
/**************************************************************
  INPUT:   A proof search object and a clause.
  RETURNS: Nothing.
  EFFECT:  The clause is removed from the docproof off index and
           list and returned as an unshared clause.
***************************************************************/
{
#ifdef CHECK
  if (!clause_IsUnorderedClause(Clause)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In prfs_ExtractDocProof: Illegal input.");
    misc_FinishErrorReport();
  }
#endif 

  prfs_SetDocProofClauses(Search,list_PointerDeleteElement(prfs_DocProofClauses(Search),Clause));
  clause_MakeUnshared(Clause,prfs_DocProofSharingIndex(Search));
}


void prfs_DeleteWorkedOff(PROOFSEARCH Search, CLAUSE Clause)
/**************************************************************
  INPUT:   A proof search object and a clause.
  RETURNS: Nothing.
  EFFECT:  The clause is deleted from the worked off index and list.
	   Sort theories are updated accordingly.
***************************************************************/
{
#ifdef CHECK
  if (!clause_IsClause(Clause, prfs_Store(Search), prfs_Precedence(Search)) ||
      !clause_GetFlag(Clause, WORKEDOFF)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In prfs_DeleteWorkedOff: Illegal input.");
    misc_FinishErrorReport();
  }
#endif 

  prfs_DeleteFromSortTheories(Search, Clause);
  prfs_SetWorkedOffClauses(Search,list_PointerDeleteElement(prfs_WorkedOffClauses(Search),Clause));
  clause_DeleteFromSharing(Clause, prfs_WorkedOffSharingIndex(Search),
			   prfs_Store(Search), prfs_Precedence(Search));
}


void prfs_DeleteUsable(PROOFSEARCH Search, CLAUSE Clause)
/**************************************************************
  INPUT:   A proof search object and a clause.
  RETURNS: Nothing.
  EFFECT:  The clause is deleted from the usable index and list.
***************************************************************/
{
#ifdef CHECK
  if (!clause_IsClause(Clause, prfs_Store(Search), prfs_Precedence(Search)) ||
      clause_GetFlag(Clause, WORKEDOFF)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In prfs_DeleteUsable: Illegal input.");
    misc_FinishErrorReport();
  }
#endif 

  prfs_SetUsableClauses(Search,list_PointerDeleteElement(prfs_UsableClauses(Search),Clause));
  clause_DeleteFromSharing(Clause,prfs_UsableSharingIndex(Search),
			   prfs_Store(Search), prfs_Precedence(Search));
}


void prfs_PrintSplit(SPLIT Split)
/**************************************************************
  INPUT:   A split.
  RETURNS: Nothing.
  EFFECT:  Prints the information kept in the split structure.
***************************************************************/
{
  LIST Scan;

  printf("\n Split: %d %ld", prfs_SplitSplitLevel(Split), (long)Split);
  fputs("\n Father: ", stdout);
  if (prfs_SplitFatherClause(Split) != (CLAUSE)NULL)
    clause_Print(prfs_SplitFatherClause(Split));
  else
    fputs("No father, unnecessary split.", stdout);
  
  fputs("\n Split is ", stdout);
  if (prfs_SplitIsUnused(Split))
    puts("unused.");
  else
    puts("used.");
  fputs(" Blocked clauses:", stdout);
  for (Scan=prfs_SplitBlockedClauses(Split);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
    putchar('\n');
    putchar(' ');
    clause_Print(list_Car(Scan));
  }
  fputs("\n Deleted clauses:", stdout);
  for (Scan=prfs_SplitDeletedClauses(Split);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
    putchar('\n');
    putchar(' ');
    clause_Print(list_Car(Scan));
  }
}


void prfs_PrintSplitStack(PROOFSEARCH PS)
/**************************************************************
  INPUT:   A proof search object.
  RETURNS: Nothing.
  EFFECT:  Prints almost all the information kept in the
           split stack structure.
***************************************************************/
{
  LIST Scan;

  fputs("\n Splitstack:", stdout);

  for (Scan = prfs_SplitStack(PS); !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    prfs_PrintSplit(list_Car(Scan));
    fputs("\n---------------------", stdout);
  }
}


void prfs_Print(PROOFSEARCH Search)
/**************************************************************
  INPUT:   A proof search object.
  RETURNS: void.
  EFFECT:  The proof search object is printed to stdout.
***************************************************************/
{
  LIST Scan;

#ifdef CHECK
  if (!prfs_Check(Search)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In prfs_Print: Illegal input.");
    misc_FinishErrorReport();
  }
#endif 

  printf("\n\n Proofsearch: Current Level: %d Last Backtrack Level: %d Splits: %d Loops: %d Backtracked: %d",
	 prfs_ValidLevel(Search),prfs_LastBacktrackLevel(Search),prfs_SplitCounter(Search),
	 prfs_Loops(Search),prfs_BacktrackedClauses(Search));
  if (prfs_NonTrivClauseNumber(Search)>0)
    printf("\n Clause %d implies a non-trivial domain.", prfs_NonTrivClauseNumber(Search));
  else
    fputs("\n Potentially trivial domain.", stdout);
  fputs("\n Empty Clauses:", stdout);
  for (Scan=prfs_EmptyClauses(Search);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
    fputs("\n ", stdout);
    clause_Print(list_Car(Scan));
  }
  fputs("\n Definitions:", stdout);
  for (Scan=prfs_Definitions(Search);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
    putchar('\n');
    putchar(' ');
    term_Print(list_Car(Scan));
  }
  fputs("\n Worked Off Clauses:", stdout);
  for (Scan=prfs_WorkedOffClauses(Search);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
    putchar('\n');
    putchar(' ');
    clause_Print(list_Car(Scan));
  }
  fputs("\n Usable Clauses:", stdout);
  for (Scan=prfs_UsableClauses(Search);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
    putchar('\n');
    putchar(' ');
    clause_Print(list_Car(Scan));
  }
  fputs("\n Finite predicates:", stdout);
  for (Scan=prfs_GetFinMonPreds(Search);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
    fputs("\n  ", stdout);
    symbol_Print((SYMBOL)list_PairFirst(list_Car(Scan)));
    fputs(": ", stdout);
    term_TermListPrintPrefix(list_PairSecond(list_Car(Scan)));
  }
  prfs_PrintSplitStack(Search);
  fputs("\n Static Sort Theory:", stdout);
  sort_TheoryPrint(prfs_StaticSortTheory(Search));
  fputs("\n Dynamic Sort Theory:", stdout);
  sort_TheoryPrint(prfs_DynamicSortTheory(Search));
  fputs("\n Approximated Dynamic Sort Theory:", stdout);
  sort_TheoryPrint(prfs_ApproximatedDynamicSortTheory(Search));
  putchar('\n');
}


CLAUSE prfs_DoSplitting(PROOFSEARCH PS, CLAUSE SplitClause, LIST Literals)
/**************************************************************
  INPUT:   An proof search object, an unshared clause to be splitted
           where 'Literals' is the list of literals to keep (in their
	   order in the SplitClause).
  RETURNS: A pointer to the (stack-, not sharing-) inserted splitted clause.
  MEMORY:  The blocked parts and the actparts literals are created
           unshared, memory for the two (more for HornSplits) new 
	   clausenodes is allocated.
  EFFECT:  A new SPLIT object is created on the split stack of the proof
           search object. The clause for the right branch will get clause
           number 0 to make it distinguishable from the negation clauses,
	   which get clause number -1.
           All newly created clauses are influenced by some flags of the
           internal flag store of the proof search object.
	   For example the maximal literals are influenced by
	   the weight of function symbols, which is defined by the
	   flag "flag_FUNCWEIGHT".
***************************************************************/
{

  SPLIT   NewSplit;
  CLAUSE  NewClause, BlockedClause;
  LITERAL NextLit,NewLit;
  int     i,j,lengthBlocked,lengthNew,lc,la,ls,nc,na,ns;

#ifdef CHECK
  if (list_Empty(Literals) ||
      !clause_IsClause(SplitClause, prfs_Store(PS), prfs_Precedence(PS))) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In prfs_DoSplitting: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  prfs_DecSplitCounter(PS);
  NewSplit = prfs_SplitCreate(PS);

  prfs_SplitSetFatherClause(NewSplit, SplitClause);

  lengthNew = list_Length(Literals);
  lengthBlocked = clause_Length(SplitClause) - lengthNew;

  NewClause = clause_CreateBody(lengthNew);          /* The left  clause */
  BlockedClause = clause_CreateBody(lengthBlocked);  /* The right clause */
  clause_DecreaseCounter(); /* reset internally increased counter! */
  clause_SetNumber(BlockedClause, 0);
  /* To detect forgotten setting at insertion! */

  lc = clause_LastConstraintLitIndex(SplitClause);
  la = clause_LastAntecedentLitIndex(SplitClause);
  ls = clause_LastSuccedentLitIndex(SplitClause);

  nc = na = ns = 0;

  j = clause_FirstLitIndex();

  for (i = clause_FirstLitIndex(); i <= ls; i++) {
    NextLit = clause_GetLiteral(SplitClause, i);

    NewLit  = clause_LiteralCopy(NextLit);

    if ((lengthNew > 0) && /* To avoid access of Nirvana. */
	list_PointerMember(Literals, NextLit)) {
      /* NewLit is literal for the NewClause. */

      lengthNew--;
      clause_SetLiteral(NewClause, j++, NewLit);
      clause_LiteralSetOwningClause(NewLit, NewClause);
      clause_AddParentClause(NewClause, clause_Number(SplitClause));
      clause_AddParentLiteral(NewClause, i);
      if (i <= lc)
	nc++;
      else if (i <= la)
	na++;
      else 
	ns++;

    } else { /* NewLit is literal for the BlockedClause. */

      clause_SetLiteral(BlockedClause, (i-j), NewLit);
      clause_LiteralSetOwningClause(NewLit, BlockedClause);
      clause_AddParentClause(BlockedClause, clause_Number(SplitClause));
      clause_AddParentLiteral(BlockedClause, i);
    }
  } /* end of 'for all literals'. */

  clause_SetNumOfConsLits(NewClause, nc);
  clause_SetNumOfConsLits(BlockedClause,
			  (clause_NumOfConsLits(SplitClause) - nc));
  clause_SetNumOfAnteLits(NewClause, na);
  clause_SetNumOfAnteLits(BlockedClause,
			  (clause_NumOfAnteLits(SplitClause) - na));
  clause_SetNumOfSuccLits(NewClause, ns);
  clause_SetNumOfSuccLits(BlockedClause,
			  (clause_NumOfSuccLits(SplitClause) - ns));

  clause_ReInit(BlockedClause, prfs_Store(PS), prfs_Precedence(PS));
  clause_UpdateSplitDataFromNewSplitting(BlockedClause, SplitClause,
					 prfs_SplitSplitLevel(NewSplit));
  clause_SetFromSplitting(BlockedClause);
  clause_SetParentLiterals(BlockedClause,
			   list_NReverse(clause_ParentLiterals(BlockedClause)));

  clause_SetDepth(BlockedClause, clause_Depth(SplitClause)+1);

  prfs_SplitAddBlockedClause(NewSplit, BlockedClause);
  prfs_SplitSetDeletedClauses(NewSplit, list_Nil());

  
  prfs_SplitStackPush(PS, NewSplit);

  clause_ReInit(NewClause, prfs_Store(PS), prfs_Precedence(PS));
  clause_UpdateSplitDataFromNewSplitting(NewClause, SplitClause,
					 prfs_SplitSplitLevel(NewSplit));
  clause_SetFromSplitting(NewClause);

  clause_SetParentLiterals(NewClause,
			   list_NReverse(clause_ParentLiterals(NewClause)));

  clause_SetDepth(NewClause, clause_Depth(SplitClause)+1);
  clause_RemoveFlag(NewClause, WORKEDOFF);

  if (clause_IsGround(NewClause)) {
    /* Keep Clauses made from NewClause for refutation case! */
    CLAUSE UnitClause;
    LIST   AtomList;

    la = clause_LastAntecedentLitIndex(NewClause);
    ls = clause_LastSuccedentLitIndex(NewClause);

    Literals = clause_ParentLiterals(NewClause);

    for (i = clause_FirstLitIndex(); i <= ls; i++) {

      NextLit    = clause_GetLiteral(NewClause, i);
      AtomList   = list_List(term_Copy(clause_LiteralAtom(NextLit)));

      if (i <= la)
	UnitClause = clause_Create(list_Nil(), list_Nil(), AtomList,
				   prfs_Store(PS), prfs_Precedence(PS));
      else
	UnitClause = clause_Create(list_Nil(), AtomList, list_Nil(),
				   prfs_Store(PS), prfs_Precedence(PS));

      clause_SetNumber(UnitClause, -1);
      /* To detect forgotten setting at reinsertion! */
      clause_DecreaseCounter();
      /* Reset internally increased counter! */

      list_Delete(AtomList);

      clause_SetFromSplitting(UnitClause);
      clause_UpdateSplitDataFromNewSplitting(UnitClause, SplitClause,
					     prfs_SplitSplitLevel(NewSplit));
      clause_AddParentClause(UnitClause, clause_Number(NewClause));
      clause_AddParentLiteral(UnitClause, i);
      clause_AddParentClause(UnitClause, clause_Number(SplitClause));
      clause_AddParentLiteral(UnitClause, (int)list_Car(Literals));
      Literals = list_Cdr(Literals);
      prfs_SplitAddBlockedClause(NewSplit, UnitClause);
    }
  }
  /* fputs("\n\nSPLITTING DONE!",stdout);
     fputs("\nAus           : ",stdout); clause_Print(SplitClause); fflush(stdout);
     fputs("\nDer erste Teil: ",stdout); clause_Print(NewClause); fflush(stdout);
     fputs("\nDer zweite Teil: ",stdout);
     clause_Print(BlockedClause); fflush(stdout);
     puts("\nDaher als BlockedClauses:");
     clause_ListPrint(prfs_SplitBlockedClauses(NewSplit)); fflush(stdout);
  */
  return NewClause;
}


static LIST prfs_GetSplitLiterals(PROOFSEARCH PS, CLAUSE Clause)
/**************************************************************
  INPUT:   A Clause and a proofsearch object
  RETURNS: A list of literals building the bigger part of a 
           variable-disjunct literal partition if one exists,
	   an empty list, else.
  MEMORY:  Allocates memory for the literal list.
***************************************************************/
{
  LITERAL NextLit;
  int     i, length, OldLength;
  LIST    LitList, VarOcc, NextOcc;
  BOOL    Change;

#ifdef CHECK
  if (!clause_IsClause(Clause, prfs_Store(PS), prfs_Precedence(PS))) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In prfs_GetSplitLiterals: Illegal input.");
    misc_FinishErrorReport();
  }
#endif 

  LitList = list_Nil();

  if (prfs_SplitCounter(PS) != 0) {

    if (clause_HasSuccLits(Clause)) {
      if (clause_HasGroundSuccLit(Clause)) {

	NextLit = clause_GetGroundSuccLit(Clause);
	LitList = list_Cons(NextLit, LitList);

	for (i = clause_LastAntecedentLitIndex(Clause);i >= clause_FirstLitIndex();i--) {
	  NextLit = clause_GetLiteral(Clause, i);
	  if (term_IsGround(clause_LiteralAtom(NextLit)))
	    LitList = list_Cons(NextLit, LitList);
	}
	return LitList;
      }

      /* Clause has no ground succedent literals, but > 1 non-ground */
      NextLit = clause_GetLiteral(Clause, clause_LastSuccedentLitIndex(Clause));
      VarOcc  = term_VariableSymbols(clause_LiteralAtom(NextLit));
      LitList = list_List(NextLit);
      length  = clause_Length(Clause);
      Change  = TRUE;

      while (Change) {
	Change = FALSE;

	for (i=clause_LastSuccedentLitIndex(Clause)-1; i>=clause_FirstLitIndex(); i--) {

	  NextLit = clause_GetLiteral(Clause, i);
	
	  if (!list_PointerMember(LitList, NextLit)) {
	    NextOcc = term_VariableSymbols(clause_LiteralAtom(NextLit));
	    if (list_HasIntersection(VarOcc, NextOcc)) { 
	      OldLength = list_Length(VarOcc);
	      VarOcc    = list_NPointerUnion(VarOcc, NextOcc);
	      LitList   = list_Cons(NextLit, LitList);
	      if (OldLength != list_Length(VarOcc))
		Change = TRUE;
	    }
	    else
	      list_Delete(NextOcc);
	  }
	}
      }
      if (list_Length(LitList) == length) {
	list_Delete(LitList);
	LitList = list_Nil();
      }
      Change = TRUE;    /* Check whether not all succedent literals are used */
      for (i = clause_FirstSuccedentLitIndex(Clause); i < length && Change; i++)
	if (!list_PointerMember(LitList,clause_GetLiteral(Clause, i)))
	  Change = FALSE;
      if (Change) {
	list_Delete(LitList);
	LitList = list_Nil();
      }
      list_Delete(VarOcc);
    }
  }
  return LitList;
}


CLAUSE prfs_PerformSplitting(PROOFSEARCH Search, CLAUSE Clause)
/**************************************************************
  INPUT:   A proof search object and an unshared clause.
  EFFECT:  If <Clause> can be split it is splitted, the first
           part of the split is returned  and the
	   splitted clause is kept in the split stack.
	   Otherwise <Clause> remains unchanged and NULL is returned.
  RETURNS: NULL if <Clause> is not splittable, the first split part otherwise.
***************************************************************/
{
  CLAUSE Result;

  Result = (CLAUSE)NULL;
  
  if (clause_HasSolvedConstraint(Clause)) {
    LIST LitList;

    LitList = prfs_GetSplitLiterals(Search, Clause);

    if (!list_Empty(LitList)) {
      Result = prfs_DoSplitting(Search, Clause, LitList);
      list_Delete(LitList);
    }
  }

  return Result;
}


void prfs_InstallFiniteMonadicPredicates(PROOFSEARCH Search, LIST Clauses,
					 LIST Predicates)
/**************************************************************
  INPUT:   A proof search object a list of clauses and a list
           of monadic predicates.
  RETURNS: Nothing.
  EFFECT:  The argument terms for <Predicates> that occur in
           positive unit clauses are extracted from <Clauses>
           and installed in <Search> as an assoc list.
***************************************************************/
{
  LIST   Pair, Scan, Result;
  CLAUSE Clause;
  TERM   Atom;

  Result = list_Nil();

  for (Scan=Clauses;!list_Empty(Scan);Scan=list_Cdr(Scan)) {
    Clause = (CLAUSE)list_Car(Scan);
    if (clause_Length(Clause) == 1 &&
	clause_NumOfSuccLits(Clause) == 1) {
      Atom = clause_GetLiteralAtom(Clause,clause_FirstSuccedentLitIndex(Clause));
      if (list_PointerMember(Predicates, (POINTER)term_TopSymbol(Atom))) {
	Pair = list_AssocListPair(Result, (POINTER)term_TopSymbol(Atom));
	if (Pair != list_PairNull())
	  list_PairRplacSecond(Pair, list_Cons(term_Copy(term_FirstArgument(Atom)),list_PairSecond(Pair)));
	else
	  Result = list_AssocCons(Result, (POINTER)term_TopSymbol(Atom), 
				  list_List(term_Copy(term_FirstArgument(Atom))));
      }
    }
  }
  
  prfs_DeleteFinMonPreds(Search);
  prfs_SetFinMonPreds(Search, Result);
}


NAT prfs_GetNumberOfInstances(PROOFSEARCH Search, LITERAL Literal, BOOL Usables)
/**************************************************************
  INPUT:   A proof search object, a literal, and a boolean flag.
  RETURNS: The number of instances of the literal's atom.
  EFFECT:  
***************************************************************/
{
  TERM         Atom;
  NAT          NrOfInstances;
  SHARED_INDEX WOIndex, UsIndex;

  Atom = clause_LiteralAtom(Literal);
  WOIndex = prfs_WorkedOffSharingIndex(Search);
  UsIndex = prfs_UsableSharingIndex(Search);
  NrOfInstances = sharing_GetNumberOfInstances(Atom, WOIndex);
  if (Usables)
    NrOfInstances += sharing_GetNumberOfInstances(Atom, UsIndex);

  if (fol_IsEquality(Atom)) {
    /* Exchange the subterms of the equation, and count the instances, too */
    Atom = term_Create(fol_Equality(), list_Reverse(term_ArgumentList(Atom)));

    NrOfInstances += sharing_GetNumberOfInstances(Atom, WOIndex);
    if (Usables)
      NrOfInstances += sharing_GetNumberOfInstances(Atom, UsIndex);

    list_Delete(term_ArgumentList(Atom));
    term_Free(Atom);

    /* If equation is oriented, consider instances of the greater side, too */
    Atom = clause_LiteralAtom(Literal);
    if (clause_LiteralIsOrientedEquality(Literal)) {
      NrOfInstances += sharing_GetNumberOfInstances(term_FirstArgument(Atom),
						    WOIndex);
      if (Usables)
	NrOfInstances += sharing_GetNumberOfInstances(term_FirstArgument(Atom),
						      UsIndex);
    }
  }
    
  return NrOfInstances;
}
