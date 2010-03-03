/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *               SPLITTING OF CLAUSES                     * */
/* *                                                        * */
/* *  $Module:   SPLIT                                      * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1997, 1998, 2000                  * */
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

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "rules-split.h"

static LIST  split_DeleteClausesDependingOnLevelFromList(PROOFSEARCH,LIST, int, LIST*);
static LIST  split_DeleteInvalidClausesFromList(PROOFSEARCH, int, LIST);
static void  split_DeleteInvalidClausesFromStack(PROOFSEARCH);
static LIST  split_RemoveUnnecessarySplits(PROOFSEARCH, CLAUSE);


/**************************************************************/
/* Functions                                                  */
/**************************************************************/


LIST split_Backtrack(PROOFSEARCH PS, CLAUSE EmptyClause, CLAUSE* SplitClause) 
/**************************************************************
  INPUT:   A proofsearch object, an empty clause and a pointer to a clause
           used as return value.
  RETURNS: A list of clauses deleted in the backtracked split levels.
           <*SplitClause> is set to the split clause for the right branch
	   of the splitting step, or NULL, if the tableau is finished.
  EFFECT:  Backtracks the top of the split stack wrt the empty clause's level
***************************************************************/
{
  SPLIT ActBacktrackSplit;
  LIST  RecoverList, Scan;
  int   Backtracklevel;

  ActBacktrackSplit = (SPLIT)NULL;
  RecoverList       = split_RemoveUnnecessarySplits(PS, EmptyClause);
  Backtracklevel    = clause_SplitLevel(EmptyClause);
  *SplitClause      = NULL;

  /* Backtrack all split levels bigger than the level of the empty clause */
  while (!prfs_SplitStackEmpty(PS) && (prfs_ValidLevel(PS) > Backtracklevel)) {
    ActBacktrackSplit = prfs_SplitStackTop(PS);
    prfs_SplitStackPop(PS);
    if (prfs_SplitFatherClause(ActBacktrackSplit) != (CLAUSE)NULL) {
      RecoverList = list_Cons(prfs_SplitFatherClause(ActBacktrackSplit),
			      RecoverList);
      prfs_SplitSetFatherClause(ActBacktrackSplit, NULL);
    }
    RecoverList = list_Nconc(prfs_SplitDeletedClauses(ActBacktrackSplit),
			     RecoverList);
    clause_DeleteClauseList(prfs_SplitBlockedClauses(ActBacktrackSplit));
    prfs_SplitFree(ActBacktrackSplit);
    prfs_DecValidLevel(PS);
  }
  
  /* Backtrack further for all right branches on top of the stack */
  while (!prfs_SplitStackEmpty(PS) &&
	 list_Empty(prfs_SplitBlockedClauses(prfs_SplitStackTop(PS)))) {
    ActBacktrackSplit = prfs_SplitStackTop(PS);
    prfs_SplitStackPop(PS);
    if (prfs_SplitFatherClause(ActBacktrackSplit) != (CLAUSE)NULL)
      RecoverList = list_Cons(prfs_SplitFatherClause(ActBacktrackSplit),
			      RecoverList);
    RecoverList = list_Nconc(prfs_SplitDeletedClauses(ActBacktrackSplit),
			     RecoverList);
    prfs_SplitFree(ActBacktrackSplit);
    prfs_DecValidLevel(PS);
  }
  
  if (!prfs_SplitStackEmpty(PS)) {
    /* Enter the right branch of the splitting step */
    int SplitMinus1;
    LIST RightClauses;

    SplitMinus1       = prfs_ValidLevel(PS) - 1;
    ActBacktrackSplit = prfs_SplitStackTop(PS);

    RecoverList       = list_Nconc(prfs_SplitDeletedClauses(ActBacktrackSplit),
				   RecoverList);
    prfs_SplitSetDeletedClauses(ActBacktrackSplit, list_Nil());    
    RecoverList       = split_DeleteInvalidClausesFromList(PS, SplitMinus1,
							   RecoverList);

    RightClauses = prfs_SplitBlockedClauses(ActBacktrackSplit);
    prfs_SplitSetBlockedClauses(ActBacktrackSplit, list_Nil());    
    for (Scan = RightClauses; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
      if (clause_Number(list_Car(Scan)) == 0) {
	/* Found the right clause, the negation clauses have number -1. */
#ifdef CHECK
	if (*SplitClause != NULL) {
	  misc_StartErrorReport();
	  misc_ErrorReport("\n In split_Backtrack:");
	  misc_ErrorReport(" Found two blocked clauses ");
	  misc_ErrorReport("\n with clause number 0 (this marks the clause ");
	  misc_ErrorReport("\n for the right branch of the tableau).");
	  misc_FinishErrorReport();
	}
#endif
	*SplitClause = list_Car(Scan);
      }
      
      clause_NewNumber((CLAUSE) list_Car(Scan));
      clause_AddParentClause((CLAUSE) list_Car(Scan), clause_Number(EmptyClause));
      clause_AddParentLiteral((CLAUSE) list_Car(Scan), 0);  /* dummy literal */
    }

#ifdef CHECK
    if (*SplitClause == NULL) {
      misc_StartErrorReport();
      misc_ErrorReport("\n In split_Backtrack: Didn´t find a blocked clause");
      misc_ErrorReport("\n with clause number 0. (this marks the clause ");
      misc_ErrorReport("\n for the right branch of the tableau).");
      misc_FinishErrorReport();
    }
#endif
    
    RecoverList = list_Nconc(RightClauses, RecoverList);

    /* Then, delete clauses from current level (Hack) */
    prfs_DecValidLevel(PS);
    prfs_MoveInvalidClausesDocProof(PS);
    split_DeleteInvalidClausesFromStack(PS);
    prfs_IncValidLevel(PS);
  } else {
    /* Don't delete clauses from current level (split is top level) */
    prfs_MoveInvalidClausesDocProof(PS);
    for (Scan = RecoverList; !list_Empty(Scan); Scan = list_Cdr(Scan))
      prfs_InsertDocProofClause(PS, list_Car(Scan));
    list_Delete(RecoverList);
    RecoverList = list_Nil();
  }
  prfs_SetLastBacktrackLevel(PS, prfs_ValidLevel(PS));

  return RecoverList;
}


static LIST split_DeleteClausesDependingOnLevelFromList(PROOFSEARCH Search,
							LIST ClauseList,
							int Level, LIST* New)
/**************************************************************
  INPUT:   A proof search object, a list of unshared clauses
           and a split level.
  EFFECT:  Deletes all clauses depending on split level from
           <ClauseList>.
           All split stored deleted clauses from the level of
           the deleted clauses from <ClauseList> are stored in
           <*New>.
  RETURNS: The updated list and the recover clauses in <*New>.
***************************************************************/
{
  LIST   Scan;
  CLAUSE Clause;
  SPLIT  Reinsert;

  for (Scan = ClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    Clause = list_Car(Scan);   
    if (clause_DependsOnSplitLevel(Clause, Level)) {
      Reinsert = prfs_GetSplitOfLevel(clause_SplitLevel(Clause), Search);
      if (prfs_SplitDeletedClauses(Reinsert) != list_Nil()) {
	*New = list_Nconc(prfs_SplitDeletedClauses(Reinsert), *New);
	prfs_SplitSetDeletedClauses(Reinsert, list_Nil());
      }
      prfs_InsertDocProofClause(Search,Clause);
      list_Rplaca(Scan, NULL);
    }
  }
  return list_PointerDeleteElement(ClauseList, NULL);
}
 

static LIST split_DeleteClausesDependingOnLevelFromSet(PROOFSEARCH PS,
						       LIST ClauseList,
						       int SplitLevel)
/**************************************************************
  INPUT:   A PROOFSEARCH object, a list of shared clauses
           and a split level.
  RETURNS: A list of clauses that have to be recovered possibly.
  EFFECT:  Clauses from the clause list depending on <SplitLevel>
           are moved to the doc proof index of <PS>.
           All formerly redundant clauses that were reduced by a clause
           of the same split level as a clause from the list depending
           on <SplitLevel> are returned.
***************************************************************/
{
  LIST   scan, delList, recover;
  CLAUSE clause;
  SPLIT  reinsert;

  delList = recover = list_Nil();

  for (scan = ClauseList; !list_Empty(scan); scan = list_Cdr(scan)){
    clause = list_Car(scan);
    if (clause_DependsOnSplitLevel(clause, SplitLevel)) {
      reinsert = prfs_GetSplitOfLevel(clause_SplitLevel(clause), PS);
      recover = list_Nconc(prfs_SplitDeletedClauses(reinsert), recover);
      prfs_SplitSetDeletedClauses(reinsert, list_Nil());
      delList = list_Cons(clause, delList);
    }
  }

  /* WARNING: The following move operations change the worked off */
  /* and usable sets of the proof search object destructively.    */
  /* So it's impossible to move those function calls into the     */
  /* loop above.                                                  */
  for ( ; !list_Empty(delList); delList = list_Pop(delList)) {
    clause = list_Car(delList);
    if (clause_GetFlag(clause, WORKEDOFF))
      prfs_MoveWorkedOffDocProof(PS, clause);
    else
      prfs_MoveUsableDocProof(PS, clause);
  }
  return recover;
}



static LIST split_DeleteInvalidClausesFromList(PROOFSEARCH Search, int Level,
					       LIST ClauseList)
/**************************************************************
  INPUT:   A proof search object, a split level and a list of clauses.
  RETURNS: The list where invalid clauses wrt 'Level' are deleted.
  EFFECT:  The invalid clauses are stored in the doc proof index
           of the proof search object if necessary.
***************************************************************/
{
  LIST   Scan;
  CLAUSE Clause;

  /*printf("\nDiese Liste soll von ungueltigen (Level > %d) "
    "befreit werden: \n",Level);fflush(stdout);
    clause_ListPrint(ClauseList);*/

  for (Scan = ClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    Clause = list_Car(Scan);
    if (!prfs_IsClauseValid(Clause,Level)) {
      prfs_InsertDocProofClause(Search,Clause);
      list_Rplaca(Scan, NULL);
    }
  }
  return list_PointerDeleteElement(ClauseList, NULL);
}

static void split_DeleteInvalidClausesFromStack(PROOFSEARCH Search)
/**************************************************************
  INPUT:   A proof search object.            
  EFFECT:  All clauses in the split stack of <Search> that have a higher
           split level than the current <Search> split level are deleted.
***************************************************************/
{
  LIST   Scan1,Scan2,ClauseList;
  int    Level;
  CLAUSE Clause;

  Level = prfs_ValidLevel(Search);

  for (Scan1=prfs_SplitStack(Search);!list_Empty(Scan1);Scan1=list_Cdr(Scan1)) {
    ClauseList = prfs_SplitDeletedClauses(list_Car(Scan1));
    for (Scan2 = ClauseList; !list_Empty(Scan2); Scan2 = list_Cdr(Scan2)) {
      Clause = (CLAUSE)list_Car(Scan2);
      if (!prfs_IsClauseValid(Clause,Level)) {
	prfs_InsertDocProofClause(Search,Clause);
	list_Rplaca(Scan2, NULL);
      }
    }
    prfs_SplitSetDeletedClauses(list_Car(Scan1),list_PointerDeleteElement(ClauseList, NULL));
  }
}


static LIST split_RemoveUnnecessarySplits(PROOFSEARCH PS, CLAUSE EmptyClause)
/**************************************************************
  INPUT:   An empty clause and a proof search object
  EFFECT:  Removes all splits up to the last backtrack level
           that were not necessary to derive the empty clause.
  RETURNS: A list of recovered clauses.
***************************************************************/
{
  LIST Scan;
  LIST Recover, New;
  LIST Deleted;
  LIST ScanStack;

  int SplitLevel;
  int LastBacktrackLevel;
  SPLIT Split,ScanSplit;

  Scan               = prfs_SplitStack(PS);
  SplitLevel         = prfs_ValidLevel(PS);
  LastBacktrackLevel = prfs_LastBacktrackLevel(PS);
  Recover            = list_Nil();

  while (SplitLevel > LastBacktrackLevel) {
    if (prfs_SplitIsUnused(list_Car(Scan)) &&
	!clause_DependsOnSplitLevel(EmptyClause, SplitLevel)) {
      New   = list_Nil();
      Split = list_Car(Scan);

      /*printf("\n\t Removed: %d",prfs_SplitSplitLevel(Split));*/
      
      clause_DeleteClauseList(prfs_SplitBlockedClauses(Split));
      prfs_SplitSetBlockedClauses(Split, list_Nil());
      
      Recover = list_Nconc(prfs_SplitDeletedClauses(Split), Recover);
      prfs_SplitSetDeletedClauses(Split, list_Nil());
      
      if (prfs_SplitFatherClause(Split) != (CLAUSE)NULL) {
	Recover = list_Cons(prfs_SplitFatherClause(Split),Recover);
	prfs_SplitSetFatherClause(Split,NULL);
      }
      Recover = split_DeleteClausesDependingOnLevelFromList(PS, Recover, SplitLevel, &New);
      
      ScanStack = prfs_SplitStack(PS);
      while (!list_StackEmpty(ScanStack) &&  
	     prfs_SplitSplitLevel((ScanSplit = (SPLIT)list_Car(ScanStack))) > LastBacktrackLevel) {
	Deleted = prfs_SplitDeletedClauses(ScanSplit);
	prfs_SplitSetDeletedClauses(ScanSplit, list_Nil()); /* IMPORTANT!, see next line */
	Deleted = split_DeleteClausesDependingOnLevelFromList(PS, Deleted, SplitLevel, &New);
	prfs_SplitSetDeletedClauses(ScanSplit, Deleted);
	ScanStack = list_Cdr(ScanStack);
      }
      
      while (!list_Empty(New)) {
	Deleted = list_Nil();
	Recover = list_Nconc(split_DeleteClausesDependingOnLevelFromList(PS, New, SplitLevel, &Deleted),
			     Recover);
	New     = Deleted;
      }
      Recover = list_Nconc(Recover, 
		    split_DeleteClausesDependingOnLevelFromSet(PS, prfs_UsableClauses(PS), SplitLevel));
      Recover = list_Nconc(Recover,
			   split_DeleteClausesDependingOnLevelFromSet(PS, prfs_WorkedOffClauses(PS), SplitLevel));
      
      prfs_SplitSetUsed(Split);
    }
    
    SplitLevel--;
    Scan = list_Cdr(Scan);
  }
  return Recover;
}


void split_DeleteClauseAtLevel(PROOFSEARCH PS, CLAUSE Clause, int Level)
/**************************************************************
  INPUT:   A clause, a level and a proofsearch object
  RETURNS: Nothing.
  EFFECT:  <Clause> is deleted from the usable or worked off set
           and made unshared.
***************************************************************/
{
  if (clause_GetFlag(Clause,WORKEDOFF)) 
    prfs_ExtractWorkedOff(PS, Clause);
  else 
    prfs_ExtractUsable(PS, Clause);

  split_KeepClauseAtLevel(PS, Clause, Level);
}


void split_KeepClauseAtLevel(PROOFSEARCH PS, CLAUSE Clause, int Level)
/**************************************************************
  INPUT:   A clause and a level as int.
  RETURNS: None.
  MEMORY:  A copy of clause is made and kept within the split stack.
***************************************************************/
{
  SPLIT  Split;

  Split = prfs_GetSplitOfLevel(Level, PS);
  prfs_SplitSetDeletedClauses(Split,list_Cons(Clause, prfs_SplitDeletedClauses(Split)));
}


LIST split_ExtractEmptyClauses(LIST Clauses, LIST* EmptyClauses)
/**************************************************************
  INPUT:   A list of clauses and a pointer to a list of empty clauses.
  RETURNS: <Clauses> without all empty clauses where the empty clauses
           are moved to <EmptyClauses>
  MEMORY:  Destructive on <Clauses>.
***************************************************************/
{
  LIST   Scan;
  CLAUSE Clause;

  for (Scan=Clauses;!list_Empty(Scan);Scan=list_Cdr(Scan)) {
    Clause = (CLAUSE)list_Car(Scan);
    if (clause_IsEmptyClause(Clause)) {
      *EmptyClauses = list_Cons(Clause,*EmptyClauses);
      list_Rplaca(Scan,NULL);
    }
  }
  Clauses = list_PointerDeleteElement(Clauses,NULL);

  return Clauses;
}

CLAUSE split_SmallestSplitLevelClause(LIST Clauses)
/**************************************************************
  INPUT:   A non-empty list of clauses.
  RETURNS: The clause with the smallest split level.
***************************************************************/
{
  CLAUSE Result;

  Result  = (CLAUSE)list_Car(Clauses);
  Clauses = list_Cdr(Clauses);
  
  while (!list_Empty(Clauses)) {
    if (clause_SplitLevel(Result) > clause_SplitLevel(list_Car(Clauses)))
      Result  = list_Car(Clauses);
    Clauses = list_Cdr(Clauses);
  }

  return Result;
}
