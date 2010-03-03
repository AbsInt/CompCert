/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *             PROOF CHECKING                             * */
/* *                                                        * */
/* *  Copyright (C) 1998, 1999, 2000, 2001                  * */
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
/* $Revision: 21527 $                                        * */
/* $State$                                            * */
/* $Date: 2005-04-24 21:10:28 -0700 (Sun, 24 Apr 2005) $                             * */
/* $Author: duraid $                                       * */
/* *                                                        * */
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

/* $RCSfile$ */

#include "proofcheck.h"


/* options */
int        pcheck_Timelimit;
const char *pcheck_ProofFileSuffix;
BOOL       pcheck_Quiet;

/* options for graph generation */
BOOL        pcheck_ClauseCg;
BOOL        pcheck_GenNamedCg, pcheck_GenRedCg;
const char  *pcheck_CgName, *pcheck_RedCgName;
GRAPHFORMAT pcheck_GraphFormat;


static int pcheck_MaxSplitLevel(LIST Clauses)
/**************************************************************
  INPUT:   A list of clauses.
  RETURNS: The maximum split level of a clause.
***************************************************************/
{
  int Max;
  int Act;
  
  Max = 0;
  while (!list_Empty(Clauses)) {
    Act = clause_SplitLevel(list_Car(Clauses));
    if (Act > Max) 
      Max = Act;
    Clauses = list_Cdr(Clauses);
  }
  return Max;
}


static __inline__ int pcheck_MaxParentSplitLevel(CLAUSE Clause) 
/**************************************************************
  INPUT:   A clause
  RETURNS: The max split level of the parent clauses
***************************************************************/
{
  return pcheck_MaxSplitLevel(clause_ParentClauses(Clause));
}


static BOOL pcheck_ClauseIsFromLeftSplit(CLAUSE Clause)
/**************************************************************
  INPUT  : A Clause                                                      
  RETURNS: TRUE iff the clause is the left half of a split
  CAUTION: This works also for clauses without parents, since
           pcheck_MaxParentSplitLevel returns 0 in that case.
***************************************************************/
{
  return (clause_SplitLevel(Clause) > pcheck_MaxParentSplitLevel(Clause));
}


static BOOL pcheck_ClauseIsFromRightSplit(CLAUSE Clause)
/**************************************************************
  INPUT:   A clause
  RETURNS: TRUE iff the clause is from the right half of a split
***************************************************************/
{
  if (list_Empty(clause_ParentClauses(Clause)))
    return FALSE;

  return clause_IsEmptyClause(list_Car(clause_ParentClauses(Clause)));
}

static BOOL pcheck_ClauseIsFromSplit(CLAUSE Clause)
/**************************************************************
 INPUT  : A clause
 RETURNS: TRUE iff the clause is from a split
***************************************************************/
{
  return (pcheck_ClauseIsFromRightSplit(Clause) ||
	  pcheck_ClauseIsFromLeftSplit(Clause));
}


static int pcheck_LabelToNumber(const char* Label)
/**************************************************************
  INPUT:   A clause label
  RETURNS: The label converted to a number.
  EFFECT:  If the conversion fails an error message is printed
           and the program exits.
***************************************************************/
{
  int Number;

  if (!string_StringToInt(Label, FALSE, &Number)) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n In pcheck_LabelToNumber:");
    misc_UserErrorReport(" Could not convert clause");
    misc_UserErrorReport(" label %s to a number.\n", Label);
    misc_FinishUserErrorReport();
  }

  return Number;
}


static int pcheck_CompareNumberAndClause(const void* Number, const void* ClausePtr)
/**************************************************************
  INPUT:   A number and a pointer to a CLAUSE.
  RETURNS: 1) a negative number if <number> is < number of <Clause>
           2) 0 if <Number> is equal to the number of <Clause>
           3) a positive number if <Number> is > number of <Clause>
  EFFECT:  This function is used as parameter to the bsearch function.
***************************************************************/
{
  return (int)Number - clause_Number(*(const CLAUSE*)ClausePtr);
}


static void pcheck_ParentNumbersToPointersInVector(CLAUSE* ClauseVector, int Size)
/**************************************************************
  INPUT:   A clause vector without duplicate clauses and the maximal
           number of elements in the vector
  EFFECTS: All clause parent numbers are replaced by pointers
           to the parents.
  CAUTION: The clause vector has to be sorted by increasing
           clause numbers, since this function performs a binary search
           on the vector.
***************************************************************/
{
  int     Position;
  LIST    NewParents, OldParents;
  LIST    ScanParents;
  int     ParentNum;
  CLAUSE* Parent;
  
  for (Position = 0; Position < Size; Position++)  {
    OldParents = clause_ParentClauses(ClauseVector[Position]);
    NewParents = list_Copy(OldParents);
    
    for (ScanParents = NewParents; !list_Empty(ScanParents); ScanParents = list_Cdr(ScanParents)) {     
      ParentNum = (int)list_Car(ScanParents);
      /* Binary search for parent clause with number <ParentNum>. */
      Parent = bsearch((const void*)ParentNum, ClauseVector, Size,
		       sizeof(CLAUSE), pcheck_CompareNumberAndClause);
      if (Parent != NULL)
	list_Rplaca(ScanParents, *Parent);  
      else {
	misc_StartUserErrorReport();
	misc_UserErrorReport("\n Error: Missing parent clause %d of clause %d.\n", 
			     ParentNum, clause_Number(ClauseVector[Position]));
	misc_FinishUserErrorReport();
      }
    }    
    clause_SetParentClauses(ClauseVector[Position], NewParents);
    list_Delete(OldParents); 
  }
}


static LIST pcheck_ForceParentNumbersToPointersInVector(CLAUSE* ClauseVector,
							int Size)
/**************************************************************
  INPUT:   A clause vector, possibly with duplicates
  RETURNS: All numbers of clauses <c> that are missing a parent clause
           from the transitive hull of parent clauses of <c>.
  EFFECTS: All MARKED and HIDDEN flags of the clauses are changed.
           All parent numbers are converted to pointers, if the
           parents exist, otherwise the parent number is deleted
           from the list.
           The parent literal list is changed accordingly.
           A clause <c> is marked as HIDDEN, if any clause
           from the transitive hull of parent clauses of <c>
           was missing in <ClauseVector>.
***************************************************************/
{
  int     Position;
  LIST    NewParents, NewPLits, Parents, PLits, Missing;
  int     ParentNum, PLitNum;
  CLAUSE  *Parent, Clause;

  Missing = list_Nil();

  for (Position = 0; Position < Size; Position++) {
    clause_RemoveFlag(ClauseVector[Position], MARKED); 
    clause_RemoveFlag(ClauseVector[Position], HIDDEN);
  }

  for (Position = 0; Position < Size; Position++)  {
    Clause = ClauseVector[Position];
    if (!clause_GetFlag(Clause, MARKED)) { 
      clause_SetFlag(Clause, MARKED);
      Parents    = clause_ParentClauses(Clause);
      PLits      = clause_ParentLiterals(Clause);
      NewParents = list_Nil();
      NewPLits   = list_Nil();

      while (!list_Empty(Parents)) {
	ParentNum = (int)list_Car(Parents);
	PLitNum   = (int)list_Car(PLits);
	/* Binary search for parent clause with number <ParentNum>. */
	Parent = bsearch((const void*)ParentNum, ClauseVector, Size,
			 sizeof(CLAUSE), pcheck_CompareNumberAndClause);
	if (Parent == NULL) {
	  Missing = list_Cons((POINTER)ParentNum, Missing); 
	  clause_SetFlag(Clause, HIDDEN);
	} else {
	  if (clause_GetFlag(*Parent, HIDDEN))
	    clause_SetFlag(Clause, HIDDEN);
	  NewParents  = list_Cons((POINTER)*Parent, NewParents);
	  NewPLits    = list_Cons((POINTER)PLitNum, NewPLits);
	}
	Parents = list_Cdr(Parents); 
	PLits   = list_Cdr(PLits);
      }
      list_Delete(clause_ParentClauses(Clause));
      list_Delete(clause_ParentLiterals(Clause));
      NewParents = list_NReverse(NewParents);
      NewPLits   = list_NReverse(NewPLits);
      clause_SetParentClauses(Clause, NewParents);
      clause_SetParentLiterals(Clause, NewPLits);
    } /* if clause is not marked */
  } /* for all clauses */
 
  return Missing;
}


static int pcheck_CompareClauseNumber(const void* C1, const void* C2)
/**************************************************************
  INPUT  : Two pointers to CLAUSEs.
  RETURNS: 1) a negative number if the number of C1 is < number of C2.
           2) 0 if C1 and C2 have the same clause number
              (that means a possible bug in SPASS)
           3) a positive number if number of C1 > number of C2
  EFFECT:  This function is used as parameter to the qsort function.
************************************************************/
{
  return clause_Number(*(const CLAUSE*)C1) - clause_Number(*(const CLAUSE*)C2);
}


static LIST pcheck_ConvertParentsInList(LIST List)
/**************************************************************
  INPUT:   A list of clauses.
  RETURNS: The list of missing parent clause numbers from the list 
  EFFECTS: Parent numbers are converted to pointers
***************************************************************/
{
  int     Size, Index;
  CLAUSE* ClauseVector;
  LIST    Missing;

  Size = list_Length(List);
  if (Size == 0)
    return list_Nil();

  /* convert list into vector for binary search */
  ClauseVector = (CLAUSE*)memory_Malloc(sizeof(CLAUSE) * Size);
  for (Index = 0; !list_Empty(List); List = list_Cdr(List), Index++)
    ClauseVector[Index] = list_Car(List);

  /* sort the clauses in vector by increasing clause number */
  qsort(ClauseVector, Size, sizeof(CLAUSE), pcheck_CompareClauseNumber);

  /* convert parent lists */
  Missing = pcheck_ForceParentNumbersToPointersInVector(ClauseVector, Size);
  
  memory_Free(ClauseVector, sizeof(CLAUSE) * Size);
  return Missing;
}


LIST pcheck_ConvertParentsInSPASSProof(PROOFSEARCH Search, LIST EmptyClauses) 
/**************************************************************
  INPUT  : A proofsearch object with clauses sorted by weight
           and an unsorted list <EmptyClauses>
  RETURNS: The lists, where the clauses in <EmptyClauses> are
           now sorted by weight, and parent numbers
           in the clauses are replaced by parent pointers
***************************************************************/
{
  LIST    AllLists; 
  LIST    Missing;

  AllLists = list_Nconc(list_Copy(prfs_DocProofClauses(Search)),
			list_Copy(EmptyClauses));
  AllLists = list_Nconc(list_Copy(prfs_UsableClauses(Search)), AllLists);
  AllLists = list_Nconc(list_Copy(prfs_WorkedOffClauses(Search)), AllLists);
  
  AllLists = pcheck_ClauseNumberMergeSort(AllLists);
  Missing  = pcheck_ConvertParentsInList(AllLists);
  list_Delete(AllLists);

  return Missing;
}


static LIST pcheck_ParentNumbersToParents(LIST Proof)
/**************************************************************
  INPUT:   A list of clauses, representing a proof.
  RETURNS: The list, where parent numbers in the
           parent list of clauses are replaced
           by the parents (pointers).
  CAUTION: For finding the clause corresponding to a
           a clause number, the <Proof> list is searched
	   with binary search. This is correct only if
	   the clause numbers in <Proof> are increasing.
************************************************************/
{
  LIST    ScanClauses;
  int     ProofLength, Position;
  CLAUSE* ClauseVector;

  if (list_Empty(Proof))
    return list_Nil();

  /* convert list into vector for binary search */
  ProofLength  = list_Length(Proof);
  ClauseVector = (CLAUSE*) memory_Malloc(ProofLength * sizeof(CLAUSE));

  for (ScanClauses = Proof, Position = 0; !list_Empty(ScanClauses);
       ScanClauses = list_Cdr(ScanClauses), Position++) {
    ClauseVector[Position] = list_Car(ScanClauses);
  }

  /* sort the clauses in vector by increasing clause number */
  qsort(ClauseVector, ProofLength, sizeof(CLAUSE), pcheck_CompareClauseNumber);
 
  /* convert parent lists */
  pcheck_ParentNumbersToPointersInVector(ClauseVector, ProofLength);
 
  memory_Free(ClauseVector, ProofLength * sizeof(CLAUSE));

  return Proof;
}


LIST pcheck_ParentPointersToParentNumbers(LIST Clauses)
/**************************************************************
 INPUT  : A list of clauses                                                      
 RETURNS: The list with parent pointers replaced by
          parent numbers
 EFFECTS: Sets marks on all clauses.                            
***************************************************************/
{
  LIST ScanClauses;
  LIST ScanParents;

  pcheck_ClauseListRemoveFlag(Clauses, MARKED);

  for (ScanClauses = Clauses; !list_Empty(ScanClauses); ScanClauses = list_Cdr(ScanClauses)) {
    if (!clause_GetFlag(list_Car(ScanClauses), MARKED)) {
      for (ScanParents = clause_ParentClauses(list_Car(ScanClauses)); !list_Empty(ScanParents);
	   ScanParents = list_Cdr(ScanParents))
	list_Rplaca(ScanParents, (POINTER)clause_Number(list_Car(ScanParents))); 
      clause_SetFlag(list_Car(ScanClauses), MARKED);
    }
  }
  return Clauses;
}


LIST pcheck_ConvertTermListToClauseList(LIST ProofRest, FLAGSTORE Flags,
					PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A list of quintupels (lists) representing a proof,
           a flag store, and a precedence.
  RETURNS: The conversion of this list into the internal clause
           structure. For each clause, the numbers of parent
	   clauses are replaced by pointers to the parents.
***************************************************************/
{
  LIST    Clauses;
  LIST    ProofLine;
  TERM    ClauseTerm;
  CLAUSE  Clause;
  int     Level;
  int     ClauseNumber;
  LIST    ParentLabels;
  LIST    ParentIds;     
  LIST    ParentLits;    /* this is a dummy list; parent lits are not yet specified in a SPASS proof */
  RULE    Origin;
  char*   ClauseLabel;

  Clauses = list_Nil();  /* result */

  while (!list_Empty(ProofRest)) {    
    /* break proof line into components */
    ProofLine     = list_Car(ProofRest);
    
    ClauseLabel   = list_First(ProofLine);
    ClauseTerm    = list_Second(ProofLine);    
    /* replace by NULL clause, since dfg_CreateClauseFromTerm deletes clause ! */
    list_Rplaca(list_Cdr(ProofLine), clause_Null()); 
    ParentLabels  = (LIST)list_Third(ProofLine);
    Level         = (int)list_Fourth(ProofLine);
    Origin        = (RULE)list_Fifth(ProofLine);

    /* Conversion */
    Clause       = dfg_CreateClauseFromTerm(ClauseTerm, TRUE, Flags,Precedence);
    /* It's necessary to update the weight since dfg_CreateClauseFromTerm */
    /* doesn't set it. */
    clause_UpdateWeight(Clause, Flags);
    ClauseNumber = pcheck_LabelToNumber(ClauseLabel);
    ParentIds    = list_Nil();
    ParentLits   = list_Nil();

    while (!list_Empty(ParentLabels)) {
      ParentIds  = list_Cons((POINTER)pcheck_LabelToNumber(list_Car(ParentLabels)), ParentIds); 
      ParentLits = list_Cons(0, ParentLits);
      ParentLabels   = list_Cdr(ParentLabels);
    }
    
    /* set all data */
    clause_SetNumber(Clause, ClauseNumber);
    ParentIds = list_NReverse(ParentIds);
    clause_SetParentClauses(Clause, ParentIds);
    clause_SetParentLiterals(Clause, ParentLits);
    Clause->origin = Origin;

    clause_SetSplitLevel(Clause, Level); 
    if (Level > 0) {
      clause_ClearSplitField(Clause);
      clause_SetSplitFieldBit(Clause, Level);
    } else 
      clause_SetSplitField(Clause, (SPLITFIELD)NULL,0);

    clause_RemoveFlag(Clause, MARKED);
    Clauses   = list_Cons(Clause, Clauses);
    ProofRest = list_Cdr(ProofRest);  
  }
  Clauses = list_NReverse(Clauses);
  
  /* convert parent numbers to pointers */
  Clauses = pcheck_ParentNumbersToParents(Clauses);
  
  return Clauses;
}


static BOOL pcheck_ClauseIsUnmarked(CLAUSE C)
/**************************************************************
  INPUT:   A clause
  RETURNS: The value of the clauses MARKED flag
***************************************************************/
{
  return !clause_GetFlag(C, MARKED);
}


static void pcheck_RemoveUnmarkedFromTableau(TABLEAU T)
/**************************************************************
  INPUT:   A tableau
  RETURNS: Nothing.
  EFFECTS: Delete all clauses that have the MARKED flag
           set from tableau.
***************************************************************/
{
  if (tab_IsEmpty(T))
    return;
  
  tab_SetClauses(T, list_DeleteElementIf(tab_Clauses(T),
					 (BOOL (*)(POINTER))pcheck_ClauseIsUnmarked));
  
  pcheck_RemoveUnmarkedFromTableau(tab_LeftBranch(T));
  pcheck_RemoveUnmarkedFromTableau(tab_RightBranch(T));
}


static void pcheck_CollectUnmarkedSplits(TABLEAU T, LIST* Splits)
/**************************************************************
  INPUT:   A tableau, a list of clauses by reference
  RETURNS: Nothing.
  EFFECTS: Add all split clauses in the tableau that are not
           marked to the <Splits> list.
***************************************************************/
{
  LIST Scan;

  if (tab_IsEmpty(T))
    return;

  for (Scan = tab_Clauses(T); !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    if (!clause_GetFlag(list_Car(Scan), MARKED) && clause_IsFromSplitting(list_Car(Scan))) 
      (*Splits) = list_Cons(list_Car(Scan), *Splits);
  }
  
  pcheck_CollectUnmarkedSplits(tab_LeftBranch(T), Splits);
  pcheck_CollectUnmarkedSplits(tab_RightBranch(T), Splits);
}


/* EK: unused, only recursive */
static void pcheck_TableauSplitsComplete(TABLEAU T)
/**************************************************************
  INPUT  : A tableau
  RETURNS: Checks that every split has exactly two or no
           successors. This condition must be true after
           tab_RemoveRedundantSplits has been called.
***************************************************************/
{
  if (tab_IsEmpty(T))
    return;
  
  if (tab_RightBranchIsEmpty(T) && !tab_LeftBranchIsEmpty(T)) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n Error: Split of clause %d has no right branch.\n", 
			 clause_Number(tab_SplitClause(T)));
    misc_FinishUserErrorReport();
  }
 
  if (!tab_RightBranchIsEmpty(T) && tab_LeftBranchIsEmpty(T)) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n Error: Split of clause %d has no left branch.\n", 
			 clause_Number(tab_SplitClause(T)));
    misc_FinishUserErrorReport();
  }
  
  pcheck_TableauSplitsComplete(tab_LeftBranch(T));
  pcheck_TableauSplitsComplete(tab_RightBranch(T));
}


static void pcheck_RightSplitParents(CLAUSE SplitClause, CLAUSE RightSplitClause,
				     CLAUSE LeftSplitClause)
/**************************************************************
  INPUT:   A split clause, and its left and right successors
  EFFECTS: Prints an error message if the split is not correctly
           closed.
***************************************************************/
{
  LIST Scan;
  BOOL HasEmpty, ContainsSplitClause;

  HasEmpty = ContainsSplitClause = FALSE;

  for (Scan = clause_ParentClauses(RightSplitClause);
       !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    if (clause_IsEmptyClause(list_Car(Scan)))
      HasEmpty = TRUE;
    if (clause_Number(list_Car(Scan)) == clause_Number(SplitClause)) 
      ContainsSplitClause = TRUE; 
  }
  
  if (!HasEmpty) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n Error: Right split clause %d has no empty clause as parent.\n", 
			 clause_Number(SplitClause));
    misc_FinishUserErrorReport();
  }

  if (!ContainsSplitClause) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n Error: Right split clause %d", clause_Number(SplitClause));
    misc_UserErrorReport(" does not have its split parent as parent clause.\n");
    misc_FinishUserErrorReport();
  }
}



/* EK: unused, only recursive */
static void pcheck_SplitFormats(TABLEAU T)
/**************************************************************
  INPUT  : A tableau
  RETURNS: TRUE iff all splits:
           - have generated negations of the left split clause
 	     if the left split clause is ground
	   - the conditions for right split clauses are
             as demanded in pcheck_RightSplitParents
***************************************************************/
{
  LIST Scan;

  if (tab_IsEmpty(T))
    return;

  /* for right splits, check that parents have an empty clause */
  /* and the split clause as a parent */

  for (Scan = tab_RightSplitClauses(T); !list_Empty(Scan);
       Scan = list_Cdr(Scan)) {
    pcheck_RightSplitParents(tab_SplitClause(T), list_Car(Scan),
			     tab_LeftSplitClause(T));
  }
    
  pcheck_SplitFormats(tab_RightBranch(T));
  pcheck_SplitFormats(tab_LeftBranch(T));
}


static void pcheck_SplitLevels(TABLEAU T)
/**************************************************************
  INPUT  : A Tableau
  RETURNS: TRUE iff all clauses in the tableau that
           are not splitting clauses have the max split
    	   level of their parents.
  CAUTION: We assume that <T> has correct and complete split
           entries. See pcheck_SplitToProblems.
***************************************************************/
{
  LIST   Scan;
  CLAUSE Clause;
  int    CorrectLevel;

  if (tab_IsEmpty(T))
    return;

  /* check split levels */
  for (Scan = tab_Clauses(T); !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    Clause = list_Car(Scan);
    if (!list_Empty(clause_ParentClauses(Clause))
	&& !clause_IsFromSplitting(Clause)) {
 
     CorrectLevel = pcheck_MaxParentSplitLevel(Clause);
     if (clause_SplitLevel(Clause) != CorrectLevel) {
       misc_StartUserErrorReport();
       misc_UserErrorReport("\n Error: Split level of clause %d should be %d.\n",
			    clause_Number(Clause), CorrectLevel);
       misc_FinishUserErrorReport();
     }
    }
  }

  pcheck_SplitLevels(tab_RightBranch(T));
  pcheck_SplitLevels(tab_LeftBranch(T));
}


/* EK: unused, only recursive */
static void pcheck_SplitPrecheck(TABLEAU T)
/**************************************************************
  INPUT  : A tableau.
  EFFECTS: Stops and prints an error message if a left half
           of a split does not subsume its parents, or
	   if negations have been generated for a non-ground
	   left split clause.
***************************************************************/
{
  if (tab_IsEmpty(T))
    return;
  
  if (!subs_Subsumes(tab_LeftSplitClause(T), tab_SplitClause(T), -1, -1)) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n Error: Incorrect split of %d,", tab_SplitClause(T));
    misc_UserErrorReport(" left half of split does not subsume splitted clause.\n");			 
    misc_FinishUserErrorReport();
  }

  if (list_Length(tab_RightSplitClauses(T)) > 1 &&
      !clause_IsGround(tab_LeftSplitClause(T))) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n Error: Incorrect split of %d,", tab_SplitClause(T));
    misc_UserErrorReport(" non-ground split generated more than two clause.\n");
    misc_FinishUserErrorReport();
  }

  pcheck_SplitPrecheck(tab_LeftBranch(T));
  pcheck_SplitPrecheck(tab_RightBranch(T));
}


BOOL pcheck_BuildTableauFromProof(LIST Proof, TABLEAU* Tableau)
/**************************************************************
  INPUT  : A list of clauses representing a proof, and a pointer
           to a tableau used as return value.
  RETURNS: TRUE iff no errors occurred, FALSE otherwise.
           If TRUE is returned <Tableau> is set to a tableau
	   representing the proof.
  EFFECTS: Errors are commented when they occur.
***************************************************************/
{
  LIST     ProofRest;
  TABLEAU  SplitPos;
  TABPATH  Path;
  CLAUSE   Clause;
  int      ClauseLevel, SplitLevel;
  int      ProofDepth;

  if (list_Empty(Proof)) {
    *Tableau = tab_EmptyTableau();
    return TRUE;
  }

  ProofDepth = pcheck_MaxSplitLevel(Proof);
  *Tableau   = tab_CreateNode();
  Path       = tab_PathCreate(ProofDepth, *Tableau);

  ProofRest = Proof;
  while (!list_Empty(ProofRest)) {

    SplitLevel  = tab_PathLength(Path);
    Clause      = list_Car(ProofRest);
    ClauseLevel = clause_SplitLevel(Clause); 

    /* Special treatment for clauses that result from a splitting step */
    if (pcheck_ClauseIsFromSplit(Clause)) {

      if (ClauseLevel == 0) {
	misc_StartUserErrorReport();
	misc_UserErrorReport("\n Error: Split level of split clause %d is 0.\n", clause_Number(Clause));
	misc_FinishUserErrorReport();
      }

      if (ClauseLevel > SplitLevel+1) {
	misc_StartUserErrorReport();
	misc_UserErrorReport("\n Error: Split level of split clause %d", clause_Number(Clause));
	misc_UserErrorReport(" is not increment of current split level.\n");
	misc_FinishUserErrorReport();
      }

      SplitPos = tab_PathNthNode(Path, ClauseLevel-1);

      if (pcheck_ClauseIsFromLeftSplit(Clause)) {
	/* Left branch of a splitting step */
	if (!tab_LeftBranchIsEmpty(SplitPos)) {
	  misc_StartUserErrorReport();
	  misc_UserErrorReport("\n Error: Multiple left splits for clause %d.\n", 
			       clause_Number(tab_SplitClause(SplitPos)));
	  misc_FinishUserErrorReport();
	}

	Path = tab_PathPrefix(ClauseLevel-1, Path);
	tab_SetSplitClause(SplitPos, list_Car(clause_ParentClauses(Clause)));
	tab_SetLeftSplitClause(SplitPos, Clause);
	tab_AddSplitAtCursor(Path, TRUE);
      } else {
	/* Right branch of a splitting step */
	if (tab_RightBranchIsEmpty(SplitPos)) {
	  
	  if (tab_LeftBranchIsEmpty(SplitPos)) {
	    misc_StartUserErrorReport();
	    misc_UserErrorReport("\n Error: Right split with incorrect split level, clause %d.\n", 
				 clause_Number(Clause));
	    misc_FinishUserErrorReport();
	  }

	  Path = tab_PathPrefix(ClauseLevel-1, Path);
	  tab_AddSplitAtCursor(Path, FALSE);
	}
	tab_AddRightSplitClause(SplitPos, Clause); 
      } /* clause from right split */
    } /* clause from split */
      
    if (ClauseLevel > tab_PathLength(Path)) {
      misc_StartUserErrorReport();
      misc_UserErrorReport("\n Error: Split level of clause %d greater than current level.\n", 
			   clause_Number(Clause));
      misc_FinishUserErrorReport();
    }
    tab_AddClauseOnItsLevel(Clause, Path); 
    
    ProofRest = list_Cdr(ProofRest);   
  } /* while proof is not empty */


  tab_PathDelete(Path);

  return TRUE;
}


static BOOL pcheck_TableauJustificationsRec(TABLEAU T, TABPATH Path)
/**************************************************************
  INPUT  : A Tableau <T>, a <Path> in the tableau
  RETURNS: TRUE iff all clauses in the last node of the
           path are correctly justified.
***************************************************************/
{
  CLAUSE  Clause;
  LIST    ScanClauses;
  LIST    ScanParents;
  LIST    Parents;
  CLAUSE  Parent;
  BOOL    Ok, RightSplit;

  if (tab_IsEmpty(T))
    return TRUE;

  Ok = TRUE; 

  /* for each clause, check that its parents have been justified */

  for (ScanClauses = tab_Clauses(tab_PathTop(Path));
       !list_Empty(ScanClauses); ScanClauses = list_Cdr(ScanClauses)) {

    Clause  = list_Car(ScanClauses);
    Parents = clause_ParentClauses(Clause);
    
    RightSplit = pcheck_ClauseIsFromRightSplit(Clause); 
    
    /* check all parents */
    
    for (ScanParents = Parents; !list_Empty(ScanParents); 
	 ScanParents = list_Cdr(ScanParents)) {
      
      Parent = list_Car(ScanParents);
      
      if ((!(RightSplit && clause_IsEmptyClause(Parent)) &&
	  !(RightSplit && pcheck_ClauseIsFromLeftSplit(Parent))) ||
	  (clause_Number(Parent) > clause_Number(Clause)) ) {
	if (!tab_PathContainsClause(Path, Parent)) {
	  misc_StartUserErrorReport();
	  misc_UserErrorReport("\n Error: Parent clause with number %d is not yet justified.\n", 
			       clause_Number(Parent));
	  misc_FinishUserErrorReport();
	}
      }
    }
  }  /* for all clauses in current node */
  
  
  /* Recursion */
  
  if (!tab_LeftBranchIsEmpty(T)) {
    Path = tab_PathPush(tab_LeftBranch(T), Path);
    Ok   = Ok && pcheck_TableauJustificationsRec(tab_LeftBranch(T), Path);
    Path = tab_PathPop(Path);
  }
  
  if (!tab_RightBranchIsEmpty(T)) {
    Path = tab_PathPush(tab_RightBranch(T), Path);
    Ok   = Ok && pcheck_TableauJustificationsRec(tab_RightBranch(T), Path);
    Path = tab_PathPop(Path);
  }

  return Ok;
}

static BOOL pcheck_TableauJustifications(TABLEAU T)
/**************************************************************
  INPUT  : A Tableau
  RETURNS: TRUE iff for each clause in tableau, all its parent
           clauses have been derived in a split on the same level
	   or below.
***************************************************************/
{
  TABPATH Path;
  BOOL    Ok;

  Path = tab_PathCreate(tab_Depth(T),T);
  Ok   = pcheck_TableauJustificationsRec(T,Path); 
  tab_PathDelete(Path);
  
  return Ok;
}

BOOL pcheck_TableauProof(TABLEAU* Tableau, LIST Proof)
/**************************************************************
  INPUT: 
  RETURNS:                                                      
***************************************************************/
{
  LIST RedundantClauses;
  LIST EmptyClauses;
  LIST UnmarkedSplits;

  tab_LabelNodes(*Tableau);
  /* print out current tableau */
  if (pcheck_GenNamedCg) 
    tab_WriteTableau(*Tableau, pcheck_CgName, pcheck_GraphFormat);
  
  RedundantClauses = list_Nil();
  if (!pcheck_Quiet) {
    fputs("pruning closed branches...", stdout);
    fflush(stdout);
  }
  (*Tableau) = tab_PruneClosedBranches(*Tableau, &RedundantClauses);   /* delete descendants of already closed branches */
  if (!pcheck_Quiet)
    puts("finished.");

  if (!pcheck_Quiet) {
    fputs("removing incomplete splits...", stdout);
    fflush(stdout);
  }
  (*Tableau) = tab_RemoveIncompleteSplits(*Tableau, &RedundantClauses);  /* reduce open node redundancies */
  if (!pcheck_Quiet)
    puts("finished.");
  
  list_Delete(RedundantClauses);

  /* remove all clauses that are not needed for the empty clauses */
  /* of the proof or for the tableau structure (splits) */

  EmptyClauses = list_Nil();
  tab_GetEarliestEmptyClauses(*Tableau, &EmptyClauses);
  pcheck_ClauseListRemoveFlag(Proof, MARKED);
  pcheck_MarkRecursive(EmptyClauses);
  UnmarkedSplits = list_Nil();
  pcheck_CollectUnmarkedSplits(*Tableau, &UnmarkedSplits);
  pcheck_MarkRecursive(UnmarkedSplits);
  pcheck_RemoveUnmarkedFromTableau(*Tableau); 
  list_Delete(UnmarkedSplits);
  list_Delete(EmptyClauses);

  /* print reduced graph */
  if (pcheck_GenRedCg) 
    tab_WriteTableau(*Tableau, pcheck_RedCgName, pcheck_GraphFormat);

  tab_SetSplitLevels(*Tableau);
  pcheck_SplitLevels(*Tableau);
  tab_CheckEmpties(*Tableau);

 if (!tab_IsClosed(*Tableau)) {
    puts("\nerror: tableau is not closed.");  
    return FALSE;
 }

  /* check justifications */
  if (!pcheck_Quiet) {
    fputs("checking justifications...", stdout);
    fflush(stdout);
  }
  if (!pcheck_TableauJustifications(*Tableau))
    return FALSE;
  if (!pcheck_Quiet)
    puts("finished.");
 
  return TRUE;
}


void pcheck_MarkRecursive(LIST Clauses)
/**************************************************************
  INPUT:   A list of clauses 
  RETURNS: Nothing.                                                      
  EFFECTS: Marks all <Clauses> and its ancestors with the
           MARKED clause flag.
***************************************************************/
{
  CLAUSE Clause;

  for (; !list_Empty(Clauses); Clauses = list_Cdr(Clauses)) {
    Clause = list_Car(Clauses);
    if (!clause_GetFlag(Clause, MARKED)) {
      pcheck_MarkRecursive(clause_ParentClauses(Clause)); 
      clause_SetFlag(Clause, MARKED);
    }
  }
}


static LIST pcheck_CollectTermVariables(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: A list of terms. For each variable in <Term> the list
           contains exactly one term representing the variable.
  EFFECT:  Memory is allocated for the terms.
***************************************************************/
{
  LIST Result, Scan;

  Result = term_VariableSymbols(Term);
  for (Scan = Result; !list_Empty(Scan); Scan = list_Cdr(Scan))
    list_Rplaca(Scan, term_Create((SYMBOL)list_Car(Scan), list_Nil()));

  return Result;
}


static BOOL pcheck_IsRightSplitHalf(CLAUSE C)
/**************************************************************
  INPUT  : A clause.
  RETURNS: TRUE iff the following conditions are fulfilled:
           - the first parent clause is an empty clause
	   - the clause subsumes its second parent
***************************************************************/
{
  LIST Parents;
  BOOL Ok;

  Parents = list_Copy(clause_ParentClauses(C));
  Parents = list_PointerDeleteDuplicates(Parents);

  Ok = FALSE;
  if (list_Length(Parents) == 2 && clause_IsEmptyClause(list_First(Parents)))
    Ok = subs_Subsumes(C, list_Second(Parents), -1, -1);

  list_Delete(Parents);

  return Ok;
}


static TERM pcheck_UnivClosure(TERM T)
/**************************************************************
  INPUT:   A term, representing a formula.
  RETURNS: The universal closure of the term.
  EFFECTS: <T> is part of the returned term!
***************************************************************/
{
  LIST Vars;

  Vars = pcheck_CollectTermVariables(T);
  
  if (list_Empty(Vars))
    return T;
  return fol_CreateQuantifier(fol_All(), Vars, list_List(T));
}


static TERM pcheck_ClauseToTerm(CLAUSE Clause)
/**************************************************************
  INPUT:   A clause.
  RETURNS: The clause represented as a TERM.
***************************************************************/
{
  int  LitScan;
  LIST Args;
  TERM Lit;
  TERM ClauseTerm;

  Args = list_Nil();

  for (LitScan = clause_FirstLitIndex(); LitScan <= clause_LastLitIndex(Clause);
       LitScan++) {
    Lit  = clause_LiteralSignedAtom(clause_GetLiteral(Clause, LitScan));
    Args = list_Cons(term_Copy(Lit), Args);
  }

  if (list_Empty(Args))
    Args = list_List(term_Create(fol_False(), list_Nil()));
  
  /* Build the disjunction of the literals */
  if (list_Empty(list_Cdr(Args))) {   /* only one arg */
    ClauseTerm = list_Car(Args);
    list_Delete(Args);
  } else
    ClauseTerm = term_Create(fol_Or(), Args);
  ClauseTerm = pcheck_UnivClosure(ClauseTerm);

  return ClauseTerm;
}


static LIST pcheck_ClauseListToTermList(LIST Clauses)
/**************************************************************
  INPUT  : A list of clauses.
  RETURNS: A new list containing the clauses represented as TERMs.
***************************************************************/
{
  LIST Terms;

  Terms = list_Nil();
  for (; !list_Empty(Clauses); Clauses = list_Cdr(Clauses))
    Terms = list_Cons(pcheck_ClauseToTerm(list_Car(Clauses)), Terms);
  
  return Terms;
}


static void pcheck_SaveNumberedDFGProblem(int Number, LIST Axioms,
					  LIST Conjectures,
					  const char* ProofFileName,
					  const char* DestPrefix)
/**************************************************************
  INPUT  : A (clause) number, a list of axioms and conjectures,
           and a filename (of the proof file of the currently
	   checked proof)
  RETURNS: Nothing.
  EFFECTS: Saves a DFG file containing <Axioms> and <Conjectures>
           under the name "<DestPrefix><Number>_<ProofFileName>"
***************************************************************/
{
  char *Filename, *Tmp, *NumStr;
  FILE *File;

  NumStr   = string_IntToString(Number);
  Tmp      = pcheck_GenericFilename(ProofFileName, NumStr);
  Filename = string_Conc(DestPrefix, Tmp);
    
  File = misc_OpenFile(Filename, "w");
  fol_FPrintDFGProblem(File, "{*Sub Proof*}", "{* Proof Checker *}",
		       "unsatisfiable",
		       "{* The problem is the correctness test for a single proof line *}",
		       Axioms, Conjectures);
  misc_CloseFile(File, Filename);

  string_StringFree(NumStr);
  string_StringFree(Tmp);
  string_StringFree(Filename);
}


static void pcheck_SplitToProblems(TABLEAU T, const char* ProofFileName,
				   const char* DestPrefix)
/**************************************************************
  INPUT:   A tableau, which isn't a leaf of the tableau tree,
           the name of a proof file and a file name prefix used for
	   generating files.
  RETURNS: Nothing.
  EFFECT:  This function generates proof check tasks for clauses
           resulting from splitting steps and writes them to
	   output files.
  CAUTION: We assume that we get non-null clauses when calling
           tab_SplitClause and tab_LeftSplitClause.
***************************************************************/
{
  TERM SplitClauseTerm, LeftClauseTerm, RightClauseTerm;
  TERM Equiv, Disj, Tmp;
  LIST Conj, Args, Negations;

#ifdef CHECK
  if (tab_IsLeaf(T)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In pcheck_SplitToProblems: Tableau is a leaf of the ");
    misc_ErrorReport("tableau tree.");
    misc_FinishErrorReport();
  }
#endif

  SplitClauseTerm = pcheck_ClauseToTerm(tab_SplitClause(T));
  LeftClauseTerm  = pcheck_ClauseToTerm(tab_LeftSplitClause(T));
  
  /* by default, take all right split clauses as negations       */
  /* if the first clause is the second half of a split clause,   */
  /* take only the rest of the right split clauses as negations. */

  Negations = tab_RightSplitClauses(T);
  if (!list_Empty(Negations) && pcheck_IsRightSplitHalf(list_Car(Negations))) {
    /* EK: Meiner Meinung nach ist es eine Invariante, daﬂ die erste */
    /* Elternklausel die rechte H‰lfte eines Splittings ist???  */
    Negations = list_Cdr(Negations);
    /* build C <=> C' v C''  */
    RightClauseTerm = pcheck_ClauseToTerm(list_Car(tab_RightSplitClauses(T)));
    Disj  = term_Create(fol_Or(), list_Cons(LeftClauseTerm, list_List(RightClauseTerm)));
    Equiv = term_Create(fol_Equiv(), list_Cons(SplitClauseTerm, list_List(Disj)));
    Conj  = list_List(Equiv);
    
    pcheck_SaveNumberedDFGProblem(clause_Number(tab_LeftSplitClause(T)),
				  list_Nil(), Conj, ProofFileName, DestPrefix);
    term_DeleteTermList(Conj);
  }
  
  Args = list_Nil();

  /* build conjunction of negations, if there are any. */
  if (!list_Empty(Negations)) {
    LeftClauseTerm = pcheck_ClauseToTerm(tab_LeftSplitClause(T));
    Args  = pcheck_ClauseListToTermList(Negations);
    /* Build the conjunction */
    if (list_Empty(list_Cdr(Args))) {  /* only one arg */
      Tmp = list_Car(Args);
      list_Delete(Args);
    } else
      Tmp = term_Create(fol_And(), Args);
    Tmp   = term_Create(fol_Not(), list_List(Tmp));
    Equiv = term_Create(fol_Implies(),list_Cons(Tmp,list_List(LeftClauseTerm)));
    Conj  = list_List(Equiv);
    
    /* problem id is number of right part of split clause, if it exists,
       number of first negation otherwise */
    pcheck_SaveNumberedDFGProblem(clause_Number(list_Car(tab_RightSplitClauses(T))), 
				  list_Nil(), Conj, ProofFileName, DestPrefix);
    term_DeleteTermList(Conj);
  }
}


void pcheck_TableauToProofTask(TABLEAU T, const char* ProofFileName,
			       const char* DestPrefix)
/**************************************************************
  INPUT:   A Tableau, two strings for filename generation.
  RETURNS: Nothing.
  EFFECTS: Generates DFG problem files for each clause in the tableau.
           The problem asserts that the clause follows from
	   its parents. For splits, see pcheck_SplitToProblems
***************************************************************/
{
  LIST   Scan;
  LIST   Axioms, Conj, Help;
  CLAUSE Clause;

  if (tab_IsEmpty(T))
    return;

  /* treat the splitting clauses at inner nodes of the tableau tree */
  if (!tab_IsLeaf(T))
    pcheck_SplitToProblems(T, ProofFileName, DestPrefix);
 
  /* treat derived clauses that don't result from splitting */
  for (Scan = tab_Clauses(T); !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    Clause = list_Car(Scan);
    if (!clause_IsFromSplitting(Clause) &&
	!list_Empty(clause_ParentClauses(Clause))) {
      Axioms = list_Copy(clause_ParentClauses(Clause));
      Axioms = list_PointerDeleteDuplicates(Axioms);
      Help   = Axioms;
      Axioms = pcheck_ClauseListToTermList(Axioms);
      list_Delete(Help);
      Conj   = list_List(pcheck_ClauseToTerm(Clause));
      pcheck_SaveNumberedDFGProblem(clause_Number(Clause), Axioms, Conj,
				    ProofFileName, DestPrefix);
      term_DeleteTermList(Axioms);
      term_DeleteTermList(Conj);
    }
  }
  
  /* recursion */
  pcheck_TableauToProofTask(tab_RightBranch(T), ProofFileName, DestPrefix);
  pcheck_TableauToProofTask(tab_LeftBranch(T), ProofFileName, DestPrefix);
}


int pcheck_SeqProofDepth(LIST Proof)
/**************************************************************
  INPUT  : A sequential proof (list of clauses)
  RETURNS: The maximum clause depth in the proof
***************************************************************/ 
{
  int Max;

  Max = 0;
  for ( ; !list_Empty(Proof); Proof = list_Cdr(Proof)) 
    if (clause_Depth(list_Car(Proof)) > Max)
      Max = clause_Depth(list_Car(Proof));
  
  return Max;
}


LIST pcheck_ReduceSPASSProof(LIST Proof)
/**************************************************************
  INPUT:   A list of clauses representing a SPASS proof.
           Parents are pointers.
  RETURNS: A list of clauses were incomplete splits
           and closed branches with descendants have been
	   removed.
***************************************************************/  
{
  LIST    EmptyClauses, RedundantClauses;
  LIST    ReducedProof;
  TABLEAU Tableau;
  LIST    UnmarkedSplits;

  if (!pcheck_BuildTableauFromProof(Proof, &Tableau)) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n Error: Proof could not be translated into a closed tableau.\n");
    misc_FinishUserErrorReport();
  }

  RedundantClauses = list_Nil();
  Tableau = tab_PruneClosedBranches(Tableau, &RedundantClauses);
  Tableau = tab_RemoveIncompleteSplits(Tableau, &RedundantClauses);
  list_Delete(RedundantClauses);
  
  tab_SetSplitLevels(Tableau);
  
  /* 
   *  get minimal proof: First find earliest derived empty clauses,
   *  then recursively mark ancestors of these clauses. Put
   *  only marked clauses in <ReducedProof>.
   */

  EmptyClauses = list_Nil();
  tab_GetEarliestEmptyClauses(Tableau, &EmptyClauses);
  pcheck_ClauseListRemoveFlag(Proof, MARKED);
  pcheck_MarkRecursive(EmptyClauses);
  UnmarkedSplits = list_Nil();
  pcheck_CollectUnmarkedSplits(Tableau, &UnmarkedSplits);
  pcheck_MarkRecursive(UnmarkedSplits);
  pcheck_RemoveUnmarkedFromTableau(Tableau); 
  list_Delete(UnmarkedSplits);

  ReducedProof = list_Nil(); 
  tab_ToClauseList(Tableau, &ReducedProof);
  ReducedProof = pcheck_ClauseNumberMergeSort(ReducedProof);

  tab_Delete(Tableau);
  list_Delete(EmptyClauses); 

  return ReducedProof;
}


void pcheck_DeleteProof(LIST Proof)
/**************************************************************
  INPUT:   A Proof
  RETURNS: Nothing.
  EFFECTS: Frees memory associated with proof
**************************************************************/
{
  LIST Line, Scan2, Scan1;
  
  Scan1 = Proof;
  while (!list_Empty(Scan1)) {
    Line = list_Car(Scan1);
    
    string_StringFree(list_Car(Line));
    if (list_Second(Line) != clause_Null())                /* clause */
      term_Delete(list_Second(Line));

    /* delete labels in justification list and list itself */

    for (Scan2 = list_Third(Line); !list_Empty(Scan2); Scan2 = list_Cdr(Scan2)) 
      string_StringFree(list_Car(Scan2));
    list_Delete(list_Third(Line));     

    /* now contents of line are deleted. Delete line. */
    list_Delete(Line);     
    Scan1 = list_Cdr(Scan1);
  }
  list_Delete(Proof);
}


char* pcheck_GenericFilename(const char* Filename, const char* Id)
/**************************************************************
  INPUT:   Two strings.
  RETURNS: A string with Suffix as new extension to Filename
           (Filename = name.ext -> name_<Id>.prf)
  EFFECTS: Memory is allocated for the returned string.
**************************************************************/
{	
  char *Help1, *Help2;
  int  i;

  Help1 = string_Conc("_", Id); 
  Help2 = string_Conc(Help1, pcheck_ProofFileSuffix); 
  string_StringFree(Help1);
  
  /* remove filename extension */
  for (i = 0; Filename[i] != '.' && i < strlen(Filename); i++)
    /* empty */;
  Help1 = string_Prefix(Filename, i);

  return string_Nconc(Help1, Help2);  /* Help1 and Help2 are freed, too */
}


void pcheck_ClauseListRemoveFlag(LIST Clauses, CLAUSE_FLAGS Flag)
/**************************************************************
  INPUT:   A list of clauses and a clause flag
  RETURNS: Nothing.
  EFFECTS: Removes the <Flag> in all clauses in the list
**************************************************************/
{
  for (; !list_Empty(Clauses); Clauses = list_Cdr(Clauses)) 
    clause_RemoveFlag(list_Car(Clauses), Flag);
}


LIST pcheck_ClauseNumberMergeSort(LIST L)
/**************************************************************
  INPUT:   A list of clauses  
  RETURNS: The sorted list: clause_Number(L[i]) < clause_Number(L[i+1])
  EFFECTS: Destructive
***************************************************************/
{
  return clause_NumberSort(L);
}
