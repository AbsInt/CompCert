/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                TERMINATOR                              * */
/* *                                                        * */
/* *  $Module:   REDRULES                                   * */
/* *                                                        * */
/* *  Copyright (C) 1999, 2000, 2001 MPI fuer Informatik    * */
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

#include "terminator.h"
#include "list.h"


static LIST red_GetTerminatorPartnerLits(TERM Atom, LITERAL Lit,
					 BOOL UnitsOnly, LIST IndexList)
/**************************************************************
  INPUT:   An atom, a literal, a boolean flag and a list of SHARED_INDEXes.
  RETURNS: A list of literals with sign complementary to <Lit>
           that are unifiable with <Atom>. The literals are searched
           in all SHARED_INDEXes from <IndexList>. Additionally,
           if <Unitsonly> is true, only literals from unit clauses
	   are returned.
  EFFECT:  <Atom> is a copy of <Lit> where some substitution
           was applied and equality literals might have been swapped.
	   <Lit> is just needed to check whether the unifiable
	   literals are complementary.
***************************************************************/
{
  LIST    Result, Unifiers, LitScan;
  LITERAL NextLit;

  Result   = list_Nil();
  for ( ; !list_Empty(IndexList); IndexList = list_Cdr(IndexList)) {
    Unifiers = st_GetUnifier(cont_LeftContext(),
			     sharing_Index(list_Car(IndexList)),
			     cont_RightContext(), Atom);
    for ( ; !list_Empty(Unifiers); Unifiers = list_Pop(Unifiers)) {
      if (!term_IsVariable(list_Car(Unifiers))) {
	for (LitScan = sharing_NAtomDataList(list_Car(Unifiers));
	     !list_Empty(LitScan); LitScan = list_Cdr(LitScan)) {
	  NextLit = list_Car(LitScan);
	  if (clause_LiteralsAreComplementary(Lit, NextLit) &&
	      (!UnitsOnly || clause_Length(clause_LiteralOwningClause(NextLit))==1))
	    /* The partner literals must have complementary sign and
	       if <UnitsOnly> == TRUE they must be from unit clauses. */
	    Result = list_Cons(NextLit, Result);
	}
      }
    }
  }
  return Result;
}


static CLAUSE red_CreateTerminatorEmptyClause(LIST FoundMap, FLAGSTORE Flags,
					      PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A list of pairs (l1, l2), where l1 and l2 are unifiable
           literals with complementary sign and a flag store.
	   More accurately, a substitution s exists,
	   such that l1 s = l2 s for all pairs (l1,l2) in
	   <FoundMap>.
	   For all literals l from the involved clauses
	   there exists one pair (l1,l2) in <FoundMap>
	   with l1=l or l2=l.
	   The flags store and the precedence are needed to create
	   the new clause.
  RETURNS: A newly created empty clause, where the data
           (parents,...) is set according to <FoundMap>.
***************************************************************/
{
  CLAUSE  Result, PClause;
  LITERAL Lit;
  LIST    Parents;
  NAT     depth;

  Result  = clause_Create(list_Nil(), list_Nil(), list_Nil(), Flags, Precedence);
  Parents = list_Nil();
  depth   = 0;
  for (; !list_Empty(FoundMap); FoundMap = list_Cdr(FoundMap)) {
    Lit     = list_PairSecond(list_Car(FoundMap));
    PClause = clause_LiteralOwningClause(Lit);
    Parents = list_Cons(PClause, Parents);
    depth   = misc_Max(depth, clause_Depth(PClause));
    clause_AddParentClause(Result, clause_Number(PClause));
    clause_AddParentLiteral(Result, clause_LiteralGetIndex(Lit));

    Lit     = list_PairFirst(list_Car(FoundMap));
    PClause = clause_LiteralOwningClause(Lit);
    Parents = list_Cons(PClause, Parents);
    depth   = misc_Max(depth, clause_Depth(PClause));
    clause_AddParentClause(Result, clause_Number(PClause));
    clause_AddParentLiteral(Result, clause_LiteralGetIndex(Lit));
  }
  clause_SetFromTerminator(Result);
  clause_SetDepth(Result, depth+1);
  clause_SetSplitDataFromList(Result, Parents);
  list_Delete(Parents);
  return Result;
}


static BOOL red_TerminatorLitIsBetter(LITERAL L1, NAT S1, LITERAL L2, NAT S2)
/**************************************************************
  INPUT:   Two literals and its sizes wrt. some substitution.
  RETURNS: TRUE, if <L1> is 'better' than <L2>, FALSE otherwise.
  EFFECT:  1. Positive literals are 'better' than negative literals
           2. If both literals have the same sign, the bigger literal
	      is better.
	   This is an heuristic that has shown to be useful in practice.
	   This function is used as parameter for the function
	   clause_MoveBestLiteralToFront.
***************************************************************/
{
  if ((clause_LiteralIsNegative(L2) && clause_LiteralIsPositive(L1)) ||
      /* The following conditions do the same as this condition: */
      /* (!clause_LiteralsAreComplementary(L1, L2) && S1 > S2)   */
      (clause_LiteralIsPositive(L1) && S1 > S2) ||
      (clause_LiteralIsNegative(L2) && S1 > S2))
    return TRUE;
  else
    return FALSE;
}


static CLAUSE red_SearchTerminator(NAT n, LIST RestLits, LIST FoundMap,
				   SUBST Subst, SYMBOL GlobalMaxVar,
				   LIST IndexList, FLAGSTORE Flags,
				   PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A natural number, a list of literals, a list of pairs,
           a substitution, the maximum variable occurring in all
	   involved clauses, a list of SHARED_INDEXes, a flag store
	   and a precedence.
  RETURNS: An empty clause, if a terminator situation was found,
           NULL otherwise.
  EFFECT:  This recursive function implements the search for
           a terminator situation with at most <n> non-unit clauses.
	   <RestLits> is the lists of literals actually missing
	   a complementary partner literal.
	   <FoundMap> is a list of pairs (l1,l2), where l1 and l2
	   are complementary, unifiable literals.
	   <Subst> is the common substitution of all those pairs.
	   <GlobalMaxVar> is the maximum variable from all
	   involved clauses.
	   To enable the search all involved clauses are made
	   variable-disjoint.
	   At the moment the function stops, if ANY terminator
	   situation occurred. This might not be desirable
	   if splitting is enabled, since there might be other
	   terminator situations resulting in an empty clause
	   of lower split level.
	   The flag store and the precedence are needed to create
	   the new clause.
***************************************************************/
{
  if (list_Empty(RestLits)) {
    /* We found a terminator situation, so stop the recursion */
    return red_CreateTerminatorEmptyClause(FoundMap, Flags, Precedence);
  } else {
    CLAUSE  Result, PClauseCopy;
    LITERAL Lit, PLit;
    SYMBOL  NewMaxVar;
    SUBST   NewSubst, RightSubst;
    TERM    AtomCopy;
    LIST    ClashList, ToDoList;
    BOOL    Swapped;
    NAT     Limit;
    int     PLitInd;

    Swapped   = FALSE;
    Result    = clause_Null();
    clause_MoveBestLiteralToFront(RestLits, Subst, GlobalMaxVar,
				  red_TerminatorLitIsBetter);
    Lit       = list_Car(RestLits);
    RestLits  = list_Cdr(RestLits);
    AtomCopy  = subst_Apply(Subst, term_Copy(clause_LiteralAtom(Lit)));

    /* The following 'endless' loop runs twice for equality literals */
    /* and only once for other literals.                             */
    while (TRUE) {
      ClashList = red_GetTerminatorPartnerLits(AtomCopy, Lit, n==0, IndexList);
      for (; !list_Empty(ClashList) && Result==NULL;
	   ClashList = list_Pop(ClashList)) {
	PLit        = list_Car(ClashList);
	PLitInd     = clause_LiteralGetIndex(PLit);
	PClauseCopy = clause_Copy(clause_LiteralOwningClause(PLit));
	Limit       = clause_Length(PClauseCopy) == 1 ? n : n-1;
	
	clause_RenameVarsBiggerThan(PClauseCopy, GlobalMaxVar);
	
	PLit        = clause_GetLiteral(PClauseCopy, PLitInd);
	FoundMap    = list_Cons(list_PairCreate(Lit, PLit), FoundMap);
	ToDoList    = clause_GetLiteralListExcept(PClauseCopy, PLitInd);
	ToDoList    = list_Nconc(ToDoList, list_Copy(RestLits));
	
	NewMaxVar   = clause_SearchMaxVar(PClauseCopy);
	if (symbol_GreaterVariable(GlobalMaxVar, NewMaxVar))
	  NewMaxVar = GlobalMaxVar;
	
	cont_Check();
	if (!unify_UnifyNoOC(cont_LeftContext(), AtomCopy,
			     cont_RightContext(), clause_LiteralAtom(PLit))) {
	  misc_StartErrorReport();
	  misc_ErrorReport("\n In red_SearchTerminator: Unification failed.");
	  misc_FinishErrorReport();
	}
	subst_ExtractUnifier(cont_LeftContext(), &NewSubst,
			     cont_RightContext(), &RightSubst);
	cont_Reset();
	
	/* The domains of both substitutions are disjoint */
	/* so we do just a simple union operation.        */
	NewSubst = subst_NUnion(NewSubst, RightSubst);
	RightSubst = NewSubst;
	NewSubst  = subst_Compose(NewSubst, subst_Copy(Subst));
	subst_Delete(RightSubst);
	
	Result = red_SearchTerminator(Limit, ToDoList, FoundMap, NewSubst,
				      NewMaxVar, IndexList, Flags, Precedence);
	
	clause_Delete(PClauseCopy);
	subst_Delete(NewSubst);
	list_Delete(ToDoList);
	list_PairFree(list_Car(FoundMap));
	FoundMap = list_Pop(FoundMap);
      }
      /* loop control */
      if (!fol_IsEquality(AtomCopy) || Swapped || Result!=NULL)
	break;
      else {
	list_Delete(ClashList);
	term_EqualitySwap(AtomCopy);
	Swapped = TRUE;
      }
    }
    /* cleanup */
    term_Delete(AtomCopy);
    /* <ClashList> may be non-empty since the loop stops */
    /* if a terminator was found.                       */
    list_Delete(ClashList);
    
    return Result;
  }
}


CLAUSE red_Terminator(CLAUSE RedClause, NAT n, SHARED_INDEX WoIndex,
		      SHARED_INDEX UsIndex, FLAGSTORE Flags,
		      PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause, two shared indexes, a number <n>
           restricting the number of non-unit clauses in
	   a possible terminator situation, a flag store
	   and a precedence.
  RETURNS: An empty clause if a terminator with at most <n>
           non-unit clauses is found, NULL otherwise.
  EFFECT:  See also description of red_SearchTerminator.
***************************************************************/
{
  LIST   Rest, IndexList;
  CLAUSE Result;

  if (clause_Length(RedClause) > 1)  /* non-unit clause */
    n--;

  /* Pass the indexes as a list to sub-functions */
  IndexList = list_Cons(WoIndex, list_List(UsIndex));
  Rest      = clause_GetLiteralList(RedClause);
  Result    = red_SearchTerminator(n, Rest, list_Nil(), subst_Nil(),
				   clause_MaxVar(RedClause), IndexList, Flags,
				   Precedence);
  
  /* cleanup */
  list_Delete(IndexList);
  list_Delete(Rest);

  return Result;
}
