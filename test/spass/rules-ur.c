/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                UR-RESOLUTION                           * */
/* *                                                        * */
/* *  $Module:   INFERENCE RULES                            * */
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

#include "rules-ur.h"
#include "list.h"


static LIST inf_GetURPartnerLits(TERM Atom, LITERAL Lit,
				 BOOL Unit, SHARED_INDEX Index)
/**************************************************************
  INPUT:   An atom, a literal, a boolean flag and a SHARED_INDEX.
  RETURNS: A list of literals with sign complementary to <Lit>
           that are unifiable with <Atom>. If <Unit> is true,
	   only literals from unit clauses are returned, if <Unit>
	   is false, only literals from non-unit clauses are
	   returned.
  EFFECT:  <Atom> is a copy of <Lit>'s atom where some substitution
           was applied and equality literals might have been swapped.
	   <Lit> is just needed to check whether the unifiable
	   literals are complementary.
***************************************************************/
{
  LIST    Result, Unifiers, LitScan;
  LITERAL PLit;
  int     length;

  Result   = list_Nil();
  Unifiers = st_GetUnifier(cont_LeftContext(), sharing_Index(Index),
			   cont_RightContext(), Atom);
  for ( ; !list_Empty(Unifiers); Unifiers = list_Pop(Unifiers)) {
    if (!term_IsVariable(list_Car(Unifiers))) {
      for (LitScan = sharing_NAtomDataList(list_Car(Unifiers));
	   !list_Empty(LitScan); LitScan = list_Cdr(LitScan)) {
	PLit   = list_Car(LitScan);
	length = clause_Length(clause_LiteralOwningClause(PLit));
	if (clause_LiteralsAreComplementary(Lit, PLit) &&
	    ((Unit && length==1) || (!Unit && length!=1)))
	  /* The partner literals must have complementary sign and
	     if <Unit> == TRUE they must be from unit clauses,
	     if <Unit> == FALSE they must be from non-unit clauses. */
	  Result = list_Cons(PLit, Result);
      }
    }
  }
  return Result;
}


static CLAUSE inf_CreateURUnitResolvent(CLAUSE Clause, int i, SUBST Subst,
					LIST FoundMap, FLAGSTORE Flags,
					PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A non-unit clause, a literal index from the clause,
           a substitution, a list of pairs (l1, l2) of literals,
	   where l1 is from the non-unit clause and l2 is from a
	   unit clause, a flag store and a precedence.
  RETURNS: The resolvent of this UR resolution inference. The
           clause consists of the literal at index <i> in <Clause>
	   after application of <Subst>.
  EFFECT:  The flag store and the precedence are needed to create
           the new clause.
***************************************************************/
{
  CLAUSE  Result, PClause;
  LITERAL Lit;
  TERM    Atom;
  LIST    Parents;
  NAT     depth;

  /* Create atom for resolvent */
  Atom = subst_Apply(Subst, term_Copy(clause_GetLiteralAtom(Clause, i)));
  /* Create clause */
  Parents = list_List(Atom);
  if (i <= clause_LastConstraintLitIndex(Clause))
    Result = clause_Create(Parents, list_Nil(), list_Nil(), Flags, Precedence);
  else if (i <= clause_LastAntecedentLitIndex(Clause))
    Result = clause_Create(list_Nil(), Parents, list_Nil(), Flags, Precedence);
  else
    Result = clause_Create(list_Nil(), list_Nil(), Parents, Flags, Precedence);
  list_Delete(Parents);

  /* Get parent clauses and literals, calculate depth of resolvent */
  Parents = list_List(Clause);
  depth   = clause_Depth(Clause);
  for ( ; !list_Empty(FoundMap); FoundMap = list_Cdr(FoundMap)) {
    Lit     = list_PairSecond(list_Car(FoundMap)); /* Literal from unit */ 
    PClause = clause_LiteralOwningClause(Lit);
    Parents = list_Cons(PClause, Parents);
    depth   = misc_Max(depth, clause_Depth(PClause));
    clause_AddParentClause(Result, clause_Number(PClause));
    clause_AddParentLiteral(Result, clause_LiteralGetIndex(Lit));

    Lit     = list_PairFirst(list_Car(FoundMap)); /* Is from <Clause> */
    clause_AddParentClause(Result, clause_Number(Clause));
    clause_AddParentLiteral(Result, clause_LiteralGetIndex(Lit));
  }
  clause_SetFromURResolution(Result);
  clause_SetDepth(Result, depth+1);
  clause_SetSplitDataFromList(Result, Parents);
  list_Delete(Parents);

  return Result;
}


static LIST inf_SearchURResolvents(CLAUSE Clause, int i, LIST FoundMap,
				   LIST RestLits, SUBST Subst,
				   SYMBOL GlobalMaxVar, SHARED_INDEX Index,
				   FLAGSTORE Flags, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A non-unit clause, a literal index from <Clause>.
           <FoundMap> is a list of pairs (l1,l2) of unifiable literals,
	   where l1 is from <Clause> and l2 is from a unit clause.
	   <RestLits> is a list of literals from <Clause> where
	   we haven't found unifiable literals from unit clauses
	   so far.
	   <Subst> is the overall substitution for <Clause>
	   (not for the unit-clauses!).
	   <GlobalMaxVar> is the maximal variable encountered so far.
	   <Index> is used to search unifiable literals.
	   The flag store and the precedence are needed to create
	   the new clauses.
  RETURNS: A list of UR resolution resolvents.
***************************************************************/
{
  if (list_Empty(RestLits)) {
    /* Stop the recursion */
    return list_List(inf_CreateURUnitResolvent(Clause, i, Subst, FoundMap,
					       Flags, Precedence));
  } else {
    LITERAL Lit, PLit;
    SYMBOL  NewMaxVar;
    SUBST   NewSubst, RightSubst;
    TERM    AtomCopy, PAtom;
    LIST    Result, Partners;
    BOOL    Swapped;

    Result   = list_Nil();
    Swapped  = FALSE;
    /* Choose the unmatched literal with the most symbols */
    RestLits = clause_MoveBestLiteralToFront(list_Copy(RestLits), Subst,
					     GlobalMaxVar,
					     clause_HyperLiteralIsBetter);
    Lit      = list_Car(RestLits);
    RestLits = list_Pop(RestLits);
    AtomCopy = subst_Apply(Subst, term_Copy(clause_LiteralAtom(Lit)));

    /* The following 'endless' loop runs twice for equality literals */
    /* and only once for other literals.                             */
    while (TRUE) {
      Partners = inf_GetURPartnerLits(AtomCopy, Lit, TRUE, Index);
      for ( ; !list_Empty(Partners); Partners = list_Pop(Partners)) {
	PLit    = list_Car(Partners);

	/* Rename the atom */
	PAtom   = term_Copy(clause_LiteralAtom(PLit));
	term_StartMaxRenaming(GlobalMaxVar);
	term_Rename(PAtom);
	/* Get the new global maximal variable */
	NewMaxVar = term_MaxVar(PAtom);
	if (symbol_GreaterVariable(GlobalMaxVar, NewMaxVar))
	  NewMaxVar = GlobalMaxVar;
	
	/* Get the substitution */
	cont_Check();
	if (!unify_UnifyNoOC(cont_LeftContext(), AtomCopy,
			     cont_RightContext(), PAtom)) {
	  misc_StartErrorReport();
	  misc_ErrorReport("\n In inf_SearchURResolvents: Unification failed.");
	  misc_FinishErrorReport();
	}
	subst_ExtractUnifier(cont_LeftContext(), &NewSubst,
			     cont_RightContext(), &RightSubst);
	cont_Reset();
	subst_Delete(RightSubst);  /* Forget substitution for unit clause */
	term_Delete(PAtom);  /* Was just needed to get the substitution */

	/* Build the composition of the substitutions */
	RightSubst = NewSubst;
	NewSubst = subst_Compose(NewSubst, subst_Copy(Subst));
	subst_Delete(RightSubst);

	FoundMap    = list_Cons(list_PairCreate(Lit, PLit), FoundMap);
	
	Result = list_Nconc(inf_SearchURResolvents(Clause,i,FoundMap,RestLits,
						   NewSubst,NewMaxVar,Index,
						   Flags, Precedence),
			    Result);
	
	list_PairFree(list_Car(FoundMap));
	FoundMap = list_Pop(FoundMap);
	subst_Delete(NewSubst);
      }
      /* loop control */
      if (!fol_IsEquality(AtomCopy) || Swapped)
	break;
      else {
	term_EqualitySwap(AtomCopy);
	Swapped = TRUE;
      }
    }
    /* cleanup */
    term_Delete(AtomCopy);
    list_Delete(RestLits);
    
    return Result;
  }
}


static LIST inf_NonUnitURResolution(CLAUSE Clause, int SpecialLitIndex,
				    LIST FoundMap, SUBST Subst,
				    SYMBOL GlobalMaxVar, SHARED_INDEX Index,
				    FLAGSTORE Flags, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A non-unit clause, a literal index from <Clause>.
           <FoundMap> is a list of pairs (l1,l2) of unifiable literals,
	   where l1 is from <Clause> and l2 is from a unit clause.
	   At this point the list has at most one element.
	   <Subst> is the substitution for <Clause>.
	   <GlobalMaxVar> is the maximal variable encountered so far.
	   <Index> is used to search unifiable literals.
	   The flag store and the precedence are needed to create
	   the new clauses.
  RETURNS: The list of UR resolution resolvents.
  EFFECT:  If inf_URResolution was called with a unit clause,
           <SpecialLitIndex> is the index of a literal from a non-unit
	   clause, that is unifiable with the unit clause's literal,
	   otherwise it is set to -1.
***************************************************************/
{
  LIST Result, RestLits;
  int  i, last;

  Result = list_Nil();
  RestLits = clause_GetLiteralListExcept(Clause, SpecialLitIndex);
  last = clause_LastLitIndex(Clause);
  for (i = clause_FirstLitIndex(); i <= last; i++) {
    /* <i> is the index of the literal that remains in the resolvent */
    if (i != SpecialLitIndex) {
      RestLits = list_PointerDeleteOneElement(RestLits,
					      clause_GetLiteral(Clause,i));
      
      Result = list_Nconc(inf_SearchURResolvents(Clause, i, FoundMap, RestLits,
						 Subst, GlobalMaxVar, Index,
						 Flags, Precedence),
			  Result);
      
      RestLits = list_Cons(clause_GetLiteral(Clause, i), RestLits);
    }
  }
  list_Delete(RestLits);
  return Result;
}


LIST inf_URResolution(CLAUSE Clause, SHARED_INDEX Index, FLAGSTORE Flags,
		      PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause, a shared index, a flag store and a precedence.
  RETURNS: The list of UR resolution resolvents.
  EFFECT:  The flag store and the precedence are needed to create
           the resolvents.
***************************************************************/
{
  LIST Result;

  if (clause_Length(Clause) != 1) {
    /* Clause isn't unit clause */
    Result = inf_NonUnitURResolution(Clause, -1, list_Nil(), subst_Nil(),
				     clause_MaxVar(Clause), Index, Flags,
				     Precedence);
  }
  else {
    /* Clause is unit clause, so search partner literals in non-unit clauses */
    LITERAL Lit, PLit;
    TERM    Atom;
    LIST    Partners, FoundMap;
    SYMBOL  MaxVar, PMaxVar;
    SUBST   LeftSubst, RightSubst;
    CLAUSE  PClause;
    int     PLitInd;
    BOOL    Swapped;

    Result   = list_Nil();
    Lit      = clause_GetLiteral(Clause, clause_FirstLitIndex());
    Atom     = term_Copy(clause_LiteralAtom(Lit));
    Swapped  = FALSE;

    /* The following 'endless' loop runs twice for equality literals */
    /* and only once for other literals.                             */
    while (TRUE) {
      /* Get complementary literals from non-unit clauses */
      Partners = inf_GetURPartnerLits(Atom, Lit, FALSE, Index);
      
      for ( ; !list_Empty(Partners); Partners = list_Pop(Partners)) {
	PLit     = list_Car(Partners);
	PLitInd  = clause_LiteralGetIndex(PLit);
	PClause  = clause_LiteralOwningClause(PLit); /* non-unit clause */
	
	PMaxVar   = clause_MaxVar(PClause);
	term_StartMaxRenaming(PMaxVar);
	term_Rename(Atom);              /* Rename atom from unit clause */
	MaxVar = term_MaxVar(Atom); 
	if (symbol_GreaterVariable(PMaxVar, MaxVar))
	  MaxVar = PMaxVar;
	
	/* Get the substitution */
	cont_Check();
	unify_UnifyNoOC(cont_LeftContext(), clause_LiteralAtom(PLit),
			cont_RightContext(), Atom);
	subst_ExtractUnifier(cont_LeftContext(), &LeftSubst,
			     cont_RightContext(), &RightSubst);
	cont_Reset();
	/* We don't need the substitution for the unit clause */
	subst_Delete(RightSubst);
	
	FoundMap = list_List(list_PairCreate(PLit, Lit));
	
	Result = list_Nconc(inf_NonUnitURResolution(PClause, PLitInd, FoundMap,
						    LeftSubst, MaxVar, Index,
						    Flags, Precedence),
			    Result);
	
	list_DeletePairList(FoundMap);
	subst_Delete(LeftSubst);
      }
      /* loop control */
      if (!fol_IsEquality(Atom) || Swapped)
	break;
      else {
	term_EqualitySwap(Atom);
	Swapped = TRUE;
      }
    }  /* end of endless loop */
    term_Delete(Atom);
  }
  return Result;
}
