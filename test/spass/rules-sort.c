/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *           INFERENCE RULES FOR SORTS                    * */
/* *                                                        * */
/* *  $Module:   SORTRULES                                  * */ 
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

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "rules-sort.h"

     
/**************************************************************/
/* Functions                                                  */
/**************************************************************/ 

static LIST inf_GetForwardPartnerLits(LITERAL, st_INDEX);
static SORT inf_GetSortFromLits(LIST, SORTTHEORY);


static BOOL inf_SubsortPrecheck(CLAUSE Clause, LIST TLits, LITERAL Special,
				st_INDEX Index, SORTTHEORY SortTheory)
/**************************************************************
  INPUT:   A clause, a list of constraint literal indices in
           that clause, a special literal, an index of clauses,
	   and the actual sort theory.
  RETURNS: TRUE, if there exists any subsort of the <TLits> sort.
***************************************************************/
{
  SORT tSort, unifierSort;
  LIST unifiers;
  BOOL result;

  unifiers = inf_GetForwardPartnerLits(clause_GetLiteral(Clause,(int)list_Car(TLits)),
				       Index);
  unifierSort = inf_GetSortFromLits(unifiers, SortTheory);
  list_Delete(unifiers);

  tSort = sort_TopSort();
  for (; !list_Empty(TLits); TLits = list_Cdr(TLits)) {
    TERM actAtom = clause_GetLiteralAtom(Clause, (int)list_Car(TLits));
    tSort = sort_Intersect(sort_TheorySortOfSymbol(SortTheory, term_TopSymbol(actAtom)),
			   tSort);
  }
  tSort = list_PointerDeleteDuplicates(tSort);

  if (Special == NULL)
    result = sort_TheoryIsSubsortOf(SortTheory, unifierSort, tSort);
  else {
    SORT extraSort;
    extraSort = sort_TheorySortOfSymbol(SortTheory, clause_LiteralPredicate(Special));
    result    = sort_TheoryIsSubsortOfExtra(SortTheory, extraSort, unifierSort, tSort);
    sort_Delete(extraSort);
  }

  sort_Delete(tSort);
  sort_Delete(unifierSort);

  return result;
}
     
static LIST inf_GetSortResolutionPartnerLits(TERM Atom, st_INDEX Index)
/**************************************************************
  INPUT:   A clause, and an Index of clauses.
  RETURNS: A list of literals with which sortresolution is possible.
  MEMORY:  Allocates memory for the list.
***************************************************************/
{
  LIST    Result, TermList, LitScan;
  LITERAL NextLit;
  CLAUSE  Clause;

#ifdef CHECK  
  if (!term_IsAtom(Atom)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In inf_GetSortResolutionPartnerLits: Variable as atom input.\n");
    misc_FinishErrorReport();
  }
#endif

  Result   = list_Nil();
  TermList = st_GetUnifier(cont_LeftContext(), Index, cont_RightContext(), Atom);
  
  for ( ; !list_Empty(TermList); TermList = list_Pop(TermList)) {
    
    if (term_IsAtom(list_Car(TermList))) {
      
      for (LitScan = sharing_NAtomDataList(list_Car(TermList)); 
	   !list_Empty(LitScan); 
	   LitScan = list_Cdr(LitScan)){
	NextLit = list_Car(LitScan);
	Clause  = clause_LiteralOwningClause(NextLit);
	
	if (clause_LiteralIsPositive(NextLit) && 
	    clause_LiteralGetFlag(NextLit,STRICTMAXIMAL) &&
	    clause_GetFlag(Clause, WORKEDOFF) &&
	    clause_HasSolvedConstraint(Clause) &&
	    !list_PointerMember(Result, NextLit)) 
	  Result = list_Cons(NextLit, Result);
      }
    }
  }
  
  return Result;
}


static CLAUSE inf_BuildConstraintHyperResolvent(CLAUSE Clause, LIST Lits,
						SUBST Subst, LIST Foundlits,
						FLAGSTORE Flags,
						PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A <Clause> where the sort constraint is resolved,
           a list <Lits> of constraint indices in <Clause> where
	   all corresponding constraints have the same term,
	   the overall substitution <Subst>,
	   a list <Foundlits> of literals of found partner clauses,
	   a flag store and a precedence.
  RETURNS: A clause, the resolvent of a resolution step.
***************************************************************/
{
  CLAUSE NewClause, ClauseCopy;
  LIST   Constraint, Antecedent, Succedent, ParentCls, ParentLits, Scan;
  TERM   Atom;
  SYMBOL MaxVar,MaxCand;
  int    i,bound, depth;
  BOOL   IsFromEmptySort;
  LIST   Partners;
  
  ParentCls   = list_Nil();
  ParentLits  = list_Nil();
  Constraint  = list_Nil();
  Antecedent  = list_Nil();
  Succedent   = list_Nil();
  Partners    = list_Nil();
  depth       = clause_Depth(Clause);

  for (Scan=Foundlits; !list_Empty(Scan); Scan=list_Cdr(Scan))
    depth = misc_Max(depth,
		     clause_Depth(clause_LiteralOwningClause(list_Car(Scan))));

  ClauseCopy  = clause_Copy(Clause);
  Partners    = list_Cons(ClauseCopy, Partners);
  clause_SubstApply(Subst, ClauseCopy);

  IsFromEmptySort = term_IsVariable(term_FirstArgument(
    clause_GetLiteralAtom(Clause, (int)list_Car(Lits))));

  bound = clause_LastConstraintLitIndex(ClauseCopy);

  for (i = clause_FirstLitIndex(); i <= bound; i++)
    if (!list_PointerMember(Lits, (POINTER)i)) {
      Atom  = term_Copy(clause_GetLiteralAtom(ClauseCopy, i));
      Constraint = list_Cons(Atom, Constraint);
    } 
    else {
      ParentCls  = list_Cons((POINTER)clause_Number(ClauseCopy), ParentCls);
      ParentLits = list_Cons((POINTER)i, ParentLits);
    }

  bound = clause_LastAntecedentLitIndex(ClauseCopy);
  for ( ; i <= bound; i++) {
    Atom = term_Copy(clause_GetLiteralAtom(ClauseCopy, i));
    Antecedent = list_Cons(Atom, Antecedent);
  }
  bound = clause_LastSuccedentLitIndex(ClauseCopy);
  for (; i <= bound; i++) {
    Atom = term_Copy(clause_GetLiteralAtom(ClauseCopy, i));
    Succedent = list_Cons(Atom, Succedent);
  }
  bound = clause_LastConstraintLitIndex(Clause);
  for (i = clause_FirstLitIndex(); i <= bound; i++) {			
    /* Hier sollen die gematchten Constraintliterale dazu fuehren, dass die */
    /* c,a und s- literale der Partnerclauses in die Listen kommen...       */

    if (list_PointerMember(Lits, (POINTER)i)) {
      CLAUSE  PartnerCopy;
      LITERAL PLit;
      TERM    PAtom;
      SUBST   NewSubst,RightSubst;
      int     j,lc,la,n,PLitInd;

      Atom      = clause_GetLiteralAtom(ClauseCopy, i);
      NewClause = clause_CreateUnnormalized(Constraint, Antecedent, Succedent);

      list_Delete(Constraint);
      list_Delete(Antecedent);
      list_Delete(Succedent);
      Constraint  = list_Nil();
      Antecedent  = list_Nil();
      Succedent   = list_Nil();

      /* Find corresponding Foundlit: */
      for (Scan = Foundlits; 
	   term_TopSymbol(Atom) !=
	     term_TopSymbol(clause_LiteralAtom(list_Car(Scan))); 
	   Scan = list_Cdr(Scan));
      PLit        = list_Car(Scan);
      PLitInd     = clause_LiteralGetIndex(PLit);
      PartnerCopy = clause_Copy(clause_LiteralOwningClause(PLit));
      Partners    = list_Cons(PartnerCopy, Partners);
      ParentCls   = list_Cons((POINTER)clause_Number(PartnerCopy), ParentCls);
      ParentLits  = list_Cons((POINTER)PLitInd, ParentLits);
      MaxVar      = clause_SearchMaxVar(ClauseCopy);
      MaxCand     = clause_SearchMaxVar(NewClause);
      MaxVar      = ((MaxVar > MaxCand) ? MaxVar : MaxCand);   
      /* MaxVar is the maximal variable in the new clause or the ClauseCopy, */
      /* the latter to guarantee the stability of variable names.            */

      clause_RenameVarsBiggerThan(PartnerCopy, MaxVar);
      PLit  = clause_GetLiteral(PartnerCopy, PLitInd);
      PAtom = clause_LiteralAtom(PLit);
      
      cont_Check();
      if (!unify_UnifyNoOC(cont_LeftContext(), PAtom, cont_RightContext(), Atom)) {
	misc_StartErrorReport();
	misc_ErrorReport("\n In inf_BuildConstraintHyperResolvent: Unification failed.");
	misc_FinishErrorReport();
      }
      subst_ExtractUnifier(cont_LeftContext(), &RightSubst, cont_RightContext(), &NewSubst);
      cont_Reset();

      clause_SubstApply(NewSubst, NewClause);
      clause_SubstApply(NewSubst, ClauseCopy);
      subst_Delete(NewSubst);
      
      n  = clause_Length(PartnerCopy);
      lc = clause_LastConstraintLitIndex(PartnerCopy);
      la = clause_LastAntecedentLitIndex(PartnerCopy);
      for (j = clause_FirstLitIndex(); j < n; j++) {
	if (j <= lc) 
	  Constraint  = list_Cons(subst_Apply(RightSubst,
	    term_Copy(clause_GetLiteralAtom(PartnerCopy, j))),
	      Constraint);
	else if (j <= la) 
	  Antecedent  = list_Cons(subst_Apply(RightSubst,
            term_Copy(clause_GetLiteralAtom(PartnerCopy, j))),
               Antecedent);
	else if (j != PLitInd)
	  Succedent  = list_Cons(subst_Apply(RightSubst,
            term_Copy(clause_GetLiteralAtom(PartnerCopy, j))),
               Succedent);
      }

      subst_Delete(RightSubst);
      
      n  = clause_Length(NewClause);
      lc = clause_LastConstraintLitIndex(NewClause);
      la = clause_LastAntecedentLitIndex(NewClause);
      
      for (j = clause_FirstLitIndex(); j < n; j++) {
	if (j <= lc) 
	  Constraint  = list_Cons(term_Copy(clause_GetLiteralAtom(NewClause, j)),
				  Constraint);
	else if (j <= la) 
	  Antecedent  = list_Cons(term_Copy(clause_GetLiteralAtom(NewClause, j)),
				  Antecedent);
	else 
	  Succedent  = list_Cons(term_Copy(clause_GetLiteralAtom(NewClause, j)),
				 Succedent);
      }      
      clause_Delete(NewClause);
      clause_DecreaseCounter();
    }
  }
  NewClause = clause_Create(Constraint, Antecedent, Succedent, Flags,Precedence);

  list_Delete(Constraint); 
  list_Delete(Antecedent); 
  list_Delete(Succedent); 

  if (IsFromEmptySort)
    clause_SetFromEmptySort(NewClause);
  else
    clause_SetFromSortResolution(NewClause);

  clause_SetDepth(NewClause, depth + 1);

  clause_SetSplitDataFromList(NewClause, Partners);
  clause_DeleteClauseList(Partners);

  clause_SetParentClauses(NewClause, list_NReverse(ParentCls));
  clause_SetParentLiterals(NewClause, list_NReverse(ParentLits));

  return NewClause;
}


static LIST inf_ConstraintHyperResolvents(CLAUSE Clause, LIST Lits,
					  SUBST Subst, LIST Restlits,
					  LIST Foundlits, st_INDEX Index,
					  FLAGSTORE Flags, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A <Clause> where the sort constraint is resolved,
           a list <Lits> of constraint indices in <Clause> where
	   all corresponding constraints have the same term,
	   the overall substitution <Subst>,
	   a list <Restlits> of constraint indeces for which
	   a partner clause is searched with respect to <Index>,
	   a list <Foundlits> of literals of already found partner clauses,
	   a flag store and a precedence.
  RETURNS: The list of possible resolvents.
***************************************************************/
{
  if (list_Empty(Restlits))
    return list_List(inf_BuildConstraintHyperResolvent(Clause,Lits,Subst,
						       Foundlits, Flags,
						       Precedence));
  else {
    CLAUSE  PartnerCopy;
    LITERAL Lit, PLit;
    LIST    Result, NextLits;
    TERM    AtomCopy;
    SUBST   NewSubst, RightSubst, HelpSubst;
    SYMBOL  MaxVar, MaxCand;
    int     PLitInd;

    Result   = list_Nil();
    Lit      = clause_GetLiteral(Clause, (int) list_Car(Restlits));
    AtomCopy = subst_Apply(Subst, term_Copy(clause_LiteralAtom(Lit)));
    NextLits = inf_GetSortResolutionPartnerLits(AtomCopy,Index);
    MaxVar   = clause_MaxVar(Clause);
    MaxCand  = clause_AtomMaxVar(AtomCopy);
    MaxVar   = (symbol_GreaterVariable(MaxVar, MaxCand) ? MaxVar : MaxCand);
      
    for ( ; !list_Empty(NextLits); NextLits = list_Pop(NextLits)) {
      PLit        = list_Car(NextLits);
      PLitInd     = clause_LiteralGetIndex(PLit);
      Foundlits   = list_Cons(PLit, Foundlits);
      PartnerCopy = clause_Copy(clause_LiteralOwningClause(PLit));

      clause_RenameVarsBiggerThan(PartnerCopy, MaxVar);
      PLit        = clause_GetLiteral(PartnerCopy, PLitInd);

      cont_Check();
      unify_UnifyNoOC(cont_LeftContext(), AtomCopy,
		      cont_RightContext(), clause_LiteralAtom(PLit));
      subst_ExtractUnifier(cont_LeftContext(), &NewSubst, cont_RightContext(), &RightSubst);
      cont_Reset();

      subst_Delete(RightSubst);
      HelpSubst = NewSubst;
      NewSubst  = subst_Compose(NewSubst, subst_Copy(Subst));

      Result = list_Nconc(inf_ConstraintHyperResolvents(Clause, Lits, NewSubst,
							list_Cdr(Restlits),
							Foundlits, Index, Flags,
							Precedence),
			  Result);
      subst_Delete(NewSubst);
      subst_Delete(HelpSubst);
      clause_Delete(PartnerCopy);

      Foundlits = list_Pop(Foundlits);
    }
    term_Delete(AtomCopy);

    return Result;
  }
}


LIST inf_BackwardSortResolution(CLAUSE GivenClause, st_INDEX Index,
				SORTTHEORY SortTheory, BOOL Precheck,
				FLAGSTORE Flags, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause with a solved sort constraint, an index of clauses,
           a sort theory, a boolean flag indicating whether the subsort
	   precheck can be applied, a flag store and a precedence.
  RETURNS: A list of clauses inferred from the GivenClause by
           SortResolution with the given clause.
  MEMORY:  A list of clauses is produced, where memory for the list
           and the clauses is allocated.
***************************************************************/
{
  LIST     result;
  int      i, ls;

#ifdef CHECK
  if (!clause_IsClause(GivenClause, Flags, Precedence) ||
      !clause_HasSolvedConstraint(GivenClause)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In inf_BackwardSortResolution: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  result = list_Nil();
  ls     = clause_LastSuccedentLitIndex(GivenClause);

  for (i = clause_FirstSuccedentLitIndex(GivenClause); i <= ls; i++) {
    LITERAL pLit;
    TERM    pAtom;

    pLit  = clause_GetLiteral(GivenClause, i);
    pAtom = clause_LiteralAtom(pLit);

    if (clause_LiteralGetFlag(pLit,STRICTMAXIMAL) && 
	clause_LiteralIsSort(pLit)) {
      LIST termList;
      termList = st_GetUnifier(cont_LeftContext(),Index,cont_RightContext(),pAtom);
      
      for ( ; !list_Empty(termList); termList = list_Pop(termList)){
	if (term_IsAtom(list_Car(termList)) &&
	    !term_IsVariable(term_FirstArgument(list_Car(termList)))) {

	  LIST litScan;
	  litScan = sharing_NAtomDataList(list_Car(termList));
	  for ( ; !list_Empty(litScan); litScan = list_Cdr(litScan)) {
	    LITERAL gLit;
	    CLAUSE gClause;
	    gLit    = list_Car(litScan);
	    gClause = clause_LiteralOwningClause(gLit);
	    if (clause_LiteralGetIndex(gLit) < clause_FirstAntecedentLitIndex(gClause) && 
		clause_GetFlag(gClause,WORKEDOFF)) {
	      TERM   gAtom;
	      int    lc, gi, j;
	      LIST   tLits, restLits;
	      gAtom     = clause_LiteralAtom(gLit);
	      lc        = clause_LastConstraintLitIndex(gClause);
	      gi        = clause_LiteralGetIndex(gLit);
	      tLits     = list_List((POINTER)gi);
	      restLits  = list_Nil();
	      for (j = clause_FirstLitIndex(); j <= lc; j++) {
		LITERAL tCand;
		tCand = clause_GetLiteral(gClause, j);
		if (j != gi &&
		    term_FirstArgument(clause_LiteralAtom(tCand))
		    == term_FirstArgument(gAtom)) {
		  tLits     = list_Cons((POINTER)j, tLits);
		  restLits  = list_Cons((POINTER)j, restLits);
		}
	      }

	      if (!Precheck ||
		  inf_SubsortPrecheck(gClause,tLits,pLit,Index,SortTheory)) {
		CLAUSE pClauseCopy;
		SYMBOL minVar;
		LIST   foundLits;
		SUBST  leftSubst, rightSubst;
		pClauseCopy = clause_Copy(GivenClause);
		minVar      = clause_MaxVar(gClause);
		foundLits   = list_List(pLit);

		clause_RenameVarsBiggerThan(pClauseCopy, minVar);
		pAtom = clause_GetLiteralAtom(pClauseCopy, i);
		/* set, to unify correctly! */

		cont_Check();
		unify_UnifyNoOC(cont_LeftContext(), gAtom, cont_RightContext(), pAtom);
		subst_ExtractUnifier(cont_LeftContext(), &leftSubst,
				     cont_RightContext(), &rightSubst);
		cont_Reset();

		subst_Delete(rightSubst);

		result =
		  list_Nconc(inf_ConstraintHyperResolvents(gClause, tLits,
							   leftSubst, restLits,
							   foundLits, Index,
							   Flags, Precedence),
			     result);

		pAtom = clause_LiteralAtom(pLit);

		subst_Delete(leftSubst);
		list_Delete(foundLits);
		clause_Delete(pClauseCopy);
	      } /* if Precheck */
	      list_Delete(tLits);
	      list_Delete(restLits);
	    }
	  }
	}
      }
    }
  }
  return result;
}


LIST inf_ForwardSortResolution(CLAUSE GivenClause, st_INDEX Index,
			       SORTTHEORY SortTheory, BOOL Precheck,
			       FLAGSTORE Flags, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause with an unsolved sort constraint, an index of clauses,
           a sort theory, a boolean flag indicating whether the subsort
	   precheck can be applied, a flag store and a precedence.
  RETURNS: A list of clauses inferred from the GivenClause by
           SortResolution on the given clause.
  MEMORY:  A list of clauses is produced, where memory for the list
           and the clauses is allocated.
***************************************************************/
{
  LIST Result, TLits, RestLits;
  int  i, j, lc;
  BOOL Hit;
  TERM TAtom;

#ifdef CHECK
  if (!clause_IsClause(GivenClause, Flags, Precedence) ||
      !clause_HasTermSortConstraintLits(GivenClause)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In inf_ForwardSortResolution: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  Result = list_Nil();
  lc     = clause_LastConstraintLitIndex(GivenClause);
  Hit    = FALSE;

  i = clause_FirstLitIndex();
  while (i <= lc && !Hit) {
    TAtom = clause_GetLiteralAtom(GivenClause, i);
    if (!term_IsVariable(term_FirstArgument(TAtom)))
      Hit = TRUE;
    else
      i++;
  }

  if (!Hit)
    return list_Nil();

  /* added because of compiler warnings */
  TAtom = clause_GetLiteralAtom(GivenClause, i);

  /* Search the other T_i from <GivenClause> */
  TLits    = list_List((POINTER)i);
  for (j = i+1; j <= lc; j++) {
    if (term_FirstArgument(clause_GetLiteralAtom(GivenClause, j))
	== term_FirstArgument(TAtom))
      TLits    = list_Cons((POINTER)j, TLits);
  }
  RestLits = list_Copy(TLits);
  
  if (!Precheck ||
      inf_SubsortPrecheck(GivenClause, TLits, NULL, Index, SortTheory)) {

    Result = inf_ConstraintHyperResolvents(GivenClause, TLits, subst_Nil(),
					   RestLits, list_Nil(), Index, Flags,
					   Precedence);

  }
  list_Delete(RestLits);
  list_Delete(TLits);

  return Result;
}


LIST inf_BackwardEmptySort(CLAUSE GivenClause, st_INDEX Index,
			   SORTTHEORY SortTheory, BOOL Precheck,
			   FLAGSTORE Flags, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause with a solved sort constraint, an 'Index' of clauses,
           a sort theory, a boolean flag indicating whether the subsort
	   precheck can be applied, a flag store and a precedence.
  RETURNS: A list of clauses inferred from the GivenClause by
           EmptySort with the given clause.
  MEMORY:  A list of clauses is produced, where memory for the list
           and the clauses is allocated.
***************************************************************/
{
  LIST result;
  int  i, ls;

#ifdef CHECK
  if (!(clause_IsClause(GivenClause, Flags, Precedence)) ||
      !clause_HasSolvedConstraint(GivenClause)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In inf_BackwardEmptySort: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  result = list_Nil();
  
  ls = clause_LastSuccedentLitIndex(GivenClause);

  for (i = clause_FirstSuccedentLitIndex(GivenClause); i <= ls; i++) {
    LITERAL pLit  = clause_GetLiteral(GivenClause, i);
    TERM    pAtom = clause_LiteralAtom(pLit);
      
    if (clause_LiteralGetFlag(pLit,STRICTMAXIMAL) && 
	clause_LiteralIsSort(pLit)) {
      LIST unifiers = st_GetUnifier(cont_LeftContext(),Index,cont_RightContext(),pAtom);
	
      for ( ; !list_Empty(unifiers); unifiers = list_Pop(unifiers)){
	if (term_IsAtom(list_Car(unifiers)) &&
	    term_IsVariable(term_FirstArgument(list_Car(unifiers)))) {
	  LIST litScan = sharing_NAtomDataList(list_Car(unifiers));
	    
	  for ( ; !list_Empty(litScan); litScan = list_Cdr(litScan)){
	    LITERAL gLit   = list_Car(litScan);
	    CLAUSE gClause = clause_LiteralOwningClause(gLit);
	      
	    if (clause_LiteralGetIndex(gLit) < clause_FirstAntecedentLitIndex(gClause) &&
		clause_GetFlag(gClause,WORKEDOFF) &&
		clause_HasOnlyVarsInConstraint(gClause, Flags, Precedence)) {
	      TERM   gAtom     = clause_LiteralAtom(gLit);
	      SYMBOL var       = term_TopSymbol(term_FirstArgument(gAtom));
	      int    lc        = clause_LastConstraintLitIndex(gClause);
	      int    gi        = clause_LiteralGetIndex(gLit);
	      BOOL   varOccursNoMore;
	      int    j, bound;

	      varOccursNoMore = TRUE;
	      bound           = clause_LastSuccedentLitIndex(gClause);
		
	      for (j = clause_FirstAntecedentLitIndex(gClause);
		   (j <= bound) && varOccursNoMore;
		   j++) {
		if (term_ContainsSymbol(clause_GetLiteralAtom(gClause, j), var))
		  varOccursNoMore = FALSE;
	      }
		
	      if (varOccursNoMore) {
		LIST tLits, restLits;

		/* Search the other T_i from <gClause> */
		tLits     = list_List((POINTER)gi);
		restLits  = list_Nil();		
		for (j = clause_FirstLitIndex(); j <= lc; j++) {
		  LITERAL tCand = clause_GetLiteral(gClause, j);

		  if (j != gi &&
		      term_FirstArgument(clause_LiteralAtom(tCand))
		      == term_FirstArgument(gAtom)) {
		    tLits     = list_Cons((POINTER)j, tLits);
		    restLits  = list_Cons((POINTER)j, restLits);
		  }
		}

		if (!Precheck ||
		    inf_SubsortPrecheck(gClause,tLits,pLit,Index,SortTheory)) {
		  CLAUSE pCopy     = clause_Copy(GivenClause);
		  SYMBOL minVar    = clause_MaxVar(gClause);
		  LIST   foundLits = list_List(pLit);
		  SUBST  leftSubst, rightSubst;

		  clause_RenameVarsBiggerThan(pCopy, minVar);
		  pAtom = clause_GetLiteralAtom(pCopy, i);
		  /* set, to adress the renamed term! */
		  
		  cont_Check();
		  unify_UnifyNoOC(cont_LeftContext(), gAtom, cont_RightContext(), pAtom);
		  subst_ExtractUnifier(cont_LeftContext(),  &leftSubst,
				       cont_RightContext(), &rightSubst);
		  cont_Reset();

		  subst_Delete(rightSubst);
		  
		  result =
		    list_Nconc(inf_ConstraintHyperResolvents(gClause, tLits,
							     leftSubst,restLits,
							     foundLits, Index,
							     Flags, Precedence),
			       result);

		  list_Delete(foundLits);
		  subst_Delete(leftSubst);
		  clause_Delete(pCopy);
		  
		  pAtom = clause_LiteralAtom(pLit);
		  /* reset to original clauses literal! */
		} /* if Precheck */
		list_Delete(tLits);
		list_Delete(restLits);
	      }
	    }
	  }
	}
      }
    }
  }
  return result;
}


LIST inf_ForwardEmptySort(CLAUSE GivenClause, st_INDEX Index,
			  SORTTHEORY SortTheory, BOOL Precheck, FLAGSTORE Flags,
			  PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause, an index of clauses, a sort theory,
           a boolean flag indicating whether the subsort
	   precheck can be applied, a flag store and a precedence.
	   The constraint of <GivenClause> is necessarily unsolved
  RETURNS: A list of clauses inferred from the GivenClause by
           EmptySort on the given clause.
  MEMORY:  A list of clauses is produced, where memory for the list
           and the clauses is allocated.
***************************************************************/
{
  LIST   Result, TLits, RestLits;
  int    i, j, lc, ls;
  BOOL   Hit;
  TERM   TAtom;
  SYMBOL Var;

#ifdef CHECK
  if (clause_HasTermSortConstraintLits(GivenClause) ||
      clause_HasSolvedConstraint(GivenClause)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In inf_ForwardEmptySort: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif
  
  Result = list_Nil();
  lc     = clause_LastConstraintLitIndex(GivenClause);
  Hit    = FALSE;
  
  i = clause_FirstLitIndex();
  while (i <= lc && !Hit) {
    TAtom = clause_GetLiteralAtom(GivenClause, i);

    if (term_IsVariable(term_FirstArgument(TAtom))) {
      Var   = term_TopSymbol(term_FirstArgument(TAtom));
      ls    = clause_LastSuccedentLitIndex(GivenClause);
      Hit = TRUE;
      /* Check if the variable occurs in antecedent or succedent literals */
      for (j = clause_FirstAntecedentLitIndex(GivenClause);
	   j <= ls && Hit; j++) {
	if (term_ContainsSymbol(clause_GetLiteralAtom(GivenClause,j), Var))
	  Hit = FALSE; /* Variable occurs in antecedent/constraint literal */
      }
    }
    if (!Hit)
      i++;
  }
  
  if (!Hit)
    return list_Nil();

  TAtom = clause_GetLiteralAtom(GivenClause, i);
  Var   = term_TopSymbol(term_FirstArgument(TAtom));

  /* Search the other T_i(t) literals */
  TLits    = list_List((POINTER)i);
  for (j = i+1; j <= lc; j++) {
    TERM TCand;
    
    TCand = clause_GetLiteralAtom(GivenClause, j);
    
    if (symbol_Equal(term_TopSymbol(term_FirstArgument(TCand)), Var))
      TLits    = list_Cons((POINTER)j, TLits);
  }
  RestLits = list_Copy(TLits);
  
  if (!Precheck ||
      inf_SubsortPrecheck(GivenClause, TLits, NULL, Index, SortTheory)) {
    
    Result = inf_ConstraintHyperResolvents(GivenClause, TLits, subst_Nil(),
					   RestLits, list_Nil(), Index, Flags,
					   Precedence);

  }
  list_Delete(RestLits);
  list_Delete(TLits);
  
  return Result;
}

static LIST inf_GetForwardPartnerLits(LITERAL Literal, st_INDEX Index)
/**************************************************************
  INPUT:   A monadic literal, and an index of clauses.
  RETURNS: A list of monadic succedent literals whose subterm
           is unifiable with the (one) subterm of <Literal>.
	   The literals are strict maximal in their respective clauses,
	   the clauses are "WORKEDOFF" and either the subterm
	   is not a variable or the clause has an empty constraint.
  MEMORY:  Allocates memory for the list.
***************************************************************/
{
  LIST result, unifiers, atomScan, litScan;

#ifdef CHECK
  if (!clause_LiteralIsLiteral(Literal) || !clause_LiteralIsSort(Literal)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In inf_GetForwardPartnerLits: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  result   = list_Nil();
  /* Search unifiers for the literal's subterm */
  unifiers = st_GetUnifier(cont_LeftContext(), Index, cont_RightContext(),
			   term_FirstArgument(clause_LiteralAtom(Literal)));
  
  for ( ; !list_Empty(unifiers); unifiers = list_Pop(unifiers)) {

    if (!term_IsAtom(list_Car(unifiers))) { /* Can happen if arg is variable */
      
      for (atomScan = term_SupertermList(list_Car(unifiers)); 
	   !list_Empty(atomScan); 
	   atomScan = list_Cdr(atomScan)) {
	TERM atomCand;
	atomCand = (TERM) list_Car(atomScan);
	if (term_IsDeclaration(atomCand)) {
	  /* We are looking for an unary atom */

	  for (litScan = sharing_NAtomDataList(atomCand);
	       !list_Empty(litScan);
	       litScan = list_Cdr(litScan)) {
	    LITERAL nextLit;
	    CLAUSE  nextClause;
	    nextLit    = list_Car(litScan);
	    nextClause = clause_LiteralOwningClause(nextLit);

	    if (clause_LiteralIsPositive(nextLit) && 
		clause_LiteralGetFlag(nextLit,STRICTMAXIMAL) &&
		clause_GetFlag(nextClause, WORKEDOFF) &&
		(!term_IsVariable(list_Car(unifiers)) ||
		 clause_HasEmptyConstraint(nextClause)) &&
		clause_HasSolvedConstraint(nextClause)) {
	      /* Add the literal from the copied clause */
	      result = list_Cons(nextLit, result);
	    }
	  }  /* litScan */
	}    /* if IsAtom */
      }      /* atomScan */
    }        /* ! variable */
  }          /* unifiers */
  return result;
}

static BOOL inf_LiteralsHaveSameSubtermAndAreFromSameClause(LITERAL L1, LITERAL L2)
/**************************************************************
  INPUT:   Two literals.
  RETURNS: TRUE, if both literals have the same term and are
           from the same clause, FALSE otherwise.
	   Since both literals are shared, pointer equality
	   is used to detect this.
	   This function is used by inf_GetBackwardPartnerLits().
***************************************************************/
{
  return (term_FirstArgument(clause_LiteralAtom(L1))
	  == term_FirstArgument(clause_LiteralAtom(L2)) &&
	  clause_LiteralOwningClause(L1) == clause_LiteralOwningClause(L2));
}

static void inf_GetBackwardPartnerLits(LITERAL Literal, st_INDEX Index,
				       LIST* ConstraintLits, LIST* Unifiers,
				       BOOL IsFromEmptySort, FLAGSTORE Flags,
				       PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A literal, an index of clauses, two pointers to lists,
           a boolean value, a flag store and a precedence.
  RETURNS:
  MEMORY:  Allocates memory for the list.
***************************************************************/
{
  LIST candidates, atomScan, litScan;
  LITERAL nextLit;
  CLAUSE  nextClause;

#ifdef CHECK
  if (!clause_LiteralIsLiteral(Literal) || !clause_LiteralIsSort(Literal)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In inf_GetBackwardPartnerLits: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  candidates = st_GetUnifier(cont_LeftContext(), Index, cont_RightContext(),
			     term_FirstArgument(clause_LiteralAtom(Literal)));

  for ( ; !list_Empty(candidates); candidates = list_Pop(candidates)) {
    if (!term_IsAtom(list_Car(candidates))) { /* May happen if arg is variable */
      /* Consider variable unifiers only if called from BackwardEmptySort */
      for (atomScan = term_SupertermList(list_Car(candidates)); 
	   !list_Empty(atomScan); 
	   atomScan = list_Cdr(atomScan)) {
	TERM atomCand;
	atomCand = (TERM) list_Car(atomScan);
	if (term_IsDeclaration(atomCand)) {
	  /* We are looking for unary atoms */

	  for (litScan = sharing_NAtomDataList(atomCand);
	       !list_Empty(litScan);
	       litScan = list_Cdr(litScan)) {
	    nextLit    = list_Car(litScan);
	    nextClause = clause_LiteralOwningClause(nextLit);
	    
	    if (clause_GetFlag(nextClause, WORKEDOFF)) {
	      if (clause_LiteralIsPositive(nextLit)) {
		if (clause_LiteralGetFlag(nextLit,STRICTMAXIMAL) &&
		    (!term_IsVariable(list_Car(candidates)) ||
		     clause_HasEmptyConstraint(nextClause)) &&
		    clause_HasSolvedConstraint(nextClause) &&
		    !symbol_Equal(clause_LiteralPredicate(Literal),
				  clause_LiteralPredicate(nextLit))) {
		  /* Don't consider literals with same top symbol as given literal */
		  /* since the given clause must be part of any inference */
		  *Unifiers = list_Cons(nextLit, *Unifiers);
		}
	      } else if (clause_LiteralGetIndex(nextLit) < clause_FirstAntecedentLitIndex(nextClause) &&
			 ((!term_IsVariable(list_Car(candidates)) && !IsFromEmptySort) ||
			  (term_IsVariable(list_Car(candidates)) && IsFromEmptySort &&
			   clause_HasOnlyVarsInConstraint(nextClause,Flags, Precedence)))) {
		*ConstraintLits = list_Cons(nextLit, *ConstraintLits);
	      }
	    }
	  } /* litScan */
	}
      }     /* atomScan */
    }
  }         /* candidates */

  /* We have to avoid constraint literals from the same clause with the same
     term or variable, since those would create the same result clause. */
  *ConstraintLits =
    list_DeleteDuplicates(*ConstraintLits,
			  (BOOL (*)(POINTER,POINTER)) inf_LiteralsHaveSameSubtermAndAreFromSameClause);
}

static void inf_MakeClausesDisjoint(CLAUSE GClause, LIST Literals)
/**************************************************************
  INPUT:   A clause and a non-empty list of literals.
  EFFECT:  All input clauses, those pointed to by the literals,
           are variable disjointly renamed.
***************************************************************/
{
  SYMBOL maxVar, maxCand;
  CLAUSE lastClause;

  maxVar     = clause_MaxVar(GClause);
  lastClause = clause_LiteralOwningClause(list_Car(Literals));
  clause_RenameVarsBiggerThan(lastClause, maxVar);
  Literals   = list_Cdr(Literals);

  for ( ; !list_Empty(Literals); Literals = list_Cdr(Literals)) {
    CLAUSE actClause;

    clause_UpdateMaxVar(lastClause);
    maxCand = clause_MaxVar(lastClause);    
    maxVar = (symbol_GreaterVariable(maxVar,maxCand)? maxVar : maxCand);

    actClause = clause_LiteralOwningClause(list_Car(Literals));
    clause_RenameVarsBiggerThan(actClause, maxVar);
  }
}

static void inf_CopyUnifierClauses(LIST Literals)
/**************************************************************
  INPUT:   A list of literals.
  EFFECT:  Replaces all literals by pointers to literals of copies
           of the respective clauses.
***************************************************************/
{
  for ( ; !list_Empty(Literals); Literals = list_Cdr(Literals)) {
    CLAUSE actClause;
    int    i;

    actClause = clause_LiteralOwningClause(list_Car(Literals));
    i         = clause_LiteralGetIndex(list_Car(Literals));
    actClause = clause_Copy(actClause);
    list_Rplaca(Literals, clause_GetLiteral(actClause, i)); /* Set to literal from copy */
  }
}

static void inf_DeleteUnifierClauses(LIST Literals)
/**************************************************************
  INPUT:   A list of literals.
  EFFECT:  Deletes all clauses the literals point to.
***************************************************************/
{
  for ( ; !list_Empty(Literals); Literals = list_Cdr(Literals)) {
    clause_Delete(clause_LiteralOwningClause(list_Car(Literals)));
    list_Rplaca(Literals, NULL);
  }
}

static SORT inf_GetSortFromLits(LIST Literals, SORTTHEORY SortTheory)
/**************************************************************
  INPUT:   A list of literals and a sort theory.
  RETURNS: The sort created from the literals' predicates.
***************************************************************/
{
  SORT result = sort_TopSort();

  for ( ; !list_Empty(Literals); Literals = list_Cdr(Literals)) {
    SORT newSort = sort_TheorySortOfSymbol(SortTheory,
					   clause_LiteralPredicate(list_Car(Literals)));
    
    result = sort_Intersect(newSort, result);
  }

  list_PointerDeleteDuplicates(result);

  return result;
}

static LIST inf_ApplyWeakening(CLAUSE Clause, LIST TLits, LIST Partners,
			       CONDITION Condition, FLAGSTORE Flags,
			       PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause, a list of constraint indices in <Clause>,
           a list of maximal, monadic succedent literals,
	   a subsort condition, a flag store and a precedence.
  RETURNS: A one-element list with a clause derived from the
           clause and the partner clauses by the Weakening or
	   Empty Sort rule.
           The flag store is needed to create the result clause.
  MEMORY:  Memory is allocated for the returned list and the clause.
***************************************************************/
{
  LIST   scan, parents;
  LIST   constraint, antecedent, succedent;
  LIST   parentClauses, parentLits;   /* clause numbers and literal indices */
  int    i, bound, depth;
  TERM   tSubterm;
  CLAUSE newClause;

#ifdef CHECK
  if (!clause_IsClause(Clause, Flags, Precedence) || list_Empty(TLits) ||
      list_Empty(Partners) || Condition == NULL) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In inf_ApplyWeakening: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  constraint    = antecedent = succedent = list_Nil();
  parentClauses = parentLits = list_Nil();
  parents       = list_Nil();                      /* Used to set split data */
  depth         = clause_Depth(Clause);
  tSubterm      = term_FirstArgument(clause_GetLiteralAtom(Clause, (int)list_Car(TLits)));

  /* Now collect the literals of the new clause */
  /* First consider the condition atoms */
  for (scan=sort_ConditionConstraint(Condition); !list_Empty(scan); scan=list_Cdr(scan)) {
    TERM termCopy;

    termCopy = term_Copy(list_Car(scan));
    term_ReplaceVariable(termCopy, sort_ConditionVar(Condition), tSubterm);
    constraint = list_Cons(cont_CopyAndApplyBindings(cont_LeftContext(), termCopy),
			   constraint);
    term_Delete(termCopy);   /* constraint contains a copy */
  }
  for (scan=sort_ConditionAntecedent(Condition); !list_Empty(scan); scan=list_Cdr(scan)) {
    TERM termCopy;

    termCopy = term_Copy(list_Car(scan));
    term_ReplaceVariable(termCopy, sort_ConditionVar(Condition), tSubterm);
    antecedent = list_Cons(cont_CopyAndApplyBindings(cont_LeftContext(), termCopy),
			   antecedent);
    term_Delete(termCopy);   /* antecedent contains a copy */ 
  }
  for (scan=sort_ConditionSuccedent(Condition); !list_Empty(scan); scan=list_Cdr(scan)) {
    TERM termCopy;
    
    termCopy = term_Copy(list_Car(scan));
    term_ReplaceVariable(termCopy, sort_ConditionVar(Condition), tSubterm);
    succedent = list_Cons(cont_CopyAndApplyBindings(cont_LeftContext(), termCopy),
			  succedent);
    term_Delete(termCopy);   /* succedent contains a copy */
  }
  /* update parents and depth from condition clauses */
  for (scan=sort_ConditionClauses(Condition); !list_Empty(scan); scan=list_Cdr(scan)) {
    CLAUSE condClause;

    condClause    = list_Car(scan);
    parents       = list_Cons(condClause, parents);
    parentClauses = list_Cons((POINTER)clause_Number(condClause), parentClauses);
    parentLits    = list_Cons((POINTER)clause_FirstSuccedentLitIndex(condClause), parentLits);
    depth         = misc_Max(depth, clause_Depth(condClause));
  }

  /* Now we consider the partner clauses */
  for (scan = Partners; !list_Empty(scan); scan = list_Cdr(scan)) {
    LITERAL pLit;
    CLAUSE  pClause;
    int     pi;

    pLit    = list_Car(scan);
    pClause = clause_LiteralOwningClause(pLit);
    pi      = clause_LiteralGetIndex(pLit);
    bound   = clause_LastConstraintLitIndex(pClause);
    for (i = clause_FirstLitIndex(); i <= bound; i++) {
      constraint = list_Cons(cont_CopyAndApplyBindings(cont_RightContext(),
						       clause_GetLiteralAtom(pClause,i)),
			     constraint);
    }
    bound = clause_LastAntecedentLitIndex(pClause);
    for (i = clause_FirstAntecedentLitIndex(pClause); i <= bound; i++) {
      antecedent = list_Cons(cont_CopyAndApplyBindings(cont_RightContext(),
						       clause_GetLiteralAtom(pClause,i)),
			     antecedent);
    }
    bound = clause_LastSuccedentLitIndex(pClause);
    for (i = clause_FirstSuccedentLitIndex(pClause); i <= bound; i++) {
      if (i != pi)
	succedent = list_Cons(cont_CopyAndApplyBindings(cont_RightContext(),
							clause_GetLiteralAtom(pClause,i)),
			      succedent);
    }

    parents = list_Cons(pClause, parents);

    parentClauses = list_Cons((POINTER)clause_Number(pClause), parentClauses);
    parentLits    = list_Cons((POINTER) pi, parentLits);

    depth = misc_Max(depth, clause_Depth(pClause));
  }

  /* Last but not least we consider the <Clause> itself */
  bound = clause_LastConstraintLitIndex(Clause);
  for (i = clause_FirstLitIndex(); i <= bound; i++) {
    if (!list_PointerMember(TLits, (POINTER)i))
	constraint = list_Cons(cont_CopyAndApplyBindings(cont_LeftContext(),
							 clause_GetLiteralAtom(Clause,i)),
			       constraint);
    else {
      parentClauses = list_Cons((POINTER)clause_Number(Clause), parentClauses);
      parentLits    = list_Cons((POINTER)i, parentLits);
    }
  }
  bound = clause_LastAntecedentLitIndex(Clause);
  for (i = clause_FirstAntecedentLitIndex(Clause); i <= bound; i++) {
    antecedent = list_Cons(cont_CopyAndApplyBindings(cont_LeftContext(),
						     clause_GetLiteralAtom(Clause,i)),
			   antecedent);
  }
  bound = clause_LastSuccedentLitIndex(Clause);
  for (i = clause_FirstSuccedentLitIndex(Clause); i <= bound; i++) {
    succedent = list_Cons(cont_CopyAndApplyBindings(cont_LeftContext(),
						    clause_GetLiteralAtom(Clause,i)),
			  succedent);
  }

  parents = list_Cons(Clause, parents);
  
  /* Now we've got all data we need */
  newClause = clause_Create(constraint, antecedent, succedent, Flags,Precedence);
  
  list_Delete(constraint);
  list_Delete(antecedent);
  list_Delete(succedent);
  
  if (term_IsVariable(tSubterm))
    clause_SetFromEmptySort(newClause);
  else
    clause_SetFromSortResolution(newClause);
  
  clause_SetDepth(newClause, depth+1);
  clause_SetFlag(newClause, DOCCLAUSE);
  
  clause_SetSplitDataFromList(newClause, parents);
  list_Delete(parents);
  
  clause_SetParentClauses(newClause, parentClauses);
  clause_SetParentLiterals(newClause, parentLits);
 
  return list_List(newClause);
}

static LIST inf_InternWeakening(CLAUSE Clause, LIST TLits, LIST Unifiers,
				LITERAL Special, LIST SojuList, FLAGSTORE Flags,
				PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A <Clause> with unsolved sort constraint,
           a list <TLits> of constraint indices in <Clause> where
	   all corresponding constraints have the same term,
	   a list <Unifiers> of monadic succedent literals whose
	   subterm is unifiable with the subterm of the <TLits>,
	   and a flag store.
	   If called from a backward rule the literal <Special>
	   will be the succedent literal from the respective
	   GivenClause, that must be part of every considered
	   SOJU sort. If called from a forward rule <Special> is NULL.
	   A list <SojuList> of sort pairs.
	   A flag store and a precedence.
  RETURNS: The list of possible resolvents.
  EFFECT:  ATTENTION: <SojuList> is deleted.
  MEMORY:  Memory is allocated for the returned list and the clauses.
***************************************************************/
{
  LIST result, myUnifiers;
  TERM searchTerm; 
  int  stack;

  LIST scan;
#ifdef CHECK
  if (!clause_IsClause(Clause, Flags, Precedence) || list_Empty(TLits) ||
      list_Empty(Unifiers)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In inf_InternWeakening: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  putchar('\n'); clause_Print(Clause);
  fputs("\nT_k = ", stdout);
  for (scan = TLits; !list_Empty(scan); scan = list_Cdr(scan)) {
    clause_LiteralPrint(clause_GetLiteral(Clause, (int)list_Car(scan)));
    putchar(' ');
  }
  fputs("\nS_k =", stdout);
  for (scan = Unifiers; !list_Empty(scan); scan = list_Cdr(scan)) {
    putchar('\n');
    clause_LiteralPrint(list_Car(scan));
    fputs(" in ", stdout);
    clause_Print(clause_LiteralOwningClause(list_Car(scan)));
  }
  putchar('\n');

  if (list_Empty(SojuList))
    return list_Nil();

  /*return list_Nil();*/
  /* Und Schluss */

  result = list_Nil();

  myUnifiers = list_Copy(Unifiers);
  inf_CopyUnifierClauses(myUnifiers);
  inf_MakeClausesDisjoint(Clause, myUnifiers);

  searchTerm =
    term_FirstArgument(clause_GetLiteralAtom(Clause, (int)list_Car(TLits)));

  stack  = stack_Bottom();

  for ( ; !list_Empty(SojuList); SojuList = list_Pop(SojuList)) {
    SOJU actSoju = list_Car(SojuList);

    fputs("\nSOJU: ", stdout); sort_PairPrint(actSoju); fflush(stdout);

    if (Special == NULL ||
	sort_ContainsSymbol(sort_PairSort(actSoju),
			    clause_LiteralPredicate(Special))) { 
      LIST actSortSymbols, symbolScan, unifierScan, subset;

      actSortSymbols = sort_GetSymbolsFromSort(sort_PairSort(actSoju));
      subset         = list_Nil();

      symbolScan  = actSortSymbols;
      unifierScan = myUnifiers;

      do {
	while (!list_Empty(symbolScan) && !list_Empty(unifierScan)) {
	  LITERAL actLit = list_Car(unifierScan);

	  if (symbol_Equal(clause_LiteralPredicate(list_Car(unifierScan)),
			   (SYMBOL)list_Car(symbolScan))) {
	    cont_StartBinding();
	    if (unify_UnifyNoOC(cont_LeftContext(), searchTerm, cont_RightContext(),
				term_FirstArgument(clause_LiteralAtom(actLit)))) {
	      /* Found corresponding literal for sort symbol */
	      stack_Push(symbolScan);
	      stack_Push(list_Cdr(unifierScan));
	      subset = list_Cons(actLit, subset);
	      /* Now search literals for the next sort symbol */
	      symbolScan = list_Cdr(symbolScan);

	      if (!list_Empty(symbolScan))
		/* Start search for literal at the beginning of unifier list */
		unifierScan = myUnifiers;
	      else
		unifierScan = list_Cdr(unifierScan);
	    } else {
	      cont_BackTrack();
	      unifierScan = list_Cdr(unifierScan);
	    }
	  } else
	    unifierScan = list_Cdr(unifierScan);
	}

	if (list_Empty(symbolScan)) {
	  /*putchar('\n');
	  clause_LiteralListPrint(subset);*/
	  /* Found subset */
	  result = list_Nconc(inf_ApplyWeakening(Clause, TLits, subset,
						 sort_PairCondition(actSoju),
						 Flags, Precedence),
			      result);
	}

	while (!stack_Empty(stack) && list_Empty(stack_Top())) {
	  /* No more literals */
	  stack_NPop(2);
	  cont_BackTrack();
	  subset = list_Pop(subset);
	}

	if (!stack_Empty(stack)) {
	  /* Implies that stack_Top is a non-empty list */
	  unifierScan = stack_PopResult();
	  symbolScan  = stack_PopResult();
	  cont_BackTrack();
	  subset = list_Pop(subset);
	}
      } while (!stack_Empty(stack) || !list_Empty(unifierScan));

      list_Delete(actSortSymbols);
    }
    sort_PairDelete(actSoju);
  } /* For all SOJUs */

  inf_DeleteUnifierClauses(myUnifiers);
  list_Delete(myUnifiers);

  return result;
}

LIST inf_ForwardWeakening(CLAUSE GivenClause, st_INDEX Index,
			  SORTTHEORY SortTheory, FLAGSTORE Flags,
			  PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause, an index of clauses, a sort theory, a flag store
           and a precedence.
           The sort constraint of the clause must contain a non-variable term
	   (this implies the sort constraint is unsolved). 
  RETURNS: A list of clauses derived from the GivenClause by
           the Weakening rule.
  MEMORY:  Memory is allocated for the returned list and the clauses.
***************************************************************/
{
  LIST    result;
  int     i, lc;
  BOOL    hit;

#ifdef CHECK
  if (!clause_HasTermSortConstraintLits(GivenClause)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In inf_ForwardWeakening: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  result = list_Nil();
  lc     = clause_LastConstraintLitIndex(GivenClause);
  hit    = FALSE;

  for (i = clause_FirstLitIndex(); i <= lc && !hit; i++) {
    
    if (!term_IsVariable(term_FirstArgument(clause_GetLiteralAtom(GivenClause, i)))) {
      /* Condition implies that constraint is unsolved */
      LITERAL tLit;
      LIST    unifiers;
      int     j;

      tLit     = clause_GetLiteral(GivenClause, i);
      hit      = TRUE; /* Try only the first appropriate constraint literal */
      unifiers = inf_GetForwardPartnerLits(tLit, Index);

      if (!list_Empty(unifiers)) {
	TERM tAtom;
	LIST tLits, sojuList;
	SORT tSort, unifierSort;

	tAtom = clause_GetLiteralAtom(GivenClause, i);

	/* Search the other T_k(t) in GivenClause */
	tLits = list_Nil();
	tSort = sort_TopSort();
	for (j = lc; j > i; j--) {
	  TERM actAtom;
	  actAtom = clause_GetLiteralAtom(GivenClause, j);
	  if (term_FirstArgument(actAtom) == term_FirstArgument(tAtom)) {
	    tLits = list_Cons((POINTER)j, tLits);
	    tSort = sort_Intersect(sort_TheorySortOfSymbol(SortTheory, term_TopSymbol(actAtom)),
				   tSort);
	  }
	}
	tLits = list_Cons((POINTER)i, tLits);
	tSort = sort_Intersect(sort_TheorySortOfSymbol(SortTheory, term_TopSymbol(tAtom)),
			       tSort);
	list_PointerDeleteDuplicates(tSort);
	/* Necessary for Christoph's function */

	unifierSort = inf_GetSortFromLits(unifiers, SortTheory);
	sojuList    = sort_TheoryComputeAllSubsortHits(SortTheory, unifierSort, tSort);
	sort_Delete(unifierSort);
	sort_Delete(tSort);

	result =
	  list_Nconc(inf_InternWeakening(GivenClause, tLits, unifiers, NULL,
					 sojuList, Flags, Precedence),
		     result);

	list_Delete(tLits);
	list_Delete(unifiers);
      }
    }
  }
  return result;
}

LIST inf_BackwardWeakening(CLAUSE GivenClause, st_INDEX Index,
			   SORTTHEORY SortTheory, FLAGSTORE Flags,
			   PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause with solved sort constraint, an index of clauses,
           a sort theory, a flag store and a precedence.
  RETURNS: A list of clauses inferred from the GivenClause by
           the Weakening rule.
  MEMORY:  Memory is allocated for the list and the clauses.
***************************************************************/
{
  LIST     result;
  int      i, ls;

#ifdef CHECK
  if (!clause_HasSolvedConstraint(GivenClause)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In inf_BackwardWeakening: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  result = list_Nil();
  ls     = clause_LastSuccedentLitIndex(GivenClause);

  for (i = clause_FirstSuccedentLitIndex(GivenClause); i <= ls; i++) {
    LITERAL sLit;
    TERM    sAtom;

    sLit  = clause_GetLiteral(GivenClause, i);
    sAtom = clause_LiteralAtom(sLit);
    if (clause_LiteralGetFlag(sLit, STRICTMAXIMAL) && 
	clause_LiteralIsSort(sLit) &&
	(!term_IsVariable(term_FirstArgument(sAtom)) ||
	 clause_HasEmptyConstraint(GivenClause))) {
      LIST unifiers, partners;
      SORT unifierSort;

      unifiers = partners = list_Nil();
      inf_GetBackwardPartnerLits(sLit,Index,&partners,&unifiers,FALSE,Flags,
				 Precedence);
      unifiers = list_Cons(sLit, unifiers);
      /* <partners> holds monadic constraint literals */
      /* <unifiers> holds monadic, maximal succedent literals */
      unifierSort = inf_GetSortFromLits(unifiers, SortTheory);
      
      for ( ; !list_Empty(partners); partners = list_Pop(partners)) {
	LITERAL tLit;
	CLAUSE  tClause;
	TERM    tAtom;
	int     ti;
	int     lc;
	int     j;
	LIST    tLits, sojuList;
	SORT    tSort;

	tLit    = list_Car(partners);
	tClause = clause_LiteralOwningClause(tLit);
	tAtom   = clause_LiteralAtom(tLit);
	ti      = clause_LiteralGetIndex(tLit);
	lc      = clause_LastConstraintLitIndex(tClause);

	/* Search the other T_k(t) in GivenClause */
	tLits = list_Nil();
	tSort = sort_TopSort();
	for (j = lc; j >= clause_FirstLitIndex(); j--) {
	  TERM actAtom;

	  actAtom = clause_GetLiteralAtom(tClause, j);
	  if (j != ti &&
	      term_FirstArgument(actAtom) == term_FirstArgument(tAtom)) {
	    tLits = list_Cons((POINTER)j, tLits);
	    tSort = sort_Intersect(sort_TheorySortOfSymbol(SortTheory, term_TopSymbol(actAtom)),
				   tSort);
	  }
	}
	tLits = list_Cons((POINTER)ti, tLits);
	tSort = sort_Intersect(sort_TheorySortOfSymbol(SortTheory, term_TopSymbol(tAtom)),
			       tSort);
	list_PointerDeleteDuplicates(tSort);

	sojuList = sort_TheoryComputeAllSubsortHits(SortTheory, unifierSort, tSort);
	sort_Delete(tSort);

	cont_StartBinding();
	unify_UnifyNoOC(cont_LeftContext(), tAtom,
			cont_RightContext(), sAtom);

	result =
	  list_Nconc(inf_InternWeakening(tClause, tLits, unifiers, sLit,
					 sojuList, Flags, Precedence),
		     result);

	cont_BackTrack();

	list_Delete(tLits);
      }
      sort_Delete(unifierSort);
      list_Delete(unifiers);
    }
  }

  return result;
}

LIST inf_ForwardEmptySortPlusPlus(CLAUSE GivenClause, st_INDEX Index,
				  SORTTHEORY SortTheory, FLAGSTORE Flags,
				  PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause,  an 'Index' of clauses, a sort theory, a flag store
           and a precedence.
           The sort constraint of the clause must not contain a
	   non-variable term, but the sort constraint has to be unsolved.
  RETURNS: A list of clauses derived from the GivenClause by
           the Empty Sort rule.
  MEMORY:  Memory is allocated for the returned list and the clauses.
***************************************************************/
{
  LIST     result;
  int      i, lc;
  BOOL     hit;
  
#ifdef CHECK
  if (clause_HasTermSortConstraintLits(GivenClause) ||
      clause_HasSolvedConstraint(GivenClause)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In inf_ForwardEmptySortPlusPlus: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif
  
  result = list_Nil();
  lc     = clause_LastConstraintLitIndex(GivenClause);
  hit    = FALSE;
  
  for (i = clause_FirstLitIndex(); i <= lc && !hit; i++) {

    if (term_IsVariable(term_FirstArgument(clause_GetLiteralAtom(GivenClause,i)))) {
      LITERAL tLit;
      TERM    var;
      int     j, ls;
      BOOL varOccursNoMore;

      tLit            = clause_GetLiteral(GivenClause, i);
      var             = term_FirstArgument(clause_LiteralAtom(tLit));
      ls              = clause_LastSuccedentLitIndex(GivenClause);
      varOccursNoMore = TRUE;
      /* Check if the variable occurs in antecedent or succedent literals */
      for (j = clause_FirstAntecedentLitIndex(GivenClause); 
	   (j <= ls) && varOccursNoMore; j++) {
	if (term_ContainsSymbol(clause_GetLiteralAtom(GivenClause,j),
				term_TopSymbol(var)))
	  varOccursNoMore = FALSE;
      }
		
      if (varOccursNoMore) {
	/* Condition implies that constraint is unsolved */
	LIST unifiers;

	unifiers = inf_GetForwardPartnerLits(tLit, Index);
	hit      = TRUE;  /* We found the first appropriate constraint literal */

	if (!list_Empty(unifiers)) {
	  TERM tAtom = clause_LiteralAtom(tLit);
	  LIST tLits, sojuList;
	  SORT tSort, unifierSort;

	  /* Search the other T_k(t) in GivenClause */
	  tLits = list_Nil();
	  tSort = sort_TopSort();
	  for (j = lc; j > i; j--) {
	    TERM actAtom;

	    actAtom = clause_GetLiteralAtom(GivenClause, j);
	    if (term_FirstArgument(actAtom) == var) {   /* tClause is shared */
	      tLits = list_Cons((POINTER)j, tLits);
	      tSort = sort_Intersect(sort_TheorySortOfSymbol(SortTheory,
							     term_TopSymbol(actAtom)),
				     tSort);
	    }
	  }
	  tLits = list_Cons((POINTER)i, tLits);
	  tSort = sort_Intersect(sort_TheorySortOfSymbol(SortTheory,
							 term_TopSymbol(tAtom)),
				 tSort);
	  list_PointerDeleteDuplicates(tSort);

	  unifierSort = inf_GetSortFromLits(unifiers, SortTheory);
	  sojuList    = sort_TheoryComputeAllSubsortHits(SortTheory, unifierSort, tSort);

	  sort_Delete(unifierSort);
	  sort_Delete(tSort);

	  result =
	    list_Nconc(inf_InternWeakening(GivenClause, tLits, unifiers, NULL,
					   sojuList, Flags, Precedence),
		       result);

	  list_Delete(tLits);
	  list_Delete(unifiers);
	}
      }
    }
  }
  return result;
}

LIST inf_BackwardEmptySortPlusPlus(CLAUSE GivenClause, st_INDEX Index,
				   SORTTHEORY SortTheory, FLAGSTORE Flags,
				   PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause with solved sort constraint, an index of clauses,
           a sort theory, a flag store and a precedence.
  RETURNS: A list of clauses inferred from the GivenClause by
           the Empty Sort rule.
  MEMORY:  Memory is allocated for the list and the clauses.
***************************************************************/
{
  LIST     result;
  int      i, ls;

#ifdef CHECK
  if (!clause_HasSolvedConstraint(GivenClause)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In inf_BackwardEmptySortPlusPlus: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  result = list_Nil();  
  ls     = clause_LastSuccedentLitIndex(GivenClause);

  for (i = clause_FirstSuccedentLitIndex(GivenClause); i <= ls; i++) {
    LITERAL sLit;
    TERM    sAtom;

    sLit  = clause_GetLiteral(GivenClause, i);
    sAtom = clause_LiteralAtom(sLit);
    if (clause_LiteralGetFlag(sLit,STRICTMAXIMAL) && 
	clause_LiteralIsSort(sLit) &&
	(!term_IsVariable(term_FirstArgument(sAtom)) ||
	 clause_HasEmptyConstraint(GivenClause))) {
      LIST unifiers, partners;
      SORT unifierSort;

      unifiers = partners = list_Nil();
      inf_GetBackwardPartnerLits(sLit, Index, &partners, &unifiers, TRUE, Flags,
				 Precedence);
      unifiers = list_Cons(sLit, unifiers);
      /* <partners> holds monadic constraint literals */
      /* <unifiers> holds monadic, maximal succedent literals */

      unifierSort = inf_GetSortFromLits(unifiers, SortTheory);

      for ( ; !list_Empty(partners); partners = list_Pop(partners)) {
	LITERAL tLit;
	CLAUSE  tClause;
	TERM    tAtom;
	int     ti;
	int     li;
	TERM    var;
	BOOL    varOccursNoMore;
	int     j;

	tLit            = list_Car(partners);
	tClause         = clause_LiteralOwningClause(tLit);
	tAtom           = clause_LiteralAtom(tLit);
	ti              = clause_LiteralGetIndex(tLit);
	li              = clause_LastSuccedentLitIndex(tClause);
	var             = term_FirstArgument(tAtom);
	varOccursNoMore = TRUE;
	for (j = clause_FirstAntecedentLitIndex(tClause);
	     j <= li && varOccursNoMore;
	     j++) {
	  if (term_ContainsSymbol(clause_GetLiteralAtom(tClause,j),
				  term_TopSymbol(var)))
	    varOccursNoMore = FALSE;
	}
 
	if (varOccursNoMore) {
	  /* Condition implies that constraint is unsolved */
	  int  lc;
	  LIST tLits, sojuList;
	  SORT tSort;

	  lc  = clause_LastConstraintLitIndex(tClause);

	  /* Search the other T_k(t) in GivenClause */
	  tLits = list_Nil();
	  tSort = sort_TopSort();
	  for (j = lc; j >= clause_FirstLitIndex(); j--) {
	    TERM actAtom;
	    
	    actAtom = clause_GetLiteralAtom(tClause, j);
	    if (j != ti &&
		term_TopSymbol(term_FirstArgument(actAtom)) == term_TopSymbol(var)) {
	      tLits = list_Cons((POINTER)j, tLits);
	      tSort = sort_Intersect(sort_TheorySortOfSymbol(SortTheory, term_TopSymbol(actAtom)),
				     tSort);
	    }
	  }
	  tLits = list_Cons((POINTER)ti, tLits);
	  tSort = sort_Intersect(sort_TheorySortOfSymbol(SortTheory, term_TopSymbol(tAtom)),
				 tSort);
	  list_PointerDeleteDuplicates(tSort);

	  sojuList = sort_TheoryComputeAllSubsortHits(SortTheory, unifierSort, tSort);
	  sort_Delete(tSort);

	  cont_StartBinding();
	  unify_UnifyNoOC(cont_LeftContext(), tAtom,
			  cont_RightContext(), sAtom);

	  result =
	    list_Nconc(inf_InternWeakening(tClause, tLits, unifiers, sLit,
					   sojuList, Flags, Precedence),
		       result);

	  cont_BackTrack();

	  list_Delete(tLits);
	}
      }
      sort_Delete(unifierSort);
      list_Delete(unifiers);
    }
  }

  return result;
}
