/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                     SUBSTITUTION                       * */
/* *                                                        * */
/* *  $Module:      SUBSTITUTION                            * */ 
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

#include "subst.h"

/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  SUBSTITUTION CREATION AND DELETION                    * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/


SUBST subst_Add(SYMBOL Symbol, TERM Codomain, SUBST Subst)
{
  SUBST Result;

  Result           = subst_Get();
  Result->next     = Subst;
  Result->dom      = Symbol;
  Result->codomain = Codomain;

  return Result;
}


void subst_Delete(SUBST Subst)
{
  SUBST Next;

  while (subst_Exist(Subst)) {
    Next = subst_Next(Subst);

    if (subst_Cod(Subst))
      term_Delete(subst_Cod(Subst));

    subst_FreeOneNode(Subst);
    Subst = Next;
  }
}

void subst_Free(SUBST Subst)
{
  SUBST Next;

  while (subst_Exist(Subst)) {
    Next = subst_Next(Subst);
    subst_FreeOneNode(Subst);
    Subst = Next;
  }
}


/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  FUNCTIONS ON SUBSTITUTIONS                            * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/


TERM subst_Term(SYMBOL Symbol, SUBST Subst)
{
  for (; subst_Exist(Subst); Subst = subst_Next(Subst))
    if (symbol_Equal(Symbol,subst_Dom(Subst)))
      return subst_Cod(Subst);
  return (TERM)NULL;
}


static TERM subst_ApplyIntern(SUBST Subst, TERM Term)
{
  TERM   RplacTerm;
  LIST   Arglist;
  SYMBOL Top;

  Top = term_TopSymbol(Term);

  if (symbol_IsVariable(Top) && (RplacTerm = subst_Term(Top,Subst))) {
    Arglist = term_CopyTermList(term_ArgumentList(RplacTerm));
    term_RplacTop(Term, term_TopSymbol(RplacTerm));
    term_DeleteTermList(term_ArgumentList(Term));
    term_RplacArgumentList(Term, Arglist);
  } else {
    for (Arglist = term_ArgumentList(Term);
	 !list_Empty(Arglist);
	 Arglist = list_Cdr(Arglist))
      subst_ApplyIntern(Subst, list_Car(Arglist));
  }     

  return Term;
}

TERM subst_Apply(SUBST Subst, TERM Term)
{
  if (subst_Empty(Subst))
    return Term;

  return subst_ApplyIntern(Subst, Term);
}


SUBST subst_Merge(SUBST Source, SUBST Drain)
{
  SUBST Scan;
  BOOL  Changed;
  
  for (; subst_Exist(Source); Source = subst_Next(Source)) {
    
    /* Apply current assignment of Source to all  */
    /* assignments of Drain. If the current ass.  */
    /* cannot be applied to any codomain in Drain */
    /* the current assignment is added to Drain.  */
    
    Changed = FALSE;

    for (Scan = Drain;
	 subst_Exist(Scan);
	 Scan = subst_Next(Scan))
      if (term_SubstituteVariable(Source->dom,
				   Source->codomain,
				   &(Scan->codomain)))
	Changed = TRUE;

    if (!Changed)
      Drain = subst_Add(Source->dom, 
			term_Copy(Source->codomain),
			Drain);
  }

  return Drain;
}

SUBST subst_Compose(SUBST Outer, SUBST Inner)
/**************************************************************
  INPUT:   Two substitutions.
  RETURNS: The substitution corresponding to the composition of
           <Outer> and <Inner>.
  EFFECT:  <Outer> is destructively applied to the codomain of <Inner>
           <Inner> is destructively extended
***************************************************************/
{
  SUBST Scan1,Scan2,New;

  New = subst_Nil();
  
  for (Scan1=Outer; subst_Exist(Scan1); Scan1 = subst_Next(Scan1)) {    
    for (Scan2 = Inner;subst_Exist(Scan2);Scan2 = subst_Next(Scan2))
      term_SubstituteVariable(subst_Dom(Scan1),subst_Cod(Scan1),&(Scan2->codomain));
    if (!subst_BindVar(subst_Dom(Scan1),Inner))
      New = subst_Add(subst_Dom(Scan1), term_Copy(subst_Cod(Scan1)),New);
  }
  return subst_NUnion(Inner,New);
}

BOOL subst_BindVar(SYMBOL Var, SUBST Subst)
/**************************************************************
  INPUT:   A variable symbol and a substitution.
  RETURNS: TRUE iff <Var> is contained in the domain of <Subst>
***************************************************************/
{
  SUBST Scan;

  for (Scan=Subst; subst_Exist(Scan); Scan = subst_Next(Scan))
    if (symbol_Equal(subst_Dom(Scan),Var))
      return TRUE;

  return FALSE;
}



SUBST subst_Copy(SUBST Subst)
{
  SUBST Copy, Result;

  for (Result = subst_Nil(),
       Copy   = subst_Nil();
       subst_Exist(Subst);
       Subst = subst_Next(Subst))
    if (subst_Exist(Result)) {
      subst_SetNext(Copy, subst_Add(subst_Dom(Subst),
				    term_Copy(subst_Cod(Subst)),
				    subst_Nil()));
      Copy = subst_Next(Copy);
    } else {
      Result = subst_Add(subst_Dom(Subst),
			 term_Copy(subst_Cod(Subst)),
			 subst_Nil());
      Copy = Result;
    }

  return Result;
}


BOOL subst_MatchTops(const CONTEXT Context, SUBST Subst)
{
  for ( ; subst_Exist(Subst); Subst = subst_Next(Subst))
    if (cont_ContextBindingTerm(Context, subst_Dom(Subst)) &&
	term_EqualTopSymbols(cont_ContextBindingTerm(Context, subst_Dom(Subst)),
			     subst_Cod(Subst)))
      return TRUE;
  return FALSE;
}


/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  UNIFICATION TEST                                      * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/


BOOL subst_Unify(CONTEXT IndexContext, SUBST Subst)
/*********************************************************
  INPUT:
  RETURNS:
  CAUTION: 'Subst' IS ASSUMED TO BE NON-EMPTY.
**********************************************************/
{
  while (subst_Exist(Subst)) {
    if (!cont_VarIsBound(IndexContext, subst_Dom(Subst))) {
      if (unify_OccurCheck(IndexContext, subst_Dom(Subst), IndexContext, subst_Cod(Subst)))
	return FALSE;
      else
	cont_CreateBinding(IndexContext, subst_Dom(Subst), IndexContext, subst_Cod(Subst));
    } else if (!unify_UnifyAllOC(IndexContext,
				 IndexContext,
				 subst_Cod(Subst),
				 cont_ContextBindingContext(IndexContext,
							       subst_Dom(Subst)),
				 cont_ContextBindingTerm(IndexContext,
							    subst_Dom(Subst))))
      return FALSE;

    Subst = subst_Next(Subst);
  }

  return TRUE;
}

BOOL subst_IsShallow(SUBST Subst) {
/**********************************************************
  INPUT:   A unifier
  RETURNS: TRUE, if the unifier is valid :
           a variable or a ground term  or a function with only
           variables or ground terms as arguments.
***********************************************************/
    SUBST SubstScan;
    for (SubstScan = Subst; SubstScan != subst_Nil();
	 SubstScan = subst_Next(SubstScan)) {
	TERM Codomain = subst_Cod(SubstScan);
	if ((!term_IsVariable(Codomain)) 
	    && (!term_IsGround(Codomain))) {
	  LIST Scan ;
	  for (Scan = term_ArgumentList(Codomain); Scan != list_Nil(); 
	       Scan = list_Cdr(Scan)) {
	    if ((!term_IsVariable(list_Car(Scan))
		 && (!term_IsGround(list_Car(Scan)))))
	      return FALSE;
	  }
	}
    }
    return TRUE;
}

/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  GENERALIZATION TEST                                   * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/


BOOL subst_Match(const CONTEXT Context, SUBST Subst)
/*********************************************************
  INPUT:
  RETURNS:
  CAUTION: 'Subst' IS ASSUMED TO BE NON-EMPTY.
**********************************************************/
{
  while (subst_Exist(Subst)) {
    if (!cont_VarIsBound(Context, subst_Dom(Subst)) ||
	!unify_Match(Context,
		     subst_Cod(Subst),
		     cont_ContextBindingTerm(Context, subst_Dom(Subst))))
      return FALSE;
    
    Subst = subst_Next(Subst);
  }

  return TRUE;
}


/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  INSTANCE TEST                                         * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/


BOOL subst_MatchReverse(const CONTEXT IndexContext, SUBST Subst)
/*********************************************************
  INPUT:
  RETURNS:
  CAUTION: 'Subst' IS ASSUMED TO BE NON-EMPTY.
**********************************************************/
{
  while (subst_Exist(Subst)) {

    if (!cont_VarIsBound(IndexContext, subst_Dom(Subst))) {
      if (symbol_IsIndexVariable(subst_Dom(Subst)))
	cont_CreateBinding(IndexContext,
			      subst_Dom(Subst),
			      cont_InstanceContext(),
			      subst_Cod(Subst));
      else
	return FALSE;
    }
    else if (!unify_MatchReverse(IndexContext,
				 subst_Cod(Subst),
				 cont_ContextBindingContext(IndexContext, subst_Dom(Subst)),
				 cont_ContextBindingTerm(IndexContext, subst_Dom(Subst))))
      return FALSE;

    Subst = subst_Next(Subst);
  }

  return TRUE;
}


/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  VARIATION TEST                                        * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/


BOOL subst_Variation(const CONTEXT Context, SUBST Subst)
/*********************************************************
  INPUT:
  RETURNS:
  CAUTION: 'Subst' IS ASSUMED TO BE NON-EMPTY.
**********************************************************/
{
  while (subst_Exist(Subst)) {

    if (!cont_VarIsBound(Context, subst_Dom(Subst)) ||
	!unify_Variation(Context,
			 subst_Cod(Subst),
			 cont_ContextBindingTerm(Context, subst_Dom(Subst))))
      return FALSE;
    
    Subst = subst_Next(Subst);
  }

  return TRUE;
}


/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  COMMON GENERALIZATIONS                                * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/


SUBST subst_ComGen(const CONTEXT Context, SUBST Subst, SUBST* SubstOld,
		   SUBST* SubstNew)
/*********************************************************
  INPUT:
  RETURNS:
  CAUTION: 'Subst' IS ASSUMED TO BE NON-EMPTY.
**********************************************************/
{
  SUBST Result;
  
  Result = *SubstOld = *SubstNew = NULL;
  
  do {
    
    if (!cont_VarIsBound(Context, subst_Dom(Subst)))
      *SubstOld=subst_Add(subst_Dom(Subst), term_Copy(subst_Cod(Subst)), *SubstOld);

    else if (term_Equal(cont_ContextBindingTerm(Context, subst_Dom(Subst)),
			subst_Cod(Subst)))
      Result = subst_Add(subst_Dom(Subst), term_Copy(subst_Cod(Subst)), Result);

    else
      if (!symbol_Equal(term_TopSymbol(cont_ContextBindingTerm(Context,
								  subst_Dom(Subst))),
			term_TopSymbol(subst_Cod(Subst)))) {

      *SubstOld=subst_Add(subst_Dom(Subst),
			  term_Copy(subst_Cod(Subst)),
			  *SubstOld);
      *SubstNew=subst_Add(subst_Dom(Subst),
			  term_Copy(cont_ContextBindingTerm(Context,
							       subst_Dom(Subst))),
			  *SubstNew);

    } else
      Result = subst_Add(subst_Dom(Subst),
			 unify_ComGenLinear(Context,
					    SubstNew,
					    cont_ContextBindingTerm(Context,
								       subst_Dom(Subst)),
					    SubstOld,
					    subst_Cod(Subst)),
			 Result);

    cont_CloseBinding(Context, subst_Dom(Subst));

    Subst = subst_Next(Subst);
  } while (subst_Exist(Subst));

  return Result;
}


/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  CLOSE BINDINGS                                        * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/


void subst_CloseVariables(const CONTEXT Context, SUBST Subst)
{
  for (; subst_Exist(Subst); Subst = subst_Next(Subst))
    cont_CloseBinding(Context, subst_Dom(Subst));
}


SUBST subst_CloseOpenVariables(SUBST Result)
{
  while (cont_LastBinding()) {
    if (cont_LastIsBound())
      Result = subst_Add(cont_LastBindingSymbol(),
			 term_Copy(cont_LastBindingTerm()),
			 Result);
    cont_BackTrackLastBinding();
  }

  return Result;
}


/**************************************************************/
/* ********************************************************** */
/* *							    * */
/* *  EXTRACT UNIFIER                                       * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/


void subst_ExtractUnifier(const CONTEXT CL,
			  SUBST* LeftSubst,
			  const CONTEXT CR,
			  SUBST* RightSubst)
/*********************************************************
  INPUT:   'LeftSubst', 'RightSubst' for the unifier,
           renaming the codomain variables starts at
           'MinimumCoVariable' excl., number of
           renamings are ADDED to 'Bindings'.
  RETURNS: Nothing.
  SUMMARY: Extracts the unifier into two substitutions
           with renamed variables in the codomain.
  CAUTION: DOES NOT RESET THE BINDINGS, CREATES EVEN
           MORE BINDINGS BECAUSE OF RENAMING.
**********************************************************/
{
  CONTEXT Scan;

  *LeftSubst  = subst_Nil();
  *RightSubst = subst_Nil();

  Scan        = cont_LastBinding();

  while (Scan) {
    if (cont_IsInContext(CL,
			    cont_BindingSymbol(Scan),
			    Scan))
      *LeftSubst = subst_Add(cont_BindingSymbol(Scan),
			     cont_CopyAndApplyBindings(cont_BindingContext(Scan),
							  cont_BindingTerm(Scan)),
			     *LeftSubst);
    else if (cont_IsInContext(CR,
				 cont_BindingSymbol(Scan),
				 Scan))
      *RightSubst = subst_Add(cont_BindingSymbol(Scan),
			      cont_CopyAndApplyBindings(cont_BindingContext(Scan),
							   cont_BindingTerm(Scan)),
			      *RightSubst);
    
    Scan = cont_BindingLink(Scan);
  }
}


void subst_ExtractUnifierCom(const CONTEXT Context, SUBST* Subst)
/*********************************************************
  INPUT:  'LeftSubst', 'RightSubst' for the unifier,
          renaming the codomain variables starts at
          'MinimumCoVariable' excl., number of
          renamings are ADDED to 'Bindings'.
 RETURNS: Nothing.
 SUMMARY: Extracts the unifier into two substitutions
          with renamed variables in the codomain.
 CAUTION: DOES NOT RESET THE BINDINGS, CREATES EVEN
          MORE BINDINGS BECAUSE OF RENAMING.
**********************************************************/
{
  CONTEXT Scan;

  *Subst = subst_Nil();

  Scan   = cont_LastBinding();

  while (Scan) {
    *Subst =
      subst_Add(cont_BindingSymbol(Scan),
		cont_CopyAndApplyBindingsCom(Context, cont_BindingTerm(Scan)),
		*Subst);

    Scan = cont_BindingLink(Scan);
  }
}


/**************************************************************/
/* ********************************************************** */
/* *							    * */
/* *  EXTRACT MATCHER                                       * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/


SUBST subst_ExtractMatcher(void)
/*********************************************************
  INPUT:   None.
  RETURNS: The matcher.
  SUMMARY: Extracts the matcher without renaming.
  CAUTION: DOES NOT RESET THE BINDINGS, DOES NOT COPY
           THE CODOMAINS.
**********************************************************/
{
  CONTEXT     Scan;
  SUBST Result;

  for (Scan = cont_LastBinding(), Result = subst_Nil();
       Scan;
       Scan = cont_BindingLink(Scan))
    Result = subst_Add(cont_BindingSymbol(Scan),
		       cont_BindingTerm(Scan),
		       Result);

  return Result;
}


/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  OUTPUT                                                * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/


void subst_Print(SUBST Subst)
{
  fputs("{ ", stdout);
  for (; subst_Exist(Subst); Subst = subst_Next(Subst)) {
    symbol_Print(subst_Dom(Subst));
    if (subst_Cod(Subst)) {
      fputs(" -> ", stdout);
      term_PrintPrefix(subst_Cod(Subst));
    }
    if (subst_Next(Subst))
      fputs("; ", stdout);
  }
  fputs(" }", stdout);
}

