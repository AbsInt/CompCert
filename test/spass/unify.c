/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                STANDARD UNIFICATION                    * */
/* *                                                        * */
/* *  $Module:   UNIFY                                      * */ 
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

#include "unify.h"

/**************************************************************/
/* ********************************************************** */
/* *							    * */
/* *  INITIALIZATION           			            * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/


void unify_Init(void)
/**********************************************************
  INPUT:   None.
  RETURNS: None.
  EFFECT:  Initializes the unify module.
********************************************************/
{

}

void unify_Free(void)
/**********************************************************
  INPUT:   None.
  RETURNS: None.
  EFFECT:  Frees internal structures of the unify module.
********************************************************/
{

}


/**************************************************************/
/* ********************************************************** */
/* *							    * */
/* *  MISC FUNCTIONS                     	            * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/


/**************************************************************/
/* ********************************************************** */
/* *							    * */
/* *  OCCUR CHECK            			            * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/


BOOL unify_OccurCheckCom(SYMBOL Top, CONTEXT Context, TERM Term)
/**********************************************************
  INPUT:   A variable symbol, a context, and a term.
  RETURNS: TRUE if there is a occur check failure with respect
           to the variable symbol <Top> and <Term>.
	   The search is started in <Term>
***********************************************************/
{
  int  Bottom;
  LIST Args;

  Bottom = stack_Bottom();

  for (;;) {

    if (term_IsVariable(Term)) {
      if (symbol_Equal(Top, term_TopSymbol(Term))) {
	stack_SetBottom(Bottom);
	return TRUE;
      } else if (cont_VarIsBound(Context, term_TopSymbol(Term))) {
	Term = cont_ContextBindingTerm(Context, term_TopSymbol(Term));
	continue;
      }

    } else if (term_IsComplex(Term)) {

      Args = term_ArgumentList(Term);
      if (!list_Empty(list_Cdr(Args)))
	stack_Push(list_Cdr(Args));

      Term = list_Car(Args);
      continue;
    }

    if (stack_Empty(Bottom))
      return FALSE;
    else {
      Args = (LIST)stack_PopResult();
      Term = list_Car(Args);
      if (!list_Empty(list_Cdr(Args)))
	stack_Push(list_Cdr(Args));
    }
  }
}


BOOL unify_OccurCheck(CONTEXT CTop, SYMBOL Top, CONTEXT CTerm, TERM Term)
/**********************************************************
  INPUT:   A context, a variable symbol, a context, and a term.
  RETURNS: TRUE if there is a occur check failure with respect
           to the variable symbol <Top> and <Term>.
	   The search is started in <Term>
***********************************************************/
{
  int    Bottom;
  LIST   Args;
  SYMBOL TermTop;

  Bottom = stack_Bottom();

  for (;;) {

    if (term_IsVariable(Term)) {

      TermTop = term_TopSymbol(Term);

      if ((CTop == CTerm) && (symbol_Equal(Top, TermTop))) {
	stack_SetBottom(Bottom);
	return TRUE;
      } else if (cont_VarIsBound(CTerm, TermTop)) {
	Term  = cont_ContextBindingTerm(CTerm, TermTop);
	CTerm = cont_ContextBindingContext(CTerm, TermTop);
	continue;
      }
    } else if (term_IsComplex(Term)) {

      Args = term_ArgumentList(Term);
      if (!list_Empty(list_Cdr(Args))) {
	stack_Push(CTerm);
	stack_Push(list_Cdr(Args));
      }
      Term = list_Car(Args);
      continue;

    }

    if (stack_Empty(Bottom))
      return FALSE;
    else {
      Args = (LIST)stack_PopResult();
      Term = list_Car(Args);
      CTerm = (CONTEXT)stack_Top();
      if (list_Empty(list_Cdr(Args)))
	stack_Pop();
      else
	stack_Push(list_Cdr(Args));
    }
  }
}


/**************************************************************/
/* ********************************************************** */
/* *							    * */
/* *  UNIFICATION           			            * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/


BOOL unify_Unify(CONTEXT CtL, TERM TermL, CONTEXT CtR, TERM TermR)
/**********************************************************
  INPUT:   Two terms which may contain the same variable symbols.
           Equal variable symbols are interpreted different in
	   <TermL> and <TermR>, respectively.
  RETURNS: TRUE, if <TermL> and <TermR> are unifiable, FALSE otherwise.
  CAUTION: None.
***********************************************************/
{
  CONTEXT CHelp;
  LIST    ArgsL, ArgsR;
  int     Bottom;
  BOOL    Bound;

  Bound  = FALSE;
  Bottom = stack_Bottom();

  for (;;) {

    while (term_IsVariable(TermL) &&
	   cont_VarIsBound(CtL, term_TopSymbol(TermL))) {
      CHelp = cont_ContextBindingContext(CtL, term_TopSymbol(TermL));
      TermL = cont_ContextBindingTerm(CtL, term_TopSymbol(TermL));
      CtL   = CHelp;
    }

    while (term_IsVariable(TermR) &&
	   cont_VarIsBound(CtR, term_TopSymbol(TermR))) {
      CHelp = cont_ContextBindingContext(CtR, term_TopSymbol(TermR));
      TermR = cont_ContextBindingTerm(CtR, term_TopSymbol(TermR));
      CtR   = CHelp;
    }

    /* Caution: Bindings from variable to variable are made with priority
       from the right context into the left context. */

    if (term_IsVariable(TermL)) {
      if (term_IsVariable(TermR)) {
	if (!(CtL == CtR && term_EqualTopSymbols(TermL, TermR)))
	  Bound = cont_CreateBinding(CtR, term_TopSymbol(TermR), CtL, TermL);
      } else if (Bound && unify_OccurCheck(CtL, term_TopSymbol(TermL), CtR, TermR)) {
	stack_SetBottom(Bottom);
	return FALSE;
      }	else
	Bound = cont_CreateBinding(CtL, term_TopSymbol(TermL), CtR, TermR);

    } else if (term_IsVariable(TermR)) {
      if (Bound && unify_OccurCheck(CtR, term_TopSymbol(TermR), CtL, TermL)) {
	stack_SetBottom(Bottom);
	return FALSE;
      }	else
	Bound = cont_CreateBinding(CtR, term_TopSymbol(TermR), CtL, TermL);

    } else if (term_EqualTopSymbols(TermL, TermR)) {
      if (term_IsComplex(TermL) && TermL != TermR) {
	ArgsL = term_ArgumentList(TermL);
	ArgsR = term_ArgumentList(TermR);
	if (!list_Empty(list_Cdr(ArgsL))) {
	  stack_Push(CtL);
	  stack_Push(CtR);
	  stack_Push(list_Cdr(ArgsL));
	  stack_Push(list_Cdr(ArgsR));
	}
	TermL = list_Car(ArgsL);
	TermR = list_Car(ArgsR);
	continue;
      }
    } else {
      stack_SetBottom(Bottom);
      return FALSE;
    }

    if (stack_Empty(Bottom))
      return TRUE;
    else {
      ArgsR = stack_PopResult();
      ArgsL = stack_PopResult();
      TermR = list_Car(ArgsR);
      TermL = list_Car(ArgsL);
      CtR   = (CONTEXT)stack_Top();
      CtL   = (CONTEXT)stack_NthTop(1);
      if (list_Empty(list_Cdr(ArgsL)))
	stack_NPop(2);
      else {
	stack_Push(list_Cdr(ArgsL));
	stack_Push(list_Cdr(ArgsR));
      }
    }
  }
}

BOOL unify_UnifyCom(CONTEXT Context, TERM TermL, TERM TermR)
/**********************************************************
  INPUT:   Two terms which may contain the same variable symbols.
           Equal variable symbols are interpreted equally in
	   <TermL> and <TermR>, respectively.
  RETURNS: TRUE, if <TermL> and <TermR> are unifiable, FALSE otherwise.
  CAUTION: None.
***********************************************************/
{
  LIST ArgsL, ArgsR;
  int  Bottom;

  Bottom = stack_Bottom();

  for (;;) {

    while (term_IsVariable(TermL) &&
	   cont_VarIsBound(Context, term_TopSymbol(TermL)))
      TermL = cont_ContextBindingTerm(Context, term_TopSymbol(TermL));

    while (term_IsVariable(TermR) &&
	   cont_VarIsBound(Context, term_TopSymbol(TermR)))
      TermR = cont_ContextBindingTerm(Context, term_TopSymbol(TermR));

    if (term_EqualTopSymbols(TermL, TermR)) {
      if (term_IsComplex(TermL) && TermL != TermR) {
	ArgsL = term_ArgumentList(TermL);
	ArgsR = term_ArgumentList(TermR);
	if (!list_Empty(list_Cdr(ArgsL))) {
	  stack_Push(list_Cdr(ArgsL));
	  stack_Push(list_Cdr(ArgsR));
	}
	TermL = list_Car(ArgsL);
	TermR = list_Car(ArgsR);
	continue;
      }
    } else if (term_IsVariable(TermL)) {
      if (term_IsVariable(TermR))
	cont_CreateBinding(Context, term_TopSymbol(TermL), Context, TermR);
      else if (unify_OccurCheckCom(term_TopSymbol(TermL), Context, TermR)) {
	stack_SetBottom(Bottom);
	return FALSE;
      } else
	cont_CreateBinding(Context, term_TopSymbol(TermL), Context, TermR);
      
    } else if (term_IsVariable(TermR)) {
      if (unify_OccurCheckCom(term_TopSymbol(TermR), Context, TermL)) {
	stack_SetBottom(Bottom);
	return FALSE;
      }	else
	cont_CreateBinding(Context, term_TopSymbol(TermR), Context, TermL);

    } else {
      stack_SetBottom(Bottom);
      return FALSE;
    }

    if (stack_Empty(Bottom))
      return TRUE;
    else {
      ArgsR = stack_PopResult();
      ArgsL = stack_PopResult();
      TermR = list_Car(ArgsR);
      TermL = list_Car(ArgsL);
      if (!list_Empty(list_Cdr(ArgsL))) {
	stack_Push(list_Cdr(ArgsL));
	stack_Push(list_Cdr(ArgsR));
      }
    }
  }
}



BOOL unify_UnifyNoOC(CONTEXT CtL, TERM TermL, CONTEXT CtR, TERM TermR)
/**********************************************************
  INPUT:   Two terms which may contain the same variable symbols.
           Equal variable symbols are interpreted different in
	   <TermL> and <TermR>, respectively.
  RETURNS: TRUE, if <TermL> and <TermR> are unifiable, FALSE otherwise.
  CAUTION: None.
***********************************************************/
{
  CONTEXT CHelp;
  LIST    ArgsL, ArgsR;
  int     Bottom;

  Bottom = stack_Bottom();

  for (;;) {

    while (term_IsVariable(TermL) &&
	   cont_VarIsBound(CtL, term_TopSymbol(TermL))) {
      CHelp = cont_ContextBindingContext(CtL, term_TopSymbol(TermL));
      TermL = cont_ContextBindingTerm(CtL, term_TopSymbol(TermL));
      CtL   = CHelp;
    }

    while (term_IsVariable(TermR) &&
	   cont_VarIsBound(CtR, term_TopSymbol(TermR))) {
      CHelp = cont_ContextBindingContext(CtR, term_TopSymbol(TermR));
      TermR = cont_ContextBindingTerm(CtR, term_TopSymbol(TermR));
      CtR   = CHelp;
    }

    /* Caution: Bindings from variable to variable are made with priority
       from the right context into the left context. */

    if (term_IsVariable(TermL)) {
      if (term_IsVariable(TermR)) {
	if (!(CtL == CtR && term_EqualTopSymbols(TermL, TermR)))
	  cont_CreateBinding(CtR, term_TopSymbol(TermR), CtL, TermL);
      } else 
	cont_CreateBinding(CtL, term_TopSymbol(TermL), CtR, TermR);

    } else if (term_IsVariable(TermR))
      cont_CreateBinding(CtR, term_TopSymbol(TermR), CtL, TermL);

    else if (term_EqualTopSymbols(TermL, TermR)) {
      if (term_IsComplex(TermL) && TermL != TermR) {
	ArgsL = term_ArgumentList(TermL);
	ArgsR = term_ArgumentList(TermR);
	if (!list_Empty(list_Cdr(ArgsL))) {
	  stack_Push(CtL);
	  stack_Push(CtR);
	  stack_Push(list_Cdr(ArgsL));
	  stack_Push(list_Cdr(ArgsR));
	}
	TermL = list_Car(ArgsL);
	TermR = list_Car(ArgsR);
	continue;
      }
    } else {
      stack_SetBottom(Bottom);
      return FALSE;
    }

    if (stack_Empty(Bottom))
      return TRUE;
    else {
      ArgsR = stack_PopResult();
      ArgsL = stack_PopResult();
      TermR = list_Car(ArgsR);
      TermL = list_Car(ArgsL);
      CtR   = (CONTEXT) stack_Top();
      CtL   = (CONTEXT) stack_NthTop(1);
      if (list_Empty(list_Cdr(ArgsL)))
	stack_NPop(2);
      else {
	stack_Push(list_Cdr(ArgsL));
	stack_Push(list_Cdr(ArgsR));
      }
    }
  }
}


/**************************************************************/
/* ********************************************************** */
/* *							    * */
/* *  UNIFICATION WITH FULL OCCUR CHECK	(recursive)         * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/


BOOL unify_UnifyAllOC(CONTEXT IndexContext, CONTEXT CtL, TERM TermL, CONTEXT CtR, TERM TermR)
{
  while (term_IsVariable(TermL)) {
    SYMBOL TermTop;

    TermTop = term_TopSymbol(TermL);

    if (cont_VarIsBound(CtL, TermTop)) {
      CONTEXT CHelp;

      CHelp = cont_ContextBindingContext(CtL, TermTop);
      TermL = cont_ContextBindingTerm(CtL, TermTop);
      CtL   = CHelp;
    } else
      break;
  }

  while (term_IsVariable(TermR)) {
    SYMBOL TermTop;

    TermTop = term_TopSymbol(TermR);

    if (cont_VarIsBound(CtR, TermTop)) {
      CONTEXT CHelp;

      CHelp = cont_ContextBindingContext(CtR, TermTop);
      TermR = cont_ContextBindingTerm(CtR, TermTop);
      CtR   = CHelp;
    } else
      break;
  }
  
  if (term_IsVariable(TermL)) {
    
    if (term_IsVariable(TermR)) {
      if ((CtL != CtR || !term_EqualTopSymbols(TermL, TermR))) {
	if (term_IsIndexVariable(TermL))
	  cont_CreateBinding(CtL, term_TopSymbol(TermL), CtR, TermR);
	else 
	  if (term_IsIndexVariable(TermR) || (CtR == IndexContext))
	    cont_CreateBinding(CtR, term_TopSymbol(TermR), CtL, TermL);
	  else
	    cont_CreateBinding(CtL, term_TopSymbol(TermL), CtR, TermR);
      }
      return TRUE;
    } 
    else 
      if (unify_OccurCheck(CtL, term_TopSymbol(TermL), CtR, TermR))
	return FALSE;
      else {
	cont_CreateBinding(CtL, term_TopSymbol(TermL), CtR, TermR);
	return TRUE;
      }
  } 
  else 
    if (term_IsVariable(TermR)) { 
      if (unify_OccurCheck(CtR, term_TopSymbol(TermR), CtL, TermL))
	return FALSE;
      else {
	cont_CreateBinding(CtR, term_TopSymbol(TermR), CtL, TermL);
	return TRUE;
      }
    } 
    else 
      if (term_EqualTopSymbols(TermL, TermR)) {
	if (term_IsComplex(TermL)) {
	  LIST ArgL, ArgR;
	  for (ArgL = term_ArgumentList(TermL), ArgR = term_ArgumentList(TermR);
	       !list_Empty(ArgL);
	       ArgL = list_Cdr(ArgL), ArgR = list_Cdr(ArgR))
	    if (!unify_UnifyAllOC(IndexContext, CtL, list_Car(ArgL), CtR, list_Car(ArgR)))
	      return FALSE;
	}
	return TRUE;
      } 
      else
	return FALSE;
}


/**************************************************************/
/* ********************************************************** */
/* *							    * */
/* *  GENERALIZATION TEST      			            * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/


BOOL unify_Match(CONTEXT Context, TERM TermL, TERM TermR)
{
  if (term_IsVariable(TermL)) {
    if (cont_VarIsBound(Context, term_TopSymbol(TermL)))
      return term_Equal(cont_ContextBindingTerm(Context, term_TopSymbol(TermL)), TermR);
    else {
      cont_CreateBinding(Context, term_TopSymbol(TermL), cont_InstanceContext(), TermR);
      return TRUE;
    }
  } else if (term_EqualTopSymbols(TermL, TermR)) {
    if (term_IsComplex(TermL)) {
      LIST ArgL;
      LIST ArgR;
      for (ArgL = term_ArgumentList(TermL), ArgR = term_ArgumentList(TermR);
	   !list_Empty(ArgL);
	   ArgL = list_Cdr(ArgL), ArgR = list_Cdr(ArgR))
	if (!unify_Match(Context, list_Car(ArgL), list_Car(ArgR)))
	  return FALSE;
    }
    return TRUE;
  } else
    return FALSE;
}

BOOL unify_MatchFlexible(CONTEXT Context, TERM TermL, TERM TermR)
/**************************************************************
  INPUT:   Two terms where symbols with flexible arity are allowed.
  RETURNS: TRUE if <TermL> matches <TermR>.        
***************************************************************/
{
  if (term_IsVariable(TermL)) {
    if (cont_VarIsBound(Context, term_TopSymbol(TermL)))
      return term_Equal(cont_ContextBindingTerm(Context, term_TopSymbol(TermL)), TermR);
    else {
      cont_CreateBinding(Context, term_TopSymbol(TermL), cont_InstanceContext(), TermR);
      return TRUE;
    }
  } else 
    if (term_EqualTopSymbols(TermL, TermR) 
	&& list_Length(term_ArgumentList(TermL)) == list_Length(term_ArgumentList(TermR))) {
      if (term_IsComplex(TermL)) {
	LIST ArgL;
	LIST ArgR;
	for (ArgL = term_ArgumentList(TermL), ArgR = term_ArgumentList(TermR);
	     !list_Empty(ArgL);
	     ArgL = list_Cdr(ArgL), ArgR = list_Cdr(ArgR))
	  if (!unify_MatchFlexible(Context, list_Car(ArgL), list_Car(ArgR)))
	    return FALSE;
      }
      return TRUE;
    } 
    else
      return FALSE;
}


void unify_EstablishMatcher(CONTEXT Context, SUBST Subst)
{
  while (subst_Exist(Subst)) {
    /* Index to query */
    cont_CreateBinding(Context, subst_Dom(Subst), cont_InstanceContext(), subst_Cod(Subst));
    Subst = subst_Next(Subst);
  }
}


BOOL unify_MatchBindingsHelp(const CONTEXT IndexContext, TERM TermL, CONTEXT CtR, TERM TermR)
{
  while (term_IsVariable(TermR)) {
    SYMBOL TermTop;

    TermTop = term_TopSymbol(TermR);

    if (symbol_IsIndexVariable(TermTop))
      CtR = IndexContext;
    else if (CtR == cont_InstanceContext())
      break;

    if (cont_VarIsBound(CtR, TermTop)) {
      CONTEXT CHelp;

      CHelp = cont_ContextBindingContext(CtR, TermTop);
      TermR = cont_ContextBindingTerm(CtR, TermTop);
      CtR   = CHelp;
    } else
      break;
  }

  if (term_IsVariable(TermL)) {
    /* Assertion: Variables of 'TermL' are bound in the index context only. */

    if (cont_VarIsBound(IndexContext, term_TopSymbol(TermL)))
      return
	cont_TermEqualModuloBindings(IndexContext,
					cont_ContextBindingContext(IndexContext,
								      term_TopSymbol(TermL)),
					cont_ContextBindingTerm(IndexContext,
								   term_TopSymbol(TermL)),
					CtR,
					TermR);
    else {
      cont_CreateBinding(IndexContext, term_TopSymbol(TermL), CtR, TermR);
      return TRUE;
    }
  } else if (term_EqualTopSymbols(TermL, TermR)) {
    if (term_IsComplex(TermL)) {
      LIST ArgL;
      LIST ArgR;

      for (ArgL = term_ArgumentList(TermL), ArgR = term_ArgumentList(TermR);
	   !list_Empty(ArgL);
	   ArgL = list_Cdr(ArgL), ArgR = list_Cdr(ArgR))
	if (!unify_MatchBindingsHelp(IndexContext, list_Car(ArgL), CtR, list_Car(ArgR)))
	  return FALSE;
    }

    return TRUE;
  } else
    return FALSE;
}


BOOL unify_MatchBindings(const CONTEXT IndexContext, TERM TermL, TERM TermR)
{
  return unify_MatchBindingsHelp(IndexContext, TermL, cont_InstanceContext(), TermR);
}


/**************************************************************/
/* ********************************************************** */
/* *							    * */
/* *  INSTANCE TEST      			            * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/


BOOL unify_MatchReverse(const CONTEXT IndexContext, TERM TermL,	CONTEXT CtR, 
			TERM TermR)
/*********************************************************
  INPUT:   'TermL' is in IndexContext and the codomain of a subst.,
           'CtR' is the context of 'TermR' which is the codomain of a subst.
           obtained by a variable binding, 'Bindings' is
           the number of established bindings.
  RETURNS: TRUE, if 'TermL' is an instance of 'TermR';
           FALSE, otherwise.
**********************************************************/
{
  while (term_IsVariable(TermR)) {
    SYMBOL TermTop;

    TermTop = term_TopSymbol(TermR);

    if (symbol_IsIndexVariable(TermTop))
      CtR = IndexContext;
    else if (CtR == cont_InstanceContext())
      break;

    if (cont_VarIsBound(CtR, TermTop)) {
      CONTEXT CHelp;

      CHelp = cont_ContextBindingContext(CtR, TermTop);
      TermR = cont_ContextBindingTerm(CtR, TermTop);
      CtR   = CHelp;
    } else
      break;
  }

  if (term_IsVariable(TermL)) {
    if ((CtR == cont_InstanceContext()) && term_EqualTopSymbols(TermL, TermR))
      /* 'TermL' and 'TermR' are exactly the same variables (via bindings),
	 therefore do not bind them, just return positive. */
      return TRUE;

    else if (term_IsIndexVariable(TermL)) {
      cont_CreateBinding(IndexContext, term_TopSymbol(TermL), CtR, TermR);
      return TRUE;

    } else if (term_IsVariable(TermR) &&
	       (term_IsIndexVariable(TermR) || (CtR == IndexContext))) {
      cont_CreateBinding(IndexContext, term_TopSymbol(TermR), cont_InstanceContext(), TermL);
      return TRUE;

    } else
      return FALSE;

  } else if (term_IsVariable(TermR)) {
    if (term_IsIndexVariable(TermR) || (CtR == IndexContext)) {
      cont_CreateBinding(IndexContext, term_TopSymbol(TermR), cont_InstanceContext(), TermL);
      return TRUE;
    } else
      return FALSE;

  } else if (term_EqualTopSymbols(TermL, TermR)) {
    
    if (term_IsComplex(TermL)) {
      LIST ArgL, ArgR;
      for (ArgL = term_ArgumentList(TermL), ArgR = term_ArgumentList(TermR);
	   !list_Empty(ArgL);
	   ArgL = list_Cdr(ArgL), ArgR = list_Cdr(ArgR))
	if (!unify_MatchReverse(IndexContext,
				list_Car(ArgL),
				CtR,
				list_Car(ArgR)))
	  return FALSE;
    }
    return TRUE;
  } else
    return FALSE;
}


/**************************************************************/
/* ********************************************************** */
/* *							    * */
/* *  VARIATION TEST      			            * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/


BOOL unify_Variation(const CONTEXT Context, TERM TermL, TERM TermR)
{
  if (term_IsVariable(TermL)) {
    if (term_EqualTopSymbols(TermL, TermR))
      /* TermL and TermR are in different contexts
	 but both are term variables which do not need to be variated.
	 Index variables cannot occur in TermR
	 which is the term to be inserted. */
      return TRUE;
    else if (term_IsIndexVariable(TermL)) {
      if (cont_VarIsBound(Context, term_TopSymbol(TermL)))
	return term_Equal(cont_ContextBindingTerm(Context, term_TopSymbol(TermL)), TermR);
      else {
	/* Index to query */
	cont_CreateBinding(Context, term_TopSymbol(TermL), Context, TermR);
	return TRUE;
      }
    }
    else
      return FALSE;

  } else if (term_EqualTopSymbols(TermL, TermR)) {
    if (term_IsComplex(TermL)) {
      LIST ArgL;
      LIST ArgR;
      for (ArgL = term_ArgumentList(TermL), ArgR = term_ArgumentList(TermR);
	   !list_Empty(ArgL);
	   ArgL = list_Cdr(ArgL), ArgR = list_Cdr(ArgR))
	if (!unify_Variation(Context, list_Car(ArgL), list_Car(ArgR)))
	  return FALSE;
    }
    return TRUE;
  } else 
    return FALSE;
}


/**************************************************************/
/* ********************************************************** */
/* *							    * */
/* *  COMMON GENERALIZATIONS   			            * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/


TERM unify_ComGenLinear(const CONTEXT IndexContext,
			SUBST* SubstL, TERM TermL, SUBST* SubstR, TERM TermR)
{
  if (term_IsIndexVariable(TermR)) {
    *SubstL = subst_Add(term_TopSymbol(TermR), term_Copy(TermL), *SubstL);

    return term_Copy(TermR);
  
  } else if (term_EqualTopSymbols(TermL, TermR)) {
   
    LIST ArgList, ArgL, ArgR;

    ArgList   = list_Nil();
    for (ArgL = term_ArgumentList(TermL), ArgR = term_ArgumentList(TermR);
	 !list_Empty(ArgL);
	 ArgL = list_Cdr(ArgL), ArgR = list_Cdr(ArgR))
      ArgList = list_Nconc(ArgList,
			   list_List(unify_ComGenLinear(IndexContext,
							SubstL,
							list_Car(ArgL),
							SubstR,
							list_Car(ArgR))));
    return term_Create(term_TopSymbol(TermL), ArgList);
    
  } else {
    
    SYMBOL Symbol;
    
    Symbol  = cont_NextIndexVariable(IndexContext);

    *SubstL = subst_Add(Symbol, term_Copy(TermL), *SubstL);
    *SubstR = subst_Add(Symbol, term_Copy(TermR), *SubstR);
    
    return term_Create(Symbol, list_Nil());
  }
}

