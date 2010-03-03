/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                CONTEXTS FOR VARIABLES                  * */
/* *                                                        * */
/* *  $Module:   CONTEXT                                    * */ 
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

#include "context.h"

/**************************************************************/
/* Global Variables                                           */
/**************************************************************/

int     cont_NOOFCONTEXTS;
LIST    cont_LISTOFCONTEXTS;
int     cont_BINDINGS;

SYMBOL  cont_INDEXVARSCANNER;

CONTEXT cont_LASTBINDING;     /* The last binding made. */
CONTEXT cont_CURRENTBINDING;  /* Help variable. */

CONTEXT cont_LEFTCONTEXT;
CONTEXT cont_RIGHTCONTEXT;
CONTEXT cont_INSTANCECONTEXT;

cont_STACK_TYPE cont_STACK;
int             cont_STACKPOINTER;

cont_CHECKSTACK_TYPE cont_CHECKSTACK;
int                  cont_CHECKSTACKPOINTER;

CONTEXT cont_STATELASTBINDING; /* Storage to save state of trails. */
int     cont_STATEBINDINGS;    /* Storage to save number of current bindings. */
int     cont_STATESTACK;       /* Storage to save state of stack. */
int     cont_STATETOPSTACK;    /* Storage to save state of the top element of the stack. */


/**************************************************************/
/* ********************************************************** */
/* *							    * */
/* *  INITIALIZATION           			            * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/


void cont_Init(void)
/**********************************************************
  INPUT:   None.
  RETURNS: None.
  EFFECT:  Initializes the unify module.
********************************************************/
{
  cont_LASTBINDING     = (CONTEXT)NULL;

  cont_ResetIndexVarScanner();

  cont_NOOFCONTEXTS    = 0;
  cont_LISTOFCONTEXTS  = list_Nil();
  cont_BINDINGS        = 0;

  cont_INSTANCECONTEXT = (CONTEXT)memory_Malloc(sizeof(CONTEXT_NODE));

  cont_LEFTCONTEXT     = cont_Create();
  cont_RIGHTCONTEXT    = cont_Create();

  cont_StackInit();
  cont_StackPush(0);
  cont_StackPop();
}


void cont_Check(void)
/**********************************************************
  INPUT:   None.
  RETURNS: None.
  EFFECT:  Frees internal structures of the unify module.
********************************************************/
{
#ifdef CHECK
  if (cont_LASTBINDING || (cont_BINDINGS != 0) ||
      !symbol_Equal(cont_INDEXVARSCANNER,
		    symbol_GetInitialIndexVarCounter())) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cont_Check: There are variable bindings not reset.\n");
    misc_FinishErrorReport();
  }
#endif
}


void cont_Free(void)
/**********************************************************
  INPUT:   None.
  RETURNS: None.
  EFFECT:  Frees internal structures of the unify module.
********************************************************/
{
  cont_Check();

  while (cont_NOOFCONTEXTS > 0)
    cont_Delete(list_Car(cont_LISTOFCONTEXTS)); /* Decreases NOOFCONTEXTS */

  cont_BINDINGS = 0;

  memory_Free(cont_INSTANCECONTEXT, sizeof(CONTEXT_NODE));
}


/**************************************************************/
/* ********************************************************** */
/* *							    * */
/* *  TERM EQUALITY WITH RESPECT TO BOUND VARIABLES         * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/


BOOL cont_TermEqual(CONTEXT Context1, TERM Term1, CONTEXT Context2, TERM Term2)
/*********************************************************
  INPUT:   Two terms and two contexts.
  RETURNS: TRUE iff the two terms are equal, where
           variables are interpreted with respect to
	   the bindings in the contexts.
********************************************************/
{
#ifdef CHECK
  if (!(term_IsTerm(Term1) && term_IsTerm(Term2))) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cont_TermEqual: Input terms are corrupted.\n");
    misc_FinishErrorReport();
  }
#endif

  Term1 = cont_Deref(&Context1,Term1);
  Term2 = cont_Deref(&Context2,Term2);

  if (!term_EqualTopSymbols(Term1, Term2))
    return FALSE;
  else if (term_ArgumentList(Term1)) {
    LIST Scan1, Scan2;
    for (Scan1=term_ArgumentList(Term1), Scan2=term_ArgumentList(Term2);
	 list_Exist(Scan1) && list_Exist(Scan2);
	 Scan1=list_Cdr(Scan1), Scan2=list_Cdr(Scan2))
      if (!cont_TermEqual(Context1,list_Car(Scan1), Context2,list_Car(Scan2)))
	return FALSE;
    return (list_Empty(Scan1) ? list_Empty(Scan2) : FALSE);
  } else
    return TRUE;
}


BOOL cont_TermEqualModuloBindings(CONTEXT IndexContext, CONTEXT CtL, TERM TermL,
				  CONTEXT CtR, TERM TermR)
/*********************************************************
  INPUT:   Two contexts, two terms.
  RETURNS: The boolean value TRUE if the terms are equal.
  CAUTION: EQUAL FUNCTION- OR PREDICATE SYMBOLS SHARE THE
           SAME ARITY. THIS IS NOT VALID FOR JUNCTORS!
*******************************************************/
{   
#ifdef CHECK
  if (!(term_IsTerm(TermL) && term_IsTerm(TermR))) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cont_TermEqualModuloBindings: Input terms are corrupted.\n");
    misc_FinishErrorReport();
  }
#endif

  while (term_IsVariable(TermL)) {
    SYMBOL TermTop;

    TermTop = term_TopSymbol(TermL);

    if (symbol_IsIndexVariable(TermTop))
      CtL = IndexContext;
    else if (CtL == cont_InstanceContext())
      break;

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

  if (!term_EqualTopSymbols(TermL, TermR))
    return FALSE;
  else 
    if (term_IsVariable(TermL)) {
      if (CtL == CtR)
	return TRUE;
      else
	return FALSE;
    }
    else 
      if (term_IsComplex(TermL)) {
	LIST ScanL, ScanR;
	
	for (ScanL=term_ArgumentList(TermL), ScanR=term_ArgumentList(TermR);
	     list_Exist(ScanL) && list_Exist(ScanR);
	     ScanL=list_Cdr(ScanL), ScanR=list_Cdr(ScanR))
	  if (!cont_TermEqualModuloBindings(IndexContext, CtL, list_Car(ScanL),
					    CtR, list_Car(ScanR)))
	    return FALSE;
	
	return (list_Empty(ScanL) ? list_Empty(ScanR) : FALSE);
	
      } 
      else
	return TRUE;
}


/**************************************************************/
/* ********************************************************** */
/* *							    * */
/* *  APPLY BINDINGS                                        * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/


TERM cont_CopyAndApplyBindings(CONTEXT TermContext, TERM Term)
{
  while (term_IsVariable(Term)) {
    SYMBOL TermTop;

    TermTop = term_TopSymbol(Term);

    if (cont_VarIsBound(TermContext, TermTop)) {
      CONTEXT HelpContext;

      HelpContext = cont_ContextBindingContext(TermContext, TermTop);
      Term        = cont_ContextBindingTerm(TermContext, TermTop);
      TermContext = HelpContext;
    } else
      break;
  }

  if (term_IsComplex(Term)) {
    LIST Scan, ArgumentList;
    for (Scan = ArgumentList = list_Copy(term_ArgumentList(Term));
	 !list_Empty(Scan);
	 Scan = list_Cdr(Scan))
      list_Rplaca(Scan, cont_CopyAndApplyBindings(TermContext, list_Car(Scan)));
    return term_Create(term_TopSymbol(Term), ArgumentList);
  } else 
    return term_Create(term_TopSymbol(Term), list_Nil());
}


TERM cont_CopyAndApplyBindingsCom(const CONTEXT Context, TERM Term)
{
  while (term_IsVariable(Term) && cont_VarIsBound(Context, term_TopSymbol(Term)))
    Term = cont_ContextBindingTerm(Context, term_TopSymbol(Term));

  if (term_IsComplex(Term)) {
    LIST Scan, ArgumentList;
    for (Scan = ArgumentList = list_Copy(term_ArgumentList(Term));
	 !list_Empty(Scan);
	 Scan = list_Cdr(Scan))
      list_Rplaca(Scan, cont_CopyAndApplyBindingsCom(Context, list_Car(Scan)));
    return term_Create(term_TopSymbol(Term), ArgumentList);
  } else 
    return term_Create(term_TopSymbol(Term), list_Nil());
}


TERM cont_ApplyBindingsModuloMatching(const CONTEXT Context, TERM Term,
				      BOOL VarCheck)
/**********************************************************
  INPUT:   A context, a term, and a boolean flag.
  RETURNS: <Term> is destructively changed with respect to
           established bindings in the context.
	   If <VarCheck> is true, all variables in <Term>
	   must be bound in the context. When compiled with
	   "CHECK" on, this condition is in fact checked.
	   This function only makes sense after a matching operation.
***********************************************************/
{
  TERM   RplacTerm;
  LIST   Arglist;
  SYMBOL Top;

#ifdef CHECK
  if (VarCheck && symbol_IsVariable(term_TopSymbol(Term)) &&
      !cont_VarIsBound(Context, term_TopSymbol(Term))) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cont_ApplyBindingsModuloMatching:");
    misc_ErrorReport(" Used in forbidden context.\n");
    misc_FinishErrorReport();
  }
#endif

  Top = term_TopSymbol(Term);

  if (symbol_IsVariable(Top)) {
    
    if (cont_VarIsBound(Context, Top)) {
      RplacTerm = cont_ContextBindingTerm(Context, Top);
      Arglist   = term_CopyTermList(term_ArgumentList(RplacTerm));
      term_RplacTop(Term, term_TopSymbol(RplacTerm));
      term_DeleteTermList(term_ArgumentList(Term));
      term_RplacArgumentList(Term, Arglist); 
    }
  }
  else {
    
    for (Arglist = term_ArgumentList(Term);
	 !list_Empty(Arglist);
	 Arglist = list_Cdr(Arglist))
      cont_ApplyBindingsModuloMatching(Context, list_Car(Arglist), VarCheck);
  }     

  return Term;
}


static TERM cont_CopyAndApplyIndexVariableBindings(const CONTEXT Context, TERM Term)
{
  SYMBOL TermTop;

#ifdef CHECK
  if (symbol_IsIndexVariable(term_TopSymbol(Term)) &&
      !cont_VarIsBound(Context, term_TopSymbol(Term))) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cont_CopyAndApplyIndexVariableBindings:");
    misc_ErrorReport(" Expected bound index variable.");
    misc_FinishErrorReport();
  }
#endif

  TermTop = term_TopSymbol(Term);

  while (symbol_IsIndexVariable(TermTop)) {
    if (cont_VarIsBound(Context, TermTop)) {
      Term    = cont_ContextBindingTerm(Context, TermTop);
      TermTop = term_TopSymbol(Term);
    }
  }

  if (term_IsComplex(Term)) {
    LIST Scan, ArgumentList;
    for (Scan = ArgumentList = list_Copy(term_ArgumentList(Term));
	 !list_Empty(Scan);
	 Scan = list_Cdr(Scan))
      list_Rplaca(Scan, cont_CopyAndApplyIndexVariableBindings(Context, list_Car(Scan)));
    return term_Create(TermTop, ArgumentList);
  } else 
    return term_Create(TermTop, list_Nil());
}


TERM cont_ApplyBindingsModuloMatchingReverse(const CONTEXT Context, TERM Term)
/**********************************************************
  INPUT:   A term.
  RETURNS: <Term> is destructively changed with respect to
           established bindings in the leftmost context. This
           function only make sense after a matching operation (reverse).
***********************************************************/
{
  TERM   RplacTerm;
  LIST   Arglist;
  SYMBOL Top;

#ifdef CHECK
  if (symbol_IsVariable(term_TopSymbol(Term)) &&
      !cont_VarIsBound(Context, term_TopSymbol(Term))) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cont_ApplyBindingsModuloMatchingReverse:");
    misc_ErrorReport(" Used in forbidden context.\n");
    misc_FinishErrorReport();
  }
#endif
    
  Top = term_TopSymbol(Term);

  if (symbol_IsVariable(Top)) {
    
    if (cont_VarIsBound(Context, Top)) {
      RplacTerm =
	cont_CopyAndApplyIndexVariableBindings(Context,
						  cont_ContextBindingTerm(Context, Top));
      term_RplacTop(Term, term_TopSymbol(RplacTerm));
      term_DeleteTermList(term_ArgumentList(Term));
      term_RplacArgumentList(Term, term_ArgumentList(RplacTerm));
      term_Free(RplacTerm);
    }
  }
  else {
    
    for (Arglist = term_ArgumentList(Term); !list_Empty(Arglist);
	 Arglist = list_Cdr(Arglist))
      cont_ApplyBindingsModuloMatchingReverse(Context, list_Car(Arglist));
  }     

  return Term;
}


BOOL cont_BindingsAreRenamingModuloMatching(const CONTEXT RenamingContext)
{
  CONTEXT Context;

#ifdef CHECK
  if (!cont_IsContextEmpty(RenamingContext)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cont_BindingsAreRenamingModuloMatching:");
    misc_ErrorReport(" Renaming context contains bindings.\n");
    misc_FinishErrorReport();
  }
#endif

  cont_StartBinding();

  Context = cont_LastBinding();

  while (Context) {
    
    if (!symbol_IsIndexVariable(cont_BindingSymbol(Context))) {
      SYMBOL CodomainSymbol;

      CodomainSymbol = term_TopSymbol(cont_BindingTerm(Context));

      if (symbol_IsVariable(CodomainSymbol)) {
	if (cont_VarIsRenamed(RenamingContext, CodomainSymbol)) {
	  cont_BackTrack();
	  return FALSE;
	} else {
	  cont_CreateBinding(RenamingContext, CodomainSymbol, NULL, NULL);
	  cont_SetContextBindingRenaming(RenamingContext, CodomainSymbol, CodomainSymbol);
	}
      } else {
	cont_BackTrack();
	return FALSE;
      }
    }

    Context = cont_BindingLink(Context);
  }

  cont_BackTrack();
  return TRUE;
}


/**************************************************************/
/* ********************************************************** */
/* *							    * */
/* *  MISC FUNCTIONS                                        * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/


SYMBOL cont_TermMaxVar(CONTEXT Context, TERM Term)
/*********************************************************
  INPUT:   A context and a term.
  RETURNS: The maximal variable in <Term> with respect to
           the bindings in <Context>
********************************************************/
{
  LIST   scan;
  SYMBOL result;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cont_TermMaxVar: Input term is corrupted.\n");
    misc_FinishErrorReport();
  }
#endif

  Term   = cont_Deref(&Context,Term);
  result = symbol_Null();

  if (term_IsStandardVariable(Term)) {
    if (term_TopSymbol(Term) > result)
      result = term_TopSymbol(Term);
  } else {
    for (scan = term_ArgumentList(Term); !list_Empty(scan); scan = list_Cdr(scan)) {
      SYMBOL max = cont_TermMaxVar(Context, list_Car(scan));
      
      if (max > result)
	result = max;
    }
  }

  return result;
}


NAT cont_TermSize(CONTEXT Context, TERM Term)
/*********************************************************
  INPUT:   A context and a term.
  RETURNS: The number of symbols in <Term> with respect to
           the bindings in <Context>
********************************************************/
{
  NAT  result;
  LIST scan;

  Term = cont_Deref(&Context, Term);
  result = 1;
  for (scan = term_ArgumentList(Term); !list_Empty(scan); scan = list_Cdr(scan))
    result += cont_TermSize(Context, list_Car(scan));

  return result;
}


BOOL cont_TermContainsSymbol(CONTEXT Context, TERM Term, SYMBOL Symbol)
/*********************************************************
  INPUT:   A context, a term and a symbol.
  RETURNS: TRUE, if <Symbol> occurs in <Term> with respect to
           the bindings in <Context>, FALSE otherwise.
********************************************************/
{
  LIST scan;

  Term = cont_Deref(&Context, Term);

  if (symbol_Equal(term_TopSymbol(Term), Symbol))
    return TRUE;
  else
    for (scan = term_ArgumentList(Term); !list_Empty(scan); scan = list_Cdr(scan)) {
      if (cont_TermContainsSymbol(Context, list_Car(scan), Symbol))
	return TRUE;
    }

  return FALSE;
}


/**************************************************************/
/* ********************************************************** */
/* *							    * */
/* *  OUTPUT             			            * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/


void cont_TermPrintPrefix(CONTEXT Context, TERM Term)
/**************************************************************
  INPUT:   A context and a term.
  RETURNS: none.
  SUMMARY: Prints the term modulo the context to stdout. 
  CAUTION: none.
***************************************************************/
{
  Term = cont_Deref(&Context, Term);

  symbol_Print(term_TopSymbol(Term));

  if (term_IsComplex(Term)) {
    LIST List;

    putchar('(');

    for (List = term_ArgumentList(Term); !list_Empty(List);
	 List = list_Cdr(List)) {
      cont_TermPrintPrefix(Context, list_Car(List));

      if (!list_Empty(list_Cdr(List)))
	putchar(',');
    }

    putchar(')');
  }
}
