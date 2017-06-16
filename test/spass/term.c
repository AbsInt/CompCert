/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                       TERMS                            * */
/* *                                                        * */
/* *  $Module:   TERM                                       * */
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


#include "term.h"

/**************************************************************/
/* Global variables                                           */
/**************************************************************/

NAT      term_MARK;
POINTER  term_BIND[symbol__MAXVARIABLES][2];
#ifdef CHECK
BOOL term_BINDPHASE;
#endif

NAT  term_STAMP;
BOOL term_STAMPBLOCKED;
static BOOL term_STAMPOVERFLOW[term_MAXSTAMPUSERS];
static NAT  term_STAMPUSERS;


/**************************************************************/
/* ********************************************************** */
/* *							    * */
/* *  TERM CREATION FUNCTIONS			            * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/

void term_Init(void)
/**********************************************************
  INPUT:   None.
  RETURNS: None.
  CAUTION: The term module is initialized.
***********************************************************/
{
  int i;

  term_MARK = 1;

  term_STAMP = 0;
  term_STAMPBLOCKED = FALSE;
  for (i = 0; i < term_MAXSTAMPUSERS; i++)
    term_STAMPOVERFLOW[i] = FALSE;
  term_STAMPUSERS = 0;
#ifdef CHECK
  term_BINDPHASE = FALSE;
#endif
}


TERM term_Create(SYMBOL Symbol, LIST List)
/**********************************************************
  INPUT:   A symbol and a list of arguments.
  RETURNS: A term consisting of the top symbol 'Symbol' and
           the arguments stored in 'List'.
  CAUTION: None.
********************************************************/
{
  TERM Result;

#ifdef CHECK
  if (!symbol_IsSymbol(Symbol) || !term_IsTermList(List)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_Create: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  Result         = (TERM)memory_Malloc(sizeof(TERM_NODE));
  Result->symbol = Symbol;
  Result->args   = List;
  Result->super.termlist = list_Nil();
  Result->stamp = 0;
  Result->size = 0;
  return Result;
}

TERM term_CreateAddFather(SYMBOL Symbol, LIST List)
/**********************************************************
  INPUT:   A symbol and a list of arguments.
  RETURNS: A term consisting of the top symbol 'Symbol' and
           the arguments stored in 'List'.
           In contrast to term_Create the superterm members are set for the arguments.
  CAUTION: None.
********************************************************/
{
  TERM Result;
  LIST l;
  Result = term_Create(Symbol, List);
  for (l=term_ArgumentList(Result); !list_Empty(l); l = list_Cdr(l))
    term_RplacSuperterm((TERM) list_Car(l), Result);
  return Result;
}

TERM term_CreateStandardVariable(void)
/**********************************************************
  RETURNS: Returns a term with a new variable as top symbol.
***********************************************************/
{
  return term_Create(symbol_CreateStandardVariable(), list_Nil());
}


void term_Delete(TERM Term)
/**********************************************************
  INPUT:   A term.
  SUMMARY: Deletes the term and frees the storage.
  CAUTION: The arguments of Term are also deleted.
********************************************************/
{
  if (term_IsComplex(Term)) {
    LIST Scan;
    for (Scan = term_ArgumentList(Term);
	 list_Exist(Scan);
	 Scan = list_Cdr(Scan))
      term_Delete(list_Car(Scan));
    list_Delete(term_ArgumentList(Term));
  }
  term_Free(Term);
}


void term_DeleteIterative(TERM Term)
/**********************************************************
  INPUT:   A term.
  SUMMARY: Deletes the term and frees the storage.
  CAUTION: The arguments of Term are also deleted.
********************************************************/
{
  if (term_IsComplex(Term)) {
    LIST Stack, Aux;
    Stack = list_StackBottom();
    do {
      if (term_IsComplex(Term))
	Stack = list_Push(term_ArgumentList(Term),Stack);
      term_Free(Term);
      while (!list_StackEmpty(Stack) && list_Empty(list_Top(Stack)))
	Stack = list_Pop(Stack);
      if (!list_StackEmpty(Stack)) {
	Aux  = list_Top(Stack);
	Term = (TERM)list_Car(Aux);
	list_RplacTop(Stack, list_Cdr(Aux));
	list_Free(Aux);
      }
    } while (!list_StackEmpty(Stack));
  }
  else
    term_Free(Term);
}

/**************************************************************/
/* ********************************************************** */
/* *			                                    * */
/* *  PRIMITIVE TERM FUNCTIONS                              * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/

BOOL term_Equal(TERM Term1, TERM Term2)
/*********************************************************
  INPUT:   Two terms.
  RETURNS: The boolean value TRUE if the terms are equal.
  CAUTION: EQUAL FUNCTION- OR PREDICATE SYMBOLS SHARE THE
           SAME ARITY. THIS IS NOT VALID FOR JUNCTORS!
**********************************************************/
{
#ifdef CHECK
  if (!term_IsTerm(Term1) || !term_IsTerm(Term2)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_Equal: Illegal input.");
    misc_FinishErrorReport();
  }
#endif
  
  /* if (term_IsIndexVariable(Term1))
     puts("\nterm_Equal: Left index variable.");
     else if (term_IsIndexVariable(Term2))
     puts("\nterm_Equal: Right index variable.");

     fflush(stdout); */

  if (Term1 == Term2)   /* pointers are equal */
    return TRUE;
  else if (!term_EqualTopSymbols(Term1, Term2))
    return FALSE;
  else if (term_ArgumentList(Term1)) {
    LIST Scan1, Scan2;
    for (Scan1=term_ArgumentList(Term1), Scan2=term_ArgumentList(Term2);
	list_Exist(Scan1) && list_Exist(Scan2);
	Scan1=list_Cdr(Scan1), Scan2=list_Cdr(Scan2))
      if (!term_Equal(list_Car(Scan1),list_Car(Scan2)))
	return FALSE;
    return (list_Empty(Scan1) ? list_Empty(Scan2) : FALSE);
  } else
    return TRUE;
}


BOOL term_EqualIterative(TERM Term1, TERM Term2)
/*********************************************************
  INPUT:   Two terms.
  RETURNS: The boolean value TRUE if the terms are equal.
  CAUTION: Notice that there may be symbols with arbitrary arity
*******************************************************/
{
  LIST Stack1,Stack2;

#ifdef CHECK
  if (!term_IsTerm(Term1) || !term_IsTerm(Term2)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_EqualIterative: Illegal input.");
    misc_FinishErrorReport();
  }
#endif
  
  Stack1 = Stack2 = list_StackBottom();
  do {
    if (term_EqualTopSymbols(Term1,Term2) &&
	term_IsComplex(Term1) && term_IsComplex(Term2)) {
      Stack1 = list_Push(term_ArgumentList(Term1),Stack1);
      Stack2 = list_Push(term_ArgumentList(Term2),Stack2);
    }
    if (!term_EqualTopSymbols(Term1,Term2) ||
	term_IsComplex(Term1) != term_IsComplex(Term2)) {
      Stack1 = list_StackFree(Stack1);
      Stack2 = list_StackFree(Stack2);
      return FALSE;
    }
    while (!list_StackEmpty(Stack1) && list_Empty(list_Top(Stack1)))
      if (!list_StackEmpty(Stack2) && list_Empty(list_Top(Stack2))) {
	Stack1 = list_Pop(Stack1);
	Stack2 = list_Pop(Stack2);
      }
      else {
	Stack1 = list_StackFree(Stack1);
	Stack2 = list_StackFree(Stack2);
	return FALSE;
      }
    if (!list_StackEmpty(Stack1)) {
      if (!list_Empty(list_Top(Stack2))) {
	Term1 = (TERM)list_Car(list_Top(Stack1));
	list_RplacTop(Stack1, list_Cdr(list_Top(Stack1)));
	Term2 = (TERM)list_Car(list_Top(Stack2));
	list_RplacTop(Stack2, list_Cdr(list_Top(Stack2)));
      }
      else {
	Stack1 = list_StackFree(Stack1);
	Stack2 = list_StackFree(Stack2);
	return FALSE;
      }
    }
  } while (!list_StackEmpty(Stack1));
  return TRUE;
}


BOOL term_VariableEqual(TERM Variable1, TERM Variable2)
/*********************************************************
  INPUT:   Two Variables.
  RETURNS: The boolean value TRUE, if the variables are
           equal.
**********************************************************/
{
  return term_EqualTopSymbols(Variable1, Variable2);
}


BOOL term_IsGround(TERM Term)
/**********************************************************
  INPUT:   A term.
  RETURNS: A boolean value which is TRUE, if 'Term' is a
           ground term, i.e. does not contain variables.
********************************************************/
{
#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_IsGround: Illegal input.");
    misc_FinishErrorReport();
  }
#endif
  
  if (term_IsComplex(Term)) {
    LIST Stack;
    Stack = list_StackBottom();
    do {
      if (term_IsComplex(Term))
	Stack = list_Push(term_ArgumentList(Term),Stack);
      else
	if (term_IsVariable(Term)) {
	  Stack = list_StackFree(Stack);
	  return FALSE;
	}
      while (!list_StackEmpty(Stack) && list_Empty(list_Top(Stack)))
	Stack = list_Pop(Stack);
      if (!list_StackEmpty(Stack)) {
	Term = (TERM)list_Car(list_Top(Stack));
	list_RplacTop(Stack, list_Cdr(list_Top(Stack)));
      }
    } while (!list_StackEmpty(Stack));
    return TRUE;
  } else
    return !term_IsVariable(Term);
}


BOOL term_IsTerm(TERM Term)
/*********************************************************
  INPUT:   A term.
  RETURNS: TRUE, if 'Term' is not NULL
           and has a symbol as its top symbol.
**********************************************************/
{
  return (Term != (TERM)NULL && symbol_IsSymbol(term_TopSymbol(Term)));
}


BOOL term_IsTermList(LIST TermList)
/*********************************************************
  INPUT:   A term.
  RETURNS: TRUE iff <TermList> is a list of terms.
*******************************************************/
{
  for ( ; !list_Empty(TermList); TermList=list_Cdr(TermList))
    if (!(term_IsTerm((TERM)list_Car(TermList))))
      return FALSE;

  return TRUE;
}


BOOL term_AllArgsAreVar(TERM Term)
/*********************************************************
  INPUT:   A term.
  RETURNS: The boolean value TRUE, if all arguments of the
           term are variables.
*******************************************************/
{
  LIST Scan;
  for (Scan = term_ArgumentList(Term);
       !list_Empty(Scan); Scan = list_Cdr(Scan))
    if (!term_IsVariable(list_Car(Scan)))
      return FALSE;
  return TRUE;
}


/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *			LOW LEVEL FUNCTIONS	            * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/


TERM term_Copy(TERM Term)
/**********************************************************
  INPUT:   A term.
  RETURNS: A copy of 'Term' where the stamp field is copied, too.
  SUMMARY: Copies "Term" and returns a pointer to the copy.
*********************************************************/
{
  TERM Result;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_Copy: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  if (term_IsComplex(Term)) {
    LIST Scan, ArgumentList;
    for (Scan = ArgumentList = list_Copy(term_ArgumentList(Term));
	 list_Exist(Scan);
	 Scan = list_Cdr(Scan))
      list_Rplaca(Scan, term_Copy(list_Car(Scan)));
    Result = term_Create(term_TopSymbol(Term), ArgumentList);
  } else
    Result = term_Create(term_TopSymbol(Term), list_Nil());

  Result->stamp = Term->stamp;
  Result->size  = Term->size;

  return Result;
}


TERM term_CopyIterative(TERM Term)
/**********************************************************
  INPUT:   A term.
  RETURNS: A copy of <Term>.
  SUMMARY: Copies <Term> and returns a pointer to the copy.
*********************************************************/
{
#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_CopyIterative: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  if (term_IsComplex(Term)) {
    LIST TopStack, ArgumentStack, ActStack;
    TopStack      = list_Push((POINTER)term_TopSymbol(Term),
			      list_StackBottom());
    ArgumentStack = list_Push(list_Copy(term_ArgumentList(Term)),
			      list_StackBottom());
    ActStack      = list_Push(list_Top(ArgumentStack),
			      list_StackBottom());

    while (!list_StackEmpty(TopStack)) {
      if (list_Empty(list_Top(ActStack))) {
	Term = term_Create((SYMBOL)list_Top(TopStack),
			   (LIST)list_Top(ArgumentStack));
	TopStack = list_Pop(TopStack);
	ArgumentStack = list_Pop(ArgumentStack);
	ActStack = list_Pop(ActStack);
	if (!list_StackEmpty(TopStack)) {
	  list_Rplaca(list_Top(ActStack), Term);
	  list_RplacTop(ActStack, list_Cdr(list_Top(ActStack)));
	}
      }
      else {
	Term = (TERM)list_Car(list_Top(ActStack));
	if (term_IsComplex(Term)) {
	  TopStack      = list_Push((POINTER)term_TopSymbol(Term), TopStack);
	  ArgumentStack = list_Push(list_Copy(term_ArgumentList(Term)),
				    ArgumentStack);
	  ActStack      = list_Push(list_Top(ArgumentStack), ActStack);
	}
	else {
	  list_Rplaca(list_Top(ActStack),
		      term_Create(term_TopSymbol(Term), list_Nil()));
	  list_RplacTop(ActStack, list_Cdr(list_Top(ActStack)));
	}
      }
    }
    return Term;
  }
  else
    return term_Create(term_TopSymbol(Term), list_Nil());
}


TERM term_CopyWithEmptyArgListNode(TERM Term, LIST ArgListNode,
				   LIST* ListNodeCopyPt)
/**********************************************************
  INPUT:   A term and a pointer to an argument list node of
           this term.
  RETURNS: A copy of 'Term' with a NULL as list_Car(ListNodeCopy).
  SUMMARY: Copies "Term" and returns a pointer to the copy.
*********************************************************/
{
#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_CopyWithEmptyArgListNode: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  if (term_IsComplex(Term)) {
    LIST Scan, ArgumentList, HelpScan;
    TERM Result;

    HelpScan = term_ArgumentList(Term);
    ArgumentList = list_Copy(HelpScan);

    for (Scan = ArgumentList;
	 list_Exist(Scan);
	 Scan = list_Cdr(Scan),HelpScan = list_Cdr(HelpScan))
      if (HelpScan != ArgListNode)
	list_Rplaca(Scan,
		    term_CopyWithEmptyArgListNode(list_Car(Scan),
						  ArgListNode,
						  ListNodeCopyPt));
      else{
	list_Rplaca(Scan, (TERM)NULL);
	*ListNodeCopyPt = Scan;
      }

    Result         = (TERM)memory_Malloc(sizeof(TERM_NODE));
    Result->symbol = term_TopSymbol(Term);
    Result->args   = ArgumentList;
    Result->super.termlist = list_Nil();

    return Result;

  } else
    return term_Create(term_TopSymbol(Term), list_Nil());
}


void term_PrintWithEmptyArgListNode(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: none.
  SUMMARY: Prints any term to stdout, especially terms with empty
           argument list nodes.
  CAUTION: Uses the other term_Output functions.
*************************************************************/
{
  if (Term == (TERM)NULL)
    fputs("(NULL)", stdout);
  
  else if (term_IsComplex(Term)) {
    putchar('(');
    symbol_Print(term_TopSymbol(Term));
    putchar(' ');
    list_Apply((void (*)(POINTER)) term_PrintWithEmptyArgListNode,
	       term_ArgumentList(Term));
    putchar(')');
    
  } else if (term_IsVariable(Term)) {
    
    symbol_Print(term_TopSymbol(Term));
    
  } else {
    
    /* term_IsConstant(Term) */
    putchar('(');
    symbol_Print(term_TopSymbol(Term));
    putchar(')');
  }
}


BOOL term_ReplaceSubtermBy(TERM Atom, TERM TermS, TERM TermT)
/**************************************************************
  INPUT:   Three terms.
  RETURNS: None.
  EFFECT:  Replaces all occurrences of TermS in Atom by TermT.
           Top level is NOT considered!
*************************************************************/
{
  LIST ArgListNode;
  BOOL Replaced;
  int B_Stack;

#ifdef CHECK
  if (!term_IsTerm(Atom) || !term_IsTerm(TermS) ||
      !term_IsTerm(TermT) || term_Equal(Atom, TermS)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_ReplaceSubtermBy: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  /*fputs("\nWe look for: ",stdout);term_Print(TermS);
    fputs("\nin: ",stdout);term_Print(Atom);
  */

  Replaced = FALSE;
  TermS    = term_Copy(TermS);

  if (!term_Equal(Atom, TermS) && !list_Empty(term_ArgumentList(Atom))) {

    B_Stack = stack_Bottom();
    stack_Push(term_ArgumentList(Atom));
    
    while (!stack_Empty(B_Stack)) {
      ArgListNode = stack_Top();
      Atom        = (TERM)list_Car(ArgListNode);
      stack_RplacTop(list_Cdr(ArgListNode));
      
      if (term_Equal(Atom, TermS)) {
	Replaced = TRUE;
	list_Rplaca(ArgListNode, term_Copy(TermT));
	term_Delete(Atom);
      }
      else
	if (term_IsComplex(Atom))
	  stack_Push(term_ArgumentList(Atom));
      
      while (!stack_Empty(B_Stack) && list_Empty(stack_Top()))
	stack_Pop();
    }
  }
  term_Delete(TermS);
  return Replaced;
}


void term_ReplaceVariable(TERM Term, SYMBOL Symbol, TERM Repl)
/**************************************************************
  INPUT:   A term, a variable symbol and a replacement term.
  RETURNS: void
  EFFECT:  All variables with <Symbol> in <Term> are replaced 
           with copies of <Repl>
  CAUTION: Destructive
***************************************************************/
{
  LIST Scan;

#ifdef CHECK
  if (!term_IsTerm(Term) || !term_IsTerm(Repl) || !symbol_IsVariable(Symbol)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_ReplaceVariable: Illegal input.");
    misc_FinishErrorReport();
  }
#endif
  
  if (symbol_Equal(term_TopSymbol(Term), Symbol)) {
    term_RplacTop(Term,term_TopSymbol(Repl));
    term_RplacArgumentList(Term,term_CopyTermList(term_ArgumentList(Repl)));
  }
  else
    for (Scan = term_ArgumentList(Term); !list_Empty(Scan); Scan = list_Cdr(Scan))
      term_ReplaceVariable(list_Car(Scan),Symbol,Repl);
}

void term_ExchangeVariable(TERM Term, SYMBOL Old, SYMBOL New)
/**************************************************************
  INPUT:   A term, and two variable symbols.
  RETURNS: void
  EFFECT:  All variables <Old> in <Term> are replaced with <New>
  CAUTION: Destructive
***************************************************************/
{
  LIST Scan;

#ifdef CHECK
  if (!term_IsTerm(Term) || !symbol_IsVariable(Old) || !symbol_IsVariable(New)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_ExchangeVariable: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  if (symbol_Equal(term_TopSymbol(Term), Old))
    term_RplacTop(Term,New);
  else
    for (Scan = term_ArgumentList(Term); !list_Empty(Scan); Scan = list_Cdr(Scan))
      term_ExchangeVariable(list_Car(Scan),Old,New);
}


BOOL term_SubstituteVariable(SYMBOL Symbol, TERM Repl, TERM* Term)
/******************************************************
   INPUT:   A Symbol which has to be found in the Term,
            a term which is the replacement for the    
            'Symbol', and a term in which the substitu-
            tions take place.                          
   RETURNS: A boolean value which is TRUE, if any sub- 
            stitutions were made.                      
   SUMMARY: term_Substitute works recursively and repl.
            every occurence of 'Symbol' in 'Term' by   
            'Repl'.                                    
   CAUTION: FUNCTION IS DESTRUCTIVE ON 'Term'. REPLACE-
            MENT IS COPIED EACH TIME A SUB. TAKES PLACE
*******************************************************/
{
#ifdef CHECK
  if (!term_IsTerm(*Term) || !term_IsTerm(Repl) || !symbol_IsSymbol(Symbol)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_SubstituteVariable: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  if (symbol_Equal(term_TopSymbol(*Term), Symbol)) {
    
    TERM New;
    New             = term_Copy(Repl);
    (*Term)->symbol = Repl->symbol;
    (*Term)->args   = term_ArgumentList(New);
    
    /* Free Top-Node of New, as the symbol has been written */
    /* into the node pointed to by `Term'. */
    memory_Free(New, sizeof(TERM_NODE));
    return TRUE;
 
  } else {
    
    BOOL Result;
    LIST List;
    
    Result	= FALSE;
    for (List	= term_ArgumentList(*Term);
	 list_Exist(List); List = list_Cdr(List))
      if (term_SubstituteVariable(Symbol, Repl, (TERM*) &(List->car)))
	Result  = TRUE;
    return Result;
  }
}


static int term_CompareByConstants(TERM Left, TERM Right)
/**************************************************************
  INPUT:   Two terms.
  RETURNS:  1 if left term < right term
            0 if left term = right term
	   -1 if left term > right term
  EFFECT:  The terms are compared by their multisets of 
           constants. The frequency of elements in the
	   multisets is a multiset itself. The frequencies
	   are sorted and the resulting sorted multisets
	   compared.
***************************************************************/
{
  LIST lconsts, rconsts;
  int result;

  /* Get multiset of constants. */

  lconsts = term_ListOfConstants(Left);
  rconsts = term_ListOfConstants(Right);

  result  = list_CompareMultisetsByElementDistribution(lconsts, rconsts); 

  list_Delete(lconsts);
  list_Delete(rconsts);

  return result;
}

static int term_CompareByFunctions(TERM Left, TERM Right) 
/**************************************************************
  INPUT:   Two terms.
  RETURNS:  1 if left term < right term
            0 if left term = right term
	   -1 if left term > right term
  EFFECT:  The terms are compared by their multisets of 
           functions. The frequency of elements in the
	   multisets is a multiset itself. The frequencies
	   are sorted and the resulting sorted multisets
	   compared.
***************************************************************/
{
  LIST lfuns, rfuns;
  int result;

  /* Get multiset of functions. */

  lfuns = term_ListOfFunctions(Left);
  rfuns = term_ListOfFunctions(Right);

  result  = list_CompareMultisetsByElementDistribution(lfuns, rfuns); 

  list_Delete(lfuns);
  list_Delete(rfuns);

  return result;
}

static int term_CompareByVariables(TERM Left, TERM Right) 
/**************************************************************
  INPUT:   Two terms.
  RETURNS:  1 if left term < right term
            0 if left term = right term
	   -1 if left term > right term
  EFFECT:  The terms are compared by their multisets of 
           variables. The frequency of elements in the
	   multisets is a multiset itself. The frequencies
	   are sorted and the resulting sorted multisets
	   compared.
***************************************************************/
{
  LIST lvars, rvars;
  int result;

  /* Get multiset of variables. */

  lvars = term_ListOfVariables(Left);
  rvars = term_ListOfVariables(Right);

  result  = list_CompareMultisetsByElementDistribution(lvars, rvars); 

  list_Delete(lvars);
  list_Delete(rvars);

  return result;
}

LIST term_ListOfConstants(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: A list of constants.
  EFFECT:  Creates a list of constants used in a term. If no
           constants are used in a term, it returns an empty 
	   list.
***************************************************************/
{
#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_ListOfConstants: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  if (symbol_IsConstant(term_TopSymbol(Term)))
    return list_List((POINTER) term_TopSymbol(Term));
  else {
    LIST result;
    LIST scan;
  
    result = list_Nil();
    for (scan = term_ArgumentList(Term); 
	 !list_Empty(scan); 
	 scan = list_Cdr(scan)) {
      /* Append to the smaller list for efficiency. 
	 A subterm's list of constants will usually 
	 be smaller than the intermediate result.
      */
      result = list_Nconc(term_ListOfConstants((TERM) list_Car(scan)), result);
    }

    return result;
  }
}

LIST term_ListOfFunctions(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: A list of functions.
  EFFECT:  Creates a list of functions used in a term. If no
           functions are used in a term, it returns an empty 
	   list.
***************************************************************/
{
  LIST result;
  LIST scan;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_ListOfFunctions: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  result = list_Nil();

  /* If the term starts with a function, add the function symbol
     to the result.
  */
  if (symbol_IsFunction(term_TopSymbol(Term))) {
    result = list_Nconc(result, list_List((POINTER) term_TopSymbol(Term)));
  }
  
  /* A function can utilize other functions, so
     traverse the argument list for further
     functions.
  */
  for (scan = term_ArgumentList(Term); 
       !list_Empty(scan); 
       scan = list_Cdr(scan)) {
    /* Append to the smaller list for efficiency. 
       A subterm's list of functions will usually 
       be smaller than the intermediate result.
    */
    result = list_Nconc(term_ListOfFunctions((TERM) list_Car(scan)), result);
  }

  return result;
}

void term_CountSymbols(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: None.
  EFFECT:  Counts the non-variable symbols in the term, and 
           increases their counts accordingly.
***************************************************************/
{
  LIST scan;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_CountSymbols: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  /* If the term starts with a function, increase the count for
     the function symbol.
  */
  if (symbol_IsFunction(term_TopSymbol(Term))) {
    SYMBOL S;

    S = term_TopSymbol(Term);
    symbol_SetCount(S, symbol_GetCount(S) + 1);
  }

  /* A function can utilize other functions, so
     traverse the argument list for further
     function symbols.
  */
  for (scan = term_ArgumentList(Term); 
       !list_Empty(scan); 
       scan = list_Cdr(scan)) {
    term_CountSymbols((TERM) list_Car(scan));
  }
}

static int term_CompareByArity(TERM Left, TERM Right)
/**************************************************************
  INPUT:   Two terms.
  RETURNS:  1 if left term < right term
            0 if left term = right term
	   -1 if left term > right term
  EFFECT:  Terms are compared top down, left to right with 
           respect to the arity of their signature symbols,
	   where variables in addition are defined to be smaller
	   than constants.
***************************************************************/
{
  NAT    lval, rval;
  SYMBOL lsymb, rsymb;
  LIST   largs, rargs;
  int    result;

  result = 0;

  /* Compare top symbols first */
  lsymb = term_TopSymbol(Left);
  rsymb = term_TopSymbol(Right);

  if (symbol_IsVariable(lsymb)) {
    if (symbol_IsVariable(rsymb))
      return 0;
    else
      return 1;
  }
  else
    if (symbol_IsVariable(rsymb))
      return -1;

  lval = symbol_Arity(lsymb);
  rval = symbol_Arity(rsymb);
  
  if (lval > rval)
    return -1;

  if (lval < rval)
    return 1;

  /* If top symbol arities are equal, compare subterms left to right */
  largs = term_ArgumentList(Left);
  rargs = term_ArgumentList(Right);

  while(!list_Empty(largs)) {
    result = term_CompareByArity(list_Car(largs), list_Car(rargs));	
    if (result != 0)
      break;

    largs = list_Cdr(largs);
    rargs = list_Cdr(rargs);
  }

  return result;
}

int term_CompareBySymbolOccurences(TERM Left, TERM Right)
/**************************************************************
  INPUT:   Two terms.
  RETURNS:  1 if left term < right term
            0 if left term = right term
	   -1 if left term > right term
  EFFECT:  Terms are compared top down, left to right with 
           respect to the frequency of their symbols.
***************************************************************/
{
  unsigned long  lval, rval;
  SYMBOL         lsymb, rsymb;
  LIST           largs, rargs;
  int            result;

  result = 0;

  /* Compare top symbols first */
  lsymb = term_TopSymbol(Left);
  rsymb = term_TopSymbol(Right);

  if (symbol_IsFunction(lsymb)) {
    if (symbol_IsFunction(rsymb)) {

      lval = symbol_GetCount(lsymb);
      rval = symbol_GetCount(rsymb);
  
      if (lval > rval)
	return -1;

      if (lval < rval)
	return 1;
    
      /* If top symbol arities are equal, compare subterms left to right */
      largs = term_ArgumentList(Left);
      rargs = term_ArgumentList(Right);

      while(!list_Empty(largs)) {
	result = term_CompareBySymbolOccurences(list_Car(largs), 
						list_Car(rargs));	
	if (result != 0)
	  break;

	largs = list_Cdr(largs);
	rargs = list_Cdr(rargs);
      }
    }
    else {
      return -1;
    }
  }
  else {
    if (symbol_IsFunction(rsymb)) {
      return 1;
    }
  }

  return result;
}

int term_CompareAbstract(TERM Left, TERM Right)
/**************************************************************
  INPUT:   Two terms.
  RETURNS:  1 if left term < right term
            0 if left term = right term
	   -1 if left term > right term
  EFFECT:  Compares two terms using an internal array of term 
           comparison functions. As soon as a term is found to 
	   compare greater than the other, the result of the 
	   comparison is returned. If all term comparison 
	   functions yield an "equal", then 0 is returned.
***************************************************************/
{
  int result;
  int i;
  int functions;

  typedef int (*TERM_COMPARE_FUNCTION) (TERM, TERM);

  static const TERM_COMPARE_FUNCTION term_compare_functions [] = {
    term_CompareByArity,
    term_CompareBySymbolOccurences,
    term_CompareByConstants,
    term_CompareByVariables,
    term_CompareByFunctions
  };

#ifdef CHECK
  if (!(term_IsTerm(Left) && term_IsTerm(Right))) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_CompareAbstract: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  result    = 0;
  functions = sizeof(term_compare_functions)/sizeof(TERM_COMPARE_FUNCTION);

  for (i = 0; i < functions; i++) {
    result = term_compare_functions[i](Left, Right);

    if ( result != 0) {
      return result;
    }
  }

  return result;
}

BOOL term_CompareAbstractLEQ(TERM Left, TERM Right)
/**************************************************************
  INPUT:   Two terms.
  RETURNS: TRUE if left term <= right term, FALSE otherwise.
  EFFECT:  Terms are compared top down, left to right with 
           respect to the arity of their signature symbols,
	   where variables in addition are defined to be smaller
	   than constants.
***************************************************************/
{
  return (term_CompareAbstract(Left, Right) >= 0);
}


NAT term_ComputeSize(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: The number of symbols in the term.
  EFFECT:  None
***************************************************************/
{
  NAT  Weight;
  LIST Scan;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_ComputeSize: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  Weight = 1;
  for (Scan=term_ArgumentList(Term); !list_Empty(Scan); Scan=list_Cdr(Scan))
    Weight += term_ComputeSize((TERM)list_Car(Scan));
  return Weight;
}

NAT term_RootDistance(TERM Term)
/**************************************************************
  INPUT:   A term with establised father links.
  RETURNS: The distance from <Term> to its root father term.
  EFFECT:  None
***************************************************************/
{
  NAT  Distance;

  Distance = 0;

  while (term_Superterm(Term) != (TERM)NULL) {
    Distance++;
    Term = term_Superterm(Term);
  }

  return Distance;
}

BOOL term_RootDistanceSmaller(TERM Term1, TERM Term2)
/**************************************************************
  INPUT:   Two terms with establised father links.
  RETURNS: TRUE iff root distance of <Term1> is smaller than
           root distance of <Term2>
  EFFECT:  None
***************************************************************/
{
  return (term_RootDistance(Term1)<term_RootDistance(Term2));
}

void term_InstallSize(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: None
  EFFECT:  Sets for every subterm the size.
***************************************************************/
{
  NAT  Weight;
  LIST Scan;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_InstallSize: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  Weight = 1;
  for (Scan=term_ArgumentList(Term); !list_Empty(Scan); Scan=list_Cdr(Scan)) {
    term_InstallSize((TERM)list_Car(Scan));
    Weight += term_Size((TERM)list_Car(Scan));
  };
  term_SetSize(Term, Weight);
}

NAT term_Depth(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: The depth of the term.
  EFFECT:  None
***************************************************************/
{
  NAT  Depth,Help;
  LIST Scan;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_Depth: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  Depth = 0;
  for (Scan=term_ArgumentList(Term); !list_Empty(Scan); Scan=list_Cdr(Scan)) {
    Help = term_Depth(list_Car(Scan));
    if (Help > Depth)
      Depth = Help;
  }
  return (Depth+1);
}

BOOL term_ContainsSymbol(TERM Term, SYMBOL Symbol)
/**************************************************************
  INPUT:   A term and a symbol.
  RETURNS: TRUE, if the symbol occurs somewhere in the term,
           FALSE otherwise.
***************************************************************/
{
  int Stack;

#ifdef CHECK
  if (!term_IsTerm(Term) || !symbol_IsSymbol(Symbol)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_ContainsSymbol: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  Stack = stack_Bottom();

  do {
    if (term_TopSymbol(Term) == Symbol) {
      stack_SetBottom(Stack);    /* Clean up the stack */
      return TRUE;
    }
    else
      if (term_IsComplex(Term))
	stack_Push(term_ArgumentList(Term));

    while (!stack_Empty(Stack) && list_Empty(stack_Top()))
      stack_Pop();

    if (!stack_Empty(Stack)) {
      Term = list_Car(stack_Top());
      stack_RplacTop(list_Cdr(stack_Top()));
    }
  } while (!stack_Empty(Stack));

  return FALSE;
}

TERM term_FindSubterm(TERM Term, SYMBOL Symbol)
/**************************************************************
  INPUT:   A term and a symbol.
  RETURNS: If the symbol occurs in the Term the subterm is returned.
           NULL otherwise.
***************************************************************/
{
  int stack;

#ifdef CHECK
  if (!term_IsTerm(Term) || !symbol_IsSymbol(Symbol)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_FindSubterm: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  stack = stack_Bottom();

  do {
    if (term_TopSymbol(Term) == Symbol) {
      stack_SetBottom(stack);    /* Clean up the stack */
      return Term;
    } else if (term_IsComplex(Term))
      stack_Push(term_ArgumentList(Term));

    while (!stack_Empty(stack) && list_Empty(stack_Top()))
      stack_Pop();

    if (!stack_Empty(stack)) {
      Term = list_Car(stack_Top());
      stack_RplacTop(list_Cdr(stack_Top()));
    }
  } while (!stack_Empty(stack));

  return NULL;
}

static int term_SharingList(TERM Term, LIST List)
/**************************************************************
  INPUT:   A term and a list cell.
  RETURNS: The number of times <List> occurs in <Term>
  EFFECT:  None
***************************************************************/
{
  LIST Scan;
  int  n;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_SharingList: Illegal input.");
    misc_FinishErrorReport();
  }
#endif
  
  n = 0;

  for (Scan=term_ArgumentList(Term); !list_Empty(Scan); Scan=list_Cdr(Scan)) {
    if (Scan == List)
      n++;
    n += term_SharingList(list_Car(Scan), List);
  }

  return n;
}


static int term_SharingTerm(TERM Term, TERM CompareTerm)
/**************************************************************
  INPUT:   A term and a compare term
  RETURNS: The number of occurrences of <CompareTerm> in <Term>
  EFFECT:  None
***************************************************************/
{
  LIST Scan;
  int  n;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_SharingTerm: Illegal input.");
    misc_FinishErrorReport();
  }
#endif
  
  n = 0;

  if (Term == CompareTerm)
    n = 1;

  for (Scan=term_ArgumentList(Term); !list_Empty(Scan); Scan=list_Cdr(Scan))
    n += term_SharingTerm(list_Car(Scan),CompareTerm);

  return n;
}


BOOL term_Sharing(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: TRUE iff the term shares list cells or subterms.
  EFFECT:  None
***************************************************************/
{
  LIST Scan;
  int  stack;
  TERM ActTerm;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_Sharing: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  stack = stack_Bottom();
  stack_Push(Term);

  while (!stack_Empty(stack)) {
    ActTerm = (TERM)stack_Top();
    stack_Pop();
    
    if (term_SharingTerm(Term,ActTerm)>1)
      return TRUE;
  
    if (term_IsComplex(Term)) {
      for (Scan = term_ArgumentList(ActTerm);
	   !list_Empty(Scan);
	   Scan=list_Cdr(Scan))
	if (term_SharingList(Term, Scan) > 1)
	  return TRUE;
	else
	  stack_Push(list_Car(Scan));
    }
  }
  
  return FALSE;
}


void term_AddFatherLinks(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: void.
  EFFECT:  The super term links of Term are cleared and then all
           its subterms are set.
***************************************************************/
{
  LIST Scan;
  TERM ActTerm;

  term_RplacSuperterm(Term,(TERM)NULL);
  
  for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
    ActTerm  = (TERM)list_Car(Scan);
    term_AddFatherLinks(ActTerm);
    term_RplacSuperterm(ActTerm,Term);
  }

}

BOOL term_FatherLinksEstablished(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: TRUE iff all father links in Term are established.
  EFFECT:  None.
***************************************************************/
{
  LIST Scan;
  
  for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan))
   if (Term != term_Superterm(list_Car(Scan)) || !term_FatherLinksEstablished(list_Car(Scan)))
     return FALSE;

  return TRUE;
}

TERM term_TopLevelTerm(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: The top level father of the term.
  EFFECT:  The father links have to be established!
***************************************************************/
{
  while (term_Superterm(Term))
    Term = term_Superterm(Term);
  return Term;
}


BOOL term_HasPointerSubterm(TERM Term, TERM Subterm)
/**************************************************************
  INPUT:   Two terms.
  RETURNS: TRUE, if <Term> has <Subterm> as a subterm.
  CAUTION: Only term pointers are compared, term_Equal isn't used.
***************************************************************/
{
  if (Term == Subterm)
    return TRUE;
  else {
    LIST scan = term_ArgumentList(Term);

    while (!list_Empty(scan)) {
      if (term_HasPointerSubterm((TERM) list_Car(scan), Subterm))
	return TRUE;
      scan = list_Cdr(scan);
    }
  }

  return FALSE;
}

BOOL term_HasSubterm(TERM Term, TERM Subterm)
/**************************************************************
  INPUT:   Two terms.
  RETURNS: TRUE, if <Term> has <Subterm> as a subterm.
  CAUTION: term_Equal is used.
***************************************************************/
{
  if (term_Equal(Term,Subterm))
    return TRUE;
  else {
    LIST Scan;
    Scan = term_ArgumentList(Term);

    while (!list_Empty(Scan)) {
      if (term_HasSubterm((TERM) list_Car(Scan), Subterm))
	return TRUE;
      Scan = list_Cdr(Scan);
    }
  }

  return FALSE;
}

BOOL term_HasProperSuperterm(TERM Term, TERM Super)
/**********************************************************
  INPUT   : Two terms.
  RETURNS : TRUE iff Super can be reached from Term by following
            the superterm member of the TERM structure.
  CAUTION : not reflexive
**********************************************************/
{
  if (Term == Super)
    return FALSE;
  while (Term != (TERM) NULL) {
    if (Term == Super)            /* Pointer equality ! */
      return TRUE;
    else
      Term = term_Superterm(Term);
  }
  return FALSE;
}


/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  TERM OUTPUT FUNCTIONS                                 * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/

void term_Print(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: none.
  SUMMARY: Prints the term to stdout.
  CAUTION: Uses the other term output functions.
***************************************************************/
{
  if (term_IsComplex(Term)) {
    putchar('(');
    symbol_Print(term_TopSymbol(Term));
    putchar(' ');
    term_TermListPrint(term_ArgumentList(Term));
    putchar(')');

  } else if (term_IsVariable(Term)) {

    symbol_Print(term_TopSymbol(Term));

  } else {

    /* term_IsConstant(Term) */
    putchar('(');
    symbol_Print(term_TopSymbol(Term));
    putchar(')');
  }
}

static void term_PrettyPrintIntern(TERM Term, int Depth)
/**************************************************************
  INPUT:   A term and a depth parameter for indentation.
  RETURNS: none.
  SUMMARY: Prints the term hopefully more pretty to stdout.
***************************************************************/
{
  int i;
  LIST scan;


  for (i=0; i < Depth; i++)
    fputs("  ", stdout);
  if (symbol_IsJunctor(term_TopSymbol(Term))) {
    if (term_IsComplex(Term)) {
      symbol_Print(term_TopSymbol(Term));
      putchar('(');
      fputs("\n", stdout);
      for (scan=term_ArgumentList(Term); !list_Empty(scan); scan= list_Cdr(scan)) {
	term_PrettyPrintIntern((TERM) list_Car(scan), Depth+1);
	if (!list_Empty(list_Cdr(scan)))
	  fputs(",\n", stdout);
      }
      putchar(')');
    }
    else {
      if (term_IsVariable(Term)) {
	symbol_Print(term_TopSymbol(Term));
      }
      else {
	putchar('(');
	symbol_Print(term_TopSymbol(Term));
	putchar(')');
      }
    }
  }
  else {
    term_PrintPrefix(Term);
  }
}

void term_PrettyPrint(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: none.
  SUMMARY: Prints the term hopefully more pretty to stdout.
***************************************************************/
{
  term_PrettyPrintIntern(Term, 0);
}


void term_FPrint(FILE* File,TERM Term)
/**************************************************************
  INPUT:   A file and a term.
  RETURNS: none.
  SUMMARY: Prints the term to the file.
  CAUTION: Uses the other term output functions.
***************************************************************/
{
  if (term_IsComplex(Term)) {
    putc('(', File);
    symbol_FPrint(File,term_TopSymbol(Term));
    putc(' ', File);
    term_TermListFPrint(File,term_ArgumentList(Term));
    putc(')', File);

  } else if (term_IsVariable(Term)) {

    symbol_FPrint(File,term_TopSymbol(Term));

  } else {

    /* term_IsConstant(Term) */
    putc('(', File);
    symbol_FPrint(File,term_TopSymbol(Term));
    putc(')', File);
  }
}


void term_TermListPrint(LIST List)
/**************************************************************
  INPUT:   A list of terms.
  RETURNS: None.
***************************************************************/
{
  for (; !list_Empty(List); List=list_Cdr(List)) {
    term_Print(list_Car(List)); fflush(stdout);
    if (!list_Empty(list_Cdr(List)))
      putchar(' ');
  }
}


void term_TermListFPrint(FILE* File, LIST List)
/**************************************************************
  INPUT:   A list of terms.
  RETURNS: None.
***************************************************************/
{
  for (; !list_Empty(List); List=list_Cdr(List)) {
    term_FPrint(File,list_Car(List));
    if (!list_Empty(list_Cdr(List)))
      putc(' ', File);
  }
}


void term_PrintPrefix(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: none.
  SUMMARY: Prints the term in prefix notation to stdout.
  CAUTION: Uses the other term output functions.
***************************************************************/
{
  if (term_IsComplex(Term)) {
    symbol_Print(term_TopSymbol(Term));
    putchar('(');
    term_TermListPrintPrefix(term_ArgumentList(Term));
    putchar(')');

  } else
    symbol_Print(term_TopSymbol(Term));
}


void term_FPrintPrefix(FILE* File, TERM Term)
/**************************************************************
  INPUT:   A file and a term.
  RETURNS: none.
  SUMMARY: Prints the term in prefix notation to the file.
  CAUTION: Uses the other term output functions.
***************************************************************/
{
  if (term_IsComplex(Term)) {
    symbol_FPrint(File,term_TopSymbol(Term));
    putc('(', File);
    term_TermListFPrintPrefix(File,term_ArgumentList(Term));
    putc(')', File);

  } else
    symbol_FPrint(File,term_TopSymbol(Term));
}


void term_TermListPrintPrefix(LIST List)
/**************************************************************
  INPUT:   A list of terms.
  RETURNS: None.
***************************************************************/
{
  for (; !list_Empty(List); List=list_Cdr(List)) {
    term_PrintPrefix(list_Car(List));
    if (!list_Empty(list_Cdr(List)))
      putchar(',');
  }
}


void term_TermListFPrintPrefix(FILE* File, LIST List)
/**************************************************************
  INPUT:   A list of terms.
  RETURNS: None.
***************************************************************/
{
  for (; !list_Empty(List); List=list_Cdr(List)) {
    term_FPrintPrefix(File,list_Car(List));
    if (!list_Empty(list_Cdr(List)))
      putc(',', File);
  }
}



void term_FPrintOtterPrefix(FILE* File, TERM Term)
/**************************************************************
  INPUT:   A file and a term.
  RETURNS: none.
  SUMMARY: Prints the term in prefix notation to the file.
  CAUTION: Uses the other term_Output functions.
***************************************************************/
{
  if (term_IsComplex(Term)) {
    symbol_FPrintOtter(File, term_TopSymbol(Term));
    putc('(', File);
    term_TermListFPrintOtterPrefix(File, term_ArgumentList(Term));
    putc(')', File);
  } else
    symbol_FPrintOtter(File, term_TopSymbol(Term));
}


void term_TermListFPrintOtterPrefix(FILE* File, LIST List)
/**************************************************************
  INPUT:   A list of terms.
  RETURNS: None.
***************************************************************/
{
  for (; !list_Empty(List); List=list_Cdr(List)) {
    term_FPrintOtterPrefix(File,list_Car(List));
    if (!list_Empty(list_Cdr(List)))
      putc(',', File);
  }
}


void term_FPrintPosition(FILE* File, TERM TopTerm, TERM Subterm)
/**************************************************************
  INPUT:   An output file and two terms where <Subterm> is a subterm
           of <TopTerm>.
  RETURNS: Nothing.
  SUMMARY: The position of <Subterm> relative to <TopTerm> is
           printed to the output file. A simple top-down search
	   is done, so the superterm pointers are not needed.
	   Note that we compare terms with respect to pointers!
	   If <Subterm> isn't a subterm of <TopTerm> at all,
	   this causes an error message followed by a core dump.
***************************************************************/
{
  NAT  pos;
  LIST Scan;

  if (TopTerm == Subterm)
    return;

  for (Scan = term_ArgumentList(TopTerm), pos = 1; !list_Empty(Scan);
       Scan = list_Cdr(Scan), pos++) {
    if (term_HasPointerSubterm(list_Car(Scan), Subterm)) {
      fprintf(File, "%u", pos);
      if (Subterm != list_Car(Scan)) {
	putc('.', File);
	term_FPrintPosition(File, list_Car(Scan), Subterm);
      }
      return;
    }
  }
  misc_StartErrorReport();
  misc_ErrorReport("\n In term_FPrintPosition: Term isn't subterm of the other one.");
  misc_FinishErrorReport();
}


/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *			HIGH LEVEL FUNCTIONS		    * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/

NAT term_Bytes(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: The number of bytes occupied by the term.
  EFFECT:  None
***************************************************************/
{
  NAT  Bytes;
  LIST Scan;

  Bytes = sizeof(TERM_NODE) + list_Bytes(term_ArgumentList(Term));
  for (Scan=term_ArgumentList(Term); !list_Empty(Scan); Scan=list_Cdr(Scan))
    Bytes += term_Bytes((TERM)list_Car(Scan));
  return Bytes;
}


LIST term_ListOfVariables(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: The list of variables occurring in the term.
           Note that there may be many terms with same variable symbol.
***************************************************************/
{
  LIST         Stack, Variables;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_ListOfVariables: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  Variables = list_Nil();
  Stack     = list_StackBottom();
  do {
    if (term_IsComplex(Term))
      Stack = list_Push(term_ArgumentList(Term),Stack);
    else
      if (term_IsVariable(Term))
	Variables = list_Cons(Term, Variables);
    while (!list_StackEmpty(Stack) && list_Empty(list_Top(Stack)))
      Stack = list_Pop(Stack);
    if (!list_StackEmpty(Stack)) {
      Term = (TERM)list_Car(list_Top(Stack));
      list_RplacTop(Stack, list_Cdr(list_Top(Stack)));
    }
  } while (!list_StackEmpty(Stack));
  return Variables;
}


void term_MarkVariables(TERM Term, NAT Mark)
/**************************************************************
  INPUT:   A term.
  RETURNS: Nothing.
  EFFECT:  All variables from <Term> are marked with <Mark>.
  CAUTION: The term module must be in a binding phase (started with
           term_StartBinding)!
***************************************************************/
{
  int Stack;

#ifdef CHECK
  if (!term_InBindingPhase()) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_MarkVariables:");
    misc_ErrorReport(" Called while not in binding phase.");
    misc_FinishErrorReport();
  }
#endif

  Stack = stack_Bottom();
  do {
    if (term_IsComplex(Term)) {
      stack_Push(term_ArgumentList(Term));
    }
    else if (term_IsVariable(Term))
      term_CreateBinding(term_TopSymbol(Term), Mark);
    while (!stack_Empty(Stack) && list_Empty(stack_Top()))
      stack_Pop();
    if (!stack_Empty(Stack)) {
      Term = (TERM)list_Car(stack_Top());
      stack_RplacTop(list_Cdr(stack_Top()));
    }
  } while (!stack_Empty(Stack));
}


LIST term_VariableSymbols(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: The list of variable symbols occurring in the term.
***************************************************************/
{
  LIST    Variables;
  int     Stack;
  SYMBOL  Top;
  NAT     ActMark;

#ifdef CHECK
  if (!term_IsTerm(Term) || term_InBindingPhase()) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_VariableSymbols: Illegal input or context.");
    misc_FinishErrorReport();
  }
#endif

  term_StartBinding();

  Variables = list_Nil();
  Stack     = stack_Bottom();
  ActMark   = term_ActMark();
  do {
    if (term_IsComplex(Term)) {
      stack_Push(term_ArgumentList(Term));
    }
    else {
      Top = term_TopSymbol(Term);
      if (symbol_IsVariable(Top) && !term_VarIsMarked(Top, ActMark)) {
	Variables = list_Cons((POINTER)Top, Variables);
	term_CreateBinding(Top, ActMark);
      }
    }
    while (!stack_Empty(Stack) && list_Empty(stack_Top()))
      stack_Pop();
    if (!stack_Empty(Stack)) {
      Term = (TERM)list_Car(stack_Top());
      stack_RplacTop(list_Cdr(stack_Top()));
    }
  } while (!stack_Empty(Stack));

  term_StopBinding();

  return Variables;
}


NAT term_NumberOfVarOccs(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: The list of variable symbols occurring in the term.
***************************************************************/
{
  NAT      Result;
  int      Stack;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_NumberOfVarOccs: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  Result = 0;
  Stack = stack_Bottom();
  do {
    if (term_IsComplex(Term)) {
      stack_Push(term_ArgumentList(Term));
    }
    else {
      if (symbol_IsVariable(term_TopSymbol(Term)))
	Result++;
    }
    while (!stack_Empty(Stack) && list_Empty(stack_Top()))
      stack_Pop();
    if (!stack_Empty(Stack)) {
      Term = (TERM)list_Car(stack_Top());
      stack_RplacTop(list_Cdr(stack_Top()));
    }
  } while (!stack_Empty(Stack));

  return Result;
}

NAT term_NumberOfSymbolOccurrences(TERM Term, SYMBOL Symbol)
/**************************************************************
  INPUT:   A term and a symbol.
  RETURNS: The number of occurrences of <Symbol> in <Term>
***************************************************************/
{
  NAT   Result;
  LIST  Scan;

#ifdef CHECK
  if (!term_IsTerm(Term) || !symbol_IsSymbol(Symbol)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_NumberOfSymbolOccurrences: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  Result = 0;
  
  if (symbol_Equal(term_TopSymbol(Term),Symbol))
    Result++;

  for (Scan = term_ArgumentList(Term); !list_Empty(Scan);  Scan=list_Cdr(Scan))
    Result += term_NumberOfSymbolOccurrences(list_Car(Scan), Symbol);

  return Result;
}


BOOL term_ContainsFunctions(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: TRUE iff the term contains a function symbol
***************************************************************/
{
  int      Stack;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_ContainsFunctions: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  Stack = stack_Bottom();
  do {
    if (term_IsComplex(Term)) {
      if (symbol_IsFunction(term_TopSymbol(Term)) && !symbol_IsConstant(term_TopSymbol(Term))) {
	stack_SetBottom(Stack);
	return TRUE;
      }
      stack_Push(term_ArgumentList(Term));
    }

    while (!stack_Empty(Stack) && list_Empty(stack_Top()))
      stack_Pop();
    if (!stack_Empty(Stack)) {
      Term = (TERM)list_Car(stack_Top());
      stack_RplacTop(list_Cdr(stack_Top()));
    }
  } while (!stack_Empty(Stack));

  return FALSE;
}

BOOL term_ContainsVariable(TERM Term, SYMBOL Var)
/**************************************************************
  INPUT:   A term and a variable symbol.
  RETURNS: TRUE iff the term contains the variable symbol
***************************************************************/
{
  int      Stack;

#ifdef CHECK
  if (!term_IsTerm(Term) || !symbol_IsSymbol(Var)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_ContainsVariable: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  Stack = stack_Bottom();
  do {
    if (term_IsComplex(Term))
      stack_Push(term_ArgumentList(Term));
    else
      if (symbol_Equal(term_TopSymbol(Term),Var)) {
	stack_SetBottom(Stack);
	return TRUE;
      }

    while (!stack_Empty(Stack) && list_Empty(stack_Top()))
      stack_Pop();
    if (!stack_Empty(Stack)) {
      Term = (TERM)list_Car(stack_Top());
      stack_RplacTop(list_Cdr(stack_Top()));
    }
  } while (!stack_Empty(Stack));

  return FALSE;
}

SYMBOL term_MaxVar(TERM Term)
/*********************************************************
  INPUT:   A term.
  RETURNS: The maximal variable in <Term>, NULL otherwise
********************************************************/
{
  LIST   Scan;
  int    Stack;
  SYMBOL Result;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_MaxVar: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  Result = (SYMBOL)NULL;
  Stack  = stack_Bottom();

  if (term_IsStandardVariable(Term)) {
    if (term_TopSymbol(Term)>Result)
      Result = term_TopSymbol(Term);
  }
  else
    if (term_IsComplex(Term))
      stack_Push(term_ArgumentList(Term));
  
  while (!stack_Empty(Stack)) {
    Scan = stack_Top();
    Term = (TERM)list_Car(Scan);
    stack_RplacTop(list_Cdr(Scan));
    
    if (term_IsStandardVariable(Term)) {
      if (term_TopSymbol(Term)>Result)
	Result = term_TopSymbol(Term);
    }
    else
      if (term_IsComplex(Term))
	stack_Push(term_ArgumentList(Term));
    
    while (!stack_Empty(Stack) && list_Empty(stack_Top()))
      stack_Pop();
  }
  
  return Result;
}



/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *			Renaming           		    * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/


void term_StartMinRenaming(void)
/**************************************************************
  INPUT:   None
  EFFECT:  Initializes the term and symbol modules for min co var renaming
***************************************************************/
{
  symbol_ResetStandardVarCounter();
  term_NewMark();
}


void term_StartMaxRenaming(SYMBOL MaxVar)
/**************************************************************
  INPUT:   A variable symbol.
  EFFECT:  Initializes the term and symbol modules for renaming above <MaxVar>
***************************************************************/
{
  symbol_SetStandardVarCounter(MaxVar);
  term_NewMark();
}


TERM term_Rename(TERM Term)
/**************************************************************
  INPUT:   A Term.
  RETURNS: The destructively renamed term.
  EFFECT:  All co variables are destructively renamed in <TERM>
***************************************************************/
{
  int     Stack;
  SYMBOL  Top;
  NAT     ActMark;
  TERM    ActTerm;
  
#ifdef CHECK
  if (!term_IsTerm(Term) || term_InBindingPhase()) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_Rename: Illegal input or context.");
    misc_FinishErrorReport();
  }
#endif

  term_StartBinding();
  
  Stack = stack_Bottom();
  ActMark = term_OldMark();
  ActTerm = Term;
  do {
    if (term_IsComplex(ActTerm)) {
      stack_Push(term_ArgumentList(ActTerm));
    }
    else {
      Top = term_TopSymbol(ActTerm);
      if (symbol_IsVariable(Top)) {
	if (!term_VarIsMarked(Top, ActMark))
	  term_CreateValueBinding(Top, ActMark, (POINTER)symbol_CreateStandardVariable());
	term_RplacTop(ActTerm,(SYMBOL)term_BindingValue(Top));
      }
    }
    
    while (!stack_Empty(Stack) && list_Empty(stack_Top()))
      stack_Pop();
    if (!stack_Empty(Stack)) {
      ActTerm = (TERM)list_Car(stack_Top());
      stack_RplacTop(list_Cdr(stack_Top()));
    }
  } while (!stack_Empty(Stack));

  term_StopBinding();
  
  return Term;
}

SYMBOL term_GetRenamedVarSymbol(SYMBOL Var)
/**************************************************************
  INPUT:   A variable symbol.
  RETURNS: The renamed variable for symbol for <var> with respect
           to the current renaming. If it does not exist, <var>
	   itself is returned.
  EFFECT:  None.
***************************************************************/
{
  NAT ActMark;

#ifdef CHECK
  if (!symbol_IsStandardVariable(Var)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_GetRenamedVarSymbol: Illegal input.");
    misc_FinishErrorReport();
  }
#endif
  
  ActMark = term_OldMark();
  
  if (term_VarIsMarked(Var, ActMark))
    return (SYMBOL)term_BindingValue(Var);

  return Var;
}


static LIST term_MakePseudoLinear(TERM Term, NAT Depth, NAT Mark)
/**************************************************************
  INPUT:   A Term and a variable and the current depth.
  RETURNS: A list of pairs (<oldvar>,<newvar>)
  EFFECT:  The term is destructively made pseudo_linear.
***************************************************************/
{
  LIST   Result,Scan;
  SYMBOL Top;

  Result = list_Nil();

  if (term_IsComplex(Term))
    for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan))
      Result = list_Nconc(term_MakePseudoLinear(list_Car(Scan),Depth+1,Mark),
			  Result);
  else {
    Top = term_TopSymbol(Term);
    if (symbol_IsVariable(Top)) {
      if (term_VarIsMarked(Top, Mark)) {
	if (Depth != (NAT)term_BindingValue(Top))
	  term_RplacTop(Term,symbol_CreateStandardVariable());
	Result = list_Cons(list_PairCreate((POINTER)Top,
					   (POINTER)term_TopSymbol(Term)),
			   Result);
      }
      else {
	term_CreateValueBinding(Top, Mark, (POINTER)Depth);
      }
    }
  }
  
  return Result;
}


LIST term_RenamePseudoLinear(TERM Term, SYMBOL Var)
/**************************************************************
  INPUT:   A Term and a variable.
  RETURNS: A list of pairs (<oldvar>,<newvar>)
  EFFECT:  The term is destructively renamed.
***************************************************************/
{
  NAT  Mark;
  LIST Result;

#ifdef CHECK
  if (!term_IsTerm(Term) || !symbol_IsVariable(Var) || term_InBindingPhase()) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_RenamePseudoLinear: Illegal input or context.");
    misc_FinishErrorReport();
  }
#endif
  
  term_StartBinding();
  symbol_SetStandardVarCounter(Var);

  term_NewMark();
  Mark   = term_ActMark();
  Result = term_MakePseudoLinear(Term,0,Mark);

  term_StopBinding();

  return Result;
}


/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *			STAMP FUNCTIONS  	            * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/

NAT term_GetStampID(void)
/**************************************************************
  INPUT:   None
  RETURNS: An identifier that must be used for some stamp functions
  EFFECT:  Each module using the term stamp has to request an
           identifier that is needed for function term_StampOverflow
           The purpose of this identifier is to synchronize
           different modules in case of an overflow of the variable
           term_STAMP.
***************************************************************/
{
  if (term_STAMPUSERS >= term_MAXSTAMPUSERS) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n In term_GetStampID: no more free stamp IDs.");
    misc_UserErrorReport("\n You have to increase the constant term_MAXSTAMPUSERS.");
    misc_FinishUserErrorReport();
  }

  return term_STAMPUSERS++;
}


BOOL term_StampOverflow(NAT ID)
/**************************************************************
  INPUT:   The identifier of the calling module as returned by
           the function term_GetStampID.
  RETURNS: True if an overflow of the variable term_STAMP occurred
           for the module with the identifier ID.
  CAUTION: If an overflow occurred for a module you can test that
           only once!!! After the first test the overflow flag
	   is cleared for that module.
***************************************************************/
{
  BOOL Result = FALSE;
  NAT i;

#ifdef CHECK
  if (ID >= term_MAXSTAMPUSERS) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_StampOverflow: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  if (term_STAMP == NAT_MAX) {
    term_STAMP = 0;
    /* set overflow flag for all other modules */
    for (i = 0; i < term_MAXSTAMPUSERS; i++)
      term_STAMPOVERFLOW[i] = TRUE;
    term_STAMPOVERFLOW[ID] = FALSE;
    Result = TRUE;
  } else if (term_STAMPOVERFLOW[ID]) {
    term_STAMPOVERFLOW[ID] = FALSE;
    Result = TRUE;
  }
  return Result;
}

void term_SetTermSubtermStamp(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: void.
  EFFECT:  Sets the current stamp to <Term> and its subterms.
***************************************************************/
{
#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_SetTermSubtermStamp: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  term_SetTermStamp(Term);
  list_Apply((void (*)(POINTER)) term_SetTermSubtermStamp,
	     term_ArgumentList(Term));
}

LIST term_ListOfAtoms(TERM Term, SYMBOL Predicate)
/**************************************************************
  INPUT:   A term and a predicate symbol.
  RETURNS: A list of pointers to all atoms in Term with
           predicate symbol <Predicate>.
***************************************************************/
{
  if (symbol_Equal(term_TopSymbol(Term), Predicate))
    return list_List(Term);
  else {
    LIST Result, List;

    Result = list_Nil();
    for (List = term_ArgumentList(Term); !list_Empty(List); List = list_Cdr(List))
      Result = list_Nconc(Result, term_ListOfAtoms(list_Car(List), Predicate));
    return Result;
  }
}

/* Currently only in CHECK mode */
#ifdef CHECK

void term_StartStamp(void)
/**************************************************************
  INPUT:   None
  RETURNS: Nothing
  EFFECT:  The stamp is prepared for a new term traversal.
***************************************************************/
{
  if (term_STAMPBLOCKED) {
    /* Error: the Stamp is already used */
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_StartStamp: Illegal context, term stamp is already used.");
    misc_FinishErrorReport();
  }
  else {
    term_STAMP++;
    term_STAMPBLOCKED = TRUE;
  }
}

#endif

LIST term_FindAllAtoms(TERM Term, SYMBOL Predicate)
/**********************************************************************
   INPUT:  A term Term and a symbol Predicate.
   RETURN: A list of all atoms of Term with Symbol as top symbol.
***********************************************************************/
{
  int stack;
  LIST Result;

#ifdef CHECK
  if (!term_IsTerm(Term) || !symbol_IsPredicate(Predicate)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In term_FindAllPredicates: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  stack  = stack_Bottom();
  Result = list_Nil();

  do {
    if (term_TopSymbol(Term) == Predicate) {
      Result = list_Cons(Term, Result);
    } else if (term_IsComplex(Term))
      stack_Push(term_ArgumentList(Term));

    while (!stack_Empty(stack) && list_Empty(stack_Top()))
      stack_Pop();

    if (!stack_Empty(stack)) {
      Term = list_Car(stack_Top());
      stack_RplacTop(list_Cdr(stack_Top()));
    }
  } while (!stack_Empty(stack));

  return Result;
}

BOOL term_CheckTermIntern(TERM Term, BOOL Links)
/**************************************************************************
  INPUT:  A term and a boolean.
  RETURN: True iff  1) the arity of each top symbol is equal to the number
                       of arguments of symbol's term.
		and 2) either all father links are set correctly iff Links is TRUE
		       or none is set iff Links is FALSE.
  COMMENT: Intern function of term_CheckTerm.
***************************************************************************/
{
  LIST Scan;
  SYMBOL Top;
  
  if (!term_IsTerm(Term))
    return FALSE;

  Top = term_TopSymbol(Term);
  if (symbol_IsSignature(Top) &&
      symbol_Arity(Top) != -1 &&
      symbol_Arity(Top) != (int)list_Length(term_ArgumentList(Term)))
    return FALSE;

  if (symbol_IsVariable(Top) && !list_Empty(term_ArgumentList(Term)))
    return FALSE;

  if (Links) {
    for (Scan = term_ArgumentList(Term); !list_Empty(Scan); Scan = list_Cdr(Scan)) {
      if (term_Superterm(list_Car(Scan)) != Term ||
	  !term_CheckTermIntern(list_Car(Scan), Links))
	return FALSE;
    }
  }
  else {
    for (Scan = term_ArgumentList(Term); !list_Empty(Scan); Scan = list_Cdr(Scan)) {
      if (term_Superterm(list_Car(Scan)) != term_Null() ||
	  !term_CheckTermIntern(list_Car(Scan), Links))
	return FALSE;
    }
  }
  return TRUE;
}

BOOL term_CheckTerm(TERM Term)
/********************************************************************************
   INPUT : A term Term.
   RETURN: TRUE iff  eihter all or no father links are set AND
                     the length of any argument list matches the arity of the respective symbol
*********************************************************************************/
{
  if (term_IsComplex(Term) &&
      term_Superterm(term_FirstArgument(Term)) != term_Null())
    /* check father links as well */
    return term_CheckTermIntern(Term, TRUE);
  else
    return term_CheckTermIntern(Term, FALSE);
}
