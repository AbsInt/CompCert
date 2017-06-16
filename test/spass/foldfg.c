/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *              FIRST ORDER LOGIC SYMBOLS                 * */
/* *                                                        * */
/* *  $Module:   FOL  DFG                                   * */ 
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


#include "foldfg.h"
#include "flags.h"


SYMBOL  fol_ALL;
SYMBOL  fol_EXIST;
SYMBOL  fol_AND;
SYMBOL  fol_OR;
SYMBOL  fol_NOT;
SYMBOL  fol_IMPLIES;
SYMBOL  fol_IMPLIED;
SYMBOL  fol_EQUIV;
SYMBOL  fol_VARLIST;
SYMBOL  fol_EQUALITY;
SYMBOL  fol_TRUE;
SYMBOL  fol_FALSE;

LIST    fol_SYMBOLS;

/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  FUNCTIONS                                             * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/

void fol_Init(BOOL All, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A boolean value determining whether only 'equality' or
           all fol symbols are created, and a precedence.
  RETURNS: Nothing.
  SUMMARY: Initializes the Fol Module.
  EFFECTS: If <All> then all fol-symbols are created,
           only 'equality' otherwise.
	   The precedence of the first order logic symbols is set
	   in <Precedence>.
  CAUTION: MUST BE CALLED BEFORE ANY OTHER fol-FUNCTION.
***************************************************************/
{ 
  if (All) {

    fol_ALL      = symbol_CreateJunctor("forall", 2, symbol_STATLEX, Precedence);
    fol_EXIST    = symbol_CreateJunctor("exists", 2, symbol_STATLEX, Precedence);
    fol_AND      = symbol_CreateJunctor("and", symbol_ArbitraryArity(),
					symbol_STATLEX, Precedence);
    fol_OR       = symbol_CreateJunctor("or", symbol_ArbitraryArity(),
					symbol_STATLEX, Precedence);
    fol_NOT      = symbol_CreateJunctor("not", 1, symbol_STATLEX, Precedence);
    fol_IMPLIES  = symbol_CreateJunctor("implies", 2, symbol_STATLEX, Precedence);
    fol_IMPLIED  = symbol_CreateJunctor("implied", 2, symbol_STATLEX, Precedence);
    fol_EQUIV    = symbol_CreateJunctor("equiv", 2, symbol_STATLEX, Precedence);
    fol_VARLIST  = symbol_CreateJunctor("", symbol_ArbitraryArity(),
					symbol_STATLEX, Precedence);
    fol_EQUALITY = symbol_CreatePredicate("equal", 2, symbol_STATLEX, Precedence);
    fol_TRUE     = symbol_CreatePredicate("true", 0, symbol_STATLEX, Precedence);
    fol_FALSE    = symbol_CreatePredicate("false", 0, symbol_STATLEX, Precedence);

    fol_SYMBOLS =
      list_Cons((POINTER)fol_ALL, list_Cons((POINTER)fol_EXIST, 
	list_Cons((POINTER)fol_AND, list_Cons((POINTER)fol_OR,
	  list_Cons((POINTER)fol_NOT,
	    list_Cons((POINTER)fol_IMPLIES, list_Cons((POINTER)fol_IMPLIED,
              list_Cons((POINTER)fol_EQUIV, list_Cons((POINTER)fol_VARLIST,
                list_Cons((POINTER)fol_EQUALITY, list_Cons((POINTER)fol_TRUE,
		  list_List((POINTER)fol_FALSE))))))))))));
  }
  else {
    fol_EQUALITY = symbol_CreatePredicate("equal", 2, symbol_STATLEX, Precedence);
    fol_NOT      = symbol_CreateJunctor("not", 1, symbol_STATLEX, Precedence);
    fol_SYMBOLS  = list_Cons((POINTER)fol_NOT, list_List((POINTER)fol_EQUALITY));
  }
}


SYMBOL fol_IsStringPredefined(const char* String)
/**************************************************************
  INPUT:   A string.
  RETURNS: The symbol iff String is a predefined fol string,
           symbol NULL otherwise
***************************************************************/
{
  LIST Scan;
  for (Scan=fol_SYMBOLS; !list_Empty(Scan); Scan=list_Cdr(Scan))
    if (string_Equal(String, symbol_Name((SYMBOL)list_Car(Scan))))
      return (SYMBOL)list_Car(Scan);
  return symbol_Null();
}


TERM fol_CreateQuantifier(SYMBOL Quantifier, LIST VarList, LIST Arguments)
/**************************************************************
  INPUT:   A symbol (which MUST be a fol quantifier),
           a list of variables that will be bound, and
           a list of arguments.
  RETURNS: A quantified term.
***************************************************************/
{                                                                  
#ifdef CHECK                                                          
  if (!fol_IsQuantifier(Quantifier)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In fol_CreateQuantifier: Symbol isn't FOL quantifier.\n");
    misc_FinishErrorReport();
  }
#endif                                                             
                                                                   
  return term_Create(Quantifier, list_Cons(term_Create(fol_Varlist(), VarList),
					   Arguments));  
}


TERM fol_CreateQuantifierAddFather(SYMBOL Quantifier, LIST VarList, LIST Arguments)
/**************************************************************
  INPUT:   A symbol (which MUST be a fol quantifier),
           a list of variables that will be bound, and
           a list of arguments.
	   In contrast to fol_CreateQuantifier the superterm members 
	   are set for the arguments.
  RETURNS: A quantified term.
***************************************************************/
{                                                                  
  return term_CreateAddFather(Quantifier,                                
			      list_Cons(term_CreateAddFather(fol_Varlist(), 
							     VarList),   
					Arguments));  
}


TERM fol_ComplementaryTerm(TERM Term)
/**************************************************************
  INPUT:   A formula.
  RETURNS: The (copied) complementary (in sign) formula of <Term>
***************************************************************/
{
  if (symbol_Equal(term_TopSymbol(Term), fol_Not()))
    return term_Copy((TERM)list_First(term_ArgumentList(Term)));
  else
    return term_Create(fol_Not(), list_List(term_Copy(Term)));
}


LIST fol_GetNonFOLPredicates(void)
/**************************************************************
  INPUT:   None.
  RETURNS: The list of all predicate symbols except the predefined
           FOL symbols.
***************************************************************/
{
  LIST Result;

  Result = symbol_GetAllPredicates();
  Result = list_DeleteElementIf(Result, (BOOL (*)(POINTER))fol_IsPredefinedPred);
  return Result;
}


LIST fol_GetAssignments(TERM Term)
/**************************************************************
  INPUT:   A formula.
  RETURNS: All assignemnts that occur inside the formula, i.e.,
           equations of the form "x=t" where "x" does not
	   occur in "t".
***************************************************************/
{
  if (term_IsAtom(Term)) {
    if (fol_IsAssignment(Term))
      return list_List(Term);
  }
  else
    if (term_IsComplex(Term)) {
      LIST Scan,Result;
      Result = list_Nil();
      for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan))
	Result = list_Nconc(fol_GetAssignments(list_Car(Scan)),Result);
      return Result;
    }

  return list_Nil();
  
}

static void fol_NormalizeVarsIntern(TERM Formula)
/**************************************************************
  INPUT:   A sentence.
  RETURNS: void.
  EFFECT:  The quantifier variables of the formula are
           normalized, i.e., no two different quantifiers
	   bind the same variable.
  CAUTION: Desctructive.
***************************************************************/
{
  SYMBOL   Top;
  LIST     Scan1;
  
#ifdef CHECK
  if (!term_IsTerm(Formula)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In fol_NormalizeVarsIntern: Formula is corrupted.\n");
    misc_FinishErrorReport();
  }
#endif

  Top = term_TopSymbol(Formula);
  
  if (term_IsComplex(Formula)) {
    if (fol_IsQuantifier(Top)) {
      SYMBOL    Var;
      LIST      OldVars,Scan2;
      OldVars = list_Nil();
      for (Scan1=fol_QuantifierVariables(Formula);!list_Empty(Scan1);Scan1=list_Cdr(Scan1)) {
	Var     = term_TopSymbol(list_Car(Scan1));
	OldVars = list_Nconc(OldVars,list_List((POINTER)term_BindingValue(Var)));
	term_CreateValueBinding(Var, term_OldMark(), (POINTER)symbol_CreateStandardVariable());
      }
      fol_NormalizeVarsIntern(term_SecondArgument(Formula));
      for (Scan1=fol_QuantifierVariables(Formula),Scan2=OldVars;
	   !list_Empty(Scan1);
	   Scan1=list_Cdr(Scan1),Scan2=list_Cdr(Scan2)) {
	Var     = term_TopSymbol(list_Car(Scan1));
	term_RplacTop(list_Car(Scan1),(SYMBOL)term_BindingValue(Var));
	term_CreateValueBinding(Var, term_OldMark(), list_Car(Scan2));
      }
      list_Delete(OldVars);
    }
    else
      for (Scan1=term_ArgumentList(Formula);!list_Empty(Scan1);Scan1=list_Cdr(Scan1))
	fol_NormalizeVarsIntern(list_Car(Scan1));
  }
  else 
    if (symbol_IsVariable(Top))
      term_RplacTop(Formula,(SYMBOL)term_BindingValue(Top));

  return;
}


void fol_NormalizeVars(TERM Formula)
/**************************************************************
  INPUT:   A sentence.
  RETURNS: void.
  EFFECT:  The quantifier variables of the formula are
           normalized, i.e., no two different quantifiers
	   bind the same variable.
  CAUTION: Destructive.
***************************************************************/
{
  symbol_ResetStandardVarCounter();
  term_NewMark();
  fol_NormalizeVarsIntern(Formula);
}


void fol_NormalizeVarsStartingAt(TERM Formula, SYMBOL S)
/**************************************************************
  INPUT:   A sentence.
  RETURNS: void.
  EFFECT:  The quantifier variables of the formula are
           normalized, i.e., no two different quantifiers
	   bind the same variable.
  CAUTION: Destructive.
***************************************************************/
{
  SYMBOL old = symbol_STANDARDVARCOUNTER;
  symbol_SetStandardVarCounter(S);
  term_NewMark();
  fol_NormalizeVarsIntern(Formula);
  symbol_SetStandardVarCounter(old);
}


void fol_RemoveImplied(TERM Formula)
/*********************************************************
  INPUT:   A formula.
  RETURNS: void.
  EFFECT:  All occurrences of "implied" are replaced by "implies"
  CAUTION: Destructive.
*******************************************************/
{
  if (!fol_IsLiteral(Formula)) {
    if (fol_IsQuantifier(term_TopSymbol(Formula)))
      fol_RemoveImplied(term_SecondArgument(Formula));
    else {
      LIST Scan;
      if (symbol_Equal(term_TopSymbol(Formula),fol_Implied())) {
	term_RplacTop(Formula,fol_Implies());
	term_RplacArgumentList(Formula,list_NReverse(term_ArgumentList(Formula)));
      }
      for (Scan=term_ArgumentList(Formula);!list_Empty(Scan);Scan=list_Cdr(Scan))
	fol_RemoveImplied(list_Car(Scan));
    }
  }
}
      

BOOL fol_VarOccursFreely(TERM Var,TERM Term)
/**************************************************************
  INPUT:   A variable and a term.
  RETURNS: TRUE iff <Var> occurs freely in <Term>
***************************************************************/
{ 
  LIST    Scan;
  int     Stack;
  SYMBOL  Top;
  BOOL    Hit;

#ifdef CHECK
  if (!term_IsTerm(Term) || !term_IsVariable(Var)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In fol_VarOccursFreely: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  Stack = stack_Bottom();

  do {
    Top = term_TopSymbol(Term);
    if (term_IsComplex(Term)) {
      if (fol_IsQuantifier(Top)) {
	Hit = TRUE;
	for (Scan=fol_QuantifierVariables(Term);!list_Empty(Scan)&&Hit;Scan=list_Cdr(Scan))
	  if (symbol_Equal(term_TopSymbol(list_Car(Scan)),term_TopSymbol(Var)))
	    Hit = FALSE;
	if (Hit)
	  stack_Push(list_Cdr(term_ArgumentList(Term)));
      }
      else
	stack_Push(term_ArgumentList(Term));
    }
    else {
      if (symbol_IsVariable(Top) && symbol_Equal(Top,term_TopSymbol(Var))) {
	stack_SetBottom(Stack);
	return TRUE;
      }
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


LIST fol_FreeVariables(TERM Term)
/**************************************************************
  INPUT:   A term where we assume that no variable is bound by more than
           one quantifier in <Term> !!!!!
  RETURNS: The list of variables occurring in the term. Variables are
           not (!) copied.
           Note that there may be many terms with same variable symbol.
	   All Variable terms are newly created.
***************************************************************/
{ 
  LIST    Variables,Scan;
  int     Stack;
  SYMBOL  Top;
  NAT     BoundMark,FreeMark;

#ifdef CHECK
  if (!term_IsTerm(Term) || term_InBindingPhase()) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In fol_FreeVariables: Illegal input or context.\n");
    misc_FinishErrorReport();
  }
#endif

  term_StartBinding();

  Variables  = list_Nil();
  Stack      = stack_Bottom();
  BoundMark  = term_ActMark();
  FreeMark   = term_ActMark();

  do {
    Top = term_TopSymbol(Term);
    if (term_IsComplex(Term)) {
      if (fol_IsQuantifier(Top)) {
	for (Scan=fol_QuantifierVariables(Term);!list_Empty(Scan);Scan=list_Cdr(Scan))
	  if (!term_VarIsMarked(term_TopSymbol(list_Car(Scan)), FreeMark))
	    term_CreateBinding(term_TopSymbol(list_Car(Scan)), BoundMark);
	stack_Push(term_ArgumentList(Term));                           /* Mark has to be removed ! */
	stack_Push(list_Cdr(term_ArgumentList(Term)));
      }
      else
	if (symbol_Equal(Top,fol_Varlist())) {
	  for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan))
	    if (!term_VarIsMarked(term_TopSymbol(list_Car(Scan)), FreeMark))
	      term_CreateBinding(term_TopSymbol(list_Car(Scan)), 0);  /* Mark has to be removed ! */
	  stack_RplacTop(list_Cdr(stack_Top()));                   /* Second Argument is Quantifier Arg */
	}
	else
	  stack_Push(term_ArgumentList(Term));
    }
    else {
      if (symbol_IsVariable(Top) && !term_VarIsMarked(Top, FreeMark) 
	  && !term_VarIsMarked(Top, BoundMark)) {
	Variables = list_Cons(Term, Variables);
	term_CreateBinding(Top, FreeMark);
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

LIST fol_BoundVariables(TERM Term)
/**************************************************************
  INPUT:   A term 
  RETURNS: The list of bound variables occurring in the term.
***************************************************************/
{
  int  stack;
  LIST result;

  stack  = stack_Bottom();
  result = list_Nil();

  do {
    if (fol_IsQuantifier(term_TopSymbol(Term))) {
      result = list_Nconc(result, list_Copy(fol_QuantifierVariables(Term))); 
      stack_Push(list_Cdr(term_ArgumentList(Term)));
    } 
    else 
      if (term_IsComplex(Term))
	stack_Push(term_ArgumentList(Term));
    
    while (!stack_Empty(stack) && list_Empty(stack_Top()))
      stack_Pop();

    if (!stack_Empty(stack)) {
      Term = list_Car(stack_Top());
      stack_RplacTop(list_Cdr(stack_Top()));
    }
  } while (!stack_Empty(stack));
  result = term_DeleteDuplicatesFromList(result);
  return result;
}


void fol_Free(void)
/**************************************************************
  INPUT:   None.
  RETURNS: void.
  EFFECT:  The memory used by the fol modul is freed.
***************************************************************/
{
  list_Delete(fol_SYMBOLS);
}


BOOL fol_FormulaIsClause(TERM Formula)
/**************************************************************
  INPUT:   A formula.
  RETURNS: TRUE, if <Formula> is a clause, FALSE otherwise.
***************************************************************/
{
  LIST LitList;

  if (term_TopSymbol(Formula) == fol_ALL)
    Formula = term_SecondArgument(Formula);

  if (term_TopSymbol(Formula) != fol_OR)
    return FALSE;
  
  LitList = term_ArgumentList(Formula);

  while (!list_Empty(LitList)) {
    if (!fol_IsLiteral(list_Car(LitList)))
      return FALSE;
    LitList = list_Cdr(LitList);
  }

  return TRUE;
}


void fol_FPrintOtterOptions(FILE* File, BOOL Equality,
			    FLAG_TDFG2OTTEROPTIONSTYPE Options)
/**************************************************************
  INPUT:   A file, a boolean flag and an Flag determining printed options.
  RETURNS: Nothing.
  SUMMARY: Prints Otter Options to <File>.
           If <Equality> then appropriate paramodulation options
	   are possibly added.
***************************************************************/
{
  switch (Options) {
  case flag_TDFG2OTTEROPTIONSPROOFCHECK:
    fputs("\nset(process_input).", File);
    fputs("\nset(binary_res).", File);
    fputs("\nset(factor).", File);
    /*fputs("\nassign(pick_given_ratio, 4).", File);*/
    fputs("\nclear(print_kept).", File);
    fputs("\nassign(max_seconds, 20).", File);
    if (Equality) {
      fputs("\nclear(print_new_demod).", File);
      fputs("\nclear(print_back_demod).", File);
      fputs("\nclear(print_back_sub).", File);
      /*fputs("\nset(knuth_bendix).", File);*/
      fputs("\nset(para_from).", File);
      fputs("\nset(para_into).", File);
      fputs("\nset(para_from_vars).", File);
      fputs("\nset(back_demod).", File);    
    } /* No break: add auto */
  case flag_TDFG2OTTEROPTIONSAUTO:
    fputs("\nset(auto).", File);
    break;
  case flag_TDFG2OTTEROPTIONSAUTO2:
    fputs("\nset(auto2).", File);
    break;
  case flag_TDFG2OTTEROPTIONSOFF:
     /* print nothing */
    break;
  default:
    misc_StartErrorReport();
    misc_ErrorReport("\n In fol_FPrintOtterOptions: Illegal parameter value %d.",
		     Options);
    misc_FinishErrorReport();
  }

  fputs("\n\n",File);
}

static void fol_FPrintOtterFormula(FILE* File, TERM Formula)
/**************************************************************
  INPUT:   A file and a formula.
  RETURNS: Nothing.
  SUMMARY: Prints the formula in Otter format to <File>. 
***************************************************************/
{
  SYMBOL Top;

  Top = term_TopSymbol(Formula);

  if (symbol_IsPredicate(Top)) {
    if (symbol_Equal(Top, fol_Equality())) {
      term_FPrintOtterPrefix(File,term_FirstArgument(Formula));
      fputs(" = ", File);
      term_FPrintOtterPrefix(File,term_SecondArgument(Formula));
    }
    else
      term_FPrintOtterPrefix(File,Formula);
  }
  else {
    if (fol_IsQuantifier(Top)) {
      LIST Scan;
      for (Scan=fol_QuantifierVariables(Formula);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
	if (symbol_Equal(Top,fol_All()))
	  fputs("all ", File);
	else
	  fputs("exists ", File);
	term_FPrintOtterPrefix(File, list_Car(Scan));
	fputs(" (", File);
      }
      fol_FPrintOtterFormula(File, term_SecondArgument(Formula));
      for (Scan=fol_QuantifierVariables(Formula);!list_Empty(Scan);Scan=list_Cdr(Scan))
	fputs(")", File);
    }
    else
      if (symbol_Equal(Top,fol_Not())) {
	fputs("- (", File);
	fol_FPrintOtterFormula(File, term_FirstArgument(Formula));
	fputs(")", File);
      }
      else
	if (symbol_Equal(Top, fol_And()) || symbol_Equal(Top, fol_Or()) || 
	    symbol_Equal(Top, fol_Equiv()) || symbol_Equal(Top, fol_Implies()) ) {
	  LIST Scan;
	  fputs("(", File);
	  for (Scan=term_ArgumentList(Formula);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
	    if (fol_IsLiteral(list_Car(Scan)))
	      fol_FPrintOtterFormula(File, list_Car(Scan));
	    else {
	      fputs("(", File);
	      fol_FPrintOtterFormula(File, list_Car(Scan));
	      fputs(")", File);
	    }
	    if (!list_Empty(list_Cdr(Scan))) {
	      if (symbol_Equal(Top, fol_And()))
		fputs(" & ", File);
	      if (symbol_Equal(Top, fol_Or()))
		fputs(" | ", File);
	      if (symbol_Equal(Top, fol_Equiv()))
		fputs(" <-> ", File);
	      if (symbol_Equal(Top, fol_Implies()))
		fputs(" -> ", File);
	    }
	  }
	  fputs(")", File);
	}
  }
}

void fol_FPrintOtter(FILE* File, LIST Formulae, FLAG_TDFG2OTTEROPTIONSTYPE Option)
/**************************************************************
  INPUT:   A file, a list of pairs (label.formula) and an option flag.
  RETURNS: Nothing.
  SUMMARY: Prints a  the respective formulae in Otter format to <File>. 
***************************************************************/
{
  LIST   Scan;
  BOOL   Equality;
  TERM   Formula;

  Equality = FALSE;

  for (Scan=Formulae;!list_Empty(Scan) && !Equality; Scan=list_Cdr(Scan)) {
    Formula  = (TERM)list_PairSecond(list_Car(Scan));
    Equality = term_ContainsSymbol(Formula, fol_Equality());
  }

  fol_FPrintOtterOptions(File, Equality, Option);

  if (!list_Empty(Formulae)) {
    fputs("formula_list(usable).\n", File);
    if (Equality)
      fputs("all x (x=x).\n", File);
    for (Scan=Formulae;!list_Empty(Scan);Scan=list_Cdr(Scan)) {
      if (list_PairFirst(list_Car(Scan)) != NULL)
	fprintf(File,"\n%% %s \n",(char *)list_PairFirst(list_Car(Scan)));
      fol_FPrintOtterFormula(File,list_PairSecond(list_Car(Scan)));
      fputs(".\n\n", File);
    }
    fputs("end_of_list.\n\n", File);
  }
}


void fol_FPrintDFGSignature(FILE* File)
/**************************************************************
  INPUT:   A file stream.
  RETURNS: Nothing.
  SUMMARY: Prints all signature symbols in DFG format to the
           file stream.
***************************************************************/

{
  NAT    i;
  SYMBOL symbol;
  LIST   functions, predicates;

  functions  = symbol_GetAllFunctions();
  predicates = fol_GetNonFOLPredicates();

  /* First print the function symbols */
  if (!list_Empty(functions)) {
    fputs("  functions[", File);
    i = 0;
    do {
      symbol = (SYMBOL) list_Top(functions);
      fprintf(File, "(%s, %d)", symbol_Name(symbol), symbol_Arity(symbol));
      functions = list_Pop(functions);
      if (!list_Empty(functions))
	fputs(", ", File);
      if (i < 15)
	i++;
      else {
	i = 0;
	fputs("\n\t", File);
      }
      
    } while (!list_Empty(functions));
    fputs("].\n", File);
  }

  /* Now print the predicate symbols */
  if (!list_Empty(predicates)) {
    i = 0;
    fputs("  predicates[", File);
    do {
      symbol = (SYMBOL) list_Top(predicates);
      fprintf(File, "(%s, %d)", symbol_Name(symbol), symbol_Arity(symbol));
      predicates = list_Pop(predicates);
      if (!list_Empty(predicates))
	fputs(", ", File);
      if (i < 15)
	i++;
      else {
	i = 0;
	fputs("\n\t", File);
      }
    } while (!list_Empty(predicates));
    fputs("].\n", File);
  }
  list_Delete(predicates);
  list_Delete(functions);
}


static void fol_TermListFPrintDFG(FILE* File, LIST List)
/**************************************************************
  INPUT:   A list of terms.
  RETURNS: Nothing.
***************************************************************/
{
  for (; !list_Empty(List); List=list_Cdr(List)) {
    fol_FPrintDFG(File,list_Car(List));
    if (!list_Empty(list_Cdr(List)))
      putc(',', File);
  }
}


void fol_FPrintDFG(FILE* File, TERM Term)
/**************************************************************
  INPUT:   A file and a term.
  RETURNS: none.
  SUMMARY: Prints the term in prefix notation to the file. 
  CAUTION: Uses the other fol_Output functions.
***************************************************************/
{
  if (term_IsComplex(Term)) {
    if (fol_IsQuantifier(term_TopSymbol(Term))) {
      symbol_FPrint(File,term_TopSymbol(Term));
      fputs("([", File);
      fol_TermListFPrintDFG(File,fol_QuantifierVariables(Term));
      fputs("],", File);
      fol_FPrintDFG(File, term_SecondArgument(Term));
      putc(')', File);
    }
    else {
      symbol_FPrint(File,term_TopSymbol(Term));
      putc('(', File);
      fol_TermListFPrintDFG(File,term_ArgumentList(Term));
      putc(')', File);
    }
  }
  else 
    symbol_FPrint(File,term_TopSymbol(Term));
}

void fol_PrintDFG(TERM Term)
{
  fol_FPrintDFG(stdout,Term);
}


void fol_PrintPrecedence(PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A precedence.
  RETURNS: void
  EFFECT:  Prints the current precedence to stdout,
           fol symbols are excluded.
***************************************************************/
{
  if (symbol_SignatureExists()) {
    LIST      Symbols, Scan;
    SYMBOL    Symbol;
    int       Index;
    SIGNATURE S;

    Symbols = list_Nil();
    for (Index = 1; Index < symbol_ACTINDEX; Index++) {
      S = symbol_Signature(Index);
      if (S != NULL) {
	Symbol = S->info;
	if  ((symbol_IsPredicate(Symbol) || symbol_IsFunction(Symbol)) &&
	     !fol_IsPredefinedPred(Symbol))
	  Symbols = list_Cons((POINTER)Symbol, Symbols);
      }
    }
    Symbols = symbol_SortByPrecedence(Symbols, Precedence);
    for (Scan = Symbols; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
      S = symbol_Signature(symbol_Index((SYMBOL)list_Car(Scan)));
      fputs(S->name, stdout);
      if (!list_Empty(list_Cdr(Scan)))
	fputs(" > ", stdout);
    }
    list_Delete(Symbols);
  }
}

void fol_FPrintPrecedence(FILE *File, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A file to print to, and a precedence.
  RETURNS: Nothing.
  EFFECT:  Prints the current precedence as a setting 
           command in DFG syntax to <File>.
	   fol symbols are excluded.
***************************************************************/
{
  if (symbol_SignatureExists()) {
    LIST      Symbols, Scan;
    SYMBOL    Symbol;
    int       Index;
    SIGNATURE S;

    Symbols = list_Nil();
    for (Index = 1; Index < symbol_ACTINDEX; Index++) {
      S = symbol_Signature(Index);
      if (S != NULL) {
	Symbol = S->info;
	if ((symbol_IsPredicate(Symbol) || symbol_IsFunction(Symbol)) &&
	    !fol_IsPredefinedPred(Symbol))
	  Symbols = list_Cons((POINTER)Symbol, Symbols);
      }
    }
    Symbols = symbol_SortByPrecedence(Symbols, Precedence);
    Index   = 0;
    fputs("set_precedence(", File);
    for (Scan = Symbols; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
      S = symbol_Signature(symbol_Index((SYMBOL)list_Car(Scan)));
      putc('(', File);
      fputs(S->name, File);
      putc(',', File);
      fprintf(File, "%d", S->weight);
      putc(',', File);
      putc((symbol_HasProperty((SYMBOL)list_Car(Scan),ORDRIGHT) ? 'r' :
	    (symbol_HasProperty((SYMBOL)list_Car(Scan),ORDMUL) ? 'm' : 'l')),
	   File);
      putc(')', File);
      if (!list_Empty(list_Cdr(Scan)))
	putc(',', File);

      if (Index > 15) {
	Index = 0;
	fputs("\n\t", File);
      }
      else
	Index++;
    }
    fputs(").", File);
    list_Delete(Symbols);
  }
}


static void fol_FPrintFormulaList(FILE* File, LIST Formulas, const char* Name)
/**************************************************************
  INPUT:   A file, a list of formulas, a name.
  EFFECTS: Print a list formulas in DFG format, with given list name.
 **************************************************************/
{
  LIST scan;

  fputs("list_of_formulae(", File);
  fputs(Name, File);
  fputs(").\n", File);
  for (scan = Formulas; !list_Empty(scan); scan= list_Cdr(scan)) {
    fputs("\tformula(", File);
    fol_FPrintDFG(File, list_Car(scan));
    fputs(").\n", File);
  }
  fputs("end_of_list.\n\n", File);
}


void fol_FPrintDFGProblem(FILE* File, const char* Name, const char* Author, 
			  const char* Status, const char* Description, 
			  LIST Axioms, LIST Conjectures)
/**************************************************************
  INPUT:   A file, two lists of formulas, ??? EK
  EFFECTS: Prints a complete DFG file containing these lists.
**************************************************************/
{
  fputs("begin_problem(Unknown).\n\n", File);

  fputs("list_of_descriptions.\n", File);
  fprintf(File,"name(%s).\n",Name);
  fprintf(File,"author(%s).\n",Author);
  fprintf(File,"status(%s).\n",Status);
  fprintf(File,"description(%s).\n",Description);
  fputs("end_of_list.\n\n", File);
  
  fputs("list_of_symbols.\n", File);
  fol_FPrintDFGSignature(File);
  fputs("end_of_list.\n\n", File);

  fol_FPrintFormulaList(File, Axioms, "axioms");
  fol_FPrintFormulaList(File, Conjectures, "conjectures");

  fputs("end_problem.\n", File);
}


BOOL fol_AssocEquation(TERM Term, SYMBOL *Result)
/**************************************************************
  INPUT:   A term.
  RETURNS: TRUE if the term is an equation defining associativity
           for some function symbol.
  EFFECT:  If the <Term> is an assoc equation, then <*Result> is
           assigned the assoc symbol.
***************************************************************/
{
  
  if (fol_IsEquality(Term)) {
    SYMBOL Top;
    TERM   Left,Right;
    Left = term_FirstArgument(Term);
    Right= term_SecondArgument(Term);
    Top  = term_TopSymbol(Left);
    if (symbol_IsFunction(Top) && symbol_Arity(Top) == 2 && 
	symbol_Equal(Top,term_TopSymbol(Right))) {
      SYMBOL v1,v2,v3;
      if (term_IsVariable(term_FirstArgument(Left)))
	v1 = term_TopSymbol(term_FirstArgument(Left));
      else
	if (term_IsVariable(term_FirstArgument(Right))) {
	  Term  = Right;
	  Right = Left;
	  Left  = Term;
	  v1 = term_TopSymbol(term_FirstArgument(Left));
	}
	else
	  return FALSE;
      if (symbol_Equal(term_TopSymbol(term_SecondArgument(Left)),Top) &&
	  symbol_IsVariable((v2=term_TopSymbol(term_FirstArgument(term_SecondArgument(Left)))))&&
	  symbol_IsVariable((v3=term_TopSymbol(term_SecondArgument(term_SecondArgument(Left)))))&&
	  symbol_Equal(term_TopSymbol(term_FirstArgument(Right)),Top) &&
	  symbol_Equal(v1,term_TopSymbol(term_FirstArgument(term_FirstArgument(Right)))) &&
	  symbol_Equal(v2,term_TopSymbol(term_SecondArgument(term_FirstArgument(Right)))) &&
	  symbol_Equal(v3,term_TopSymbol(term_SecondArgument(Right)))) {
	*Result = Top;
	return TRUE;
      }
    }
  }

  return FALSE;
}


BOOL fol_DistributiveEquation(TERM Term, SYMBOL* Addition,
			      SYMBOL* Multiplication)
/**************************************************************
  INPUT:   A term.
  RETURNS: TRUE if the term is an equation defining distributivity
           for two function symbols, FALSE otherwise.
  EFFECT:  If the function returns TRUE, < Addition> and
           <Multiplication> return the respective symbols.
***************************************************************/
{
  TERM left, right, help, v1, v2, v3;

  if (!fol_IsEquality(Term))
    return FALSE;

  left  = term_FirstArgument(Term);
  right = term_SecondArgument(Term);
  
  if (term_EqualTopSymbols(left, right) ||
      !symbol_IsFunction(term_TopSymbol(left)) ||
      !symbol_IsFunction(term_TopSymbol(right)) ||
      symbol_Arity(term_TopSymbol(left)) != 2 ||
      symbol_Arity(term_TopSymbol(right)) != 2)
    return FALSE;
  
  if (term_IsVariable(term_FirstArgument(left)))
    v1 = term_FirstArgument(left);
  else if (term_IsVariable(term_FirstArgument(right))) {
    help  = right;   /* Exchange left and right terms */
    right = left;
    left  = help;
    v1 = term_FirstArgument(left);
  } else
    return FALSE;

  if (!term_EqualTopSymbols(left, term_FirstArgument(right)) ||
      !term_EqualTopSymbols(left, term_SecondArgument(right)) ||
      !term_EqualTopSymbols(term_SecondArgument(left), right))
    return FALSE;

  v2 = term_FirstArgument(term_SecondArgument(left));
  v3 = term_SecondArgument(term_SecondArgument(left));

  if (term_IsVariable(v2) && term_IsVariable(v3) &&
      term_EqualTopSymbols(term_FirstArgument(term_FirstArgument(right)), v1) &&
      term_EqualTopSymbols(term_SecondArgument(term_FirstArgument(right)), v2) &&
      term_EqualTopSymbols(term_FirstArgument(term_SecondArgument(right)), v1) &&
      term_EqualTopSymbols(term_SecondArgument(term_SecondArgument(right)), v3)) {
    *Addition       = term_TopSymbol(right);
    *Multiplication = term_TopSymbol(left);
    return TRUE;
  }

  return FALSE;
}


static LIST fol_InstancesIntern(TERM Formula, TERM ToMatch, NAT Symbols)
/**************************************************************
  INPUT:   A formula in which all instances of <ToMatch> are searched.
	   The number of symbols of <ToMatch>.
  RETURNS: The list of found instances.
  CAUTION: Bound variables must be different, for otherwise the
           used matching produces wrong results!!
***************************************************************/
{
  NAT  HitSymbols;
  LIST Result;
  int  Stack;
  
  Stack  = stack_Bottom();
  Result = list_Nil();

  do {    
    HitSymbols = term_Size(Formula);    /* First check number of symbols of current formula */

    if (HitSymbols >= Symbols && (Formula != ToMatch)) {
      cont_StartBinding();
      if (unify_MatchFlexible(cont_LeftContext(), ToMatch, Formula))
	Result = list_Cons(Formula, Result);
      else 
	if (!symbol_IsPredicate(term_TopSymbol(Formula))) {
	  if (fol_IsQuantifier(term_TopSymbol(Formula)))
	    stack_Push(list_Cdr(term_ArgumentList(Formula)));
	  else
	    stack_Push(term_ArgumentList(Formula));
	}
      cont_BackTrack();
    }
    
    while (!stack_Empty(Stack) && list_Empty(stack_Top()))
      stack_Pop();
    if (!stack_Empty(Stack)) {
      Formula = (TERM)list_Car(stack_Top());
      stack_RplacTop(list_Cdr(stack_Top()));
    }
  } while (!stack_Empty(Stack));
  
  return Result;
}
 
   
LIST fol_Instances(TERM Formula, TERM ToMatch)
/**************************************************************
  INPUT:   A formula in which all instances of <ToMatch> are searched.
  RETURNS: The list of found occurrences matched by <ToMatch>.
           The formula <ToMatch> is not included!
***************************************************************/
{
  NAT Symbols;
  
  Symbols = term_ComputeSize(ToMatch); /* We use the number of symbols as a filter */
  term_InstallSize(Formula);

  return fol_InstancesIntern(Formula, ToMatch, Symbols);
}


static LIST fol_GeneralizationsIntern(TERM Formula, TERM MatchedBy, NAT Symbols)
/**************************************************************
  INPUT:   A formula in which all instances of <ToMatch> are searched.
	   The number of symbols of <ToMatch>.
  RETURNS: The list of found instances.
  CAUTION: Bound variables must be different, for otherwise the
           used matching produces wrong results!!
***************************************************************/
{
  NAT  HitSymbols;
  LIST Result;
  int  Stack;
  
  Stack  = stack_Bottom();
  Result = list_Nil();

  do {    
    if (Formula != MatchedBy) {
      HitSymbols = term_Size(Formula);    /* First check number of symbols of current formula */
      if (HitSymbols <= Symbols) {
	cont_StartBinding();
	if (unify_MatchFlexible(cont_LeftContext(), Formula, MatchedBy))
	  Result = list_Cons(Formula, Result);
	else 
	  if (!symbol_IsPredicate(term_TopSymbol(Formula))) {
	    if (fol_IsQuantifier(term_TopSymbol(Formula)))
	      stack_Push(list_Cdr(term_ArgumentList(Formula)));
	    else
	      stack_Push(term_ArgumentList(Formula));
	  }
	cont_BackTrack();
      }
      else
	if (!symbol_IsPredicate(term_TopSymbol(Formula))) {
	  if (fol_IsQuantifier(term_TopSymbol(Formula)))
	    stack_Push(list_Cdr(term_ArgumentList(Formula)));
	  else
	    stack_Push(term_ArgumentList(Formula));
	}
    }
    
    while (!stack_Empty(Stack) && list_Empty(stack_Top()))
      stack_Pop();
    if (!stack_Empty(Stack)) {
      Formula = (TERM)list_Car(stack_Top());
      stack_RplacTop(list_Cdr(stack_Top()));
    }
  } while (!stack_Empty(Stack));
  
  return Result;
}


LIST fol_Generalizations(TERM Formula, TERM MatchedBy)
/**************************************************************
  INPUT:   A formula in which all first-order generalizations of <MatchedBy> are searched.
  RETURNS: The list of found occurrences that are more general than <MatchedBy>.
           The formula <MatchedBy> is not included!
***************************************************************/
{
  NAT Symbols;
  
  Symbols = term_ComputeSize(MatchedBy); /* We use the number of symbols as a filter */
  term_InstallSize(Formula);

  return fol_GeneralizationsIntern(Formula, MatchedBy, Symbols);
}


TERM fol_MostGeneralFormula(LIST Formulas)
/**************************************************************
  INPUT:   A list of formulas.
  RETURNS: A most general formula out of the list, i.e., if
           some formula is returned, there is no formula in the
	   list that is more general than that formula.
***************************************************************/
{
  TERM Result, Candidate;
  LIST Scan;

#ifdef CHECK
  if (list_Empty(Formulas)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In fol_MostGeneralFormula: Called with empty list.\n");
    misc_FinishErrorReport();
  }
#endif

  Result = list_Car(Formulas);

  for (Scan=list_Cdr(Formulas);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
    Candidate = (TERM)list_Car(Scan);
    cont_StartBinding();
    if (unify_MatchFlexible(cont_LeftContext(), Candidate, Result))
      Result = Candidate;
    cont_BackTrack();
  }

  return Result;
}


void fol_ReplaceVariable(TERM Term, SYMBOL Symbol, TERM Repl)
/**************************************************************
  INPUT:   A term, a variable symbol and a replacement term.
  RETURNS: void
  EFFECT:  All free variables with <Symbol> in <Term> are replaced with copies of <Repl>
  CAUTION: Destructive
***************************************************************/
{
  LIST Scan;

#ifdef CHECK
  if (!(term_IsTerm(Term) && term_IsTerm(Repl) && symbol_IsVariable(Symbol))) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In fol_ReplaceVariable: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  if (fol_IsQuantifier(term_TopSymbol(Term))) {
    for (Scan=term_ArgumentList(term_FirstArgument(Term)); !list_Empty(Scan); Scan=list_Cdr(Scan))
      if (symbol_Equal(term_TopSymbol(list_Car(Scan)), Symbol)) /* var is bound */
	return;
    fol_ReplaceVariable(term_SecondArgument(Term), Symbol, Repl);
  }
    
  if (symbol_Equal(term_TopSymbol(Term), Symbol)) {
    term_RplacTop(Term,term_TopSymbol(Repl));
    term_RplacArgumentList(Term,term_CopyTermList(term_ArgumentList(Repl)));
  } 
  else 
    for (Scan = term_ArgumentList(Term); !list_Empty(Scan); Scan = list_Cdr(Scan))
      fol_ReplaceVariable(list_Car(Scan),Symbol,Repl);
}


static void fol_PrettyPrintInternDFG(TERM Term, int Depth)
/**************************************************************
  INPUT:   A term and a depth parameter for indentation.
  RETURNS: none.
  SUMMARY: Prints the term hopefully more pretty to stdout.
***************************************************************/
{
  int     i;
  LIST   scan;
  SYMBOL Top;

  Top = term_TopSymbol(Term);
  if (!symbol_Equal(Top,fol_Varlist())) {
    for (i = 0; i < Depth; i++) 
      fputs("  ", stdout);
    if (fol_IsLiteral(Term))
      term_PrintPrefix(Term);
    else {
      if (symbol_IsJunctor(Top)) {
	if (term_IsComplex(Term)) {
	  symbol_Print(Top);
	  putchar('(');
	  if (!fol_IsQuantifier(Top))
	    putchar('\n');
	  for (scan=term_ArgumentList(Term); !list_Empty(scan); scan= list_Cdr(scan)) {
	    fol_PrettyPrintInternDFG((TERM) list_Car(scan), Depth+1);
	    if (!list_Empty(list_Cdr(scan)))
	      fputs(",\n", stdout);
	  }
	  putchar(')');
	}
	else {
	  if (term_IsVariable(Term)) {
	    symbol_Print(Top);
	  }
	  else {
	    putchar('(');
	    symbol_Print(Top);
	    putchar(')');
	  }
	}
      }
      else {
	term_PrintPrefix(Term);
      }
    }
  }
  else {
    putchar('[');
    term_TermListPrintPrefix(term_ArgumentList(Term));
    putchar(']');
  }  
}


void fol_PrettyPrintDFG(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: none.
  SUMMARY: Prints the term hopefully more pretty to stdout. 
***************************************************************/
{
  fol_PrettyPrintInternDFG(Term, 0);
}


TERM fol_CheckFatherLinksIntern(TERM Term) 
/**************************************************************
  INPUT:   A term.
  RETURNS: A subterm whose superterm pointer is not set correctly,
           else NULL.
  SUMMARY: Checks if all superterm links except of those from quantifier
           variables are set correctly.
***************************************************************/ 
{
  LIST l;
  if (fol_IsQuantifier(term_TopSymbol(Term)))
    return fol_CheckFatherLinksIntern(term_SecondArgument(Term));
  if (term_IsComplex(Term)) {
    for (l=term_ArgumentList(Term); !list_Empty(l); l=list_Cdr(l)) {
      TERM result;
      if (term_Superterm((TERM) list_Car(l)) != Term)
	return (TERM) list_Car(l);
      result = fol_CheckFatherLinksIntern((TERM) list_Car(l));
      if (result != NULL)
	return result;
    }
  }
  return NULL;
}


void fol_CheckFatherLinks(TERM Term) 
/**************************************************************
  INPUT:   A term.
  RETURNS: none.
  SUMMARY: Checks if all superterm links except of those from
           quantifier variables are set correctly.
***************************************************************/ 
{
  TERM Result;

  Result = fol_CheckFatherLinksIntern(Term);
#ifdef CHECK
  if (Result != NULL || term_Superterm(Term) != NULL) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In fol_CheckFatherLinks:");
    misc_ErrorReport(" Found a term where the father links");
    misc_ErrorReport(" are not correctly set.");
    misc_FinishErrorReport();    
  }
#endif
}


static void fol_PrettyPrintIntern(TERM Term, int Depth)
/**************************************************************
  INPUT:   A term and a depth parameter for indentation.
  RETURNS: none.
  SUMMARY: Prints the term hopefully more pretty to stdout.
***************************************************************/
{
  int i;
  LIST scan;

  for (i = 0; i < Depth; i++) 
    fputs("  ", stdout);
  if (symbol_IsJunctor(term_TopSymbol(Term))) {
    if (term_IsComplex(Term)) {
      if (fol_IsQuantifier(term_TopSymbol(Term))) {
	symbol_Print(term_TopSymbol(Term));
	fputs("([", stdout);
	for (scan=fol_QuantifierVariables(Term); !list_Empty(scan); scan=list_Cdr(scan)) {
	  symbol_Print(term_TopSymbol((TERM) list_Car(scan)));
	  if (!list_Empty(list_Cdr(scan)))
	    putchar(',');
	}
	fputs("],\n", stdout);
	fol_PrettyPrintIntern(term_SecondArgument(Term), Depth+1);
      }
      else {
	symbol_Print(term_TopSymbol(Term));
	fputs("(\n", stdout);
	for (scan=term_ArgumentList(Term); !list_Empty(scan); scan= list_Cdr(scan)) {
	  fol_PrettyPrintIntern((TERM) list_Car(scan), Depth+1);
	  if (!list_Empty(list_Cdr(scan)))
	    fputs(",\n", stdout);
	}
	putchar(')');
      }
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


void fol_PrettyPrint(TERM Term)  
/**************************************************************
  INPUT:   A term.
  RETURNS: none.
  SUMMARY: Prints the term hopefully more pretty to stdout. 
***************************************************************/
{
  fol_PrettyPrintIntern(Term, 0);
}


LIST fol_GetSubstEquations(TERM Term)
/**************************************************************
  INPUT:   A Term.
  RETURNS: The list of all equations of the form x=t or t=x in <Term>
           where x is a variable and t is a term not containing x.
***************************************************************/
{
  LIST Result;
  LIST Scan;

  Result = list_Nil();

  if (fol_IsQuantifier(term_TopSymbol(Term)))
    return fol_GetSubstEquations(term_SecondArgument(Term));
  if (fol_IsEquality(Term)) {
    if (term_IsVariable(term_SecondArgument(Term))) {
      if (!term_ContainsSymbol(term_FirstArgument(Term), term_TopSymbol(term_SecondArgument(Term))))
	Result = list_Cons(Term, Result);
    }
    else {
      if (term_IsVariable(term_FirstArgument(Term)))
	if (!term_ContainsSymbol(term_SecondArgument(Term), term_TopSymbol(term_FirstArgument(Term))))
	  Result = list_Cons(Term, Result);
    }
  }
  if (symbol_IsPredicate(term_TopSymbol(Term)))
    return Result;
  else 
    for (Scan = term_ArgumentList(Term); !list_Empty(Scan); Scan = list_Cdr(Scan))
      Result = list_Nconc(Result, fol_GetSubstEquations(list_Car(Scan)));

  return Result;
}


TERM fol_GetBindingQuantifier(TERM Term, SYMBOL Symbol)
/**************************************************************
  INPUT:   A symbol and a term containing the symbol.
  RETURNS: The Quantifier binding the symbol.
***************************************************************/
{ 
  LIST Scan;

#ifdef CHECK
  if (!term_IsTerm(Term) || !symbol_IsSymbol(Symbol)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In fol_GetBindingQuantifier: Illegal input.\n");
    misc_FinishErrorReport();    
  }
#endif

  if (fol_IsQuantifier(term_TopSymbol(Term))) {
    for ( Scan = fol_QuantifierVariables(Term); !list_Empty(Scan); Scan = list_Cdr(Scan))
      if (symbol_Equal(Symbol, term_TopSymbol(list_Car(Scan)))) {
	return Term;
      }
  }

  return fol_GetBindingQuantifier(term_Superterm(Term), Symbol);
}


int fol_TermPolarity(TERM SubTerm, TERM Term)
/**************************************************************
  INPUT:   Two terms, SubTerm subterm of Term.
           It is assumed that the superterm links in <Term>
	   are established.
  RETURNS: The polarity of SubTerm in Term.
***************************************************************/
{
  TERM SuperTerm;

#ifdef CHECK
  if (!term_IsTerm(SubTerm) || !term_IsTerm(Term) || !term_FatherLinksEstablished(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In fol_TermPolarity: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  if (SubTerm == Term)
    return 1;
  
  SuperTerm = term_Superterm(SubTerm);

  if (SuperTerm) {
    SYMBOL Top;
    Top = term_TopSymbol(SuperTerm);

    if (symbol_Equal(Top,fol_AND) || symbol_Equal(Top,fol_OR) || fol_IsQuantifier(Top))
      return fol_TermPolarity(SuperTerm, Term);

    if (symbol_Equal(Top,fol_NOT))
      return (-fol_TermPolarity(SuperTerm, Term));

    if (symbol_Equal(Top,fol_EQUIV))
      return 0;

    if (symbol_Equal(Top, fol_IMPLIES)) { 
      if (SubTerm == term_FirstArgument(SuperTerm))
	return (-fol_TermPolarity(SuperTerm, Term));
      else
	return fol_TermPolarity(SuperTerm, Term);
    }
    if (symbol_Equal(Top, fol_IMPLIED)) {
      if (SubTerm == term_SecondArgument(SuperTerm))
	return (-fol_TermPolarity(SuperTerm, Term));
      else 
	return  fol_TermPolarity(SuperTerm, Term);
    }
    misc_StartErrorReport();
    misc_ErrorReport("\n In fol_TermPolarity: Unknown first-order operator.\n");
    misc_FinishErrorReport();
  }

  return 1;
}


static int fol_PolarCheckCount(TERM Nowterm, TERM SuperTerm, int Nowpolar)
/**************************************************************
   INPUT:   Two terms, Nowterm and its superterm, and the polarity of 
            Nowterm.
   RETURNS: The polarity of SuperTerm according to Nowterm.
   COMMENT: Helpfunction for fol_PolarCheck.
***************************************************************/
{ 
  SYMBOL Top;
  Top = term_TopSymbol(SuperTerm);

  if (Nowterm == SuperTerm)
    return Nowpolar;

  if (symbol_Equal(Top, fol_OR) || symbol_Equal(Top, fol_AND) || fol_IsQuantifier(Top) ||
      (symbol_Equal(Top, fol_IMPLIES) && Nowterm == term_SecondArgument(SuperTerm)) ||
      (symbol_Equal(Top, fol_IMPLIED) && Nowterm == term_FirstArgument(SuperTerm)))
    return Nowpolar;

  if (symbol_Equal(term_TopSymbol(SuperTerm), fol_EQUIV))
    return 0;

  return -Nowpolar;
}


static BOOL fol_PolarCheckAllquantor(TERM Subterm, TERM Term, int SubtermPolar)
/**************************************************************
   INPUT:   Two terms, Subterm subterm of Term, and polarity of Subterm.
   RETURNS: TRUE iff Subterm occurs in Term disjunctively.
   COMMENT: Help function for fol_PolarCheck. Dual case to Exist quantor.
***************************************************************/
{
  TERM    SuperTerm;
  SYMBOL  Top;
  int     SubPolar;

  if (Subterm == Term)  
    return TRUE;

  SuperTerm  = term_Superterm(Subterm);

  if (SuperTerm == Term)  /* Ugly, but it does not make sense to introduce a further function */
    return TRUE;

  Top        = term_TopSymbol(SuperTerm);
  SubPolar   = fol_PolarCheckCount(Subterm, SuperTerm, SubtermPolar);

  /* To be clarified: can the below condition generalized to universal quantifiers? */

  if (symbol_Equal(Top,fol_NOT) ||                   
     (symbol_Equal(Top, fol_OR) && SubPolar == 1) ||
     (symbol_Equal(Top, fol_AND) && SubPolar == -1) ||
     (symbol_Equal(Top,fol_IMPLIES) && SubPolar == 1) ||
     (symbol_Equal(Top,fol_IMPLIED) && SubPolar == 1))
    return fol_PolarCheckAllquantor(SuperTerm, Term, SubPolar);

  return FALSE;
}


static BOOL fol_PolarCheckExquantor(TERM Subterm, TERM Term, int SubtermPolar)
/**************************************************************
  INPUT:   Two terms, Subterm subterm of Term, and polarity of Subterm.
  RETURNS: TRUE iff Subterm occurs in Term conjunctively.
  COMMENT: Help function for fol_PolarCheck. Dual case to Allquantor.
***************************************************************/
{
  TERM    SuperTerm;
  SYMBOL  Top;
  int     SubPolar;

  if (Subterm == Term)  
    return TRUE;

  SuperTerm  = term_Superterm(Subterm);

  if (SuperTerm == Term)  /* Ugly, but it does not make sense to introduce a further function */
    return TRUE;

  Top        = term_TopSymbol(SuperTerm);
  SubPolar   = fol_PolarCheckCount(Subterm, SuperTerm, SubtermPolar);

  /* To be clarified: can the below condition generalized to existential quantifiers? */

  if (symbol_Equal(Top,fol_NOT) ||
      (symbol_Equal(Top, fol_OR) && SubPolar == -1) ||
      (symbol_Equal(Top, fol_AND) && SubPolar == 1) ||
      (symbol_Equal(Top,fol_IMPLIES) && SubPolar == -1) ||
      (symbol_Equal(Top,fol_IMPLIED) && SubPolar == -1))
    return fol_PolarCheckExquantor(SuperTerm, Term, SubPolar);

  return FALSE;
}

BOOL fol_PolarCheck(TERM Subterm, TERM Term)
/**************************************************************
  INPUT:   Two terms, <Subterm> is of the form x=t, where x or t variable. 
           <Subterm> is a subterm of <Term> and the top symbol of
	   <Term> must be the binding quantifier of x or t.
  RETURNS: BOOL if check is ok.
***************************************************************/
{
  int SubtermPolar;
  SYMBOL Top;

  SubtermPolar = fol_TermPolarity(Subterm, Term);
  Top          = term_TopSymbol(Term);

  if (SubtermPolar == -1 && symbol_Equal(Top, fol_ALL))
    return fol_PolarCheckAllquantor(Subterm, Term, SubtermPolar);

  if (SubtermPolar == 1 && symbol_Equal(Top, fol_EXIST))
    return fol_PolarCheckExquantor(Subterm, Term, SubtermPolar);

  return FALSE;
}


void fol_PopQuantifier(TERM Term) 
/**************************************************************
  INPUT:   A term whose top symbol is a quantifier.
  RETURNS: Nothing.
  EFFECT:  Removes the quantifier.
           If supertermlinks were set, they are updated.
***************************************************************/
{
  TERM SubTerm;
  LIST Scan;

#ifdef CHECK
  if (!fol_IsQuantifier(term_TopSymbol(Term))) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In fol_PopQuantifier: Top symbol of term isn't a quantifier.\n");
    misc_FinishErrorReport();
  }
#endif

  term_Delete(term_FirstArgument(Term));
  SubTerm = term_SecondArgument(Term);
  list_Delete(term_ArgumentList(Term));
  term_RplacTop(Term,term_TopSymbol(SubTerm));
  term_RplacArgumentList(Term,term_ArgumentList(SubTerm));
  for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan))
    if (term_Superterm(list_Car(Scan)))
      term_RplacSuperterm(list_Car(Scan),Term);
  term_Free(SubTerm);
}


void fol_DeleteQuantifierVariable(TERM Quant,SYMBOL Var)
/****************************************************************
  INPUT:   A term starting with a quantifier and a variable symbol.
  RETURNS: Nothing.
  EFFECT:  The variable is deleted from the list of variables
           bound by the quantor of <Quant>
*****************************************************************/
{
  LIST Scan;

  for (Scan=fol_QuantifierVariables(Quant);!list_Empty(Scan);Scan=list_Cdr(Scan))
    if (symbol_Equal(term_TopSymbol(list_Car(Scan)), Var)) {
      term_Delete((TERM)list_Car(Scan));
      list_Rplaca(Scan, (POINTER)NULL);
    }
  term_RplacArgumentList(term_FirstArgument(Quant),
			 list_PointerDeleteElement(fol_QuantifierVariables(Quant),(POINTER)NULL));
  if (list_Empty(fol_QuantifierVariables(Quant)))
    fol_PopQuantifier(Quant);
}



void fol_SetTrue(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: Nothing.
  EFFECT:  Replaces Term destructively by fol_True().
***************************************************************/
{
  term_DeleteTermList(term_ArgumentList(Term));
  term_RplacArgumentList(Term, list_Nil());
  term_RplacTop(Term, fol_True());
}

void fol_SetFalse(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: Nothing.
  EFFECT:  Replaces Term destructively by fol_False().
***************************************************************/
{
  term_DeleteTermList(term_ArgumentList(Term));
  term_RplacArgumentList(Term, list_Nil());
  term_RplacTop(Term, fol_False());
}


static void fol_ReplaceByArgCon(TERM Term)
/**************************************************************
  INPUT:   A term of the form f(...)=f(...), where f is a function.
  RETURNS: True.
  EFFECT:  Substitutes Term by <and(t1=s1, t2=s2, ..., tn=sn)>,
           where ti and si are the arguments of both f's in Term.
***************************************************************/
{
  LIST Scan, Bscan, List, Hlist;
  TERM Func1, Func2, NewTerm;

  Func1 = term_FirstArgument(Term);
  Func2 = term_SecondArgument(Term);
  List  = term_ArgumentList(Term);
  Scan  = list_Nil();
  term_RplacArgumentList(Term, list_Nil());
  term_RplacTop(Term, fol_And());

  for (Scan = term_ArgumentList(Func1),Bscan = term_ArgumentList(Func2);
       !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    Hlist = list_Nil();
    Hlist = list_Cons(list_Car(Bscan), Hlist);
    Hlist = list_Cons(list_Car(Scan), Hlist);
    NewTerm = term_Create(fol_Equality(), Hlist);
    term_RplacArgumentList(Term, list_Cons(NewTerm, term_ArgumentList(Term)));
    Bscan = list_Cdr(Bscan);
  }

  list_Delete(term_ArgumentList(Func1));
  list_Delete(term_ArgumentList(Func2));
  term_RplacArgumentList(Func1, list_Nil());
  term_RplacArgumentList(Func2, list_Nil());
  term_Delete(Func1);
  term_Delete(Func2);
  list_Delete(List);
}


BOOL fol_PropagateFreeness(TERM Term)
/**************************************************************
  INPUT:   A term and a list of functions.
  RETURNS: True iff a subterm of the form f(...)=f(...) occurs in the term,
           where f has property FREELY and GENERATED.
  EFFECT:  Substitutes all occurences of f=f by <and(t1=s1,...tn=sn)>,where
           ti and si are the arguments of each f in f=f. 
***************************************************************/
{
  BOOL    Free;
  LIST    Scan;
  TERM    Argum1, Argum2;

  Free = FALSE;

  if (fol_IsQuantifier(term_TopSymbol(Term)))
    return fol_PropagateFreeness(term_SecondArgument(Term));

  if (!term_IsAtom(Term)) {
    for (Scan = term_ArgumentList(Term); !list_Empty(Scan); Scan = list_Cdr(Scan))
      if (fol_PropagateFreeness(list_Car(Scan)))
	Free = TRUE;
  }
  else
    if (fol_IsEquality(Term)) {
      Argum1 = term_FirstArgument(Term);
      Argum2 = term_SecondArgument(Term);
      if (symbol_Equal(term_TopSymbol(Argum1), term_TopSymbol(Argum2)) &&
	  symbol_HasProperty(term_TopSymbol(Argum1), FREELY) &&
	  symbol_HasProperty(term_TopSymbol(Argum1), GENERATED)) {
	fol_ReplaceByArgCon(Term);
	return TRUE;
      }
    }

  return Free;
}


static BOOL fol_PropagateWitnessIntern(TERM Equation, SYMBOL Variable)
/**************************************************************
  INPUT:   A Term which is an equation where <Variable> is one
           of the equation's arguments that does not occur in the
           other argument. Father links must exist.
  RETURNS: True in case of witness propagation.
  EFFECT:  Checks whether subterm the equation is part of
           is of the form described in fol_PropagateWitness and
           substitutes in case of a hit.
***************************************************************/
{
  TERM    SuperTerm, BindQuantor, Predicat;
  SYMBOL  SuperTop;

  SuperTerm   = term_Superterm(Equation);  
  
  if (SuperTerm == term_Null())
    return FALSE;

  SuperTop    = term_TopSymbol(SuperTerm);
  BindQuantor = term_Superterm(SuperTerm);

  if (BindQuantor == term_Null())
    return FALSE;

  if (!fol_IsQuantifier(term_TopSymbol(BindQuantor)) ||
      list_Length(term_ArgumentList(SuperTerm)) != 2)
    return FALSE;

  if (Equation == term_SecondArgument(SuperTerm)) 
    Predicat  = term_FirstArgument(SuperTerm);
  else 
    Predicat = term_SecondArgument(SuperTerm);

  if (symbol_Equal(term_TopSymbol(BindQuantor), fol_All()) &&
      symbol_Equal(SuperTop, fol_Or()) &&
      symbol_Equal(term_TopSymbol(Predicat), fol_Not()) &&
      symbol_HasProperty(term_TopSymbol(term_FirstArgument(Predicat)), FREELY) && 
      symbol_HasProperty(term_TopSymbol(term_FirstArgument(Predicat)), GENERATED) &&
      symbol_Equal(term_TopSymbol(term_FirstArgument(term_FirstArgument(Predicat))), Variable)) {
    fol_SetFalse(BindQuantor);
    return TRUE;
  }
  if (!symbol_HasProperty(term_TopSymbol(Predicat), FREELY)    ||
      !symbol_HasProperty(term_TopSymbol(Predicat), GENERATED) ||
      !symbol_Equal(Variable, term_TopSymbol(term_FirstArgument(Predicat))))
    return FALSE;

  if (symbol_Equal(term_TopSymbol(BindQuantor), fol_All())) {
    if (symbol_Equal(SuperTop, fol_Implies()) && 
	term_SecondArgument(SuperTerm) == Equation) {
      fol_SetFalse(BindQuantor);
      return TRUE;
    }
    if (symbol_Equal(SuperTop, fol_Implied()) &&
	term_FirstArgument(SuperTerm) == Equation) {
      fol_SetFalse(BindQuantor);
      return TRUE;
    }
  }
  else /* Exquantor */
    if (symbol_Equal(SuperTop, fol_And())) {
      fol_SetTrue(BindQuantor);
      return TRUE;
    }

  return FALSE;
}


BOOL fol_PropagateWitness(TERM Term)
/**************************************************************
  INPUT:   A Term.
  RETURNS: True in case of witness propagation.
  EFFECT:  Substitutes any subterm of Term of the form
             forall([x],implies(P(x),x=t))
             forall([x],implied(x=t,P(x)))
             forall([x],or(notP(x),x=t))   by FALSE  and
             exists([x],and(P(x),x=t))     by TRUE,  where
           P has property FREELY and GENERATED, x doesn't occur in t.
***************************************************************/
{
  BOOL Hit;
  LIST Scan;

  Hit = FALSE;

  if (fol_IsQuantifier(term_TopSymbol(Term)))
    return fol_PropagateWitness(term_SecondArgument(Term));
  if (fol_IsEquality(Term)) {
    if (term_IsVariable(term_SecondArgument(Term))) {
      if (!term_ContainsSymbol(term_FirstArgument(Term), term_TopSymbol(term_SecondArgument(Term))))
        Hit = fol_PropagateWitnessIntern(Term,term_TopSymbol(term_SecondArgument(Term)));
    }
    else {
      if (term_IsVariable(term_FirstArgument(Term)))
	if (!term_ContainsSymbol(term_SecondArgument(Term), term_TopSymbol(term_FirstArgument(Term))))
	  Hit = fol_PropagateWitnessIntern(Term,term_TopSymbol(term_FirstArgument(Term)));
    }
  }
  if (symbol_IsPredicate(term_TopSymbol(Term)))
    return FALSE;

  for (Scan = term_ArgumentList(Term); !list_Empty(Scan); Scan = list_Cdr(Scan))
    if (fol_PropagateWitness(list_Car(Scan)))
      Hit = TRUE;

  return Hit;
}

BOOL fol_PropagateTautologies(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: True iff function replaced a subterm.
  EFFECT:  Replaces all occurences of t=t, or(A,not(A)) by TRUE
           and and(A,not(A)) by FALSE.
***************************************************************/
{
  BOOL    Hit;
  LIST    Scan, Bscan, ArgumentList;
  SYMBOL  Top;

  Top          = term_TopSymbol(Term);
  Hit          = FALSE;
  ArgumentList = term_ArgumentList(Term);

  if (fol_IsQuantifier(Top))
    return fol_PropagateTautologies(term_SecondArgument(Term));

  if (fol_IsEquality(Term)) {
    if (term_Equal(term_FirstArgument(Term), term_SecondArgument(Term))) {
      fol_SetTrue(Term);
      return TRUE;
    }
  }

  if (symbol_Equal(Top, fol_Or()) || symbol_Equal(Top, fol_And())) {
    for (Scan = ArgumentList; !list_Empty(Scan); Scan = list_Cdr(Scan)) 
      if (symbol_Equal(term_TopSymbol(list_Car(Scan)), fol_Not())) {
      for (Bscan = ArgumentList; !list_Empty(Bscan); Bscan = list_Cdr(Bscan)) {
	if (list_Car(Scan) != list_Car(Bscan) &&
	    fol_AlphaEqual(term_FirstArgument(list_Car(Scan)), list_Car(Bscan))) {
	  if (symbol_Equal(Top, fol_Or()))
	    fol_SetTrue(Term);
	  else
	    fol_SetFalse(Term);
	  return TRUE;
	}
      }
    }
  }

  if (!term_IsAtom(Term))
    for (Scan = ArgumentList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
      if (fol_PropagateTautologies(list_Car(Scan)))
	Hit = TRUE;
    }

  return Hit;
}


static BOOL fol_AlphaEqualIntern(TERM Term1, TERM Term2, NAT Mark)
/**************************************************************
  INPUT:   Two terms which represent formulae and a binding mark.
  RETURNS: True iff Term2 is equal to Term1 with respect to the
           renaming of bound variables.
***************************************************************/
{
  LIST    Scan, Bscan;
  SYMBOL  Top1, Top2;

  Top1  = term_TopSymbol(Term1);
  Top2  = term_TopSymbol(Term2);

  if (symbol_IsVariable(Top1) && symbol_IsVariable(Top2)) {
    if (term_VarIsMarked(Top2, Mark))
      return symbol_Equal(Top1, (SYMBOL)term_BindingValue(Top2));
    else
      return symbol_Equal(Top1, Top2);
  }

  if (!symbol_Equal(Top1, Top2))
    return FALSE;

  if (fol_IsQuantifier(Top1)) {
    if (list_Length(fol_QuantifierVariables(Term1)) != list_Length(fol_QuantifierVariables(Term2)))
      return FALSE;
    for (Scan = fol_QuantifierVariables(Term1), Bscan = fol_QuantifierVariables(Term2);
	 !list_Empty(Scan);
	 Scan = list_Cdr(Scan), Bscan = list_Cdr(Bscan))
      term_CreateValueBinding(term_TopSymbol(list_Car(Bscan)), Mark, 
			      (POINTER)term_TopSymbol(list_Car(Scan)));

    if (!fol_AlphaEqualIntern(term_SecondArgument(Term1), term_SecondArgument(Term2), Mark))
      return FALSE;
    for (Scan = fol_QuantifierVariables(Term1), Bscan = fol_QuantifierVariables(Term2);
	 !list_Empty(Scan);
         Scan = list_Cdr(Scan), Bscan = list_Cdr(Bscan))
      term_SetBindingMark(term_TopSymbol(list_Car(Bscan)), term_NullMark());
  }
  else {
    if (list_Length(term_ArgumentList(Term1)) != list_Length(term_ArgumentList(Term2)))
      return FALSE;

    for (Scan = term_ArgumentList(Term1), Bscan = term_ArgumentList(Term2);
	 !list_Empty(Scan); Scan = list_Cdr(Scan), Bscan = list_Cdr(Bscan))
      if (!fol_AlphaEqualIntern(list_Car(Scan), list_Car(Bscan), Mark))
	return FALSE;
  }
  return TRUE;
}


BOOL fol_AlphaEqual(TERM Term1, TERM Term2)
/**************************************************************
  INPUT:   Two terms of the form Qx(<rest>). All variables that occur in 
           Term1 and Term2 must be bound by only one quantifier!
  RETURNS: TRUE iff Term2 is bound renaming of Term1.
***************************************************************/
{
  BOOL Hit;

#ifdef CHECK
  if (Term1 == term_Null() || Term2 == term_Null()) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In fol_AlphaEqual: Corrupted term as parameter.\n");
    misc_FinishErrorReport();
  }
  if (fol_VarBoundTwice(Term1) || fol_VarBoundTwice(Term2)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In fol_AlphaEqual: Variables are bound more than once.\n");
    misc_FinishErrorReport();
  }
  if (term_InBindingPhase()) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In fol_AlphaEqual: Term context is in binding phase.\n");
    misc_FinishErrorReport();
  }
#endif

  term_StartBinding();

  Hit = fol_AlphaEqualIntern(Term1, Term2, term_ActMark());

  term_StopBinding();

  return Hit;
}


static BOOL fol_VarBoundTwiceIntern(TERM Term, NAT Mark)
/**************************************************************
  INPUT:   A term, possibly a NULL Term and a valid binding mark.
  RETURNS: TRUE iff a variable in <Term> is bound by more than one quantifier.
***************************************************************/
{
  LIST Scan;

  if (Term == term_Null())
    return FALSE;

  if (term_IsAtom(Term))
    return FALSE;

  if (!fol_IsQuantifier(term_TopSymbol(Term))) {
    for (Scan = term_ArgumentList(Term); !list_Empty(Scan); Scan = list_Cdr(Scan))
      if (fol_VarBoundTwiceIntern(list_Car(Scan), Mark))
	return TRUE;
  }
  else {
    for (Scan = fol_QuantifierVariables(Term); !list_Empty(Scan); Scan = list_Cdr(Scan)) {
      if (!term_VarIsMarked(term_TopSymbol(list_Car(Scan)), Mark))
	term_SetBindingMark(term_TopSymbol(list_Car(Scan)), Mark);
      else
	return TRUE;
    }
    if (fol_VarBoundTwiceIntern(term_SecondArgument(Term), Mark))
      return TRUE;
    for (Scan = fol_QuantifierVariables(Term); !list_Empty(Scan); Scan = list_Cdr(Scan))
      term_SetBindingMark(term_TopSymbol(list_Car(Scan)), term_NullMark());
  }
  return FALSE;
}


BOOL fol_VarBoundTwice(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: TRUE iff a variable in term is bound by more than one quantifier.
***************************************************************/
{
  BOOL Hit;

#ifdef CHECK
  if (term_InBindingPhase()) {
    misc_StartErrorReport();
    misc_ErrorReport("\n\n Context in fol_VarBoundTwice: term in binding phase\n");
    misc_FinishErrorReport();
  }
#endif

  term_StartBinding();

  Hit = fol_VarBoundTwiceIntern(Term, (NAT)term_ActMark());

  term_StopBinding();

  return Hit;
}


NAT fol_Depth(TERM Term)
/**************************************************************
  INPUT:   A formula.
  RETURNS: The depth of the formula up to predicate level.
***************************************************************/
{
  NAT  Depth,Help;
  LIST Scan;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
     misc_StartErrorReport();
    misc_ErrorReport("\n In fol_Depth: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  Depth = 0;

  if (symbol_IsPredicate(term_TopSymbol(Term)))
    return 1;

  if (fol_IsQuantifier(term_TopSymbol(Term)))
    return (fol_Depth(term_SecondArgument(Term)) + 1);

  for (Scan=term_ArgumentList(Term); !list_Empty(Scan); Scan=list_Cdr(Scan)) {
    Help = fol_Depth(list_Car(Scan));
    if (Help > Depth)
      Depth = Help;
  }

  return (Depth+1);
}


static void fol_ApplyContextToTermIntern(CONTEXT Context, TERM Term)
/********************************************************************
   INPUT:  A context (Context) and a term (Term).
   RETURN: void.
   EFFECT: Term is destructively changed modulo Context.
*********************************************************************/
{
  LIST Scan;

  if (fol_IsQuantifier(term_TopSymbol(Term))) {
    fol_ApplyContextToTermIntern(Context, term_SecondArgument(Term));
  }
  else if (symbol_IsVariable(term_TopSymbol(Term))) {
    if (cont_VarIsBound(Context, term_TopSymbol(Term)))
      Term = cont_ApplyBindingsModuloMatching(Context, Term, TRUE);
  }
  else {
    for (Scan=term_ArgumentList(Term); !list_Empty(Scan); Scan=list_Cdr(Scan))
      fol_ApplyContextToTermIntern(Context, list_Car(Scan));
  }
}


static BOOL fol_CheckApplyContextToTerm(CONTEXT Context, TERM Term)
/*************************************************************
   INPUT:   A Context and a term.
   RETURN:  TRUE iff Context can be applied to Term.
   COMMENT: Intern funktion of fol_ApplyContextToTerm.
**************************************************************/
{
  LIST Scan;
  BOOL Apply;

  Apply = TRUE;

  if (fol_IsQuantifier(term_TopSymbol(Term))) {
    for (Scan=fol_QuantifierVariables(Term); !list_Empty(Scan); Scan=list_Cdr(Scan))
      if (cont_VarIsBound(Context, term_TopSymbol(list_Car(Scan))))
	return FALSE;
    for (Scan=term_ArgumentList(term_SecondArgument(Term)); !list_Empty(Scan); Scan=list_Cdr(Scan)) {
      if (!fol_CheckApplyContextToTerm(Context, list_Car(Scan)))
	Apply = FALSE;
    }
  }
  else {
    for (Scan=term_ArgumentList(Term); !list_Empty(Scan); Scan=list_Cdr(Scan))
      if (!fol_CheckApplyContextToTerm(Context, list_Car(Scan)))
	Apply = FALSE;
  }
  return Apply;
}


BOOL fol_ApplyContextToTerm(CONTEXT Context, TERM Term)
/***************************************************************
   INPUT:  A context (Context) and a term (Term).
   RETURN: TRUE iff context could be applied on Term.
   EFFECT: Term is destructively changed modulo Context iff possible.
****************************************************************/
{
  if (fol_CheckApplyContextToTerm(Context, Term)) {
    fol_ApplyContextToTermIntern(Context, Term);
    return TRUE;
  }

  return FALSE;
}


BOOL fol_SignatureMatchFormula(TERM Formula, TERM Instance, BOOL Variant)
/********************************************************************
   INPUT : Two formulas and a flag.
           It is assumed that the symbol context is clean. 
   RETURN: TRUE iff <Formula> can be matched to <Instance> by matching
           variables as well as signature symbols. If <Variant> is TRUE
	   variables must be matched to variables.
   EFFECT: The symbol matches are stored in the symbol context.
*********************************************************************/
{
  int     Stack;
  SYMBOL  FormulaTop, InstanceTop;
  NAT     ActMark;
  TERM    ActFormula, ActInstance;

#ifdef CHECK
  if (!term_IsTerm(Formula) || term_InBindingPhase() || 
      !term_IsTerm(Instance) || !symbol_ContextIsClean()) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In fol_SignatureMatchFormula: Illegal input or context.");
    misc_FinishErrorReport();
  }
#endif

  term_StartBinding();

  Stack       = stack_Bottom();
  term_NewMark();
  ActMark     = term_OldMark();
  ActFormula  = Formula;
  ActInstance = Instance;
  
  do {
    FormulaTop  = term_TopSymbol(ActFormula);
    InstanceTop = term_TopSymbol(ActInstance);

    if (!symbol_IsVariable(FormulaTop)) { 
      if (!symbol_ContextIsBound(FormulaTop)) {
	if (!symbol_IsJunctor(FormulaTop) && !symbol_IsJunctor(InstanceTop) &&
	    !fol_IsPredefinedPred(FormulaTop) && !fol_IsPredefinedPred(InstanceTop))
	  symbol_ContextSetValue(FormulaTop, InstanceTop);    /* Symbols are ALWAYS bound !*/
	else {
	  if (!symbol_Equal(FormulaTop, InstanceTop)) {
	    term_StopBinding();
	    return FALSE;
	  }
	}
      }
      else {
	if (symbol_ContextIsBound(FormulaTop) && 
	    !symbol_Equal(symbol_ContextGetValue(FormulaTop),InstanceTop)) {
	  term_StopBinding();
	  return FALSE;
	}
      }
    }

    if (list_Length(term_ArgumentList(ActFormula)) != list_Length(term_ArgumentList(ActInstance))) {
      term_StopBinding();
      return FALSE;	
    }
    
    if (term_IsComplex(ActFormula)) {
      stack_Push(term_ArgumentList(ActInstance));
      stack_Push(term_ArgumentList(ActFormula));
    }
    else {
      if (symbol_IsVariable(FormulaTop)) {
	if (!term_VarIsMarked(FormulaTop, ActMark)) {
	  if (!Variant || symbol_IsVariable(InstanceTop))
	    term_CreateValueBinding(FormulaTop, ActMark, (POINTER)InstanceTop);
	  else {
	    term_StopBinding();
	    return FALSE;
	  }
	}
	else {
	  if (!symbol_Equal((SYMBOL)term_BindingValue(FormulaTop), InstanceTop)) {
	    term_StopBinding();
	    return FALSE;
	  }
	}
      }
    }

    while (!stack_Empty(Stack) && list_Empty(stack_Top())) {
      stack_Pop();
      stack_Pop();
    }
    if (!stack_Empty(Stack)) {
      ActFormula  = (TERM)list_Car(stack_Top());
      ActInstance = (TERM)list_Car(stack_NthTop(1));
      stack_RplacTop(list_Cdr(stack_Top()));
      stack_RplacNthTop(1,list_Cdr(stack_NthTop(1)));
    }
  } while (!stack_Empty(Stack));

  term_StopBinding();

  return TRUE;
}


BOOL fol_SignatureMatch(TERM Term, TERM Instance, LIST* Bindings, BOOL Variant)
/*****************************************************************
   INPUT : Two formulas, a binding list and a boolean flag.
   RETURN: TRUE iff <Term> can be matched to <Instance> by matching
           variables as well as signature symbols. If <Variant> is TRUE
	   variables must be matched to variables. Signature symbol
	   matchings have to be injective.
   EFFECT: The symbol matches are stored in the symbol context.
******************************************************************/
{
  int     Stack;
  SYMBOL  TermTop, InstanceTop;
  NAT     ActMark;
  TERM    ActTerm, ActInstance;

#ifdef CHECK
  if (!term_IsTerm(Term) || !term_IsTerm(Instance)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In fol_SignatureMatch: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  Stack       = stack_Bottom();
  ActMark     = term_OldMark();
  ActTerm     = Term;
  ActInstance = Instance;
  
  do {
    TermTop     = term_TopSymbol(ActTerm);
    InstanceTop = term_TopSymbol(ActInstance);

    if (!symbol_IsVariable(TermTop)) { 
      if (!symbol_ContextIsBound(TermTop)) {
	if (!symbol_IsJunctor(TermTop) && !symbol_IsJunctor(InstanceTop) &&
	    !fol_IsPredefinedPred(TermTop) && !fol_IsPredefinedPred(InstanceTop) &&
	    !symbol_ContextIsMapped(InstanceTop)) {
	  symbol_ContextSetValue(TermTop, InstanceTop);    /* Symbols are ALWAYS bound !*/
	  *Bindings = list_Cons((POINTER)TermTop,*Bindings);
	}
	else {
	  if (!symbol_Equal(TermTop, InstanceTop)) {
	    return FALSE;
	  }
	}
      }
      else {
	if (symbol_ContextIsBound(TermTop) && 
	    !symbol_Equal(symbol_ContextGetValue(TermTop),InstanceTop)) {
	  return FALSE;
	}
      }
    }

    if (list_Length(term_ArgumentList(ActTerm)) != list_Length(term_ArgumentList(ActInstance))) {
      return FALSE;	
    }
    
    if (term_IsComplex(ActTerm)) {
      stack_Push(term_ArgumentList(ActInstance));
      stack_Push(term_ArgumentList(ActTerm));
    }
    else {
      if (symbol_IsVariable(TermTop)) {
	if (!term_VarIsMarked(TermTop, ActMark)) {
	  if (!Variant || symbol_IsVariable(InstanceTop)) {
	    term_CreateValueBinding(TermTop, ActMark, (POINTER)InstanceTop);
	    *Bindings = list_Cons((POINTER)TermTop,*Bindings);
	  }
	  else
	    return FALSE;
	}
	else {
	  if (!symbol_Equal((SYMBOL)term_BindingValue(TermTop), InstanceTop)) {
	    return FALSE;
	  }
	}
      }
    }

    while (!stack_Empty(Stack) && list_Empty(stack_Top())) {
      stack_Pop();
      stack_Pop();
    }
    if (!stack_Empty(Stack)) {
      ActTerm  = (TERM)list_Car(stack_Top());
      ActInstance = (TERM)list_Car(stack_NthTop(1));
      stack_RplacTop(list_Cdr(stack_Top()));
      stack_RplacNthTop(1,list_Cdr(stack_NthTop(1)));
    }
  } while (!stack_Empty(Stack));

  return TRUE;
}


BOOL fol_CheckFormula(TERM Formula)
/*******************************************************************
   INPUT : A term Formula.
   RETURN: TRUE iff  no free variables occure in Formula
                 and father links are properly set
		 and argument list lengths match arities
********************************************************************/
{
  LIST FreeVars;

  FreeVars = fol_FreeVariables(Formula);

  if (!list_Empty(FreeVars)) {
    list_Delete(FreeVars);
    return FALSE;
  }
  
  return term_CheckTerm(Formula);
}
