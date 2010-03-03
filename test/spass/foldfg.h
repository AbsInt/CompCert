/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *              FIRST ORDER LOGIC SYMBOLS                 * */
/* *                                                        * */
/* *  $Module:   FOL      DFG                               * */ 
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

#ifndef _FOLDFG_
#define _FOLDFG_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "flags.h"
#include "unify.h"
#include "context.h"
#include "term.h"

/**************************************************************/
/* Global Variables and Constants (Only seen by macros)       */
/**************************************************************/

extern SYMBOL  fol_ALL;
extern SYMBOL  fol_EXIST;
extern SYMBOL  fol_AND;
extern SYMBOL  fol_OR;
extern SYMBOL  fol_NOT;
extern SYMBOL  fol_IMPLIES;
extern SYMBOL  fol_IMPLIED;
extern SYMBOL  fol_EQUIV;
extern SYMBOL  fol_VARLIST;
extern SYMBOL  fol_EQUALITY;
extern SYMBOL  fol_TRUE;
extern SYMBOL  fol_FALSE;

/**************************************************************/
/* Access to the first-order symbols.                         */
/**************************************************************/

static __inline__ SYMBOL fol_All(void)
{
  return fol_ALL;
}

static __inline__ SYMBOL fol_Exist(void)
{
  return fol_EXIST;
}

static __inline__ SYMBOL fol_And(void)
{
  return fol_AND;
}

static __inline__ SYMBOL fol_Or(void)
{
  return fol_OR;
}

static __inline__ SYMBOL fol_Not(void)
{
  return fol_NOT;
}

static __inline__ SYMBOL fol_Implies(void)
{
  return fol_IMPLIES;
}

static __inline__ SYMBOL fol_Implied(void)
{
  return fol_IMPLIED;
}

static __inline__ SYMBOL fol_Equiv(void)
{
  return fol_EQUIV;
}

static __inline__ SYMBOL fol_Varlist(void)
{
  return fol_VARLIST;
}

static __inline__ SYMBOL fol_Equality(void)
{
  return fol_EQUALITY;
}

static __inline__ SYMBOL fol_True(void)
{
  return fol_TRUE;
}

static __inline__ SYMBOL fol_False(void)
{
  return fol_FALSE;
}

/**************************************************************/
/* Macros                                                     */
/**************************************************************/

static __inline__ BOOL fol_IsQuantifier(SYMBOL S)
{
  return symbol_Equal(fol_ALL,S) || symbol_Equal(fol_EXIST,S);
}

static __inline__ BOOL fol_IsTrue(TERM S)
{
  return symbol_Equal(fol_TRUE,term_TopSymbol(S));
}

static __inline__ BOOL fol_IsFalse(TERM S)
{
  return symbol_Equal(fol_FALSE,term_TopSymbol(S));
}

static  __inline__ LIST fol_QuantifierVariables(TERM T)
  /* T's top symbol must be a quantifier ! */
{
  return term_ArgumentList(term_FirstArgument(T));
}

static __inline__ BOOL fol_IsLiteral(TERM T)
{
  return symbol_IsPredicate(term_TopSymbol(T)) ||
    (symbol_Equal(term_TopSymbol(T),fol_Not()) && 
     symbol_IsPredicate(term_TopSymbol(term_FirstArgument(T))));
}

static __inline__ BOOL fol_IsNegativeLiteral(TERM T)
{
  return (symbol_Equal(term_TopSymbol(T),fol_Not()) && 
	  symbol_IsPredicate(term_TopSymbol(term_FirstArgument(T))));
}


static __inline__ BOOL fol_IsJunctor(SYMBOL S)
{
  return fol_IsQuantifier(S) || symbol_Equal(S, fol_AND) || 
    symbol_Equal(S, fol_OR) || symbol_Equal(S, fol_NOT) ||
    symbol_Equal(S, fol_IMPLIED) ||  symbol_Equal(S, fol_VARLIST) ||
    symbol_Equal(S, fol_IMPLIES) || symbol_Equal(S, fol_EQUIV);
}

static __inline__ BOOL fol_IsPredefinedPred(SYMBOL S)
{
  return symbol_Equal(S, fol_EQUALITY) || symbol_Equal(S, fol_TRUE) ||
    symbol_Equal(S, fol_FALSE);
}

static __inline__ TERM fol_Atom(TERM Lit)
{
  if (term_TopSymbol(Lit) == fol_NOT)
    return term_FirstArgument(Lit);
  else
    return Lit;
}

static __inline__ BOOL fol_IsEquality(TERM Term)
{
  return term_TopSymbol(Term) == fol_EQUALITY;
}


static __inline__ BOOL fol_IsAssignment(TERM Term)
{
  return (term_TopSymbol(Term) == fol_EQUALITY &&
	  ((term_IsVariable(term_FirstArgument(Term)) &&
	    !term_ContainsVariable(term_SecondArgument(Term),
				   term_TopSymbol(term_FirstArgument(Term)))) ||
	   (term_IsVariable(term_SecondArgument(Term)) &&
	    !term_ContainsVariable(term_FirstArgument(Term),
				   term_TopSymbol(term_SecondArgument(Term))))));
}


static __inline__ LIST fol_DeleteFalseTermFromList(LIST List)
/**************************************************************
  INPUT:   A list of terms.
  RETURNS: The list where all terms equal to the 'False' term are removed.
  EFFECTS:  'False' is a special predicate from the fol module.
           Terms are compared with respect to the term_Equal function.
           The terms are deleted, too.
***************************************************************/
{
  return list_DeleteElementIfFree(List, (BOOL (*)(POINTER))fol_IsFalse,
				  (void (*)(POINTER))term_Delete);
}


static __inline__ LIST fol_DeleteTrueTermFromList(LIST List)
/**************************************************************
  INPUT:   A list of terms.
  RETURNS: The list where all terms equal to the 'True' term are removed.
  EFFECTS:  'True' is a special predicate from the fol module.
           Terms are compared with respect to the term_Equal function.
           The terms are deleted, too.
***************************************************************/
{
  return list_DeleteElementIfFree(List, (BOOL (*)(POINTER))fol_IsTrue,
				  (void (*)(POINTER))term_Delete);
}


/**************************************************************/
/* Functions                                                  */
/**************************************************************/

void   fol_Init(BOOL, PRECEDENCE);
SYMBOL fol_IsStringPredefined(const char*);
TERM   fol_CreateQuantifier(SYMBOL, LIST, LIST);
TERM   fol_CreateQuantifierAddFather(SYMBOL, LIST, LIST);
LIST   fol_GetNonFOLPredicates(void);
TERM   fol_ComplementaryTerm(TERM);
LIST   fol_GetAssignments(TERM);
void   fol_Free(void);
void   fol_CheckFatherLinks(TERM);
BOOL   fol_FormulaIsClause(TERM);
void   fol_FPrintOtterOptions(FILE*, BOOL, FLAG_TDFG2OTTEROPTIONSTYPE);
void   fol_FPrintOtter(FILE*, LIST, FLAG_TDFG2OTTEROPTIONSTYPE);
void   fol_FPrintDFGSignature(FILE*);
void   fol_PrettyPrintDFG(TERM);
void   fol_PrintDFG(TERM);
void   fol_FPrintDFG(FILE*, TERM);
void   fol_FPrintDFGProblem(FILE*, const char*, const char*, const char*, const char*, LIST, LIST);
void   fol_PrintPrecedence(PRECEDENCE);
void   fol_FPrintPrecedence(FILE*, PRECEDENCE);
LIST   fol_Instances(TERM, TERM);
LIST   fol_Generalizations(TERM, TERM);
TERM   fol_MostGeneralFormula(LIST);
void   fol_NormalizeVars(TERM);
void   fol_NormalizeVarsStartingAt(TERM, SYMBOL);
LIST   fol_FreeVariables(TERM);
LIST   fol_BoundVariables(TERM);
BOOL   fol_VarOccursFreely(TERM,TERM);
BOOL   fol_AssocEquation(TERM, SYMBOL *);
BOOL   fol_DistributiveEquation(TERM, SYMBOL*, SYMBOL*);
void   fol_ReplaceVariable(TERM, SYMBOL, TERM);
void   fol_PrettyPrint(TERM);
LIST   fol_GetSubstEquations(TERM);
TERM   fol_GetBindingQuantifier(TERM, SYMBOL);
int    fol_TermPolarity(TERM, TERM);
BOOL   fol_PolarCheck(TERM, TERM);
void   fol_PopQuantifier(TERM);
void   fol_DeleteQuantifierVariable(TERM,SYMBOL);
void   fol_SetTrue(TERM);
void   fol_SetFalse(TERM);
void   fol_RemoveImplied(TERM);
BOOL   fol_PropagateFreeness(TERM);
BOOL   fol_PropagateWitness(TERM);
BOOL   fol_PropagateTautologies(TERM);
BOOL   fol_AlphaEqual(TERM, TERM);
BOOL   fol_VarBoundTwice(TERM);
NAT    fol_Depth(TERM);
BOOL   fol_ApplyContextToTerm(CONTEXT, TERM);
BOOL   fol_CheckFormula(TERM);
BOOL   fol_SignatureMatchFormula(TERM, TERM, BOOL);
BOOL   fol_SignatureMatch(TERM, TERM, LIST*, BOOL);

#endif
