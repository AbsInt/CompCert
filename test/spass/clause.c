/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                   CLAUSES                              * */
/* *                                                        * */
/* *  $Module:   CLAUSE                                     * */
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
/* $Revision: 21527 $                                       * */
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

#include "clause.h"

/**************************************************************/
/* Global variables and constants                             */
/**************************************************************/

/* Means weight of literal or clause is undefined */
const NAT clause_WEIGHTUNDEFINED = NAT_MAX;

int  clause_CLAUSECOUNTER;
NAT  clause_STAMPID;

/* The following array is used for bucket sort on clauses */
#define clause_MAXWEIGHT 20
LIST clause_SORT[clause_MAXWEIGHT+1];

/**************************************************************/
/* Inline functions                                           */
/**************************************************************/

static __inline__ void clause_FreeLitArray(CLAUSE Clause)
{
  NAT Length = clause_Length(Clause);
  if (Length > 0)
    memory_Free(Clause->literals, sizeof(LITERAL) * Length);
}


/**************************************************************/
/* Primitive literal functions                                */
/**************************************************************/

BOOL clause_LiteralIsLiteral(LITERAL Literal)
/*********************************************************
  INPUT:   A literal.
  RETURNS: TRUE, if 'Literal' is not NULL and has a predicate
           symbol as its atoms top symbol.
**********************************************************/
{
  return ((Literal != NULL) &&
	  symbol_IsPredicate(clause_LiteralPredicate(Literal)));
}

NAT clause_LiteralComputeWeight(LITERAL Literal, FLAGSTORE Flags)
/*********************************************************
  INPUT:   A literal and a flag store.
  RETURNS: The weight of the literal.
  CAUTION: This function does not update the weight of the literal!
**********************************************************/
{
  TERM Term;
  int  Bottom;
  NAT  Number;

#ifdef CHECK
  if (!clause_LiteralIsLiteral(Literal)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_LiteralComputeWeight :");
    misc_ErrorReport("Illegal Input. Input not a literal.");
    misc_FinishErrorReport();
  }
#endif

  Term = clause_LiteralSignedAtom(Literal);
  Bottom = stack_Bottom();
  Number = 0;
  
  do {
    if (term_IsComplex(Term)) {
      Number += flag_GetFlagValue(Flags, flag_FUNCWEIGHT);
      stack_Push(term_ArgumentList(Term));
    }
    else
      if (term_IsVariable(Term))
	Number += flag_GetFlagValue(Flags, flag_VARWEIGHT);
      else
	Number += flag_GetFlagValue(Flags, flag_FUNCWEIGHT);
    
    while (!stack_Empty(Bottom) && list_Empty(stack_Top()))
      stack_Pop();
    if (!stack_Empty(Bottom)) {
      Term = (TERM) list_Car(stack_Top());
      stack_RplacTop(list_Cdr(stack_Top()));
    }
  } while (!stack_Empty(Bottom));

  return Number;

}

LITERAL clause_LiteralCreate(TERM Atom, CLAUSE Clause)
/**********************************************************
  INPUT:   A Pointer to a signed Predicate-Term and one to a
           clause it shall belong to.
  RETURNS: An appropriate literal where the other values
           are set to default values.
  MEMORY:  A LITERAL_NODE is allocated.
  CAUTION: The weight of the literal is not set correctly!
***********************************************************/
{
  LITERAL Result;

#ifdef CHECK
  if (!term_IsTerm(Atom)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_LiteralCreate:");
    misc_ErrorReport("\n Illegal input. Input not a term.");
    misc_FinishErrorReport();
  }
  if (!symbol_IsPredicate(term_TopSymbol(Atom)) &&
      (term_TopSymbol(Atom) != fol_Not())) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_LiteralCreate:");
    misc_ErrorReport("\n Illegal input. No predicate- or negated term.");
    misc_FinishErrorReport();
  }
#endif

  Result                = (LITERAL)memory_Malloc(sizeof(LITERAL_NODE));
  
  Result->atomWithSign  = Atom;
  Result->oriented      = FALSE;
  Result->weight        = clause_WEIGHTUNDEFINED;
  Result->maxLit        = 0;
  Result->owningClause  = Clause;

  return Result;
}


LITERAL clause_LiteralCreateNegative(TERM Atom, CLAUSE Clause)
/**********************************************************
  INPUT:   A Pointer to a unsigned Predicate-Term and one to a
           clause it shall belong to.
  RETURNS: An appropriate literal where the other values
           are set to default values and the term gets a sign.
  MEMORY:  A LITERAL_NODE is allocated.
  CAUTION: The weight of the literal is not set correctly!
***********************************************************/
{
  LITERAL Result;

#ifdef CHECK
  if (!term_IsTerm(Atom)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_LiteralCreateNegative:");
    misc_ErrorReport("\n Illegal input. Input not an atom.");
    misc_FinishErrorReport();
  }
  if (!symbol_IsPredicate(term_TopSymbol(Atom)) &&
      (term_TopSymbol(Atom) != fol_Not())) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_LiteralCreateNegative:");
    misc_ErrorReport("\n Illegal input. Input term not normalized.");
    misc_FinishErrorReport();
  }
#endif

  Result                = (LITERAL)memory_Malloc(sizeof(LITERAL_NODE));
  
  term_RplacSupertermList(Atom, list_Nil());

  Result->atomWithSign  = term_Create(fol_Not(), list_List(Atom));
  Result->oriented      = FALSE;
  Result->maxLit        = 0;
  Result->weight        = clause_WEIGHTUNDEFINED;
  Result->owningClause  = Clause;

  return Result;
}


void clause_LiteralDelete(LITERAL Literal)
/*********************************************************
  INPUT:   A literal, which has an unshared Atom. For Shared
           literals clause_LiteralDeleteFromSharing(Lit) is
	   available.
  RETURNS: Nothing.
  MEMORY:  The Atom of 'Literal' is deleted and its memory
           is freed as well as the LITERAL_NODE.
**********************************************************/
{
#ifdef CHECK
  if (!clause_LiteralIsLiteral(Literal)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_LiteralDelete:");
    misc_ErrorReport("\n Illegal input. Input not a literal.");
    misc_FinishErrorReport();
  }
#endif

  term_Delete(clause_LiteralSignedAtom(Literal));

  clause_LiteralFree(Literal);
}


void clause_LiteralInsertIntoSharing(LITERAL Lit, SHARED_INDEX ShIndex)
/**********************************************************
  INPUT:   A Literal with an unshared Atom and an Index.
  RETURNS: The literal with a shared Atom inserted into the
           'Index'.
  MEMORY:  Allocates TERM_NODE memory needed to insert 'Lit'
           into the sharing and frees the memory of the
           unshared Atom.
***********************************************************/
{

  TERM Atom;
  
#ifdef CHECK
  if (!clause_LiteralIsLiteral(Lit)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_LiteralInsertIntoSharing:");
    misc_ErrorReport("\n Illegal literal input.");
    misc_FinishErrorReport();
  }
#endif
  
  Atom = clause_LiteralAtom(Lit);
  
  clause_LiteralSetAtom(Lit, sharing_Insert(Lit, Atom, ShIndex));
  
  term_Delete(Atom);
}


void clause_LiteralDeleteFromSharing(LITERAL Lit, SHARED_INDEX ShIndex)
/**********************************************************
  INPUT:   A Literal and an 'Index'.
  RETURNS: Nothing.
  MEMORY:  Deletes 'Lit' from Sharing, frees no more used
           TERM memory and frees the LITERAL_NODE.
********************************************************/
{

  TERM Atom;

#ifdef CHECK
  if (!clause_LiteralIsLiteral(Lit)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_LiteralDeleteFromSharing:");
    misc_ErrorReport("\n Illegal literal input.");
    misc_FinishErrorReport();
  }
#endif

  Atom = clause_LiteralAtom(Lit);

  if (clause_LiteralIsNegative(Lit)) {
    list_Free(term_ArgumentList(clause_LiteralSignedAtom(Lit)));
    term_Free(clause_LiteralSignedAtom(Lit));
  }
 
  sharing_Delete(Lit, Atom, ShIndex);

  clause_LiteralFree(Lit);

}


static LIST clause_CopyLitInterval(CLAUSE Clause, int Start, int End)
/**************************************************************
 INPUT:   A clause and two integers representing
          literal indices.
 RETURNS: Copies of all literals in <Clause> with index i and
          in the interval [Start:End] are prepended to <List>.
 MEMORY:  All atoms are copied.
***************************************************************/
{
  TERM Atom;
  LIST List;

  List = list_Nil();

  for ( ; Start <= End; Start++) {
    Atom = term_Copy(clause_GetLiteralAtom(Clause, Start));
    List = list_Cons(Atom, List);
  }
  
  return List;
}


static LIST clause_CopyLitIntervalExcept(CLAUSE Clause, int Start, int End,
					 int i)
/**************************************************************
 INPUT:   A clause and three integers representing
          literal indeces.
 RETURNS: A list of atoms from literals within the interval
          [Start:End] except the literal at index <i>.
 MEMORY:  All atoms are copied.
***************************************************************/
{
  TERM Atom;
  LIST Result;
  
  Result = list_Nil();
  for ( ; End >= Start; End--)
    if (End != i) {
      Atom   = term_Copy(clause_GetLiteralAtom(Clause, End));
      Result = list_Cons(Atom, Result);
    }
  return Result;
}


LIST clause_CopyConstraint(CLAUSE Clause)
/**************************************************************
 INPUT:   A clause.
 RETURNS: The list of copied constraint literals from <Clause>.
***************************************************************/
{
  return clause_CopyLitInterval(Clause,
				clause_FirstConstraintLitIndex(Clause),
				clause_LastConstraintLitIndex(Clause));
}


LIST clause_CopyAntecedentExcept(CLAUSE Clause, int i)
/**************************************************************
 INPUT:   A clause.
 RETURNS: A list containing copies of all antecedent literals
          except <i>.
***************************************************************/
{
  return clause_CopyLitIntervalExcept(Clause,
				      clause_FirstAntecedentLitIndex(Clause),
				      clause_LastAntecedentLitIndex(Clause),
				      i);
}

LIST clause_CopySuccedent(CLAUSE Clause)
/**************************************************************
 INPUT:   A clause.
 RETURNS: The list of copied succedent literals from <Clause>.
***************************************************************/
{
  return clause_CopyLitInterval(Clause,
				clause_FirstSuccedentLitIndex(Clause),
				clause_LastSuccedentLitIndex(Clause));
}


LIST clause_CopySuccedentExcept(CLAUSE Clause, int i)
/**************************************************************
 INPUT:   A clause.
 RETURNS: A list containing copies of all succedent literals
          except <i>.
***************************************************************/
{
  return clause_CopyLitIntervalExcept(Clause,
				      clause_FirstSuccedentLitIndex(Clause),
				      clause_LastSuccedentLitIndex(Clause),
				      i);
}


/**************************************************************/
/* Specials                                                   */
/**************************************************************/

BOOL clause_IsUnorderedClause(CLAUSE Clause)
/*********************************************************
  INPUT:   A clause.
  RETURNS: TRUE, if the invariants concerning splitting etc. hold
           Invariants concerning maximality restrictions are not tested.
**********************************************************/
{
  return ((Clause != NULL) &&
	  clause_CheckSplitLevel(Clause) &&
	  (clause_IsEmptyClause(Clause) ||
	   /* Check the first literal as a "random" sample */
	   clause_LiteralIsLiteral(clause_GetLiteral(Clause,clause_FirstLitIndex()))) &&
	  (clause_SplitLevel(Clause) == 0 || Clause->splitfield_length>0) &&
	  clause_DependsOnSplitLevel(Clause,clause_SplitLevel(Clause)));
}


BOOL clause_IsClause(CLAUSE Clause, FLAGSTORE FlagStore, PRECEDENCE Precedence)
/*********************************************************
  INPUT:   A clause, a flag store and a precedence.
  RETURNS: TRUE, if literals are correctly ordered and the
           invariants concerning splitting etc. hold
**********************************************************/
{
  int     i;
  LITERAL ActLit;

  if (!clause_IsUnorderedClause(Clause))
    return FALSE;

  for (i=clause_FirstAntecedentLitIndex(Clause);i<=clause_LastSuccedentLitIndex(Clause);i++) {
    ActLit = clause_GetLiteral(Clause,i);
    if (fol_IsEquality(clause_LiteralSignedAtom(ActLit))) {
      ord_RESULT HelpRes;
	
      HelpRes =
	ord_Compare(term_FirstArgument(clause_LiteralSignedAtom(ActLit)),
		    term_SecondArgument(clause_LiteralSignedAtom(ActLit)),
		    FlagStore, Precedence);
	
      if (ord_IsSmallerThan(HelpRes))
	return FALSE;
    }
  }

  return TRUE;
}


BOOL clause_ContainsPositiveEquations(CLAUSE Clause)
/*********************************************************
  INPUT:   A clause.
  RETURNS: TRUE, if the clause contains a positive equality literal.
**********************************************************/
{
  int i;
  
  for (i = clause_FirstSuccedentLitIndex(Clause);
       i < clause_Length(Clause);
       i++)
    if (clause_LiteralIsEquality(clause_GetLiteral(Clause, i)))
      return TRUE;

  return FALSE;
}


BOOL clause_ContainsNegativeEquations(CLAUSE Clause)
/*********************************************************
  INPUT:   A clause.
  RETURNS: TRUE, if the clause contains a positive equality literal.
**********************************************************/
{
  int i;
  
  for (i = clause_FirstAntecedentLitIndex(Clause);
       i < clause_FirstSuccedentLitIndex(Clause);
       i++)
    if (clause_LiteralIsEquality(clause_GetLiteral(Clause, i)))
      return TRUE;

  return FALSE;
}


int clause_ContainsFolAtom(CLAUSE Clause, BOOL *Prop, BOOL *Grd, BOOL *Monadic,
			   BOOL *NonMonadic)
/*********************************************************
  INPUT:   A clause.
  RETURNS: The number of boolean variables changed.
           If <*Prop> is FALSE and the clause contains a propositional
	   variable, it is changed to TRUE.
	   If <*Grd> is FALSE and the clause contains a non-propositional
	   ground atom, it is changed to TRUE.
           If <*Monadic> is FALSE and the clause contains a monadic atom,
	      it is changed to TRUE.
	   If <*NonMonadic> is FALSE and the clause contains an at least
	   2-place non-equality atom, it is changed to TRUE.
**********************************************************/
{
  int  i,Result,Arity;
  BOOL Ground;

  Result = 0;
  i      = clause_FirstLitIndex();

  while (Result < 4 &&
	 i < clause_Length(Clause) &&
	 (!(*Prop) || !(*Monadic) || !(*NonMonadic))) {
    Arity  = symbol_Arity(term_TopSymbol(clause_GetLiteralAtom(Clause,i)));
    Ground = term_IsGround(clause_GetLiteralAtom(Clause,i));
    if (!(*Prop) && Arity == 0) {
      Result++;
      *Prop = TRUE;
    }
    if (!(*Grd) && Arity > 0 && Ground &&
	!fol_IsEquality(clause_GetLiteralAtom(Clause,i))) {
      Result++;
      *Grd = TRUE;
    }
    if (!(*Monadic) && Arity == 1 && !Ground) {
      Result++;
      *Monadic = TRUE;
    }
    if (!(*NonMonadic) && Arity > 1 && !Ground &&
	!fol_IsEquality(clause_GetLiteralAtom(Clause,i))) {
      Result++;
      *NonMonadic = TRUE;
    }
    i++;
  }
  return Result;
}


BOOL clause_ContainsVariables(CLAUSE Clause)
/*********************************************************
  INPUT:   A clause.
  RETURNS: TRUE, if the clause contains at least one variable
**********************************************************/
{
  int  i;
  TERM Term;

  for (i = clause_FirstLitIndex(); i < clause_Length(Clause); i++) {
    Term = clause_GetLiteralAtom(Clause,i);
    if (term_NumberOfVarOccs(Term)>0)
      return TRUE;
  }

  return FALSE;
}


void clause_ContainsSortRestriction(CLAUSE Clause, BOOL *Sortres, BOOL *USortres)
/*********************************************************
  INPUT:   A clause.
  RETURNS: TRUE, if the clause contains a negative monadic atom with
           a variable argument
**********************************************************/
{
  int  i;
  TERM Term;

  for (i = clause_FirstLitIndex();
       i <= clause_LastAntecedentLitIndex(Clause) && (!*Sortres || !*USortres);
       i++) {
    Term = clause_GetLiteralAtom(Clause,i);
    if (symbol_IsBaseSort(term_TopSymbol(Term))) {
      *USortres = TRUE;
      if (symbol_IsVariable(term_TopSymbol(term_FirstArgument(Term))))
	*Sortres = TRUE;
    }
  }
}

BOOL clause_ContainsFunctions(CLAUSE Clause)
/*********************************************************
  INPUT:   A clause.
  RETURNS: TRUE, if the clause contains at least one function symbol
**********************************************************/
{
  int  i;
  TERM Term;

  for (i = clause_FirstLitIndex(); i < clause_Length(Clause); i++) {
    Term = clause_GetLiteralAtom(Clause,i);
    if (term_ContainsFunctions(Term))
      return TRUE;
  }

  return FALSE;
}

BOOL clause_ContainsSymbol(CLAUSE Clause, SYMBOL Symbol)
/*********************************************************
  INPUT:   A clause and a symbol.
  RETURNS: TRUE, if the clause contains the symbol
**********************************************************/
{
  int  i;

  for (i = clause_FirstLitIndex(); i < clause_Length(Clause); i++)
    if (term_ContainsSymbol(clause_GetLiteralAtom(Clause,i), Symbol))
      return TRUE;
  return FALSE;
}

NAT clause_NumberOfSymbolOccurrences(CLAUSE Clause, SYMBOL Symbol)
/*********************************************************
  INPUT:   A clause and a symbol.
  RETURNS: the number of occurrences of <Symbol> in <Clause>
**********************************************************/
{
  int  i;
  NAT  Result;

  Result = 0;

  for (i = clause_FirstLitIndex(); i < clause_Length(Clause); i++)
    Result += term_NumberOfSymbolOccurrences(clause_GetLiteralAtom(Clause,i), Symbol);

  return Result;
}

BOOL clause_ImpliesFiniteDomain(CLAUSE Clause)
/*********************************************************
  INPUT:   A clause.
  RETURNS: TRUE, if the clause consists of a positive disjunction
           of equations, where each equation is of the form "x=t" for
	   some variable "x" and ground term "t"
**********************************************************/
{
  int  i;
  TERM Term;

  if (clause_FirstLitIndex() != clause_FirstSuccedentLitIndex(Clause))
    return FALSE;

  for (i = clause_FirstLitIndex(); i < clause_Length(Clause); i++) {
    Term = clause_GetLiteralTerm(Clause,i);
    if (!symbol_Equal(term_TopSymbol(Term),fol_Equality()) ||
	(!symbol_IsVariable(term_TopSymbol(term_FirstArgument(Term))) &&
	 !symbol_IsVariable(term_TopSymbol(term_SecondArgument(Term)))) ||
	(symbol_IsVariable(term_TopSymbol(term_FirstArgument(Term))) &&
	 !term_IsGround(term_SecondArgument(Term))) ||
	(symbol_IsVariable(term_TopSymbol(term_SecondArgument(Term))) &&
	 !term_IsGround(term_FirstArgument(Term))))
      return FALSE;
  }

  return TRUE;
}

BOOL clause_ImpliesNonTrivialDomain(CLAUSE Clause)
/*********************************************************
  INPUT:   A clause.
  RETURNS: TRUE, if the clause consists of a negative equation
           with two syntactically different arguments
**********************************************************/
{
  if (clause_Length(Clause) == 1 &&
      !clause_HasEmptyAntecedent(Clause) &&
      clause_LiteralIsEquality(clause_FirstAntecedentLit(Clause)) &&
      !term_Equal(term_FirstArgument(clause_LiteralAtom(clause_FirstAntecedentLit(Clause))),
		  term_SecondArgument(clause_LiteralAtom(clause_FirstAntecedentLit(Clause)))))
    return TRUE;
  
  return FALSE;
}

LIST clause_FiniteMonadicPredicates(LIST Clauses)
/*********************************************************
  INPUT:   A list of clauses.
  RETURNS: A list of all predicate symbols that are guaranteed
           to have a finite extension in any minimal Herbrand model.
	   These predicates must only positively occur
           in unit clauses and must have a ground term argument.
**********************************************************/
{
  LIST   Result, NonFinite, Scan;
  CLAUSE Clause;
  int    i, n;
  SYMBOL Pred;

  Result    = list_Nil();
  NonFinite = list_Nil();

  for (Scan=Clauses;!list_Empty(Scan);Scan=list_Cdr(Scan)) {
    Clause = (CLAUSE)list_Car(Scan);
    n      = clause_Length(Clause);
    for (i=clause_FirstSuccedentLitIndex(Clause);i<n;i++) {
      Pred = term_TopSymbol(clause_GetLiteralAtom(Clause,i));
      if (symbol_Arity(Pred) == 1 &&
	  !list_PointerMember(NonFinite, (POINTER)Pred)) {
	if (term_NumberOfVarOccs(clause_GetLiteralAtom(Clause,i)) > 0 ||
	    n > 1) {
	  NonFinite = list_Cons((POINTER)Pred, NonFinite);
	  Result    = list_PointerDeleteElement(Result, (POINTER)Pred);
	}
	else {
	  if (!list_PointerMember(Result, (POINTER)Pred))
	    Result = list_Cons((POINTER)Pred, Result);
	}
      }
    }
  }
  list_Delete(NonFinite);

  Result = list_PointerDeleteElement(Result, (POINTER)fol_Equality());

  return Result;
}

NAT clause_NumberOfVarOccs(CLAUSE Clause)
/**************************************************************
  INPUT:   A Clause.
  RETURNS: The number of variable occurrences in the clause.
***************************************************************/
{
  int i,n;
  NAT Result;

  Result = 0;
  n      = clause_Length(Clause);

  for (i = clause_FirstLitIndex(); i < n; i++)
    Result += term_NumberOfVarOccs(clause_GetLiteralTerm(Clause,i));
  
  return Result;
}


NAT clause_ComputeWeight(CLAUSE Clause, FLAGSTORE Flags)
/**************************************************************
  INPUT:   A clause and a flag store.
  RETURNS: The Weight of the literals in the clause,
           up to now the number of variable symbols plus
	   twice the number of signature symbols.
  EFFECT:  The weight of the literals is updated, but not the
           weight of the clause!
***************************************************************/
{
  int     i, n;
  NAT     Weight;
  LITERAL Lit;

  Weight = 0;
  n      = clause_Length(Clause);

  for (i = clause_FirstLitIndex(); i < n; i++) {
    Lit = clause_GetLiteral(Clause, i);
    clause_UpdateLiteralWeight(Lit, Flags);
    Weight += clause_LiteralWeight(Lit);
  }
  return Weight;
}


NAT clause_ComputeTermDepth(CLAUSE Clause)
/**************************************************************
  INPUT:   A Clause.
  RETURNS: Maximal depth of a literal in <Clause>.
***************************************************************/
{
  int     i,n;
  NAT     Depth,Help;

#ifdef CHECK
  if (!clause_IsUnorderedClause(Clause)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_ComputeTermDepth:");
    misc_ErrorReport("\n Illegal input. Input not a clause.");
    misc_FinishErrorReport();
  }
#endif

  Depth = 0;
  n     = clause_Length(Clause);

  for (i = clause_FirstLitIndex();i < n;i++) {
    Help   = term_Depth(clause_GetLiteralAtom(Clause,i));
    if (Help > Depth)
      Depth = Help;
  }
  return Depth;
}

NAT clause_MaxTermDepthClauseList(LIST Clauses)
/**************************************************************
  INPUT:   A list of clauses.
  RETURNS: Maximal depth of a clause in <Clauses>.
***************************************************************/
{
  NAT  Depth,Help;

  Depth = 0;

  while (!list_Empty(Clauses)) {
    Help = clause_ComputeTermDepth(list_Car(Clauses));
    if (Help > Depth)
      Depth = Help;
    Clauses = list_Cdr(Clauses);
  }

  return Depth;
}


NAT clause_ComputeSize(CLAUSE Clause)
/**************************************************************
  INPUT:   A Clause.
  RETURNS: The Size of the literals in the clause,
           up to now the number of symbols.
***************************************************************/
{
  int     i,n;
  NAT     Size;

#ifdef CHECK
  if (!clause_IsUnorderedClause(Clause)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_ComputeSize:");
    misc_ErrorReport("\n Illegal input. Input not a clause.");
    misc_FinishErrorReport();
  }
#endif

  Size = 0;
  n    = clause_Length(Clause);

  for (i = clause_FirstLitIndex();i < n;i++)
    Size += term_ComputeSize(clause_GetLiteralTerm(Clause,i));
  
  return Size;
}


BOOL clause_WeightCorrect(CLAUSE Clause, FLAGSTORE Flags, PRECEDENCE Precedence)
/*********************************************************
  INPUT:   A clause, a flag store and a precedence.
  RETURNS: TRUE iff the weight fields of the clause and its
           literals are correct.
**********************************************************/
{
  int     i, n;
  NAT     Weight, Help;
  LITERAL Lit;

#ifdef CHECK
  if (!clause_IsClause(Clause, Flags, Precedence)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_WeightCorrect:");
    misc_ErrorReport("\n Illegal input. Input not a clause.");
    misc_FinishErrorReport();
  }
#endif

  Weight = 0;
  n      = clause_Length(Clause);

  for (i = clause_FirstLitIndex(); i < n; i++) {
    Lit  = clause_GetLiteral(Clause, i);
    Help = clause_LiteralComputeWeight(Lit, Flags);
    if (Help != clause_LiteralWeight(Lit))
      return FALSE;
    Weight += Help;
  }

  return (clause_Weight(Clause) == Weight);
}


LIST clause_InsertWeighed(CLAUSE Clause, LIST UsList, FLAGSTORE Flags,
			  PRECEDENCE Precedence)
/*********************************************************
  INPUT:   A clause, a list to insert the clause into,
           a flag store and a precedence.
  RETURNS: The list where the clause is inserted wrt its
           weight (Weight(Car(list)) <= Weight(Car(Cdr(list)))).
  MEMORY:  A new listnode is allocated.
**********************************************************/
{
  LIST Scan;
  NAT  Weight;

#ifdef CHECK
  if (!clause_IsClause(Clause, Flags, Precedence)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_InsertWeighted:");
    misc_ErrorReport("\n Illegal input. Input not a clause.");
    misc_FinishErrorReport();
  }
#endif

  Weight = clause_Weight(Clause);

  Scan = UsList;

  if (list_Empty(Scan) ||
      (clause_Weight(list_Car(Scan)) > Weight)) {
    return list_Cons(Clause, Scan);

  } else {
    while (!list_Empty(list_Cdr(Scan)) &&
	   (clause_Weight(list_Car(list_Cdr(Scan))) <= Weight)) {
      Scan = list_Cdr(Scan);
    }
    list_Rplacd(Scan, list_Cons(Clause, list_Cdr(Scan)));
    return UsList;
  }
}


LIST clause_ListSortWeighed(LIST Clauses)
/*********************************************************
  INPUT:   A list of clauses.
  RETURNS: The clause list sorted with respect to the weight
           of clauses, minimal weight first.
  EFFECT:  The original list is destructively changed!
           This function doesn't sort stable!
           The function uses bucket sort for clauses with weight
	   smaller than clause_MAXWEIGHT, and the usual list sort
	   function for clauses with weight >= clause_MAXWEIGHT.
	   This implies the function uses time O(n-c + c*log c),
	   where n is the length of the list and c is the number
	   of clauses with weight >= clause_MAXWEIGHT.
	   For c=0 you get time O(n), for c=n you get time (n*log n).
**********************************************************/
{
  int  weight;
  LIST Scan;

  for (Scan=Clauses; !list_Empty(Scan); Scan=list_Cdr(Scan)) {
    weight = clause_Weight(list_Car(Scan));
    if (weight < clause_MAXWEIGHT)
      clause_SORT[weight] = list_Cons(list_Car(Scan),clause_SORT[weight]);
    else
      clause_SORT[clause_MAXWEIGHT] = list_Cons(list_Car(Scan),clause_SORT[clause_MAXWEIGHT]);
  }
  Scan = list_NumberSort(clause_SORT[clause_MAXWEIGHT],
			 (NAT (*)(POINTER)) clause_Weight);
  clause_SORT[clause_MAXWEIGHT] = list_Nil();
  for (weight = clause_MAXWEIGHT-1; weight >= 0; weight--) {
    Scan                = list_Nconc(clause_SORT[weight],Scan);
    clause_SORT[weight] = list_Nil();
  }
  list_Delete(Clauses);
  return Scan;
}


LITERAL clause_LiteralCopy(LITERAL Literal)
/*********************************************************
  INPUT:   A literal.
  RETURNS: An unshared copy of the literal, where the owning
           clause-slot is set to NULL.
  MEMORY:  Memory for a new LITERAL_NODE and all its TERMs
           subterms is allocated.
**********************************************************/
{

  LITERAL Result;

#ifdef CHECK
  if (!clause_LiteralIsLiteral(Literal)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_LiteralCopy:");
    misc_ErrorReport("\n Illegal input. Input not a literal.");
    misc_FinishErrorReport();
  }
#endif

  Result                = (LITERAL)memory_Malloc(sizeof(LITERAL_NODE));
  
  Result->atomWithSign  = term_Copy(clause_LiteralSignedAtom(Literal));
  Result->oriented      = clause_LiteralIsOrientedEquality(Literal);

  Result->maxLit        = Literal->maxLit;
  Result->weight        = Literal->weight;
  Result->owningClause  = (POINTER)NULL;

  return Result;
}


CLAUSE clause_Copy(CLAUSE Clause)
/*********************************************************
  INPUT:   A Clause.
  RETURNS: An unshared copy of the Clause.
  MEMORY:  Memory for a new CLAUSE_NODE, LITERAL_NODE and
           all its TERMs subterms is allocated.
**********************************************************/
{

  CLAUSE Result;
  int i,c,a,s,l;

  Result                = (CLAUSE)memory_Malloc(sizeof(CLAUSE_NODE));

  Result->clausenumber  = clause_Number(Clause);
  Result->maxVar        = clause_MaxVar(Clause);
  Result->flags         = Clause->flags;
  clause_InitSplitData(Result);
  Result->validlevel    = clause_SplitLevel(Clause);
  clause_SetSplitField(Result, Clause->splitfield, Clause->splitfield_length);
  Result->depth         = clause_Depth(Clause);
  Result->weight        = Clause->weight;
  Result->parentCls     = list_Copy(clause_ParentClauses(Clause));
  Result->parentLits    = list_Copy(clause_ParentLiterals(Clause));
  Result->origin        = clause_Origin(Clause);

  Result->c             = (c = clause_NumOfConsLits(Clause));
  Result->a             = (a = clause_NumOfAnteLits(Clause));
  Result->s             = (s = clause_NumOfSuccLits(Clause));

  l = c + a + s;
  if (l != 0)
    Result->literals      = (LITERAL *)memory_Malloc(l * sizeof(LITERAL));

  for (i = 0; i < l; i++) {
    clause_SetLiteral(Result, i,
		      clause_LiteralCopy(clause_GetLiteral(Clause, i)));
    clause_LiteralSetOwningClause((Result->literals[i]), Result);
  }

  return Result;
}


SYMBOL clause_LiteralMaxVar(LITERAL Literal)
/*********************************************************
  INPUT:   A literal.
  RETURNS: The maximal symbol of the literals variables,
           if the literal is ground, symbol_GetInitialStandardVarCounter().
**********************************************************/
{

  TERM Term;
  int Bottom;
  SYMBOL MaxSym,Help;

#ifdef CHECK
  if (!clause_LiteralIsLiteral(Literal)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_LiteralMaxVar:");
    misc_ErrorReport("\n Illegal input. Input not a literal.");
    misc_FinishErrorReport();
  }
#endif

  Bottom = stack_Bottom();
  MaxSym = symbol_GetInitialStandardVarCounter();
  Term   = clause_LiteralAtom(Literal);

  do {
    if (term_IsComplex(Term))
      stack_Push(term_ArgumentList(Term));
    else
      if (term_IsVariable(Term))
	MaxSym = ((MaxSym < (Help = term_TopSymbol(Term))) ?
		  Help : MaxSym);
    while (!stack_Empty(Bottom) && list_Empty(stack_Top()))
      stack_Pop();
    if (!stack_Empty(Bottom)) {
      Term = (TERM) list_Car(stack_Top());
      stack_RplacTop(list_Cdr(stack_Top()));
    }
  } while (!stack_Empty(Bottom));

  return MaxSym;
}


SYMBOL clause_AtomMaxVar(TERM Term)
/*********************************************************
  INPUT:   A term.
  RETURNS: The maximal symbol of the lcontained variables,
           if <Term> is ground, symbol_GetInitialStandardVarCounter().
**********************************************************/
{
  int Bottom;
  SYMBOL VarSym,Help;

  Bottom = stack_Bottom();
  VarSym = symbol_GetInitialStandardVarCounter();

  do {
    if (term_IsComplex(Term))
      stack_Push(term_ArgumentList(Term));
    else
      if (term_IsVariable(Term))
	VarSym = ((VarSym < (Help = term_TopSymbol(Term))) ?
		  Help : VarSym);
    while (!stack_Empty(Bottom) && list_Empty(stack_Top()))
      stack_Pop();
    if (!stack_Empty(Bottom)) {
      Term = (TERM)list_Car(stack_Top());
      stack_RplacTop(list_Cdr(stack_Top()));
    }
  } while (!stack_Empty(Bottom));

  return VarSym;
}


void clause_SetMaxLitFlags(CLAUSE Clause, FLAGSTORE FlagStore,
			   PRECEDENCE Precedence)
/**********************************************************
  INPUT:   A clause, a flag store and a precedence.
  RETURNS: Nothing.
  EFFECT:  Sets the maxLit-flag for maximal literals.
***********************************************************/
{
  int        i,j,n,fa;
  LITERAL    ActLit,CompareLit;
  BOOL       Result, Twin;
  ord_RESULT HelpRes;
  
  n   = clause_Length(Clause);
  fa  = clause_FirstAntecedentLitIndex(Clause);
  clause_RemoveFlag(Clause,CLAUSESELECT);
  for (i = clause_FirstLitIndex(); i < n; i++)
    clause_LiteralFlagReset(clause_GetLiteral(Clause, i));
  if (term_StampOverflow(clause_STAMPID))
    for (i = clause_FirstLitIndex(); i < n; i++)
      term_ResetTermStamp(clause_LiteralSignedAtom(clause_GetLiteral(Clause, i)));
  term_StartStamp();

  /*printf("\n Start: "); clause_Print(Clause);*/

  for (i = fa; i < n; i++) {
    ActLit = clause_GetLiteral(Clause, i);
    if (!term_HasTermStamp(clause_LiteralSignedAtom(ActLit))) {
      Result  = TRUE;
      Twin    = FALSE;
      for (j = fa; j < n && Result; j++)
	if (i != j) {
	  CompareLit = clause_GetLiteral(Clause, j);
	  HelpRes    = ord_LiteralCompare(clause_LiteralSignedAtom(ActLit),
					  clause_LiteralIsOrientedEquality(ActLit),
					  clause_LiteralSignedAtom(CompareLit),
					  clause_LiteralIsOrientedEquality(CompareLit),
					  FALSE, FlagStore, Precedence);
	  
	  /*printf("\n\tWe compare: ");
	    fol_PrintDFG(clause_LiteralAtom(ActLit));
	    putchar(' ');
	    fol_PrintDFG(clause_LiteralAtom(CompareLit));
	    printf(" Result: "); ord_Print(HelpRes);*/

	  if (ord_IsEqual(HelpRes))
	    Twin = TRUE;
	  if (ord_IsSmallerThan(HelpRes))
	    Result = FALSE;
	  if (ord_IsGreaterThan(HelpRes))
	    term_SetTermStamp(clause_LiteralSignedAtom(CompareLit));
	}
      if (Result) {
	clause_LiteralSetFlag(ActLit, MAXIMAL);
	if (!Twin)
	  clause_LiteralSetFlag(ActLit, STRICTMAXIMAL);
      }
    }
  }
  term_StopStamp();
  /*printf("\n End: "); clause_Print(Clause);*/
}


SYMBOL clause_SearchMaxVar(CLAUSE Clause)
/**********************************************************
  INPUT:   A clause.
  RETURNS: The maximal symbol of the clauses variables.
           If the clause is ground, symbol_GetInitialStandardVarCounter().
***********************************************************/
{
  int i, n;
  SYMBOL Help, MaxSym;
  
  n = clause_Length(Clause);

  MaxSym = symbol_GetInitialStandardVarCounter();

  for (i = 0; i < n; i++) {
    Help = clause_LiteralMaxVar(clause_GetLiteral(Clause, i));
    if (Help > MaxSym)
      MaxSym = Help;
  }
  return MaxSym;
}


void clause_RenameVarsBiggerThan(CLAUSE Clause, SYMBOL MinVar)
/**********************************************************
  INPUT:   A clause and a variable symbol.
  RETURNS: The clause with variables renamed in a way, that
           all vars are (excl.) bigger than MinVar.
***********************************************************/
{
  int i,n;
  
#ifdef CHECK
  if (!clause_IsUnorderedClause(Clause)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_RenameVarsBiggerThan:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  if (MinVar != symbol_GetInitialStandardVarCounter()) {
    n = clause_Length(Clause);

    term_StartMaxRenaming(MinVar);

    for (i = clause_FirstLitIndex(); i < n; i++)
      term_Rename(clause_GetLiteralTerm(Clause, i));
  }
}

void clause_Normalize(CLAUSE Clause)
/**********************************************************
  INPUT:   A clause.
  RETURNS: The term with normalized Variables, DESTRUCTIVE
           on the variable subterms' topsymbols.
***********************************************************/
{
  int i,n;
  
  n = clause_Length(Clause);

  term_StartMinRenaming();

  for (i = clause_FirstLitIndex(); i < n; i++)
    term_Rename(clause_GetLiteralTerm(Clause, i));
}


void clause_SubstApply(SUBST Subst, CLAUSE Clause)
/**********************************************************
  INPUT:   A clause.
  RETURNS: Nothing.
  EFFECTS: Applies the substitution to the clause.
***********************************************************/
{
  int i,n;

#ifdef CHECK
  if (!clause_IsUnorderedClause(Clause)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_SubstApply:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  n = clause_Length(Clause);

  for (i=clause_FirstLitIndex(); i<n; i++)
    clause_LiteralSetAtom(clause_GetLiteral(Clause, i),
			  subst_Apply(Subst,clause_GetLiteralAtom(Clause,i)));
}


void clause_ReplaceVariable(CLAUSE Clause, SYMBOL Var, TERM Term)
/**********************************************************
  INPUT:   A clause, a variable symbol, and a term.
  RETURNS: Nothing.
  EFFECTS: All occurences of the variable <Var> in <Clause>
           are replaced by copies if <Term>.
  CAUTION: The maximum variable of the clause is not updated!
***********************************************************/
{
  int i, li;

#ifdef CHECK
  if (!symbol_IsVariable(Var)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_ReplaceVariable: symbol is not a variable");
    misc_FinishErrorReport();
  }
#endif

  li = clause_LastLitIndex(Clause);
  for (i = clause_FirstLitIndex(); i <= li; i++)
    term_ReplaceVariable(clause_GetLiteralAtom(Clause,i), Var, Term);
}


void clause_UpdateMaxVar(CLAUSE Clause)
/**********************************************************
  INPUT:   A clause.
  RETURNS: Nothing.
  EFFECTS: Actualizes the MaxVar slot wrt the actual literals.
***********************************************************/
{
  clause_SetMaxVar(Clause, clause_SearchMaxVar(Clause));
}



void clause_OrientEqualities(CLAUSE Clause, FLAGSTORE FlagStore, 
			     PRECEDENCE Precedence)
/**********************************************************
  INPUT:   An unshared clause, a flag store and a precedence.
  RETURNS: Nothing.
  EFFECTS: Reorders the arguments of equality literals
           wrt. the ordering. Thus first arguments aren't smaller
	   after the application.
***********************************************************/
{
  int        i,length;
  LITERAL    EqLit;
  ord_RESULT HelpRes;

  /*printf("\n Clause: ");clause_Print(Clause);*/

  length = clause_Length(Clause);

  for (i = clause_FirstLitIndex(); i < length; i++) {
    EqLit = clause_GetLiteral(Clause, i);

    if (clause_LiteralIsEquality(EqLit)) {
      HelpRes = ord_Compare(term_FirstArgument(clause_LiteralAtom(EqLit)),
			    term_SecondArgument(clause_LiteralAtom(EqLit)),
			    FlagStore, Precedence);
      
      /*printf("\n\tWe compare: ");
      fol_PrintDFG(term_FirstArgument(clause_LiteralAtom(EqLit)));
      putchar(' ');
      fol_PrintDFG(term_SecondArgument(clause_LiteralAtom(EqLit)));
      printf("\nResult: "); ord_Print(HelpRes);*/

      switch(HelpRes) {

      case ord_SMALLER_THAN:
	/* printf("\nSwapping: ");
	   term_Print(clause_LiteralAtom(EqLit)); DBG */
	term_EqualitySwap(clause_LiteralAtom(EqLit));
	clause_LiteralSetOrientedEquality(EqLit);
	/*	Swapped = TRUE; */
	break;
      case ord_GREATER_THAN:
	clause_LiteralSetOrientedEquality(EqLit);
	break;
      default:
	clause_LiteralSetNoOrientedEquality(EqLit);
	break;
      }
    }
    else
      clause_LiteralSetNoOrientedEquality(EqLit);
  }
}


void  clause_InsertFlatIntoIndex(CLAUSE Clause, st_INDEX Index)
/**********************************************************
  INPUT:   An unshared clause and an index.
  EFFECT:  The atoms of <Clause> are inserted into the index.
           A link from the atom to its literal via the supertermlist
	   is established.
***********************************************************/
{
  int     i,n;
  LITERAL Lit;
  TERM    Atom    ;

  n = clause_Length(Clause);

  for (i=clause_FirstLitIndex();i<n;i++) {
    Lit  = clause_GetLiteral(Clause,i);
    Atom = clause_LiteralAtom(Lit);
    term_RplacSupertermList(Atom, list_List(Lit));
    st_EntryCreate(Index, Atom, Atom, cont_LeftContext());
  }
}

void  clause_DeleteFlatFromIndex(CLAUSE Clause, st_INDEX Index)
/**********************************************************
  INPUT:   An unshared clause and an index.
  EFFECT:  The clause is deleted from the index and deleted itself.
***********************************************************/
{
  int     i,n;
  LITERAL Lit;
  TERM    Atom    ;

  n = clause_Length(Clause);

  for (i=clause_FirstLitIndex();i<n;i++) {
    Lit  = clause_GetLiteral(Clause,i);
    Atom = clause_LiteralAtom(Lit);
    list_Delete(term_SupertermList(Atom));
    term_RplacSupertermList(Atom, list_Nil());
    st_EntryDelete(Index, Atom, Atom, cont_LeftContext());
  }
  clause_Delete(Clause);
}


void  clause_DeleteClauseListFlatFromIndex(LIST Clauses, st_INDEX Index)
/**********************************************************
  INPUT:   An list of unshared clause and an index.
  EFFECT:  The clauses are deleted from the index and deleted itself.
           The list is deleted.
***********************************************************/
{
  LIST Scan;

  for (Scan=Clauses;!list_Empty(Scan);Scan=list_Cdr(Scan))
    clause_DeleteFlatFromIndex(list_Car(Scan), Index);
  
  list_Delete(Clauses);
}


/******************************************************************/
/* Some special functions used by hyper inference/reduction rules */
/******************************************************************/

static void clause_VarToSizeMap(SUBST Subst, NAT* Map, NAT MaxIndex)
/**************************************************************
  INPUT:   A substitution, an array <Map> of size <MaxIndex>+1.
  RETURNS: Nothing.
  EFFECT:  The index i within the array corresponds to the index
           of a variable x_i. For each variable x_i, 0<=i<=MaxIndex
           the size of its substitution term is calculated
           and written to Map[i].
***************************************************************/
{
  NAT *Scan;

#ifdef CHECK
  if (subst_Empty(Subst) || Map == NULL) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_VarToSizeMap: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  /* Initialization */
  for (Scan = Map + MaxIndex; Scan >= Map; Scan--)
    *Scan = 1;
  /* Compute the size of substitution terms */
  for ( ; !subst_Empty(Subst); Subst = subst_Next(Subst))
    Map[subst_Dom(Subst)] = term_ComputeSize(subst_Cod(Subst));
}


static NAT clause_ComputeTermSize(TERM Term, NAT* VarMap)
/**************************************************************
  INPUT:   A term and a an array of NATs.
  RETURNS: The number of symbols in the term.
  EFFECT:  This function calculates the number of symbols in <Term>
           with respect to some substitution s.
           A naive way to do this is to apply the substitution
           to a copy of the term, and to count the number of symbols
           in the copied term.
           We use a more sophisticated algorithm, that first stores
	   the size of every variable's substitution term in <VarMap>.
           We then 'scan' the term and for a variable occurrence x_i
           we simply add the corresponding value VarMap[i] to the result.
           This way we avoid copying the term and the substitution terms,
           which is especially useful if we reuse the VarMap several times.
***************************************************************/
{
  NAT Stack, Size;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_ComputeTermSize: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  Size  = 0;
  Stack = stack_Bottom();
  do {
    if (VarMap!=NULL && symbol_IsVariable(term_TopSymbol(Term)))
      Size += VarMap[symbol_VarIndex(term_TopSymbol(Term))];
    else {
      Size++;
      if (term_IsComplex(Term))
        stack_Push(term_ArgumentList(Term));
    }
    while (!stack_Empty(Stack) && list_Empty(stack_Top()))
      stack_Pop();

    if (!stack_Empty(Stack)) {
      Term = list_Car(stack_Top());
      stack_RplacTop(list_Cdr(stack_Top()));
    }
  } while (!stack_Empty(Stack));

  return Size;
}


LIST clause_MoveBestLiteralToFront(LIST Literals, SUBST Subst, SYMBOL MaxVar,
				   BOOL (*Better)(LITERAL, NAT, LITERAL, NAT))
/**************************************************************
  INPUT:   A list of literals, a substitution, the maximum variable
           from the domain of the substitution, and a comparison
	   function. The function <Better> will be called with two
	   literals L1 and L2 and two number S1 and S2, where Si is
	   the size of the atom of Li with respect to variable bindings
	   in <Subst>.
  RETURNS: The same list.
  EFFECT:  This function moves the first literal L to the front of the
           list, so that no other literal L' is better than L with respect
	   to the function <Better>.
	   The function exchanges only the literals, the order of list
	   items within the list is not changed.
***************************************************************/
{
  NAT  *Map, MapSize, BestSize, Size;
  LIST Best, Scan;

#ifdef CHECK
  if (!list_IsSetOfPointers(Literals)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_MoveBestLiteralToFront: List contains duplicates");
    misc_FinishErrorReport();
  }
#endif

  if (list_Empty(Literals) || list_Empty(list_Cdr(Literals)))
    /* < 2 list items, so nothing to do */
    return Literals;

  Map     = NULL;
  MapSize = 0;

  if (!subst_Empty(Subst)) {
    MapSize = symbol_VarIndex(MaxVar) + 1;
    Map     = memory_Malloc(sizeof(NAT)*MapSize);
    clause_VarToSizeMap(Subst, Map, MapSize-1);
  }
  Best     = Literals; /* Remember list item, not literal itself */
  BestSize = clause_ComputeTermSize(clause_LiteralAtom(list_Car(Best)), Map);
  for (Scan = list_Cdr(Literals); !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    Size = clause_ComputeTermSize(clause_LiteralAtom(list_Car(Scan)), Map);
    if (Better(list_Car(Scan), Size, list_Car(Best), BestSize)) {
      /* Actual literal is better than the best encountered so far */
      BestSize = Size;
      Best     = Scan;
    }
  }
  if (Best != Literals) {
    /* Move best literal to the front. We just exchange the literals. */
    LITERAL h = list_Car(Literals);
    list_Rplaca(Literals, list_Car(Best));
    list_Rplaca(Best, h);
  }
  /* cleanup */
  if (Map != NULL)
    memory_Free(Map, sizeof(NAT)*MapSize);

  return Literals;
}


/**************************************************************/
/* Literal Output Functions                                   */
/**************************************************************/

void clause_LiteralPrint(LITERAL Literal)
/**************************************************************
  INPUT:   A Literal.
  RETURNS: Nothing.
***************************************************************/
{
#ifdef CHECK
  if (!clause_LiteralIsLiteral(Literal)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_LiteralPrint:");
    misc_ErrorReport("\n Illegal input. Input not a literal.");
    misc_FinishErrorReport();
  }
#endif

  term_PrintPrefix(clause_LiteralSignedAtom(Literal));
}


void clause_LiteralListPrint(LIST LitList)
/**************************************************************
  INPUT:   A list of literals.
  RETURNS: Nothing.
  SUMMARY: Prints the literals  to stdout.
***************************************************************/
{
  while (!(list_Empty(LitList))) {
    clause_LiteralPrint(list_First(LitList));
    LitList = list_Cdr(LitList);

    if (!list_Empty(LitList))
      putchar(' ');
  }
}


void clause_LiteralPrintUnsigned(LITERAL Literal)
/**************************************************************
  INPUT:   A Literal.
  RETURNS: Nothing.
  SUMMARY:
***************************************************************/
{
#ifdef CHECK
  if (!clause_LiteralIsLiteral(Literal)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_LiteralPrintUnsigned:");
    misc_ErrorReport("\n Illegal input. Input not a literal.");
    misc_FinishErrorReport();
  }
#endif

  term_PrintPrefix(clause_LiteralAtom(Literal));
  fflush(stdout);
}


void clause_LiteralPrintSigned(LITERAL Literal)
/**************************************************************
  INPUT:   A Literal.
  RETURNS: Nothing.
  SUMMARY:
***************************************************************/
{
#ifdef CHECK
  if (!clause_LiteralIsLiteral(Literal)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_LiteralPrintSigned:");
    misc_ErrorReport("\n Illegal input. Input not a literal.");
    misc_FinishErrorReport();
  }
#endif

  term_PrintPrefix(clause_LiteralSignedAtom(Literal));
  fflush(stdout);
}


void clause_LiteralFPrint(FILE* File, LITERAL Lit)
/**************************************************************
  INPUT:   A file and a literal.
  RETURNS: Nothing.
************************************************************/
{
  term_FPrintPrefix(File, clause_LiteralSignedAtom(Lit));
}


LIST clause_GetLiteralSubSetList(CLAUSE Clause, int StartIndex, int EndIndex, 
				 FLAGSTORE FlagStore, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause, a start literal index, an end index, a
           flag store and a precedence.
  RETURNS: The list of literals between the start and the end 
           index. 
	   It is a list of pointers, not a list of indices.
**************************************************************/
{

  LIST Result;
  int  i;

#ifdef CHECK
  if (!clause_IsClause(Clause, FlagStore, Precedence)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_ReplaceLiteralSubSet:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
  if ((StartIndex < clause_FirstLitIndex())
      || (EndIndex > clause_LastLitIndex(Clause))) {
    misc_ErrorReport("\n In clause_ReplaceLiteralSubSet:");
    misc_ErrorReport("\n Illegal input.");
    misc_ErrorReport("\n Index out of range.");
    misc_FinishErrorReport();
  }
#endif

  Result = list_Nil();

  for (i=StartIndex;
       i<=EndIndex;
       i++) {
    Result = list_Cons(clause_GetLiteral(Clause, i), Result);
  }

  return Result;
}


void clause_ReplaceLiteralSubSet(CLAUSE Clause, int StartIndex, 
				 int EndIndex, LIST Replacement,
				 FLAGSTORE FlagStore, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause, a start literal index, an end literal 
           index, a flag store and a precedence.
  RETURNS: None.
  EFFECT:  Replaces the subset of literals in <Clause> with 
           indices between (and including) <StartIndex> and
	   <EndIndex> with literals from the <Replacement>
	   list.
**************************************************************/
{

  int i;
  LIST Scan;

#ifdef CHECK
  if (!clause_IsClause(Clause, FlagStore, Precedence)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_ReplaceLiteralSubSet:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
  if ((StartIndex < clause_FirstLitIndex())
      || (EndIndex > clause_LastLitIndex(Clause))) {
    misc_ErrorReport("\n In clause_ReplaceLiteralSubSet:");
    misc_ErrorReport("\n Illegal input.");
    misc_ErrorReport("\n Index out of range.");
    misc_FinishErrorReport();
  }
  if (list_Length(Replacement) != (EndIndex - StartIndex + 1)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_ReplaceLiteralSubSet:");
    misc_ErrorReport("\n Illegal input.  Replacement list size");
    misc_ErrorReport("\n and set size don't match");
    misc_FinishErrorReport();
  }
#endif

  for (i = StartIndex, Scan = Replacement; 
       i <= EndIndex; 
       i++, Scan = list_Cdr(Scan)) {
    clause_SetLiteral(Clause, i, list_Car(Scan));
  } 
}

static __inline__ BOOL clause_LiteralsCompare(LITERAL Left, LITERAL Right)
/**************************************************************
  INPUT:   Two literals.
  RETURNS: TRUE if Left <= Right, FALSE otherwise.
  EFFECT:  Compares literals by comparing their terms' arities.
***************************************************************/
{
#ifdef CHECK
  if (!(clause_LiteralIsLiteral(Left) && clause_LiteralIsLiteral(Right))) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_LiteralsCompare:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  return term_CompareAbstractLEQ(clause_LiteralSignedAtom(Left),
				 clause_LiteralSignedAtom(Right));
}

static __inline__ void clause_FixLiteralSubsetOrder(CLAUSE Clause, 
						    int StartIndex, 
						    int EndIndex,
						    FLAGSTORE FlagStore,
						    PRECEDENCE Precedence) 
/**************************************************************
  INPUT:   A clause, a start index, an end index a flag store
           and a precedence.
  RETURNS: None.
  EFFECT:  Sorts literals with indices between (and including)
           <StartIndex> and <EndIndex> with respect to an abstract
	   list representation of terms that identifies function
	   symbols with their arity.
***************************************************************/
{

  LIST literals;

#ifdef CHECK
  if ((StartIndex < clause_FirstLitIndex())
      || (EndIndex > clause_LastLitIndex(Clause))) {
    misc_ErrorReport("\n In clause_FixLiteralSubSetOrder:");
    misc_ErrorReport("\n Illegal input.");
    misc_ErrorReport("\n Index out of range.");
    misc_FinishErrorReport();
  }
#endif

  /* Get the literals */
  literals = clause_GetLiteralSubSetList(Clause, StartIndex, EndIndex, FlagStore, Precedence);

  /* Sort them */
  literals = list_Sort(literals, (BOOL (*) (POINTER, POINTER)) clause_LiteralsCompare);

  /* Replace clause literals in subset with sorted literals */
  clause_ReplaceLiteralSubSet(Clause, StartIndex, EndIndex, literals, FlagStore, Precedence);

  list_Delete(literals);
}

void clause_FixLiteralOrder(CLAUSE Clause, FLAGSTORE FlagStore, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause, a flag store, and a precedence.
  RETURNS: None.
  EFFECT:  Fixes literal order in a <Clause>. Different literal
           types are ordered separately.
***************************************************************/
{
#ifdef CHECK
  if (!clause_IsClause(Clause, FlagStore, Precedence)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_FixLiteralOrder:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  /* Fix antecedent literal order */
  clause_FixLiteralSubsetOrder(Clause,
			       clause_FirstAntecedentLitIndex(Clause), 
			       clause_LastAntecedentLitIndex(Clause),
			       FlagStore, Precedence);

  /* Fix succedent literal order */
  clause_FixLiteralSubsetOrder(Clause,
			       clause_FirstSuccedentLitIndex(Clause), 
			       clause_LastSuccedentLitIndex(Clause),
			       FlagStore, Precedence);

  /* Fix constraint literal order */
  clause_FixLiteralSubsetOrder(Clause,
			       clause_FirstConstraintLitIndex(Clause), 
			       clause_LastConstraintLitIndex(Clause),
			       FlagStore, Precedence);  

  /* Normalize clause, to get variable names right. */
  clause_Normalize(Clause);
}

static int clause_CompareByWeight(CLAUSE Left, CLAUSE Right)
/**************************************************************
  INPUT:   Two clauses.
  RETURNS: 1 if left > right, -1 if left < right, 0 otherwise.
  EFFECT:  Compares two clauses by their weight.
***************************************************************/
{
  NAT lweight, rweight;
  int result;

  lweight = clause_Weight(Left);
  rweight = clause_Weight(Right);

  if (lweight < rweight) {
    result = -1;
  }
  else if (lweight > rweight) {
    result = 1;
  }
  else {
    result = 0;
  }

  return result;
}

static int clause_CompareByClausePartSize(CLAUSE Left, CLAUSE Right) 
/**************************************************************
  INPUT:   Two clauses.
  RETURNS: 1 if left > right, -1 if left < right, 0 otherwise.
  EFFECT:  Compares two clauses by the number of literals in
           the antecedent, succedent and constraint.
***************************************************************/
{
  int lsize, rsize;
  
  lsize = clause_NumOfAnteLits(Left);
  rsize = clause_NumOfAnteLits(Right);
  if (lsize < rsize)
    return -1;
  else if (lsize > rsize)
    return 1;
  
  lsize = clause_NumOfSuccLits(Left);
  rsize = clause_NumOfSuccLits(Right);
  
  if (lsize < rsize)
    return -1;
  else if (lsize > rsize)
    return 1;
  
  lsize = clause_NumOfConsLits(Left);
  rsize = clause_NumOfConsLits(Right);
  
  if (lsize < rsize)
    return -1;
  else if (lsize > rsize)
    return 1;
  
  return 0;
}

void clause_CountSymbols(CLAUSE Clause)
/**************************************************************
  INPUT:   A clause.
  RETURNS: None.
  EFFECT:  Counts the non-variable symbols in the clause, and 
           increases their counts accordingly.
***************************************************************/
{
  int i;

  for (i=clause_FirstLitIndex(); i<=clause_LastLitIndex(Clause); i++) {
    LITERAL l;
    TERM    t;

    l = clause_GetLiteral(Clause, i);
    if (clause_LiteralIsPredicate(l)) {
      SYMBOL S;

      S = clause_LiteralPredicate(l);
      symbol_SetCount(S, symbol_GetCount(S) + 1);
    }

    t = clause_GetLiteralAtom(Clause, i);

    term_CountSymbols(t);
  }
}


LIST clause_ListOfPredicates(CLAUSE Clause)
/**************************************************************
  INPUT:   A clause.
  RETURNS: A list of symbols.
  EFFECT:  Creates a list of predicates occurring in the clause.
           A predicate occurs several times in the list, if 
	   it does so in the clause.
***************************************************************/
{
  LIST preds;
  int i;

  preds = list_Nil();

  for (i=clause_FirstLitIndex(); i<=clause_LastLitIndex(Clause); i++) {
    LITERAL l;
	
    l = clause_GetLiteral(Clause, i);
    if (clause_LiteralIsPredicate(l)) {
      preds = list_Cons((POINTER) clause_LiteralPredicate(l), preds);
    }
  }

  return preds;
}

LIST clause_ListOfConstants(CLAUSE Clause)
/**************************************************************
  INPUT:   A clause.
  RETURNS: A list of symbols.
  EFFECT:  Creates a list of constants occurring in the clause.
           A constant occurs several times in the list, if 
	   it does so in the clause.
***************************************************************/
{
  LIST consts;
  int i;

  consts = list_Nil();

  for (i=clause_FirstLitIndex(); i<=clause_LastLitIndex(Clause); i++) {
    TERM t;
	
    t = clause_GetLiteralAtom(Clause, i);

    consts = list_Nconc(term_ListOfConstants(t), consts);
  }

  return consts;
}

LIST clause_ListOfVariables(CLAUSE Clause)
/**************************************************************
  INPUT:   A clause.
  RETURNS: A list of variables.
  EFFECT:  Creates a list of variables occurring in the clause.
           A variable occurs several times in the list, if 
	   it does so in the clause.
***************************************************************/
{
  LIST vars;
  int i;

  vars = list_Nil();

  for (i=clause_FirstLitIndex(); i<=clause_LastLitIndex(Clause); i++) {
    TERM t;
	
    t = clause_GetLiteralAtom(Clause, i);

    vars = list_Nconc(term_ListOfVariables(t), vars);
  }

  return vars;
}

LIST clause_ListOfFunctions(CLAUSE Clause)
/**************************************************************
  INPUT:   A clause.
  RETURNS: A list of symbols.
  EFFECT:  Creates a list of functions occurring in the clause.
           A function occurs several times in the list, if 
	   it does so in the clause.
***************************************************************/
{
  LIST funs;
  int i;

  funs = list_Nil();

  for (i=clause_FirstLitIndex(); i<=clause_LastLitIndex(Clause); i++) {
    TERM t;
	
    t = clause_GetLiteralAtom(Clause, i);

    funs = list_Nconc(term_ListOfFunctions(t), funs);
  }

  return funs;
}

static int clause_CompareByPredicateDistribution(CLAUSE Left, CLAUSE Right)
/**************************************************************
  INPUT:   Two clauses.
  RETURNS: 1 if left > right, -1 if left < right, 0 otherwise.
  EFFECT:  Compares two clauses by the frequency of predicates.
***************************************************************/
{
  LIST lpreds, rpreds;
  int  result;

  lpreds = clause_ListOfPredicates(Left);
  rpreds = clause_ListOfPredicates(Right);

  result = list_CompareMultisetsByElementDistribution(lpreds, rpreds);

  list_Delete(lpreds);
  list_Delete(rpreds);

  return result;
}

static int clause_CompareByConstantDistribution(CLAUSE Left, CLAUSE Right)
/**************************************************************
  INPUT:   Two clauses.
  RETURNS: 1 if left > right, -1 if left < right, 0 otherwise.
  EFFECT:  Compares two clauses by the frequency of constants.
***************************************************************/
{
  LIST lconsts, rconsts;
  int  result;

  lconsts = clause_ListOfConstants(Left);
  rconsts = clause_ListOfConstants(Right);

  result = list_CompareMultisetsByElementDistribution(lconsts, rconsts);

  list_Delete(lconsts);
  list_Delete(rconsts);

  return result;
}

static int clause_CompareByVariableDistribution(CLAUSE Left, CLAUSE Right)
/**************************************************************
  INPUT:   Two clauses.
  RETURNS: 1 if left > right, -1 if left < right, 0 otherwise.
  EFFECT:  Compares two clauses by the frequency of variables.
***************************************************************/
{
  LIST lvars, rvars;
  int  result;

  lvars = clause_ListOfVariables(Left);
  rvars = clause_ListOfVariables(Right);

  result = list_CompareMultisetsByElementDistribution(lvars, rvars);

  list_Delete(lvars);
  list_Delete(rvars);

  return result;
}

static int clause_CompareByFunctionDistribution(CLAUSE Left, CLAUSE Right)
/**************************************************************
  INPUT:   Two clauses.
  RETURNS: 1 if left > right, -1 if left < right, 0 otherwise.
  EFFECT:  Compares two clauses by the frequency of functions.
***************************************************************/
{
  LIST lfuns, rfuns;
  int  result;

  lfuns = clause_ListOfFunctions(Left);
  rfuns = clause_ListOfFunctions(Right);

  result = list_CompareMultisetsByElementDistribution(lfuns, rfuns);

  list_Delete(lfuns);
  list_Delete(rfuns);

  return result;
}

static int clause_CompareByDepth(CLAUSE Left, CLAUSE Right) 
/**************************************************************
  INPUT:   Two clauses.
  RETURNS: 1 if left > right, -1 if left < right, 0 otherwise.
  EFFECT:  Compares two clauses by their depth.
***************************************************************/
{
  if (clause_Depth(Left) < clause_Depth(Right))
    return -1;
  else if (clause_Depth(Left) > clause_Depth(Right))
    return 1;

  return 0;
}

static int clause_CompareByMaxVar(CLAUSE Left, CLAUSE Right)
/**************************************************************
  INPUT:   Two clauses.
  RETURNS: 1 if left > right, -1 if left < right, 0 otherwise.
  EFFECT:  Compares two clauses by their maximal variable.
***************************************************************/ 
{
  if (clause_MaxVar(Left) < clause_MaxVar(Right))
    return -1;
  else if (clause_MaxVar(Left) > clause_MaxVar(Right))
    return 1;

  return 0;
}

static int clause_CompareByLiterals(CLAUSE Left, CLAUSE Right) 
/**************************************************************
  INPUT:   Two clauses.
  RETURNS: 1 if left > right, -1 if left < right, 0 otherwise.
  EFFECT:  Compares two clauses by comparing their literals 
           from left to right.
***************************************************************/
{
  int firstlitleft, lastlitleft;
  int firstlitright, lastlitright;
  int i, j;
  int result;

  result = 0;

  /* Compare sorted literals from right to left */
  
  firstlitleft  = clause_FirstLitIndex();
  lastlitleft   = clause_LastLitIndex(Left);
  firstlitright = clause_FirstLitIndex();
  lastlitright  = clause_LastLitIndex(Right);
  
  for (i = lastlitleft, j = lastlitright;
       i >= firstlitleft && j >= firstlitright;
       --i, --j) {
    TERM lterm, rterm;
    
    lterm = clause_GetLiteralTerm(Left, i);
    rterm = clause_GetLiteralTerm(Right, j);
    
    result = term_CompareAbstract(lterm, rterm);
    
    if (result != 0)
      break;
  }

  if (result == 0) {
    /* All literals compared equal, so check if someone has 
       uncompared literals left over.
    */
    if ( i > j) {
      /* Left clause has uncompared literals left over. */
      result =  1;
    }
    else if (i < j) {
      /* Right clause has uncompared literals left over. */
      result = -1;
    }
  }

  return result;
}

static int clause_CompareBySymbolOccurences(CLAUSE Left, CLAUSE Right) 
/**************************************************************
  INPUT:   Two clauses.
  RETURNS: 1 if left > right, -1 if left < right, 0 otherwise.
  EFFECT:  Compares two clauses by comparing the occurrences of
           symbols in their respective literals from left to 
	   right. If a symbol occurs less frequently than
	   its positional equivalent in the other clause,
	   then the first clause is smaller.
***************************************************************/
{
  int firstlitleft, lastlitleft;
  int firstlitright, lastlitright;
  int i, j;
  int result;

  result = 0;

  /* Compare sorted literals from right to left */
  
  firstlitleft  = clause_FirstLitIndex();
  lastlitleft   = clause_LastLitIndex(Left);
  firstlitright = clause_FirstLitIndex();
  lastlitright  = clause_LastLitIndex(Right);
  
  for (i = lastlitleft, j = lastlitright;
       i >= firstlitleft && j >= firstlitright;
       --i, --j) {
    TERM lterm, rterm;
    LITERAL llit, rlit;
	
    llit = clause_GetLiteral(Left, i);
    rlit = clause_GetLiteral(Right, j);

    if (clause_LiteralIsPredicate(llit)) {
      if (clause_LiteralIsPredicate(rlit)) {
	if (symbol_GetCount(clause_LiteralPredicate(llit)) 
	    < symbol_GetCount(clause_LiteralPredicate(rlit))) {
	  return -1;
	}
	else if (symbol_GetCount(clause_LiteralPredicate(llit)) 
	    > symbol_GetCount(clause_LiteralPredicate(rlit))) {
	  return 1;
	}
      }
    }
    
    lterm = clause_GetLiteralTerm(Left, i);
    rterm = clause_GetLiteralTerm(Right, j);
    
    result = term_CompareBySymbolOccurences(lterm, rterm);
    
    if (result != 0)
      break;
  }

  return result;
}

int clause_CompareAbstract(CLAUSE Left, CLAUSE Right)
/**************************************************************
  INPUT:   Two clauses.
  RETURNS: 1 if left > right, -1 if left < right, 0 otherwise.
  EFFECT:  Compares two clauses by their weight. If the weight
           is equal, it compares the clauses by the arity of
	   their literals from right to left.
  CAUTION: Expects clause literal order to be fixed.
***************************************************************/
{

  typedef int (*CLAUSE_COMPARE_FUNCTION) (CLAUSE, CLAUSE);

  static const CLAUSE_COMPARE_FUNCTION clause_compare_functions [] = {
    clause_CompareByWeight,
    clause_CompareByDepth,
    clause_CompareByMaxVar,
    clause_CompareByClausePartSize,
    clause_CompareByLiterals,
    clause_CompareBySymbolOccurences,
    clause_CompareByPredicateDistribution,
    clause_CompareByConstantDistribution,
    clause_CompareByFunctionDistribution,
    clause_CompareByVariableDistribution,
  };

  int result;
  int i;
  int functions;

  result    = 0;
  functions = sizeof(clause_compare_functions)/sizeof(CLAUSE_COMPARE_FUNCTION);

  for (i = 0; i < functions; i++) {
    result = clause_compare_functions[i](Left, Right);

    if ( result != 0) {
      return result;
    }
  }

  return 0;
}


/**************************************************************/
/* Clause functions                                           */
/**************************************************************/

void clause_Init(void)
/**************************************************************
  INPUT:   None.
  RETURNS: Nothing.
  SUMMARY: Initializes the clause counter and other variables
           from this module.
***************************************************************/
{
  int i;
  clause_SetCounter(1);
  clause_STAMPID = term_GetStampID();
  for (i = 0; i <= clause_MAXWEIGHT; i++)
    clause_SORT[i] = list_Nil();
}


CLAUSE clause_CreateBody(int ClauseLength)
/**************************************************************
  INPUT:   The number of literals as integer.
  RETURNS: A new generated clause node for 'ClauseLength'
  MEMORY:  Allocates a CLAUSE_NODE and the needed array for LITERALs.
*************************************************************/
{
  CLAUSE Result;

  Result                = (CLAUSE)memory_Malloc(sizeof(CLAUSE_NODE));

  Result->clausenumber  = clause_IncreaseCounter();
  Result->maxVar        = symbol_GetInitialStandardVarCounter();
  Result->flags         = 0;
  Result->depth         = 0;
  clause_InitSplitData(Result);
  Result->weight        = clause_WEIGHTUNDEFINED;
  Result->parentCls     = list_Nil();
  Result->parentLits    = list_Nil();

  Result->c             = 0;
  Result->a             = 0;
  Result->s             = 0;

  if (ClauseLength != 0)
    Result->literals =
      (LITERAL *)memory_Malloc((ClauseLength) * sizeof(LITERAL));

  clause_SetFromInput(Result);

  return Result;
}


CLAUSE clause_Create(LIST Constraint, LIST Antecedent, LIST Succedent,
		     FLAGSTORE Flags, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   Three lists of pointers to atoms, a flag store and 
           a precedence.
  RETURNS: The new generated clause.
  MEMORY:  Allocates a CLAUSE_NODE and the needed LITERAL_NODEs,
           uses the terms from the lists, additionally allocates
	   termnodes for the fol_Not() in Const. and Ante.
*************************************************************/
{
  CLAUSE Result;
  int    i, c, a, s;
  
  Result                = (CLAUSE)memory_Malloc(sizeof(CLAUSE_NODE));
  
  Result->clausenumber  = clause_IncreaseCounter();
  Result->flags         = 0;
  Result->depth         = 0;
  Result->weight        = clause_WEIGHTUNDEFINED;
  clause_InitSplitData(Result);
  Result->parentCls     = list_Nil();
  Result->parentLits    = list_Nil();

  Result->c             = (c = list_Length(Constraint));
  Result->a             = (a = list_Length(Antecedent));
  Result->s             = (s = list_Length(Succedent));

  if (!clause_IsEmptyClause(Result))
    Result->literals =
      (LITERAL *) memory_Malloc((c+a+s) * sizeof(LITERAL));
  
  for (i = 0; i < c; i++) {
    Result->literals[i] =
      clause_LiteralCreate(term_Create(fol_Not(),
	list_List((TERM)list_Car(Constraint))),Result);
    Constraint = list_Cdr(Constraint);
  }
  
  a += c;
  for ( ; i < a; i++) {
    Result->literals[i] =
      clause_LiteralCreate(term_Create(fol_Not(),
	list_List((TERM)list_Car(Antecedent))), Result);
    Antecedent = list_Cdr(Antecedent);
  }
  
  s += a;
  for ( ; i < s; i++) {
    Result->literals[i] =
      clause_LiteralCreate((TERM) list_Car(Succedent), Result);
    Succedent = list_Cdr(Succedent);
  }
  
  clause_OrientAndReInit(Result, Flags, Precedence);
  clause_SetFromInput(Result);
  
  return Result;
}


CLAUSE clause_CreateCrude(LIST Constraint, LIST Antecedent, LIST Succedent,
			  BOOL Con)
/**************************************************************
  INPUT:   Three lists of pointers to literals (!) and a Flag indicating
           whether the clause comes from the conjecture part of of problem.
	   It is assumed that Constraint and Antecedent literals are negative,
	   whereas Succedent literals are positive.
  RETURNS: The new generated clause, where a clause_OrientAndReInit has still
           to be performed, i.e., variables are not normalized, maximal literal
	   flags not set, equations not oriented, the weight is not set.
  MEMORY:  Allocates a CLAUSE_NODE and the needed LITERAL_NODEs,
           uses the terms from the lists, additionally allocates
	   termnodes for the fol_Not() in Const. and Ante.
****************************************************************/
{
  CLAUSE Result;
  int i,c,a,s;
  
  Result                = (CLAUSE)memory_Malloc(sizeof(CLAUSE_NODE));
  
  Result->clausenumber  = clause_IncreaseCounter();
  Result->flags         = 0;
  if (Con)
    clause_SetFlag(Result, CONCLAUSE);

  Result->depth         = 0;
  Result->weight        = clause_WEIGHTUNDEFINED;
  clause_InitSplitData(Result);
  Result->parentCls     = list_Nil();
  Result->parentLits    = list_Nil();

  Result->c             = (c = list_Length(Constraint));
  Result->a             = (a = list_Length(Antecedent));
  Result->s             = (s = list_Length(Succedent));

  if (!clause_IsEmptyClause(Result))
    Result->literals = (LITERAL *)memory_Malloc((c+a+s) * sizeof(LITERAL));
  
  for (i = 0; i < c; i++) {
    Result->literals[i] =
      clause_LiteralCreate(list_Car(Constraint),Result);
    Constraint = list_Cdr(Constraint);
  }
  
  a += c;
  for ( ; i < a; i++) {
    Result->literals[i] =
      clause_LiteralCreate(list_Car(Antecedent), Result);
    Antecedent = list_Cdr(Antecedent);
  }
  
  s += a;
  for ( ; i < s; i++) {
    Result->literals[i] = clause_LiteralCreate(list_Car(Succedent), Result);
    Succedent = list_Cdr(Succedent);
  }
  
  clause_SetFromInput(Result);
  
  return Result;
}


CLAUSE clause_CreateUnnormalized(LIST Constraint, LIST Antecedent,
				 LIST Succedent)
/**************************************************************
  INPUT:   Three lists of pointers to atoms.
  RETURNS: The new generated clause.
  MEMORY:  Allocates a CLAUSE_NODE and the needed LITERAL_NODEs,
           uses the terms from the lists, additionally allocates
	   termnodes for the fol_Not() in Const. and Ante.
  CAUTION: The weight of the clause is not set correctly and
           equations are not oriented!
****************************************************************/
{
  CLAUSE Result;
  int i,c,a,s;

  Result                = (CLAUSE)memory_Malloc(sizeof(CLAUSE_NODE));

  Result->clausenumber  = clause_IncreaseCounter();
  Result->flags         = 0;
  Result->depth         = 0;
  Result->weight        = clause_WEIGHTUNDEFINED;
  clause_InitSplitData(Result);
  Result->parentCls     = list_Nil();
  Result->parentLits    = list_Nil();

  Result->c             = (c = list_Length(Constraint));
  Result->a             = (a = list_Length(Antecedent));
  Result->s             = (s = list_Length(Succedent));

  if (!clause_IsEmptyClause(Result)) {
    Result->literals = (LITERAL *)memory_Malloc((c+a+s) * sizeof(LITERAL));
  
    for (i = 0; i < c; i++) {
      Result->literals[i] =
	clause_LiteralCreate(term_Create(fol_Not(),
					 list_List(list_Car(Constraint))),
			     Result);
      Constraint = list_Cdr(Constraint);
    }

    a += c;
    for ( ; i < a; i++) {
      Result->literals[i]  =
	clause_LiteralCreate(term_Create(fol_Not(),
					 list_List(list_Car(Antecedent))),
			     Result);
      Antecedent = list_Cdr(Antecedent);
    }

    s += a;
    for ( ; i < s; i++) {
      Result->literals[i] =
	clause_LiteralCreate((TERM)list_Car(Succedent), Result);
      Succedent = list_Cdr(Succedent);
    }
    clause_UpdateMaxVar(Result);
  }

  return Result;
}


CLAUSE clause_CreateFromLiterals(LIST LitList, BOOL Sorts, BOOL Conclause,
				 BOOL Ordering, FLAGSTORE Flags,
				 PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A list of literals, three boolean flags indicating whether
           sort constraint literals should be generated, whether the
	   clause is a conjecture clause, whether the ordering information
	   should be established, a flag store and a precedence.
  RETURNS: The new generated clause.
  EFFECT:  The result clause will be normalized and the maximal
           variable will be set. If <Ordering> is FALSE no additional
	   initializations will be done. This mode is intended for
	   the parser for creating clauses at a time when the ordering
	   and weight flags aren't determined finally.
	   Only if <Ordering> is TRUE the equations will be oriented,
	   the maximal literals will be marked and the clause weight
	   will be set correctly.
  MEMORY:  Allocates a CLAUSE_NODE and the needed LITERAL_NODEs,
           uses the terms from the lists.
****************************************************************/
{
  CLAUSE Result;
  LIST   Antecedent,Succedent,Constraint;
  TERM   Atom;

  Antecedent = list_Nil();
  Succedent  = list_Nil();
  Constraint = list_Nil();

  while (!list_Empty(LitList)) {
    if (term_TopSymbol(list_Car(LitList)) == fol_Not()) {
      Atom = term_FirstArgument(list_Car(LitList));
      if (Sorts && symbol_IsBaseSort(term_TopSymbol(Atom)) && term_IsVariable(term_FirstArgument(Atom)))
	Constraint = list_Cons(list_Car(LitList),Constraint);
      else
	Antecedent = list_Cons(list_Car(LitList),Antecedent);
    }
    else
      Succedent = list_Cons(list_Car(LitList),Succedent);
    LitList = list_Cdr(LitList);
  }
  
  Constraint = list_NReverse(Constraint);
  Antecedent = list_NReverse(Antecedent);
  Succedent  = list_NReverse(Succedent);
  Result = clause_CreateCrude(Constraint, Antecedent, Succedent, Conclause);

  list_Delete(Constraint);
  list_Delete(Antecedent);
  list_Delete(Succedent);

  if (Ordering)
    clause_OrientAndReInit(Result, Flags, Precedence);
  else {
    clause_Normalize(Result);
    clause_UpdateMaxVar(Result);
  }
  
  return Result;
}

void clause_SetSortConstraint(CLAUSE Clause, BOOL Strong, FLAGSTORE Flags,
			      PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause, a flag indicating whether also negative
           monadic literals with a real term argument should be
	   put in the sort constraint, a flag store and a precedence.
  RETURNS: Nothing.
  EFFECT:  Negative monadic literals are put in the sort constraint.
****************************************************************/
{
  LITERAL ActLit,Help;
  TERM    ActAtom;
  int     i,k,NewConLits;


#ifdef CHECK
  if (!clause_IsUnorderedClause(Clause)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_SetSortConstraint:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  i          = clause_LastConstraintLitIndex(Clause);
  NewConLits = 0;

  for (k=clause_FirstAntecedentLitIndex(Clause);k<=clause_LastAntecedentLitIndex(Clause);k++) {
    ActLit  = clause_GetLiteral(Clause,k);
    ActAtom = clause_LiteralAtom(ActLit);
    if (symbol_IsBaseSort(term_TopSymbol(ActAtom)) &&
	(Strong || term_IsVariable(term_FirstArgument(ActAtom)))) {
      if (++i != k) {
	Help = clause_GetLiteral(Clause,i);
	clause_SetLiteral(Clause,i,ActLit);
	clause_SetLiteral(Clause,k,Help);
      }
      NewConLits++;
    }
  }

  clause_SetNumOfConsLits(Clause, clause_NumOfConsLits(Clause) + NewConLits);
  clause_SetNumOfAnteLits(Clause, clause_NumOfAnteLits(Clause) - NewConLits);
  clause_ReInit(Clause, Flags, Precedence);

#ifdef CHECK
  if (!clause_IsUnorderedClause(Clause)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_SetSortConstraint:");
    misc_ErrorReport("\n Illegal computations.");
    misc_FinishErrorReport();
  }
#endif

}



void clause_Delete(CLAUSE Clause)
/**************************************************************
  INPUT:   A Clause.
  RETURNS: Nothing.
  MEMORY:  Frees the memory of the clause.
***************************************************************/
{
  int i, n;

#ifdef CHECK
  if (!clause_IsUnorderedClause(Clause)) { /* Clause may be a byproduct of some hyper rule */
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_Delete:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  n = clause_Length(Clause);
  
  for (i = 0; i < n; i++)
    clause_LiteralDelete(clause_GetLiteral(Clause,i));

  clause_FreeLitArray(Clause);
  
  list_Delete(clause_ParentClauses(Clause));
  list_Delete(clause_ParentLiterals(Clause));
#ifdef CHECK
  if ((Clause->splitfield != NULL) && (Clause->splitfield_length == 0))
    {
      misc_StartErrorReport();
      misc_ErrorReport("\n In clause_Delete:");
      misc_ErrorReport("\n Illegal splitfield_length.");
      misc_FinishErrorReport();
    }
  if ((Clause->splitfield == NULL) && (Clause->splitfield_length != 0))
    {
      misc_StartErrorReport();
      misc_ErrorReport("\n In clause_Delete:");
      misc_ErrorReport("\n Illegal splitfield.");
      misc_FinishErrorReport();
    }
#endif
  if (Clause->splitfield != NULL) {
    
    memory_Free(Clause->splitfield,
		sizeof(SPLITFIELDENTRY) * Clause->splitfield_length);
  }
  clause_Free(Clause);
}


/**************************************************************/
/* Functions to use the sharing for clauses.                  */
/**************************************************************/

void clause_InsertIntoSharing(CLAUSE Clause, SHARED_INDEX ShIndex,
			      FLAGSTORE Flags, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A Clause, an index, a flag store and a precedence.
  RETURNS: Nothing.
  SUMMARY: Inserts the unsigned atoms of 'Clause' into the sharing index.
***************************************************************/
{
  int i, litnum;

#ifdef CHECK
  if (!clause_IsClause(Clause, Flags, Precedence)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_Delete:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
  clause_Check(Clause, Flags, Precedence);
#endif

  litnum = clause_Length(Clause);

  for (i = 0; i < litnum; i++) {
    clause_LiteralInsertIntoSharing(clause_GetLiteral(Clause,i), ShIndex);
  }
}


void clause_DeleteFromSharing(CLAUSE Clause, SHARED_INDEX ShIndex,
			      FLAGSTORE Flags, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A Clause, an Index, a flag store and a precedence.
  RETURNS: Nothing.
  SUMMARY: Deletes 'Clause' and all its literals from the sharing,
           frees the memory of 'Clause'.
***************************************************************/
{
  int i, length;

#ifdef CHECK
  if (!clause_IsClause(Clause, Flags, Precedence)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_DeleteFromSharing:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  length = clause_Length(Clause);
  
  for (i = 0; i < length; i++)
    clause_LiteralDeleteFromSharing(clause_GetLiteral(Clause,i),ShIndex);
  
  clause_FreeLitArray(Clause);
  
  list_Delete(clause_ParentClauses(Clause));
  list_Delete(clause_ParentLiterals(Clause));
#ifdef CHECK
  if ((Clause->splitfield != NULL) && (Clause->splitfield_length == 0))
    {
      misc_StartErrorReport();
      misc_ErrorReport("\n In clause_DeleteFromSharing:");
      misc_ErrorReport("\n Illegal splitfield_length.");
      misc_FinishErrorReport();
    }
  if ((Clause->splitfield == NULL) && (Clause->splitfield_length != 0))
    {
      misc_StartErrorReport();
      misc_ErrorReport("\n In clause_DeleteFromSharing:");
      misc_ErrorReport("\n Illegal splitfield.");
      misc_FinishErrorReport();
    }
#endif
  if (Clause->splitfield != NULL) {
    memory_Free(Clause->splitfield,
		sizeof(SPLITFIELDENTRY) * Clause->splitfield_length);
  }
  clause_Free(Clause);
}


void clause_MakeUnshared(CLAUSE Clause, SHARED_INDEX ShIndex)
/**************************************************************
  INPUT:   A Clause and an Index.
  RETURNS: Nothing.
  SUMMARY: Deletes the clauses literals from the sharing and
           replaces them by unshared copies.
***************************************************************/
{
  LITERAL ActLit;
  TERM SharedAtom, AtomCopy;
  int i,LastAnte,length;

#ifdef CHECK
  if (!clause_IsUnorderedClause(Clause)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_MakeUnshared:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  LastAnte = clause_LastAntecedentLitIndex(Clause);
  length   = clause_Length(Clause);

  for (i = clause_FirstLitIndex(); i <= LastAnte; i++) {
    ActLit     = clause_GetLiteral(Clause, i);
    SharedAtom = clause_LiteralAtom(ActLit);
    AtomCopy   = term_Copy(SharedAtom);
    sharing_Delete(ActLit, SharedAtom, ShIndex);
    clause_LiteralSetNegAtom(ActLit, AtomCopy);
  }

  for ( ; i < length; i++) {
    ActLit     = clause_GetLiteral(Clause, i);
    SharedAtom = clause_LiteralSignedAtom(ActLit);
    AtomCopy   = term_Copy(SharedAtom);
    sharing_Delete(ActLit, SharedAtom, ShIndex);
    clause_LiteralSetPosAtom(ActLit, AtomCopy);
  }
}

void clause_MoveSharedClause(CLAUSE Clause, SHARED_INDEX Source,
			     SHARED_INDEX Destination, FLAGSTORE Flags,
			     PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A Clause, two indexes, a flag store, and a precedence.
  RETURNS: Nothing.
  EFFECT:  Deletes <Clause> from <Source> and inserts it into 
           <Destination>.
***************************************************************/
{
  LITERAL Lit;
  TERM    Atom,Copy;
  int     i,length;

#ifdef CHECK
  if (!clause_IsClause(Clause, Flags, Precedence)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_MoveSharedClause:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  length   = clause_Length(Clause);

  for (i = clause_FirstLitIndex(); i < length; i++) {
    Lit  = clause_GetLiteral(Clause, i);
    Atom = clause_LiteralAtom(Lit);
    Copy = term_Copy(Atom);        /* sharing_Insert works destructively on <Copy>'s superterms */
    clause_LiteralSetAtom(Lit, sharing_Insert(Lit, Copy, Destination));
    sharing_Delete(Lit, Atom, Source);
    term_Delete(Copy);
  }
}


void clause_DeleteSharedLiteral(CLAUSE Clause, int Indice, SHARED_INDEX ShIndex, 
				FLAGSTORE Flags, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A Clause, a literals indice, an Index, a flag store
           and a precedence.
  RETURNS: Nothing.
  SUMMARY: Deletes the shared literal from the clause.
  MEMORY:  Various.
***************************************************************/
{

#ifdef CHECK
  if (!clause_IsClause(Clause, Flags, Precedence)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_DeleteSharedLiteral:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  clause_MakeUnshared(Clause, ShIndex);
  clause_DeleteLiteral(Clause, Indice, Flags, Precedence);
  clause_InsertIntoSharing(Clause, ShIndex, Flags, Precedence);
}


void clause_DeleteClauseList(LIST ClauseList)
/**************************************************************
  INPUT:   A list of unshared clauses.
  RETURNS: Nothing.
  SUMMARY: Deletes all clauses in the list and the list.
  MEMORY:  Frees the lists and the clauses' memory.
 ***************************************************************/
{
  LIST Scan;

  for (Scan = ClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan))
    if (clause_Exists(list_Car(Scan)))
      clause_Delete(list_Car(Scan));

  list_Delete(ClauseList);
}


void clause_DeleteSharedClauseList(LIST ClauseList, SHARED_INDEX ShIndex,
				   FLAGSTORE Flags, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A list of clauses, an index, a flag store and 
           a precedence.
  RETURNS: Nothing.
  SUMMARY: Deletes all clauses in the list from the sharing.
  MEMORY:  Frees the lists and the clauses' memory.
***************************************************************/
{
  LIST Scan;

  for (Scan = ClauseList; !list_Empty(Scan); Scan = list_Cdr(Scan))
    clause_DeleteFromSharing(list_Car(Scan), ShIndex, Flags, Precedence);

  list_Delete(ClauseList);
}


void clause_DeleteAllIndexedClauses(SHARED_INDEX ShIndex, FLAGSTORE Flags,
				    PRECEDENCE Precedence)
/**************************************************************
  INPUT:   An Index, a flag store and a precedence.
  RETURNS: Nothing.
  SUMMARY: Deletes all clauses' terms from the sharing, frees their
           memory.
  MEMORY:  Frees the memory of all clauses with terms in the index.
***************************************************************/
{
  LIST TermList,DelList,Scan;
  TERM NewVar;
  SYMBOL NewVarSymbol;

  NewVar = term_CreateStandardVariable();
  NewVarSymbol = term_TopSymbol(NewVar);

  TermList = st_GetInstance(cont_LeftContext(), sharing_Index(ShIndex), NewVar);
  /* This should yield a list of all terms in the index
     and thus the sharing. */

  while (!list_Empty(TermList)) {

    DelList = sharing_GetDataList(list_Car(TermList), ShIndex);

    for (Scan = DelList;
	 !list_Empty(Scan);
	 Scan = list_Cdr(Scan))
      list_Rplaca(Scan, clause_LiteralOwningClause(list_Car(Scan)));

    DelList = list_PointerDeleteDuplicates(DelList);

    for (Scan = DelList;
	 !list_Empty(Scan);
	 Scan = list_Cdr(Scan))
      clause_DeleteFromSharing(list_Car(Scan), ShIndex, Flags, Precedence);

    list_Delete(TermList);

    TermList = st_GetInstance(cont_LeftContext(), sharing_Index(ShIndex), NewVar);

    list_Delete(DelList);
  }
  term_Delete(NewVar);
  symbol_Delete(NewVarSymbol);
}


void clause_PrintAllIndexedClauses(SHARED_INDEX ShIndex)
/**************************************************************
  INPUT:   An Index.
  RETURNS: Nothing.
  SUMMARY: Prints all indexed clauses to stdout.
***************************************************************/
{
  LIST TermList,ClList,PrintList,Scan;
  TERM NewVar;
  SYMBOL NewVarSymbol;

  NewVar = term_CreateStandardVariable();
  NewVarSymbol = term_TopSymbol(NewVar);

  TermList = st_GetInstance(cont_LeftContext(), sharing_Index(ShIndex), NewVar);
  /* This should yield a list of all terms in the index
     and thus the sharing. */

  PrintList = list_Nil();

  while (!list_Empty(TermList)) {

    ClList = sharing_GetDataList(list_Car(TermList), ShIndex);

    for (Scan = ClList;
	 !list_Empty(Scan);
	 Scan = list_Cdr(Scan))
      list_Rplaca(Scan, clause_LiteralOwningClause(list_Car(Scan)));

    PrintList = list_NPointerUnion(ClList, PrintList);

    Scan = TermList;
    TermList = list_Cdr(TermList);
    list_Free(Scan);
  }
  clause_ListPrint(PrintList);

  list_Delete(PrintList);

  term_Delete(NewVar);
  symbol_Delete(NewVarSymbol);
}


LIST clause_AllIndexedClauses(SHARED_INDEX ShIndex)
/**************************************************************
  INPUT:   An index
  RETURNS: A list of all the clauses in the index
  MEMORY:  Memory is allocated for the list nodes
***************************************************************/
{
  LIST clauselist, scan;
  clauselist = sharing_GetAllSuperTerms(ShIndex);
  for (scan = clauselist; scan != list_Nil(); scan = list_Cdr(scan))
    list_Rplaca(scan, clause_LiteralOwningClause(list_Car(scan)));
  clauselist = list_PointerDeleteDuplicates(clauselist);
  return clauselist;
}


/**************************************************************/
/* Clause Access Functions                                    */
/**************************************************************/

void clause_DeleteLiteralNN(CLAUSE Clause, int Indice)
/**************************************************************
  INPUT:   An unshared clause, and a literal index.
  RETURNS: Nothing.
  EFFECT:  The literal is position <Indice> is deleted from <Clause>.
           The clause isn't reinitialized afterwards.
  MEMORY:  The memory of the literal with the 'Indice' and 
           memory of its atom is freed.
***************************************************************/
{
  int     i, lc, la, length, shift;
  LITERAL *Literals;

#ifdef CHECK
  if (!clause_IsUnorderedClause(Clause) || (clause_Length(Clause) <= Indice) ||
      Indice < 0) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_DeleteLiteral:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  lc     = clause_LastConstraintLitIndex(Clause);
  la     = clause_LastAntecedentLitIndex(Clause);
  length = clause_Length(Clause);

  /* Create a new literal array */
  if (length > 1)
    Literals = (LITERAL*) memory_Malloc(sizeof(LITERAL) * (length-1));
  else
    Literals = (LITERAL*) NULL;

  /* Copy literals to the new array */
  shift = 0;
  length--;  /* The loop iterates over the new array */
  for (i = 0; i < length; i++) {
    if (i == Indice)
      shift = 1;
    Literals[i] = Clause->literals[i+shift];
  }

  /* Free literal and old array and set new one */
  clause_LiteralDelete(clause_GetLiteral(Clause, Indice));
  clause_FreeLitArray(Clause);
  Clause->literals = Literals;

  /* Update clause */
  if (Indice <= lc)
    clause_SetNumOfConsLits(Clause, clause_NumOfConsLits(Clause) - 1);
  else if (Indice <= la)
    clause_SetNumOfAnteLits(Clause, clause_NumOfAnteLits(Clause) - 1);
  else
    clause_SetNumOfSuccLits(Clause, clause_NumOfSuccLits(Clause) - 1);
  /* Mark the weight as undefined */
  Clause->weight = clause_WEIGHTUNDEFINED;
}


void clause_DeleteLiteral(CLAUSE Clause, int Indice, FLAGSTORE Flags,
			  PRECEDENCE Precedence)
/**************************************************************
  INPUT:   An unshared clause, a literals index, a flag store,
           and a precedence.
  RETURNS: Nothing.
  EFFECT:  The literal at position <Indice> is deleted from <Clause>.
           In contrast to the function clause_DeleteLiteralNN
	   the clause is reinitialized afterwards.
  MEMORY:  The memory of the literal with the 'Indice' and memory
           of its atom is freed.
***************************************************************/
{
  clause_DeleteLiteralNN(Clause, Indice);
  clause_ReInit(Clause, Flags, Precedence);
}


void clause_DeleteLiterals(CLAUSE Clause, LIST Indices, FLAGSTORE Flags,
			   PRECEDENCE Precedence)
/**************************************************************
  INPUT:   An unshared clause, a list of literal indices a
           flag store and a precedence.
  RETURNS: Nothing.
  EFFECT:  The literals given by <Indices> are deleted.
           The clause is reinitialized afterwards.
  MEMORY:  The memory of the literals with the 'Indice' and
           memory of its atom is freed.
***************************************************************/
{
  LITERAL *NewLits;
  int     i, j, nc, na, ns, lc, la, olength, nlength;

#ifdef CHECK
  LIST Scan;
  if (!list_IsSetOfPointers(Indices)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_DeleteLiterals:");
    misc_ErrorReport(" list contains duplicate indices.");
    misc_FinishErrorReport();
  }
  /* check the literal indices */
  for (Scan = Indices; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    i = (int) list_Car(Scan);
    if (i < 0 || i > clause_LastLitIndex(Clause)) {
      misc_StartErrorReport();
      misc_ErrorReport("\n In clause_DeleteLiterals:");
      misc_ErrorReport(" literal index %d is out ", i);
      misc_ErrorReport(" of bounds");
      misc_FinishErrorReport();
    }
  }
#endif

  nc = 0;
  na = 0;
  ns = 0;
  lc = clause_LastConstraintLitIndex(Clause);
  la = clause_LastAntecedentLitIndex(Clause);

  olength = clause_Length(Clause);
  nlength = olength - list_Length(Indices);

  if (nlength != 0)
    NewLits = (LITERAL*) memory_Malloc(sizeof(LITERAL) * nlength);
  else
    NewLits = (LITERAL*) NULL;

  for (i=clause_FirstLitIndex(), j=clause_FirstLitIndex(); i < olength; i++)
 
    if (list_PointerMember(Indices, (POINTER) i))
      clause_LiteralDelete(clause_GetLiteral(Clause,i));
    else {

      NewLits[j++] = clause_GetLiteral(Clause,i);

      if (i <= lc)
	nc++;
      else if (i <= la)
	na++;
      else
	ns++;
    }
  clause_FreeLitArray(Clause);
  Clause->literals = NewLits;

  clause_SetNumOfConsLits(Clause, nc);
  clause_SetNumOfAnteLits(Clause, na);
  clause_SetNumOfSuccLits(Clause, ns);

  clause_ReInit(Clause, Flags, Precedence);
}


/**************************************************************/
/* Clause Comparisons                                         */
/**************************************************************/

BOOL clause_IsHornClause(CLAUSE Clause)
/**************************************************************
  INPUT:   A clause.
  RETURNS: The boolean value TRUE if 'Clause' is a hornclause
           FALSE else.
  ***************************************************************/
{
#ifdef CHECK
  if (!clause_IsUnorderedClause(Clause)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_IsHornClause:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
#endif
  return (clause_NumOfSuccLits(Clause) <= 1);
}


BOOL clause_HasTermSortConstraintLits(CLAUSE Clause)
/**************************************************************
  INPUT:   A clause,
  RETURNS: TRUE iff there is at least one sort constraint atom having
           a term as its argument
***************************************************************/
{
  int i,n;

#ifdef CHECK
  if (!clause_IsUnorderedClause(Clause)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_HasTermSortConstraintLits:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
#endif
  
  n = clause_LastConstraintLitIndex(Clause);

  for (i = clause_FirstConstraintLitIndex(Clause); i <= n; i++)
    if (!term_AllArgsAreVar(clause_GetLiteralAtom(Clause,i)))
      return TRUE;

  return FALSE;
}


BOOL clause_HasSolvedConstraint(CLAUSE Clause)
/**************************************************************
  INPUT:   A clause.
  RETURNS: The boolean value TRUE if 'Clause' has a solved
           constraint, i.e. only variables as sort arguments,
	   FALSE else.
***************************************************************/
{
  int  i,c;
  LIST CVars, LitVars;

#ifdef CHECK
  if (!clause_IsUnorderedClause(Clause)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_HasSolvedConstraint:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  CVars = list_Nil();
  c     = clause_NumOfConsLits(Clause);

  if (c == 0)
    return TRUE;

  if (clause_HasTermSortConstraintLits(Clause))
    return FALSE;

  for (i = 0; i < c; i++)
    CVars = list_NPointerUnion(term_VariableSymbols(clause_GetLiteralAtom(Clause, i)), CVars);

  if (i == c) {
    c       = clause_Length(Clause);
    LitVars = list_Nil();

    for ( ; i < c; i++)
      LitVars = list_NPointerUnion(LitVars, term_VariableSymbols(clause_GetLiteralAtom(Clause, i)));
    
    if (list_Empty(CVars = list_NPointerDifference(CVars, LitVars))) {
      list_Delete(LitVars);
      return TRUE;
    }
    list_Delete(LitVars);
  }

  list_Delete(CVars);

  return FALSE;
}


BOOL clause_HasSelectedLiteral(CLAUSE Clause, FLAGSTORE Flags,
			       PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A Clause, a flag store and a precedence.
  RETURNS: The boolean value TRUE iff <Clause> has a selected literal
***************************************************************/
{
  int  i,negs;

#ifdef CHECK
  if (!clause_IsClause(Clause, Flags, Precedence)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_HasSelectedLiteral:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  negs = clause_LastAntecedentLitIndex(Clause);

  for (i=clause_FirstAntecedentLitIndex(Clause); i <= negs; i++)
    if (clause_LiteralGetFlag(clause_GetLiteral(Clause,i), LITSELECT))
      return TRUE;

  return FALSE;
}


BOOL clause_IsDeclarationClause(CLAUSE Clause)
/**************************************************************
  INPUT:   A clause.
  RETURNS: The boolean value TRUE, if 'Clause' has only variables
           as arguments in constraint literals.
***************************************************************/
{
  int     i,length;
  LITERAL Lit;

#ifdef CHECK
  if (!clause_IsUnorderedClause(Clause)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_IsDeclarationClause:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
#endif
  
  if (!clause_HasSolvedConstraint(Clause))
    return FALSE;

  length = clause_Length(Clause);

  for (i=clause_FirstSuccedentLitIndex(Clause);i<length;i++) {
    Lit = clause_GetLiteral(Clause,i);
    if (clause_LiteralIsMaximal(Lit) &&
	symbol_IsBaseSort(term_TopSymbol(clause_LiteralSignedAtom(Lit))))
      return TRUE;
  }

  return FALSE;
}


BOOL clause_IsSortTheoryClause(CLAUSE Clause, FLAGSTORE Flags,
			       PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A Clause, a flag store and a precedence.
  RETURNS: The boolean value TRUE, if 'Clause' has only variables
           as arguments in constraint literals, no antecedent literals
	   and exactly one monadic succedent literal.
***************************************************************/
{
  LITERAL Lit;

#ifdef CHECK
  if (!clause_IsClause(Clause, Flags, Precedence)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_IsSortTheoryClause:");
    misc_ErrorReport("\n Illegal input. Input not a clause.");
    misc_FinishErrorReport();
  }
#endif
  
  if (clause_NumOfAnteLits(Clause) > 0 ||
      clause_NumOfSuccLits(Clause) > 1 ||
      !clause_HasSolvedConstraint(Clause))
    return FALSE;

  Lit = clause_GetLiteral(Clause,clause_FirstSuccedentLitIndex(Clause));
  if (symbol_IsBaseSort(term_TopSymbol(clause_LiteralSignedAtom(Lit))))
    return TRUE;

  return FALSE;
}

BOOL clause_IsPotentialSortTheoryClause(CLAUSE Clause, FLAGSTORE Flags,
					PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A Clause, a flag store and a precedence.
  RETURNS: The boolean value TRUE, if 'Clause' has monadic literals
           only variables as arguments in antecedent/constraint literals,
	   no other antecedent literals and exactly one monadic succedent
	   literal.
***************************************************************/
{
  LITERAL Lit;
  int     i;

#ifdef CHECK
  if (!clause_IsClause(Clause, Flags, Precedence)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_IsPotentialSortTheoryClause:");
    misc_ErrorReport("\n Illegal input. Input not a clause.");
    misc_FinishErrorReport();
  }
#endif
  
  if (clause_NumOfSuccLits(Clause) != 1)
    return FALSE;

  for (i=clause_FirstLitIndex();i<clause_FirstSuccedentLitIndex(Clause);i++) {
    Lit = clause_GetLiteral(Clause,i);
    if (!symbol_IsBaseSort(term_TopSymbol(clause_LiteralAtom(Lit))) ||
	!term_IsVariable(term_FirstArgument(clause_LiteralAtom(Lit))))
      return FALSE;
  }

  Lit = clause_GetLiteral(Clause,clause_FirstSuccedentLitIndex(Clause));
  if (symbol_IsBaseSort(term_TopSymbol(clause_LiteralSignedAtom(Lit))))
    return TRUE;

  return FALSE;
}


BOOL clause_HasOnlyVarsInConstraint(CLAUSE Clause, FLAGSTORE Flags,
				    PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A Clause, a flag store and a precedence.
  RETURNS: The boolean value TRUE, if 'Clause' has only variables
           as arguments in constraint literals.
***************************************************************/
{
  int  i,nc;

#ifdef CHECK
  if (!clause_IsClause(Clause, Flags, Precedence)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_HasOnlyVarsInConstraint:");
    misc_ErrorReport("\n Illegal input. Input not a clause.");
    misc_FinishErrorReport();
  }
#endif

  nc = clause_NumOfConsLits(Clause);

  for (i = 0; i < nc && term_AllArgsAreVar(clause_GetLiteralAtom(Clause,i)); i++)
    /* empty */;

  return (i == nc);
}


BOOL clause_HasSortInSuccedent(CLAUSE Clause, FLAGSTORE Flags,
			       PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A Clause, a flag store and a precedence.
  RETURNS: The boolean value TRUE, if 'Clause' has a maximal succedent
           sort literal; FALSE, else.
***************************************************************/
{
  LITERAL Lit;
  int     i,l;
  BOOL    result = FALSE;

#ifdef CHECK
  if (!clause_IsClause(Clause, Flags, Precedence)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_HasSortInSuccedent:");
    misc_ErrorReport("\n Illegal input. Input not a clause.");
    misc_FinishErrorReport();
  }
#endif
 
  l  = clause_Length(Clause);

  for (i = clause_FirstSuccedentLitIndex(Clause); i < l && !result ; i++) {
    Lit = clause_GetLiteral(Clause, i);
    result = (symbol_Arity(term_TopSymbol(clause_LiteralAtom(Lit))) == 1);
  }
  return result;
}


BOOL clause_LitsHaveCommonVar(LITERAL Lit1, LITERAL Lit2)
/**************************************************************
  INPUT:   Two literals.
  RETURNS: The boolean value TRUE, if 'Lit1' and 'Lit2' have
           common variables, FALSE, else.
***************************************************************/
{
  LIST Vars1, Vars2;
  BOOL Result;

  Vars1  = term_VariableSymbols(clause_LiteralAtom(Lit1));
  Vars2  = term_VariableSymbols(clause_LiteralAtom(Lit2));
  Result = list_HasIntersection(Vars1, Vars2);
  list_Delete(Vars1);
  list_Delete(Vars2);

  return Result;
}


/**************************************************************/
/* Clause Input and Output Functions                          */
/**************************************************************/

void clause_Print(CLAUSE Clause)
/**************************************************************
  INPUT:   A Clause.
  RETURNS: Nothing.
  SUMMARY: The clause is printed to stdout.
***************************************************************/
{
  RULE Origin;
  LITERAL Lit;
  int i,c,a,s;

#ifdef CHECK
  if (!clause_IsUnorderedClause(Clause)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_Print:");
    misc_ErrorReport("\n Illegal input. Input not a clause.");
    misc_FinishErrorReport();
  }
#endif

  if (!clause_Exists(Clause))
    fputs("(CLAUSE)NULL", stdout);
  else {
    printf("%d",clause_Number(Clause));
    
    Origin = clause_Origin(Clause);
    printf("[%d:", clause_SplitLevel(Clause));

#ifdef CHECK
    if (Clause->splitfield_length <= 1)
      fputs("0.", stdout);
    else
      for (i=Clause->splitfield_length-1; i > 0; i--)
	printf("%lu.", Clause->splitfield[i]);
    if (Clause->splitfield_length == 0)
      putchar('1');
    else
      printf("%lu", (Clause->splitfield[0] | 1));
    printf(":%c%c:%c:%d:%d:", clause_GetFlag(Clause, CONCLAUSE) ? 'C' : 'A',
	   clause_GetFlag(Clause, WORKEDOFF) ? 'W' : 'U',
	   clause_GetFlag(Clause, NOPARAINTO) ? 'N' : 'P',
	   clause_Weight(Clause), clause_Depth(Clause));
#endif
    
    clause_PrintOrigin(Clause);
    
    if (Origin == INPUT) {
      ;
    } else  {      
      putchar(':');
      clause_PrintParentClauses(Clause);
    }
    putchar(']');

    c = clause_NumOfConsLits(Clause);
    a = clause_NumOfAnteLits(Clause);
    s = clause_NumOfSuccLits(Clause);

    for (i = 0; i < c; i++) {
      putchar(' ');
      Lit = clause_GetLiteral(Clause, i);
      clause_LiteralPrintUnsigned(Lit);
    }
    fputs(" || ", stdout);

    a += c;
    for ( ; i < a; i++) {

      Lit = clause_GetLiteral(Clause, i);
      clause_LiteralPrintUnsigned(Lit);
      if (clause_LiteralIsMaximal(Lit)) {
	putchar('*');
	if (clause_LiteralIsOrientedEquality(Lit))
	  putchar('*');
      }
      if (clause_LiteralGetFlag(Lit,LITSELECT))
	putchar('+');
      if (i+1 < a)
	putchar(' ');
    }
    fputs(" -> ",stdout);

    s += a;
    for ( ; i < s; i++) {

      Lit = clause_GetLiteral(Clause, i);
      clause_LiteralPrintUnsigned(Lit);
      if (clause_LiteralIsMaximal(Lit)) {
	putchar('*');
	if (clause_LiteralIsOrientedEquality(Lit))
	  putchar('*');
      }
#ifdef CHECK
      if (clause_LiteralGetFlag(Lit,LITSELECT)) {
	misc_StartErrorReport();
	misc_ErrorReport("\n In clause_Print: Clause has selected positive literal.\n");
	misc_FinishErrorReport();
      }
#endif
      if (i+1 < s)
	putchar(' ');
    }
    putchar('.');
  }
}


void clause_PrintMaxLitsOnly(CLAUSE Clause, FLAGSTORE Flags,
			     PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A Clause, a flag store and a precedence.
  RETURNS: Nothing.
  SUMMARY:
***************************************************************/
{
  int i,c,a,s;

#ifdef CHECK
  if (!clause_IsClause(Clause, Flags, Precedence)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_PrinMaxLitsOnly:");
    misc_ErrorReport("\n Illegal input. Input not a clause.");
    misc_FinishErrorReport();
  }
#endif

  c = clause_NumOfConsLits(Clause);
  a = clause_NumOfAnteLits(Clause);
  s = clause_NumOfSuccLits(Clause);

  for (i = 0; i < c; i++) {
    if (clause_LiteralIsMaximal(clause_GetLiteral(Clause, i)))
      clause_LiteralPrint(clause_GetLiteral(Clause, i));
    if (clause_LiteralGetFlag(clause_GetLiteral(Clause, i),STRICTMAXIMAL)) {
      clause_LiteralPrint(clause_GetLiteral(Clause, i));
      fputs("(strictly)", stdout);
    }
  }
  fputs(" || ", stdout);
  
  a += c;
  for ( ; i < a; i++) {
    if (clause_LiteralIsMaximal(clause_GetLiteral(Clause, i)))
      clause_LiteralPrint(clause_GetLiteral(Clause, i));
    if (clause_LiteralGetFlag(clause_GetLiteral(Clause, i),STRICTMAXIMAL)) {
      clause_LiteralPrint(clause_GetLiteral(Clause, i));
      fputs("(strictly)", stdout);
    }
  }
  fputs(" -> ", stdout);

  s += a;
  for ( ; i < s; i++) {
    if (clause_LiteralIsMaximal(clause_GetLiteral(Clause, i)))
      clause_LiteralPrint(clause_GetLiteral(Clause, i));
    if (clause_LiteralGetFlag(clause_GetLiteral(Clause, i),STRICTMAXIMAL)) {
      clause_LiteralPrint(clause_GetLiteral(Clause, i));
      fputs("(strictly)", stdout);
    }
  }
  puts(".");  /* with newline */
}


void clause_FPrint(FILE* File, CLAUSE Clause)
/**************************************************************
  INPUT:   A file and a clause.
  RETURNS: Nothing.
  SUMMARY: Prints any clause to the file 'File'.
  CAUTION: Uses the term_Output functions.
***************************************************************/
{
  int i, c, a, s;

  c = clause_NumOfConsLits(Clause);
  a = clause_NumOfAnteLits(Clause);
  s = clause_NumOfSuccLits(Clause);

  for (i = 0; i < c; i++)
    term_FPrint(File, clause_GetLiteralAtom(Clause, i));

  fputs(" || ", stdout);

  a += c;
  for ( ; i < a; i++)
    term_FPrint(File, clause_GetLiteralAtom(Clause, i));

  fputs(" -> ", stdout);

  s += a;
  for ( ; i < s; i++)
    term_FPrint(File, clause_GetLiteralAtom(Clause, i));
  
  putc('.', File);
}


void clause_ListPrint(LIST ClauseList)
/**************************************************************
  INPUT:   A list of clauses.
  RETURNS: Nothing.
  SUMMARY: Prints the clauses to stdout.
  CAUTION: Uses the clause_Print function.
***************************************************************/
{
  while (!(list_Empty(ClauseList))) {
    clause_Print(list_First(ClauseList));
    ClauseList = list_Cdr(ClauseList);
    if (!list_Empty(ClauseList))
      putchar('\n');
  }
}


void clause_PrintParentClauses(CLAUSE Clause)
/**************************************************************
  INPUT:   A Clause.
  RETURNS: Nothing.
  SUMMARY: Prints the clauses parentclauses and -literals to stdout.
***************************************************************/
{
  LIST Scan1,Scan2;
  
  if (!list_Empty(clause_ParentClauses(Clause))) {
    
    Scan1 = clause_ParentClauses(Clause);
    Scan2 = clause_ParentLiterals(Clause);
    printf("%d.%d", (int)list_Car(Scan1), (int)list_Car(Scan2));
    
    for (Scan1 = list_Cdr(Scan1), Scan2 = list_Cdr(Scan2);
	 !list_Empty(Scan1);
	 Scan1 = list_Cdr(Scan1), Scan2 = list_Cdr(Scan2))
      printf(",%d.%d", (int)list_Car(Scan1), (int)list_Car(Scan2));
  }
}


RULE clause_GetOriginFromString(const char* RuleName)
/**************************************************************
  INPUT:   A string containing the abbreviated name of a rule.
  RETURNS: The RULE corresponding to the <RuleName>.
***************************************************************/
{
  if      (string_Equal(RuleName, "App")) return CLAUSE_DELETION;
  else if (string_Equal(RuleName, "EmS")) return EMPTY_SORT;
  else if (string_Equal(RuleName, "SoR")) return SORT_RESOLUTION;
  else if (string_Equal(RuleName, "EqR")) return EQUALITY_RESOLUTION;
  else if (string_Equal(RuleName, "EqF")) return EQUALITY_FACTORING;
  else if (string_Equal(RuleName, "MPm")) return MERGING_PARAMODULATION;
  else if (string_Equal(RuleName, "SpR")) return SUPERPOSITION_RIGHT;
  else if (string_Equal(RuleName, "SPm")) return PARAMODULATION;
  else if (string_Equal(RuleName, "OPm")) return ORDERED_PARAMODULATION;
  else if (string_Equal(RuleName, "SpL")) return SUPERPOSITION_LEFT;
  else if (string_Equal(RuleName, "Res")) return GENERAL_RESOLUTION;
  else if (string_Equal(RuleName, "SHy")) return SIMPLE_HYPER;
  else if (string_Equal(RuleName, "OHy")) return ORDERED_HYPER;
  else if (string_Equal(RuleName, "URR")) return UR_RESOLUTION;
  else if (string_Equal(RuleName, "Fac")) return GENERAL_FACTORING;
  else if (string_Equal(RuleName, "Spt")) return SPLITTING;
  else if (string_Equal(RuleName, "Inp")) return INPUT;
  else if (string_Equal(RuleName, "Rew")) return REWRITING;
  else if (string_Equal(RuleName, "CRw")) return CONTEXTUAL_REWRITING;
  else if (string_Equal(RuleName, "Con")) return CONDENSING;
  else if (string_Equal(RuleName, "AED")) return ASSIGNMENT_EQUATION_DELETION;
  else if (string_Equal(RuleName, "Obv")) return OBVIOUS_REDUCTIONS;
  else if (string_Equal(RuleName, "SSi")) return SORT_SIMPLIFICATION;
  else if (string_Equal(RuleName, "MRR")) return MATCHING_REPLACEMENT_RESOLUTION;
  else if (string_Equal(RuleName, "UnC")) return UNIT_CONFLICT;
  else if (string_Equal(RuleName, "Def")) return DEFAPPLICATION;
  else if (string_Equal(RuleName, "Ter")) return TERMINATOR;
  else {
    misc_StartErrorReport();
    misc_ErrorReport("\nIn clause_GetOriginFromString: Unknown clause origin.");
    misc_FinishErrorReport();
    return CLAUSE_DELETION; /* Just for the compiler, code is not reachable */
  }
}

void clause_FPrintOrigin(FILE* File, CLAUSE Clause)
/**************************************************************
  INPUT:   A Clause.
  RETURNS: Nothing.
  SUMMARY: Prints the clause's origin to the file.
***************************************************************/
{
  RULE Result;

  Result = clause_Origin(Clause);

  switch(Result) {
  case CLAUSE_DELETION:                 fputs("App", File); break;
  case EMPTY_SORT:                      fputs("EmS", File); break;
  case SORT_RESOLUTION:                 fputs("SoR", File); break;
  case EQUALITY_RESOLUTION:             fputs("EqR", File); break;
  case EQUALITY_FACTORING:              fputs("EqF", File); break;
  case MERGING_PARAMODULATION:          fputs("MPm", File); break;
  case SUPERPOSITION_RIGHT:             fputs("SpR", File); break;
  case PARAMODULATION:                  fputs("SPm", File); break;
  case ORDERED_PARAMODULATION:          fputs("OPm", File); break;
  case SUPERPOSITION_LEFT:              fputs("SpL", File); break;
  case GENERAL_RESOLUTION:              fputs("Res", File); break;
  case SIMPLE_HYPER:                    fputs("SHy", File); break;
  case ORDERED_HYPER:                   fputs("OHy", File); break;
  case UR_RESOLUTION:                   fputs("URR", File); break;
  case GENERAL_FACTORING:               fputs("Fac", File); break;
  case SPLITTING:                       fputs("Spt", File); break;
  case INPUT:                           fputs("Inp", File); break;
  case REWRITING:                       fputs("Rew", File); break;
  case CONTEXTUAL_REWRITING:            fputs("CRw", File); break;
  case CONDENSING:                      fputs("Con", File); break;
  case ASSIGNMENT_EQUATION_DELETION:    fputs("AED", File); break;
  case OBVIOUS_REDUCTIONS:              fputs("Obv", File); break;
  case SORT_SIMPLIFICATION:             fputs("SSi", File); break;
  case MATCHING_REPLACEMENT_RESOLUTION: fputs("MRR", File); break;
  case UNIT_CONFLICT:                   fputs("UnC", File); break;
  case DEFAPPLICATION:                  fputs("Def", File); break;
  case TERMINATOR:                      fputs("Ter", File); break;
  case TEMPORARY:                       fputs("Temporary", File); break;
  default:
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_FPrintOrigin: Clause has no origin.");
    misc_FinishErrorReport();
  }
}


void clause_PrintOrigin(CLAUSE Clause)
/**************************************************************
  INPUT:   A Clause.
  RETURNS: Nothing.
  SUMMARY: Prints the clauses origin to stdout.
***************************************************************/
{
  clause_FPrintOrigin(stdout, Clause);
}


void clause_PrintVerbose(CLAUSE Clause, FLAGSTORE Flags, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A Clause, a flag store and a precedence.
  RETURNS: Nothing.
  SUMMARY: Prints almost all the information kept in the
           clause structure.
***************************************************************/
{
  int c,a,s;

#ifdef CHECK
  if (!clause_IsClause(Clause, Flags, Precedence)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_PrintVerbose:");
    misc_ErrorReport("\n Illegal input. Input not a clause.");
    misc_FinishErrorReport();
  }
#endif

  c = clause_NumOfConsLits(Clause);
  a = clause_NumOfAnteLits(Clause);
  s = clause_NumOfSuccLits(Clause);

  printf(" c = %d a = %d s = %d", c,a,s);
  printf(" Weight : %d", clause_Weight(Clause));
  printf(" Depth  : %d", clause_Depth(Clause));
  printf(" %s %s ",
	 (clause_GetFlag(Clause,WORKEDOFF) ? "WorkedOff" : "Usable"),
	 (clause_GetFlag(Clause,CLAUSESELECT) ? "Selected" : "NotSelected"));

  clause_Print(Clause);
}


CLAUSE clause_GetNumberedCl(int number, LIST ClList)
/**************************************************************
  INPUT:   
  RETURNS: 
  CAUTION: 
***************************************************************/
{
  while (!list_Empty(ClList) &&
	 clause_Number((CLAUSE)list_Car(ClList)) != number)
    ClList = list_Cdr(ClList);
  
  if (list_Empty(ClList))
    return NULL;
  else
    return list_Car(ClList);
}

static __inline__ BOOL clause_NumberLower(CLAUSE A, CLAUSE B)
{
  return (BOOL) (clause_Number(A) < clause_Number(B));
}

LIST clause_NumberSort(LIST List)
/**************************************************************
  INPUT:   A list of clauses.
  RETURNS: The same list where the elements are sorted wrt their number.
  CAUTION: Destructive.
***************************************************************/
{
  return list_Sort(List, (BOOL (*) (POINTER, POINTER)) clause_NumberLower);
}


LIST clause_NumberDelete(LIST List, int Number)
/**************************************************************
  INPUT:   A list of clauses and an integer.
  RETURNS: The same list where the clauses with <Number> are deleted.
  CAUTION: Destructive.
***************************************************************/
{
  LIST Scan1,Scan2;
  
  for (Scan1 = List; !list_Empty(Scan1); )
    if (clause_Number(list_Car(Scan1))==Number) {
      
      Scan2 = Scan1;
      Scan1 = list_Cdr(Scan1);
      List  = list_PointerDeleteOneElement(List, list_Car(Scan2));
    } else
      Scan1 = list_Cdr(Scan1);

  return List;
}


static NAT clause_NumberOfMaxLits(CLAUSE Clause)
/**************************************************************
  INPUT:   A clause.
  RETURNS: The number of maximal literals in a clause.
***************************************************************/
{
  NAT Result,i,n;

  Result = 0;
  n      = clause_Length(Clause);

  for (i = clause_FirstAntecedentLitIndex(Clause); i < n; i++)
    if (clause_LiteralIsMaximal(clause_GetLiteral(Clause,i)))
      Result++;

  return Result;
}

/* Unused ! */
NAT clause_NumberOfMaxAntecedentLits(CLAUSE Clause)
/**************************************************************
  INPUT:   A clause.
  RETURNS: The number of maximal antecedent literals in a clause.
***************************************************************/
{
  NAT Result,i,n;

  Result = 0;
  n      = clause_LastAntecedentLitIndex(Clause);

  for (i = clause_FirstAntecedentLitIndex(Clause); i <= n; i++)
    if (clause_LiteralIsMaximal(clause_GetLiteral(Clause,i)))
      Result++;

  return Result;
}


void clause_SelectLiteral(CLAUSE Clause, FLAGSTORE Flags)
/**************************************************************
  INPUT:   A clause and a flag store.
  RETURNS: Nothing.
  EFFECT:  If the clause contains more than 2 maximal literals,
           at least one antecedent literal, the literal with
	   the highest weight is selected.
***************************************************************/
{
  if (clause_HasSolvedConstraint(Clause) &&
      !clause_GetFlag(Clause,CLAUSESELECT) &&
      clause_NumOfAnteLits(Clause) > 0 &&
      (flag_GetFlagValue(Flags, flag_SELECT) == flag_SELECTALWAYS ||
       (flag_GetFlagValue(Flags, flag_SELECT) == flag_SELECTIFSEVERALMAXIMAL &&
	clause_NumberOfMaxLits(Clause) > 1))) {
    NAT     i,n;
    LITERAL Lit;
    
    n   = clause_LastAntecedentLitIndex(Clause);
    i   = clause_FirstAntecedentLitIndex(Clause);
    Lit = clause_GetLiteral(Clause,i);
    i++;
    
    for ( ; i <= n; i++)
      if (clause_LiteralWeight(Lit)
	  < clause_LiteralWeight(clause_GetLiteral(Clause,i)))
	Lit = clause_GetLiteral(Clause,i);
    
    clause_LiteralSetFlag(Lit,LITSELECT);
    clause_SetFlag(Clause,CLAUSESELECT);
  }
}


void clause_SetSpecialFlags(CLAUSE Clause, BOOL SortDecreasing, FLAGSTORE Flags,
			    PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause, a flag indicating whether all equations are
           sort decreasing, a flag store and a precedence.
  RETURNS: void.
  EFFECT:  If the clause is a sort theory clause and its declaration
           top symbol is a set declaration sort, i.e., it occurred in a
	   declaration right from the beginning, the paramodulation/superposition
	   steps into the clause are forbidden by setting the
	   NOPARAINTO clause flag
***************************************************************/
{
  if (SortDecreasing &&
      clause_IsSortTheoryClause(Clause, Flags, Precedence) &&
      symbol_HasProperty(term_TopSymbol(clause_GetLiteralTerm(Clause,clause_FirstSuccedentLitIndex(Clause))),
			 DECLSORT))
    clause_SetFlag(Clause,NOPARAINTO);
}


BOOL clause_ContainsPotPredDef(CLAUSE Clause, FLAGSTORE Flags,
			       PRECEDENCE Precedence, NAT* Index, LIST* Pair)
/**************************************************************
  INPUT:   A clause, a flag store, a precedence and a pointer to an index.
  RETURNS: TRUE iff a succedent literal of the clause is a predicate
           having only variables as arguments, the predicate occurs only
	   once in the clause and no other variables but the predicates'
	   occur.
	   In that case Index is set to the index of the predicate and
	   Pair contains two lists : the literals for which positive
	   occurrences must be found and a list of literals for which negative
	   occurrences must be found for a complete definition.
***************************************************************/
{
  NAT i;

#ifdef CHECK
  if (!clause_IsClause(Clause, Flags, Precedence)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_ContainsPotPredDef:");
    misc_ErrorReport("\n Illegal input. Input not a clause.");
    misc_FinishErrorReport();
  }
#endif

  /* Iterate over all succedent literals */
  for (i=clause_FirstSuccedentLitIndex(Clause); i < clause_Length(Clause); i++) {
    LITERAL lit;
    TERM atom;
    LIST pair;

    lit = clause_GetLiteral(Clause, i);
    atom = clause_LiteralSignedAtom(lit);
    if (symbol_IsPredicate(term_TopSymbol(atom))) {
      LIST l;
      BOOL ok;
      ok = TRUE;
      pair = list_PairCreate(list_Nil(), list_Nil());
      
      /* Make sure all arguments of predicate are variables */
      for (l=term_ArgumentList(atom); !list_Empty(l); l=list_Cdr(l)) {
	if (!term_IsStandardVariable((TERM) list_Car(l))) {
	  ok = FALSE;
	  break;
	}
      }
      if (ok) {
	/* Make sure predicate occurs only once in clause */
	NAT j, count;
	count = 0;
	for (j=0; (j < clause_Length(Clause)) && (count < 2); j++) {
	  TERM t;
	  t = clause_GetLiteralAtom(Clause, j);
	  if (symbol_Equal(term_TopSymbol(t), term_TopSymbol(atom)))
	    count++;
	}
	if (count > 1)
	  ok = FALSE;
      }
      if (ok) {
	/* Build lists of positive and negative literals */
	/* At the same time check if other variables than those among
	   the predicates arguments are found */
	NAT j;
	LIST predvars, vars;
	predvars = fol_FreeVariables(atom);
	
	/* Build list of literals for which positive occurrences are required */
	for (j=0; (j < clause_FirstSuccedentLitIndex(Clause)) && ok; j++) {
	  list_Rplaca(pair, list_Cons(clause_GetLiteralAtom(Clause, j), list_PairFirst(pair)));
	  vars = fol_FreeVariables(clause_GetLiteralTerm(Clause, j));
	  for (l = vars; !list_Empty(l); l = list_Cdr(l)) {
	    if (!term_ListContainsTerm(predvars, list_Car(l))) {
	      ok = FALSE;
	      break;
	    }
	  }
	  list_Delete(vars);
	}
	
	/* Build list of literals for which negative occurrences are required */
	for (j = clause_FirstSuccedentLitIndex(Clause);
	     (j < clause_Length(Clause)) && ok; j++) {
	  if (j != i) {
	    list_Rplacd(pair, list_Cons(clause_GetLiteralAtom(Clause, j), list_PairSecond(pair)));
	    vars = fol_FreeVariables(clause_GetLiteralAtom(Clause, j));
	    for (l=vars; !list_Empty(l); l=list_Cdr(l)) {
	      if (!term_ListContainsTerm(predvars, list_Car(l))) {
		ok = FALSE;
		break;
	      }
	    }
	    list_Delete(vars);
	  }
	}
	list_Delete(predvars);
      }

      if (ok) {
	*Index = i;
	*Pair = pair;
	return TRUE;
      }
      else {
	list_Delete(list_PairFirst(pair));
	list_Delete(list_PairSecond(pair));
	list_PairFree(pair);
      }
    }
  }
  return FALSE;
}

BOOL clause_IsPartOfDefinition(CLAUSE Clause, TERM Predicate, int *Index,
			       LIST Pair)
/**************************************************************
  INPUT:   A clause, a term, a pointer to an int and a pair of term lists.
  RETURNS: TRUE iff the predicate occurs among the negative literals of
           the clause and the other negative and positive literals are found
	   in the pairs' lists.
	   In that case they are removed from the lists.
	   Index is set to the index of the defined predicate in Clause.
***************************************************************/
{
  NAT predindex, i;
  BOOL ok;

  ok = TRUE;

  /* Check whether Predicate is among antecedent or constraint literals */
  for (predindex=clause_FirstLitIndex();
       predindex < clause_FirstSuccedentLitIndex(Clause);
       predindex++)
    if (term_Equal(Predicate, clause_GetLiteralAtom(Clause, predindex)))
      break;
  if (predindex == clause_FirstSuccedentLitIndex(Clause))
    return FALSE;
  *Index = predindex;

  /* Check if other negative literals are required for definition */
  for (i=clause_FirstLitIndex();
       (i < clause_FirstSuccedentLitIndex(Clause)) && ok; i++) {
    if (i != predindex)
      if (!term_ListContainsTerm((LIST) list_PairSecond(Pair),
				 clause_GetLiteralAtom(Clause, i)))
	ok = FALSE;
  }

  /* Check if positive literals are required for definition */
  for (i=clause_FirstSuccedentLitIndex(Clause);
       (i < clause_Length(Clause)) && ok; i++)
    if (!term_ListContainsTerm((LIST) list_PairFirst(Pair),
			       clause_GetLiteralAtom(Clause, i)))
      ok = FALSE;
  
  if (!ok)
    return FALSE;
  else {
    /* Complement for definition found, remove literals from pair lists */
    for (i=0; i < clause_FirstSuccedentLitIndex(Clause); i++)
      if (i != predindex)
	list_Rplacd(Pair,
		    list_DeleteElement((LIST) list_PairSecond(Pair),
				       clause_GetLiteralAtom(Clause, i),
				       (BOOL (*)(POINTER, POINTER)) term_Equal));
    for (i=clause_FirstSuccedentLitIndex(Clause); i < clause_Length(Clause); i++)
      list_Rplaca(Pair,
		  list_DeleteElement((LIST) list_PairFirst(Pair),
				     clause_GetLiteralAtom(Clause, i),
				     (BOOL (*)(POINTER, POINTER)) term_Equal));
    return TRUE;
  }
}

void clause_FPrintRule(FILE* File, CLAUSE Clause)
/**************************************************************
  INPUT:   A file and a clause.
  RETURNS: Nothing.
  SUMMARY: Prints any term of the clause to file in rule format.
  CAUTION: Uses the term_Output functions.
***************************************************************/
{
  int  i,n;
  TERM Literal;
  LIST scan,antecedent,succedent,constraints;

  n = clause_Length(Clause);

  constraints = list_Nil();
  antecedent  = list_Nil();
  succedent   = list_Nil();

  for (i = 0; i < n; i++) {
    Literal = clause_GetLiteralTerm(Clause,i);
    if (symbol_Equal(term_TopSymbol(Literal),fol_Not())) {
      if (symbol_Arity(term_TopSymbol(fol_Atom(Literal))) == 1 &&
	  symbol_IsVariable(term_TopSymbol(term_FirstArgument(fol_Atom(Literal)))))
	constraints = list_Cons(Literal,constraints);
      else
	antecedent = list_Cons(Literal,antecedent);
    }
    else
      succedent = list_Cons(Literal,succedent);
  }

  for (scan = constraints; !list_Empty(scan); scan = list_Cdr(scan)) {
    term_FPrint(File, fol_Atom(list_Car(scan)));
    putc(' ', File);
  }
  fputs("||", File);
  for (scan = antecedent; !list_Empty(scan); scan = list_Cdr(scan)) {
    putc(' ', File);
    term_FPrint(File,fol_Atom(list_Car(scan)));
    if (list_Empty(list_Cdr(scan)))
      putc(' ', File);
  }
  fputs("->", File);
  for (scan = succedent; !list_Empty(scan); scan = list_Cdr(scan)) {
    putc(' ', File);
    term_FPrint(File,list_Car(scan));
  }
  fputs(".\n", File);
  
  list_Delete(antecedent);
  list_Delete(succedent);
  list_Delete(constraints);
}


void clause_FPrintOtter(FILE* File, CLAUSE clause)
/**************************************************************
  INPUT:   A file and a clause.
  RETURNS: Nothing.
  SUMMARY: Prints any clause to File.
  CAUTION: Uses the other clause_Output functions.
***************************************************************/
{
  int     n,j;
  LITERAL Lit;
  TERM    Atom;
  
  n = clause_Length(clause);

  if (n == 0)
    fputs(" $F ", File);
  else {
    for (j = 0; j < n; j++) {
      Lit  = clause_GetLiteral(clause,j);
      Atom = clause_LiteralAtom(Lit);
      if (clause_LiteralIsNegative(Lit))
	putc('-', File);
      if (fol_IsEquality(Atom)) {
	if (clause_LiteralIsNegative(Lit))
	  putc('(', File);
	term_FPrintOtterPrefix(File,term_FirstArgument(Atom));
	fputs(" = ", File);
	term_FPrintOtterPrefix(File,term_SecondArgument(Atom));
	if (clause_LiteralIsNegative(Lit))
	  putc(')', File);
      }
      else
	term_FPrintOtterPrefix(File,Atom);
      if (j <= (n-2))
	fputs(" | ", File);
    }
  }

  fputs(".\n", File);
}


void clause_FPrintCnfDFG(FILE* File, BOOL OnlyProductive, LIST Axioms,
			 LIST Conjectures, FLAGSTORE Flags,
			 PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A file, a list of axiom clauses and a list of conjecture clauses.
           A flag indicating whether only potentially productive clauses should
	   be printed.
	   A flag store.
	   A precedence.
  RETURNS: Nothing.
  SUMMARY: Prints a  the respective clause lists to <File> dependent
           on <OnlyProductive>.
***************************************************************/
{
  LIST   scan;
  CLAUSE Clause;

  if (Axioms) {
    fputs("list_of_clauses(axioms, cnf).\n", File);
    for (scan=Axioms;!list_Empty(scan);scan=list_Cdr(scan)) {
      Clause = (CLAUSE)list_Car(scan);
      if (!OnlyProductive ||
	  (clause_HasSolvedConstraint(Clause) &&
	   !clause_HasSelectedLiteral(Clause, Flags, Precedence)))
	clause_FPrintDFG(File,Clause,FALSE);
    }
    fputs("end_of_list.\n\n", File);
  }

  if (Conjectures) {
    fputs("list_of_clauses(conjectures, cnf).\n", File);
    for (scan=Conjectures;!list_Empty(scan);scan=list_Cdr(scan)) {
      Clause = (CLAUSE)list_Car(scan);
      if (!OnlyProductive ||
	  (clause_HasSolvedConstraint(Clause) &&
	   !clause_HasSelectedLiteral(Clause, Flags, Precedence)))
	clause_FPrintDFG(File,Clause,FALSE);
    }
    fputs("end_of_list.\n\n", File);
  }
}


static void clause_FPrintDescription(FILE* File, const char* Name,
				     const char* Author, const char* Status,
				     const char* Description)
{
  fputs("list_of_descriptions.\n", File);
  fprintf(File, "name(%s).\n", Name);
  fprintf(File, "author(%s).\n", Author);
  fprintf(File, "status(%s).\n", Status);
  fprintf(File, "description(%s).\n", Description);
  fputs("end_of_list.\n", File);
}

void clause_FPrintCnfDFGProblem(FILE* File, const char* Name,
				const char* Author, const char* Status,
				const char* Description, LIST Clauses)
/**************************************************************
  INPUT:   A file, the problems name, author, status and description
           to be included in the description block given as strings
	   and a list of clauses.
  RETURNS: Nothing.
  SUMMARY: Prints a complete DFG problem clause file to <File>.
***************************************************************/
{
  LIST Scan;

  fputs("begin_problem(Unknown).\n\n", File);
  clause_FPrintDescription(File, Name,  Author, Status,  Description);
  putc('\n', File);
  fputs("list_of_symbols.\n", File);
  fol_FPrintDFGSignature(File);
  fputs("end_of_list.\n\n", File);
  fputs("list_of_clauses(axioms, cnf).\n", File);
  
  for (Scan=Clauses;!list_Empty(Scan);Scan=list_Cdr(Scan))
    if (!clause_GetFlag(list_Car(Scan),CONCLAUSE))
      clause_FPrintDFG(File,list_Car(Scan),FALSE);

  fputs("end_of_list.\n\n", File);
  fputs("list_of_clauses(conjectures, cnf).\n", File);
  
  for (Scan=Clauses; !list_Empty(Scan); Scan=list_Cdr(Scan))
    if (clause_GetFlag(list_Car(Scan),CONCLAUSE))
      clause_FPrintDFG(File,list_Car(Scan),FALSE);
 
  fputs("end_of_list.\n\n", File);
  fputs("\nend_problem.\n\n", File);
}


void clause_FPrintCnfFormulasDFGProblem(FILE* File, BOOL OnlyProductive,
					const char* Name, const char* Author,
					const char* Status,
					const char* Description, LIST Axioms,
					LIST Conjectures, FLAGSTORE Flags,
					PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A file, a list of axiom clauses and a list of conjecture clauses.
           A flag indicating whether only potentially productive clauses should
	   be printed.
	   A bunch of strings that are printed to the description.
	   A flag store.
	   A precedence.
  RETURNS: Nothing.
  SUMMARY: Prints the respective clause lists as a complete DFG formulae output
           to <File>.
***************************************************************/
{
  LIST   scan;
  CLAUSE Clause;

  fputs("begin_problem(Unknown).\n\n", File);
  clause_FPrintDescription(File, Name,  Author, Status,  Description);
  fputs("\nlist_of_symbols.\n", File);
  fol_FPrintDFGSignature(File);
  fputs("end_of_list.\n\n", File);

  if (Axioms) {
    fputs("list_of_formulae(axioms).\n", File);
    for (scan=Axioms; !list_Empty(scan); scan=list_Cdr(scan)) {
      Clause = (CLAUSE)list_Car(scan);
      if (!OnlyProductive ||
	  (clause_HasSolvedConstraint(Clause) &&
	   !clause_HasSelectedLiteral(Clause, Flags, Precedence)))
	clause_FPrintFormulaDFG(File,Clause,FALSE);
    }
    fputs("end_of_list.\n\n", File);
  }

  if (Conjectures) {
    fputs("list_of_formulae(conjectures).\n", File);
    for (scan=Conjectures; !list_Empty(scan); scan=list_Cdr(scan)) {
      Clause = (CLAUSE)list_Car(scan);
      if (!OnlyProductive ||
	  (clause_HasSolvedConstraint(Clause) &&
	   !clause_HasSelectedLiteral(Clause, Flags, Precedence)))
	clause_FPrintFormulaDFG(File,Clause,FALSE);
    }
    fputs("end_of_list.\n\n", File);
  }

  fputs("list_of_settings(SPASS).\n{*\n", File);
  fol_FPrintPrecedence(File, Precedence);
  fputs("\n*}\nend_of_list.\n\nend_problem.\n\n", File);
}

void clause_FPrintCnfOtter(FILE* File, LIST Clauses, FLAGSTORE Flags)
/**************************************************************
  INPUT:   A file, a list of clauses and a flag store.
  RETURNS: Nothing.
  SUMMARY: Prints the clauses to <File> in a format readable by Otter.
***************************************************************/
{
  LIST   scan;
  int    i;
  BOOL   Equality;
  CLAUSE Clause;

  Equality = FALSE;

  for (scan=Clauses;!list_Empty(scan) && !Equality; scan=list_Cdr(scan)) {
    Clause = (CLAUSE)list_Car(scan);
    for (i=clause_FirstAntecedentLitIndex(Clause);i<clause_Length(Clause);i++)
      if (fol_IsEquality(clause_GetLiteralAtom(Clause,i))) {
	Equality = TRUE;
	i = clause_Length(Clause);
      }
  }

  fol_FPrintOtterOptions(File, Equality,
			 flag_GetFlagValue(Flags, flag_TDFG2OTTEROPTIONS));

  if (Clauses) {
    fputs("list(usable).\n", File);
    if (Equality)
      fputs("x=x.\n", File);
    for (scan=Clauses;!list_Empty(scan);scan=list_Cdr(scan))
      clause_FPrintOtter(File,list_Car(scan));
    fputs("end_of_list.\n\n", File);
  }
}


void clause_FPrintCnfDFGDerivables(FILE* File, LIST Clauses, BOOL Type)
/**************************************************************
  INPUT:   A file, a list of clauses and a bool flag Type.
  RETURNS: Nothing.
  SUMMARY: If <Type> is true then all axiom clauses in <Clauses> are
	   written to <File>. Otherwise all conjecture clauses in
	   <Clauses> are written to <File>.
***************************************************************/
{
  CLAUSE Clause;

  while (Clauses) {
    Clause = (CLAUSE)list_Car(Clauses);
    if ((Type && !clause_GetFlag(Clause,CONCLAUSE)) ||
	(!Type && clause_GetFlag(Clause,CONCLAUSE)))
      clause_FPrintDFG(File,Clause,FALSE);
    Clauses = list_Cdr(Clauses);
  }
}


void clause_FPrintDFGStep(FILE* File, CLAUSE Clause, BOOL Justif)
/**************************************************************
  INPUT:   A file, a clause and a boolean value.
  RETURNS: Nothing.
  SUMMARY: Prints any clause together with a label (the clause number)
	   to File. If <Justif> is TRUE also the labels of the parent
	   clauses are printed.
  CAUTION: Uses the other clause_Output functions.
***************************************************************/
{
  int     n,j;
  LITERAL Lit;
  TERM    Atom;
  LIST    Variables,Iter;
  
  n = clause_Length(Clause);

  fputs("  step(", File);
  fprintf(File, "%d,", clause_Number(Clause));

  Variables = list_Nil();

  for (j = 0; j < n; j++)
    Variables =
      list_NPointerUnion(Variables,
	term_VariableSymbols(clause_GetLiteralAtom(Clause,j)));

  if (!list_Empty(Variables)) {
    symbol_FPrint(File, fol_All());
    fputs("([", File);
    for (Iter = Variables; !list_Empty(Iter); Iter = list_Cdr(Iter)) {
      symbol_FPrint(File, (SYMBOL) list_Car(Iter));
      if (!list_Empty(list_Cdr(Iter)))
	putc(',', File);
    }
    fputs("],", File);
  }
  
  symbol_FPrint(File, fol_Or());
  putc('(', File);

  for (j = 0; j < n; j++) {
    Lit  = clause_GetLiteral(Clause,j);
    Atom = clause_LiteralSignedAtom(Lit);
    term_FPrintPrefix(File,Atom);
    if (j+1 < n)
      putc(',', File);
  }
  if (n==0)
    symbol_FPrint(File,fol_False());

  if (!list_Empty(Variables)) {
    list_Delete(Variables);
    putc(')', File);
  }
  fputs("),", File);
  clause_FPrintOrigin(File, Clause);

  fputs(",[", File);
  for (Iter = clause_ParentClauses(Clause);
      !list_Empty(Iter);
      Iter = list_Cdr(Iter)) {
    fprintf(File, "%d", (int)list_Car(Iter));
    if (!list_Empty(list_Cdr(Iter)))
      putc(',', File);
  }
  putc(']', File);
  fprintf(File, ",[splitlevel:%d]", clause_SplitLevel(Clause));
  
  fputs(").\n", File);
}

void clause_FPrintDFG(FILE* File, CLAUSE Clause, BOOL Justif)
/**************************************************************
  INPUT:   A file, a clause and a boolean value.
  RETURNS: Nothing.
  SUMMARY: Prints any clause together with a label (the clause number)
	   to File. If Justif is TRUE also the labels of the parent
	   clauses are printed.
  CAUTION: Uses the other clause_Output functions.
***************************************************************/
{
  int     n,j;
  LITERAL Lit;
  TERM    Atom;
  LIST    Variables,Iter;
  
  n = clause_Length(Clause);

  fputs("  clause(", File);
  Variables = list_Nil();

  for (j = 0; j < n; j++)
    Variables =
      list_NPointerUnion(Variables,
	term_VariableSymbols(clause_GetLiteralAtom(Clause,j)));

  if (!list_Empty(Variables)) {
    symbol_FPrint(File, fol_All());
    fputs("([", File);
    for (Iter = Variables; !list_Empty(Iter); Iter = list_Cdr(Iter)) {
      symbol_FPrint(File, (SYMBOL) list_Car(Iter));
      if (!list_Empty(list_Cdr(Iter)))
	putc(',', File);
    }
    fputs("],", File);
  }
  
  symbol_FPrint(File, fol_Or());
  putc('(', File);

  for (j = 0; j < n; j++) {
    Lit  = clause_GetLiteral(Clause,j);
    Atom = clause_LiteralSignedAtom(Lit);
    term_FPrintPrefix(File,Atom);
    if (j+1 < n)
      putc(',', File);
  }
  if (n==0)
    symbol_FPrint(File,fol_False());

  if (!list_Empty(Variables)) {
    list_Delete(Variables);
    putc(')', File);
  }
  fprintf(File, "),%d", clause_Number(Clause));

  if (Justif) {
    putc(',', File);
    clause_FPrintOrigin(File, Clause);
    fputs(",[", File);
    for (Iter = clause_ParentClauses(Clause);
	!list_Empty(Iter);
	Iter = list_Cdr(Iter)) {
      fprintf(File, "%d", (int)list_Car(Iter));
      if (!list_Empty(list_Cdr(Iter)))
	putc(',', File);
    }
    putc(']', File);
    fprintf(File, ",%d", clause_SplitLevel(Clause));
  }
  
  fputs(").\n", File);
}

void clause_FPrintFormulaDFG(FILE* File, CLAUSE Clause, BOOL Justif)
/**************************************************************
  INPUT:   A file, a clause and a boolean value.
  RETURNS: Nothing.
  SUMMARY: Prints any clause together with a label (the clause number)
	   as DFG Formula to File. If Justif is TRUE also the labels of the
	   parent clauses are printed.
  CAUTION: Uses the other clause_Output functions.
***************************************************************/
{
  int     n,j;
  LITERAL Lit;
  TERM    Atom;
  LIST    Variables,Iter;
  
  n = clause_Length(Clause);

  fputs("  formula(", File);
  Variables = list_Nil();

  for (j = 0; j < n; j++)
    Variables =
      list_NPointerUnion(Variables,
	term_VariableSymbols(clause_GetLiteralAtom(Clause,j)));

  if (!list_Empty(Variables)) {
    symbol_FPrint(File, fol_All());
    fputs("([", File);
    for (Iter = Variables; !list_Empty(Iter); Iter = list_Cdr(Iter)) {
      symbol_FPrint(File, (SYMBOL) list_Car(Iter));
      if (!list_Empty(list_Cdr(Iter)))
	putc(',', File);
    }
    fputs("],", File);
  }
  
  if (n>1) {
    symbol_FPrint(File, fol_Or());
    putc('(', File);
  }

  for (j = 0; j < n; j++) {
    Lit  = clause_GetLiteral(Clause,j);
    Atom = clause_LiteralSignedAtom(Lit);
    term_FPrintPrefix(File,Atom);
    if (j+1 < n)
      putc(',', File);
  }
  if (n==0)
    symbol_FPrint(File,fol_False());

  if (!list_Empty(Variables)) {
    list_Delete(Variables);
    putc(')', File);
  }

  if (n>1)
    fprintf(File, "),%d", clause_Number(Clause));
  else
    fprintf(File, ",%d", clause_Number(Clause));

  if (Justif) {
    putc(',', File);
    clause_FPrintOrigin(File, Clause);
    fputs(",[", File);
    for (Iter = clause_ParentClauses(Clause);
	 !list_Empty(Iter);
	 Iter = list_Cdr(Iter)) {
      fprintf(File, "%d", (int)list_Car(Iter));
      if (!list_Empty(list_Cdr(Iter)))
	putc(',', File);
    }
    putc(']', File);
    fprintf(File, ",%d", clause_SplitLevel(Clause));
  }
  
  fputs(").\n", File);
}


void clause_Check(CLAUSE Clause, FLAGSTORE Flags, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause, a flag store and a precedence.
  RETURNS: Nothing.
  EFFECT:  Checks whether the clause is in a proper state. If
           not, a core is dumped.
***************************************************************/
{
  CLAUSE Copy;
  if (!clause_Exists(Clause))
    return;
  
  if (!clause_IsClause(Clause, Flags, Precedence)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_Check: Clause not consistent !\n");
    misc_FinishErrorReport();
  }

  Copy = clause_Copy(Clause);
  clause_OrientAndReInit(Copy, Flags, Precedence);
  if ((clause_Weight(Clause) != clause_Weight(Copy)) ||
      (clause_MaxVar(Clause) != clause_MaxVar(Copy))) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_Check: Weight or maximal variable not properly set.\n");
    misc_FinishErrorReport();
  }
  clause_Delete(Copy);
}

/* The following are output procedures for clauses with parent pointers */


void clause_PParentsFPrintParentClauses(FILE* File, CLAUSE Clause, BOOL ParentPts)
/**************************************************************
  INPUT:   A file, a clause and a boolean flag indicating whether
           the clause's parents are given by numbers or pointers.
  RETURNS: Nothing.
  SUMMARY: Prints the clauses parent clauses and -literals to the file.
           If <ParentPts> is TRUE the parent clauses are defined
           by pointers, else by numbers.
***************************************************************/
{
  LIST Scan1,Scan2;
  int  length;
  int  ParentNum;
  
  if (!list_Empty(clause_ParentClauses(Clause))) {
    
    Scan1 = clause_ParentClauses(Clause);
    Scan2 = clause_ParentLiterals(Clause);
    
    if (ParentPts)
      ParentNum = clause_Number(list_Car(Scan1));
    else
      ParentNum = (int)list_Car(Scan1);

    fprintf(File, "%d.%d", ParentNum, (int)list_Car(Scan2));
    
    if (!list_Empty(list_Cdr(Scan1))) {
      
      length = list_Length(Scan1) - 2;
      putc(',', File);
      Scan1 = list_Cdr(Scan1);
      Scan2 = list_Cdr(Scan2);
      
      if (ParentPts)
	ParentNum = clause_Number(list_Car(Scan1));
      else
	ParentNum = (int)list_Car(Scan1);

      fprintf(File, "%d.%d", ParentNum, (int)list_Car(Scan2));
      
      for (Scan1 = list_Cdr(Scan1), Scan2 = list_Cdr(Scan2);
	   !list_Empty(Scan1);
	   Scan1 = list_Cdr(Scan1), Scan2 = list_Cdr(Scan2)) {
	
	length -= 2;
	
	if (ParentPts)
	  ParentNum = clause_Number(list_Car(Scan1));
	else
	  ParentNum = (int)list_Car(Scan1);

	fprintf(File, ",%d.%d", ParentNum, (int)list_Car(Scan2));
      }
    }
  }
}

void clause_PParentsLiteralFPrintUnsigned(FILE* File, LITERAL Literal)
/**************************************************************
  INPUT:   A Literal.
  RETURNS: Nothing.
  SUMMARY:
***************************************************************/
{
#ifdef CHECK
  if (!clause_LiteralIsLiteral(Literal)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_PParentsLiteralFPrintUnsigned:");
    misc_ErrorReport("\n Illegal input. Input not a literal.");
    misc_FinishErrorReport();
  }
#endif

  term_FPrintPrefix(File, clause_LiteralAtom(Literal));
  fflush(stdout);
}

void clause_PParentsFPrintGen(FILE* File, CLAUSE Clause, BOOL ParentPts)
/**************************************************************
  INPUT:   A file, a clause, a boolean flag.
  RETURNS: Nothing.
  EFFECTS: Prints the clause to file in SPASS format. If <ParentPts>
           is TRUE, the parents of <Clause> are interpreted as pointers.
***************************************************************/
{
  LITERAL Lit;
  int i,c,a,s;

  if (!clause_Exists(Clause))
    fputs("(CLAUSE)NULL", File);
  else {
    fprintf(File, "%d",clause_Number(Clause));
    
    fprintf(File, "[%d:", clause_SplitLevel(Clause));

#ifdef CHECK
    if (Clause->splitfield_length <= 1)
      fputs("0.", File);
    else
      for (i=Clause->splitfield_length-1; i > 0; i--)
	fprintf(File, "%lu.", Clause->splitfield[i]);
    if (Clause->splitfield_length == 0)
      putc('1', File);
    else
      fprintf(File, "%lu", (Clause->splitfield[0] | 1));
    fprintf(File,":%c%c:%c:%d:%d:", clause_GetFlag(Clause, CONCLAUSE) ? 'C' : 'A',
	   clause_GetFlag(Clause, WORKEDOFF) ? 'W' : 'U',
	   clause_GetFlag(Clause, NOPARAINTO) ? 'N' : 'P',
	   clause_Weight(Clause), clause_Depth(Clause));
#endif
    
    clause_FPrintOrigin(File, Clause);
    
    if (!list_Empty(clause_ParentClauses(Clause))) {
      putc(':', File);
      clause_PParentsFPrintParentClauses(File, Clause, ParentPts);
    }
    putc(']', File);

    c = clause_NumOfConsLits(Clause);
    a = clause_NumOfAnteLits(Clause);
    s = clause_NumOfSuccLits(Clause);

    for (i = 0; i < c; i++) {
      Lit = clause_GetLiteral(Clause, i);
      clause_PParentsLiteralFPrintUnsigned(File, Lit);
      if (i+1 < c)
	putc(' ', File);
    }
    fputs(" || ", File);

    a += c;
    for ( ; i < a; i++) {

      Lit = clause_GetLiteral(Clause, i);
      clause_PParentsLiteralFPrintUnsigned(File, Lit);
      if (clause_LiteralIsMaximal(Lit)) {
	putc('*', File);
	if (clause_LiteralIsOrientedEquality(Lit))
	  putc('*', File);
      }
      if (clause_LiteralGetFlag(Lit,LITSELECT))
	putc('+', File);
      if (i+1 < a)
	putc(' ', File);
    }
    fputs(" -> ",File);

    s += a;
    for ( ; i < s; i++) {

      Lit = clause_GetLiteral(Clause, i);
      clause_PParentsLiteralFPrintUnsigned(File, Lit);
      if (clause_LiteralIsMaximal(Lit)) {
	putc('*', File);
	if (clause_LiteralIsOrientedEquality(Lit))
	  putc('*', File);
      }
#ifdef CHECK
      if (clause_LiteralGetFlag(Lit, LITSELECT)) {
	misc_StartErrorReport();
	misc_ErrorReport("\n In clause_PParentsFPrintGen: Clause has selected positive literal.\n");
	misc_FinishErrorReport();
      }
#endif
      if (i+1 < s)
	putc(' ', File);
    }
    putc('.', File);
  }
}

void clause_PParentsFPrint(FILE* File, CLAUSE Clause)
/**************************************************************
  INPUT:   A file handle and a clause.
  RETURNS: Nothing.
  EFFECTS: Prints out the clause to file in SPASS output format
***************************************************************/
{
  clause_PParentsFPrintGen(File, Clause, TRUE);
}

void clause_PParentsListFPrint(FILE* File, LIST L)
/**************************************************************
 INPUT:   A file handle, a list of clauses with parent pointers
 RETURNS: Nothing.
 EFFECTS: Print the list to <file>.
***************************************************************/
{
  while (!list_Empty(L)) {
    clause_PParentsFPrint(File, list_Car(L));
    putc('\n', File);
    L = list_Cdr(L);
  }
}


void clause_PParentsPrint(CLAUSE Clause)
/**************************************************************
 INPUT:   A clause with parent pointers
 RETURNS: Nothing.
 EFFECTS: The clause is printed to stdout.
***************************************************************/
{
  clause_PParentsFPrint(stdout, Clause);
}

void clause_PParentsListPrint(LIST L)
/**************************************************************
 INPUT:   A file handle, a list of clauses with parent pointers
 RETURNS: Nothing.
 EFFECTS: Print the clause list to stdout.
***************************************************************/
{
  clause_PParentsListFPrint(stdout, L);
}
