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

#ifndef _CLAUSE_
#define _CLAUSE_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "sharing.h"
#include "foldfg.h"
#include "order.h"
#include "subst.h"
#include "flags.h"
#include "symbol.h"

/**************************************************************/
/* Data Structures and Constants                              */
/**************************************************************/

/* Means weight of literal or clause is undefined */
extern const NAT clause_WEIGHTUNDEFINED;

extern int clause_CLAUSECOUNTER;

typedef enum {MAXIMAL=1, STRICTMAXIMAL=2, LITSELECT=4} MAXFLAG;

typedef enum {CLAUSE_DELETION, EMPTY_SORT, SORT_RESOLUTION,
	      EQUALITY_RESOLUTION, EQUALITY_FACTORING, MERGING_PARAMODULATION,
	      PARAMODULATION, ORDERED_PARAMODULATION,
	      SUPERPOSITION_RIGHT,  SUPERPOSITION_LEFT,
	      SIMPLE_HYPER, ORDERED_HYPER, UR_RESOLUTION,
	      GENERAL_RESOLUTION, GENERAL_FACTORING, SPLITTING, INPUT,
	      CONDENSING, ASSIGNMENT_EQUATION_DELETION, OBVIOUS_REDUCTIONS,
	      SORT_SIMPLIFICATION, REWRITING, CONTEXTUAL_REWRITING,
	      MATCHING_REPLACEMENT_RESOLUTION, UNIT_CONFLICT, DEFAPPLICATION,
	      TERMINATOR, TEMPORARY
} RULE;

typedef unsigned long SPLITFIELDENTRY;
typedef SPLITFIELDENTRY* SPLITFIELD;

typedef enum  {WORKEDOFF=1,CLAUSESELECT=2,DOCCLAUSE=4,CONCLAUSE=8,BLOCKED=16,
	       NOPARAINTO=32, MARKED=64, HIDDEN=128} CLAUSE_FLAGS;


/* As there are a lot of implications a clauses properties may have */
/* for the prover, this information should be kept with the clause. */
/* That for a flagfield is foreseen, most likely an integer used    */
/* like the sort-Bitfield existing for term, now used for varoccs.  */

typedef struct CLAUSE_HELP{
  int      clausenumber;
  NAT      weight;     /* The sum of the weight of all literals */
  NAT      depth;      /* The depth of the clause in the derivation  */
  NAT      validlevel; /* Level of splitting where clause is valid. */
  SPLITFIELD splitfield;
  unsigned splitfield_length;
  
  LIST     parentCls, parentLits; /* Parents clauses' clause and lit numbers.*/
  NAT      flags;
  SYMBOL   maxVar;     /* The maximal variable symbol in the clause */
  struct LITERAL_HELP{
    NAT    maxLit;     /* for clause intern literal ordering */
    NAT    weight;     /* weight of the <atomWithSign> below */
    BOOL   oriented;   /* Flag, TRUE if clause is oriented, i.e. equalities
			  with bigger first arg and all other predicates */
    struct CLAUSE_HELP *owningClause;
    TERM   atomWithSign; /* Pointer to the term, where an unshared
			    Term for the sign of negative literals
			    is supplied additionally.              */
  } **literals;        /* An Array of (c+a+s) literalpointers in this order. */
  int      c;          /* number of constraint literals */
  int      a;          /* number of antecedent literals */
  int	   s;          /* number of succedent literals */
  RULE    origin;
} *CLAUSE, CLAUSE_NODE;

typedef struct LITERAL_HELP *LITERAL, LITERAL_NODE;


/**************************************************************/
/* Functions Prototypes                                       */
/**************************************************************/

/**************************************************************/
/* Functions on clauses and literals creation and deletion.   */
/**************************************************************/

void    clause_Init(void);

CLAUSE  clause_CreateBody(int);
CLAUSE  clause_Create(LIST, LIST, LIST, FLAGSTORE, PRECEDENCE);
CLAUSE  clause_CreateCrude(LIST, LIST, LIST, BOOL);
CLAUSE  clause_CreateUnnormalized(LIST, LIST, LIST);
CLAUSE  clause_CreateFromLiterals(LIST, BOOL, BOOL, BOOL, FLAGSTORE, PRECEDENCE);
void    clause_Delete(CLAUSE);

LITERAL clause_LiteralCreate(TERM, CLAUSE);
LITERAL clause_LiteralCreateNegative(TERM, CLAUSE);        /* Unused */
void    clause_LiteralDelete(LITERAL);

LIST    clause_CopyConstraint(CLAUSE);
LIST    clause_CopyAntecedentExcept(CLAUSE, int);
LIST    clause_CopySuccedent(CLAUSE);
LIST    clause_CopySuccedentExcept(CLAUSE, int);


/**************************************************************/
/* Functions to use the sharing for clauses and literals.     */
/**************************************************************/

void    clause_InsertIntoSharing(CLAUSE, SHARED_INDEX, FLAGSTORE, PRECEDENCE);
void    clause_DeleteFromSharing(CLAUSE, SHARED_INDEX, FLAGSTORE, PRECEDENCE);

void    clause_MakeUnshared(CLAUSE, SHARED_INDEX);
void    clause_MoveSharedClause(CLAUSE, SHARED_INDEX, SHARED_INDEX, FLAGSTORE, PRECEDENCE);
void    clause_DeleteSharedLiteral(CLAUSE, int, SHARED_INDEX, FLAGSTORE, PRECEDENCE);

void    clause_LiteralInsertIntoSharing(LITERAL, SHARED_INDEX);
void    clause_LiteralDeleteFromSharing(LITERAL, SHARED_INDEX);  /* Used only in clause.c */

void    clause_DeleteClauseList(LIST);
void    clause_DeleteSharedClauseList(LIST, SHARED_INDEX, FLAGSTORE, PRECEDENCE);
void    clause_DeleteAllIndexedClauses(SHARED_INDEX, FLAGSTORE, PRECEDENCE); /* Necessary? */
void    clause_PrintAllIndexedClauses(SHARED_INDEX);       /* For Debugging */
LIST    clause_AllIndexedClauses(SHARED_INDEX);

/**************************************************************/
/* Clause Comparisons                                         */
/**************************************************************/

BOOL    clause_IsHornClause(CLAUSE);
int     clause_CompareAbstract(CLAUSE, CLAUSE);

/**************************************************************/
/* Clause and literal Input and Output Functions              */
/**************************************************************/

void    clause_Print(CLAUSE);
void    clause_PrintVerbose(CLAUSE, FLAGSTORE, PRECEDENCE);
void    clause_PrintMaxLitsOnly(CLAUSE, FLAGSTORE, PRECEDENCE); /* For Debugging */
void    clause_FPrint(FILE*, CLAUSE);                /* For Debugging */
void    clause_FPrintRule(FILE*, CLAUSE);
void    clause_FPrintOtter(FILE*, CLAUSE);           /* Unused */
void    clause_FPrintCnfDFG(FILE* , BOOL, LIST, LIST, FLAGSTORE, PRECEDENCE);
void    clause_FPrintCnfDFGProblem(FILE* , const char*, const char*, const char*, const char*, LIST);
void    clause_FPrintCnfFormulasDFGProblem(FILE* , BOOL, const char*, const char*, const char*, const char*, LIST, LIST, FLAGSTORE, PRECEDENCE);
void    clause_FPrintCnfDFGDerivables(FILE*, LIST, BOOL);
void    clause_FPrintDFG(FILE*, CLAUSE, BOOL);
void    clause_FPrintDFGStep(FILE*, CLAUSE, BOOL);
void    clause_FPrintFormulaDFG(FILE*, CLAUSE, BOOL);
void    clause_FPrintCnfOtter(FILE*, LIST, FLAGSTORE);

void    clause_LiteralPrint(LITERAL);                /* For Debugging */
void    clause_LiteralListPrint(LIST);               /* For Debugging */
void    clause_LiteralPrintUnsigned(LITERAL);        /* For Debugging */
void    clause_LiteralPrintSigned(LITERAL);          /* For Debugging */
void    clause_LiteralFPrint(FILE*, LITERAL);        /* For Debugging */

void    clause_ListPrint(LIST);

void    clause_PrintParentClauses(CLAUSE);           /* For Debugging */
void    clause_PrintOrigin(CLAUSE);                  /* For Debugging */
void    clause_FPrintOrigin(FILE*, CLAUSE);

/**************************************************************/
/* Specials                                                   */
/**************************************************************/

CLAUSE  clause_Copy(CLAUSE);
LITERAL clause_LiteralCopy(LITERAL);

static __inline__ LIST clause_CopyClauseList(LIST List)
{
  return list_CopyWithElement(List, (POINTER (*)(POINTER)) clause_Copy);
}

void    clause_DeleteLiteral(CLAUSE, int, FLAGSTORE, PRECEDENCE);
void    clause_DeleteLiteralNN(CLAUSE, int);
void    clause_DeleteLiterals(CLAUSE, LIST, FLAGSTORE, PRECEDENCE);  /* Unused */
LIST    clause_GetLiteralSubSetList(CLAUSE, int, int, FLAGSTORE, PRECEDENCE);
void    clause_ReplaceLiteralSubSet(CLAUSE, int, int, LIST, FLAGSTORE, PRECEDENCE);
void    clause_FixLiteralOrder(CLAUSE, FLAGSTORE, PRECEDENCE);

SYMBOL  clause_AtomMaxVar(TERM);
void    clause_SetMaxLitFlags(CLAUSE, FLAGSTORE, PRECEDENCE);
SYMBOL  clause_LiteralMaxVar(LITERAL);        /* Used only in clause.c */
SYMBOL  clause_SearchMaxVar(CLAUSE);
void    clause_UpdateMaxVar(CLAUSE);

void    clause_RenameVarsBiggerThan(CLAUSE, SYMBOL);
void    clause_Normalize(CLAUSE);
void    clause_SetSortConstraint(CLAUSE, BOOL, FLAGSTORE, PRECEDENCE);
void    clause_SubstApply(SUBST, CLAUSE);
void    clause_ReplaceVariable(CLAUSE, SYMBOL, TERM);
void    clause_OrientEqualities(CLAUSE, FLAGSTORE, PRECEDENCE);
NAT     clause_NumberOfVarOccs(CLAUSE);
NAT     clause_NumberOfSymbolOccurrences(CLAUSE, SYMBOL);
NAT     clause_ComputeWeight(CLAUSE, FLAGSTORE);
NAT     clause_LiteralComputeWeight(LITERAL, FLAGSTORE);
NAT     clause_ComputeTermDepth(CLAUSE);
NAT     clause_MaxTermDepthClauseList(LIST);
NAT     clause_ComputeSize(CLAUSE);
BOOL    clause_WeightCorrect(CLAUSE, FLAGSTORE, PRECEDENCE);   /* Unused */

LIST    clause_MoveBestLiteralToFront(LIST, SUBST, SYMBOL,
				      BOOL (*)(LITERAL, NAT, LITERAL, NAT));


LIST    clause_InsertWeighed(CLAUSE, LIST, FLAGSTORE, PRECEDENCE);
LIST    clause_ListSortWeighed(LIST);

BOOL    clause_HasTermSortConstraintLits(CLAUSE);
BOOL    clause_HasSolvedConstraint(CLAUSE);
BOOL    clause_IsDeclarationClause(CLAUSE);
BOOL    clause_IsSortTheoryClause(CLAUSE, FLAGSTORE, PRECEDENCE);
BOOL    clause_IsPartOfDefinition(CLAUSE, TERM, int*, LIST);
BOOL    clause_IsPotentialSortTheoryClause(CLAUSE, FLAGSTORE, PRECEDENCE);
BOOL    clause_HasOnlyVarsInConstraint(CLAUSE, FLAGSTORE, PRECEDENCE);
BOOL    clause_HasSortInSuccedent(CLAUSE, FLAGSTORE, PRECEDENCE);
BOOL    clause_ContainsPotPredDef(CLAUSE, FLAGSTORE, PRECEDENCE, NAT*, LIST*);
BOOL    clause_LitsHaveCommonVar(LITERAL, LITERAL);

void    clause_SelectLiteral(CLAUSE, FLAGSTORE);
void    clause_SetSpecialFlags(CLAUSE,BOOL, FLAGSTORE, PRECEDENCE);

BOOL    clause_LiteralIsLiteral(LITERAL);
BOOL    clause_IsClause(CLAUSE, FLAGSTORE, PRECEDENCE);
BOOL    clause_IsUnorderedClause(CLAUSE);
BOOL    clause_ContainsPositiveEquations(CLAUSE);
BOOL    clause_ContainsNegativeEquations(CLAUSE);
int     clause_ContainsFolAtom(CLAUSE,BOOL*,BOOL*,BOOL*,BOOL*);
BOOL    clause_ContainsVariables(CLAUSE);
BOOL    clause_ContainsFunctions(CLAUSE);
BOOL    clause_ContainsSymbol(CLAUSE, SYMBOL);
void    clause_ContainsSortRestriction(CLAUSE,BOOL*,BOOL*);
BOOL    clause_ImpliesFiniteDomain(CLAUSE);
BOOL    clause_ImpliesNonTrivialDomain(CLAUSE);
LIST    clause_FiniteMonadicPredicates(LIST);

CLAUSE  clause_GetNumberedCl(int, LIST);
LIST    clause_NumberSort(LIST);
LIST    clause_NumberDelete(LIST,int);
void    clause_Check(CLAUSE, FLAGSTORE, PRECEDENCE);

void    clause_DeleteFlatFromIndex(CLAUSE, st_INDEX);
void    clause_InsertFlatIntoIndex(CLAUSE, st_INDEX);
void    clause_DeleteClauseListFlatFromIndex(LIST, st_INDEX);

RULE    clause_GetOriginFromString(const char*);

void    clause_CountSymbols(CLAUSE);

LIST    clause_ListOfPredicates(CLAUSE);
LIST    clause_ListOfConstants(CLAUSE);
LIST    clause_ListOfVariables(CLAUSE);
LIST    clause_ListOfFunctions(CLAUSE);

/* special output functions for clauses with parent pointers */
void clause_PParentsFPrint(FILE*, CLAUSE);
void clause_PParentsListFPrint(FILE*, LIST L);
void clause_PParentsPrint(CLAUSE);
void clause_PParentsListPrint(LIST);
void clause_PParentsFPrintGen(FILE*, CLAUSE, BOOL);


/**************************************************************/
/* Inline Functions                                           */
/**************************************************************/

/**************************************************************/
/* Accessing Literals 1                                       */
/**************************************************************/

static __inline__ TERM clause_LiteralSignedAtom(LITERAL L)
{
  return L->atomWithSign;
}


static __inline__ CLAUSE clause_LiteralOwningClause(LITERAL L)
{
  return L->owningClause;
}

static __inline__ void clause_LiteralSetOwningClause(LITERAL L, CLAUSE C)
{
  L->owningClause = C;
}


static __inline__ void clause_LiteralSetOrientedEquality(LITERAL L)
{
  L->oriented = TRUE;
}

static __inline__ void clause_LiteralSetNoOrientedEquality(LITERAL L)
{
  L->oriented = FALSE;
}


static __inline__ NAT clause_LiteralWeight(LITERAL L)
{
#ifdef CHECK
  if (L->weight == clause_WEIGHTUNDEFINED) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_LiteralWeight:");
    misc_ErrorReport(" Tried to access undefined weight.");
    misc_FinishErrorReport();
  }
#endif
  return L->weight;
}


static __inline__ void clause_UpdateLiteralWeight(LITERAL L, FLAGSTORE Flags)
{
  L->weight = clause_LiteralComputeWeight(L, Flags);
}


static __inline__ void clause_LiteralFlagReset(LITERAL L)
{
  L->maxLit = 0;
}

static __inline__ BOOL clause_LiteralGetFlag(LITERAL L, MAXFLAG Flag)
{
  return ((L->maxLit & Flag) != 0);
}

static __inline__ void clause_LiteralSetFlag(LITERAL L, MAXFLAG Flag)
{
  L->maxLit = (L->maxLit) | Flag;
}

static __inline__ BOOL clause_LiteralIsMaximal(LITERAL L)
{
  return clause_LiteralGetFlag(L, MAXIMAL);
}



static __inline__ BOOL clause_LiteralIsOrientedEquality(LITERAL L)
{
  return L->oriented;
}


static __inline__ BOOL clause_LiteralIsNotOrientedEquality(LITERAL L)
{
  return !(L->oriented);
}


/**************************************************************/
/* Literal Comparison 1                                       */
/**************************************************************/

static __inline__ BOOL clause_LiteralIsNegative(LITERAL L)
{
  return (term_TopSymbol(clause_LiteralSignedAtom(L)) == fol_Not());
}

static __inline__ BOOL clause_LiteralIsPositive(LITERAL L)
{
  return !clause_LiteralIsNegative(L);
}


static __inline__ BOOL clause_LiteralsAreComplementary(LITERAL L1, LITERAL L2)
{
  return ((clause_LiteralIsNegative(L1) &&
	   clause_LiteralIsPositive(L2)) ||
	  (clause_LiteralIsNegative(L2) &&
	   clause_LiteralIsPositive(L1)));      /* xor */
}

static __inline__ BOOL clause_HyperLiteralIsBetter(LITERAL Dummy1, NAT S1,
						   LITERAL Dummy2, NAT S2)
/**************************************************************
  INPUT:   Two literals and its sizes wrt. some substitution.
  RETURNS: TRUE, if the first literal is 'better' than the second literal,
           FALSE otherwise.
  EFFECT:  A literal is 'better' than another, if S1 > Ss.
           Since we have to find unifiable complementary literals
	   for every remaining antecedent literal, it seems to be
	   a good idea to try the most 'difficult' literal first,
	   in order to stop the search as early as possible..
	   Here we prefer the literal with the highest number
	   of symbols..
           This function is used as parameter for the function
	   clause_MoveBestLiteralToFront.
  CAUTION: The parameters <Dummy1> and <Dummy2> are unused, they're just
           added to keep the compiler quiet.
***************************************************************/
{
  return (S1 > S2);
}


/**************************************************************/
/* Accessing Literals 2                                       */
/**************************************************************/

static __inline__ TERM clause_LiteralAtom(LITERAL L)
{
  if (clause_LiteralIsNegative(L))
    return term_FirstArgument(clause_LiteralSignedAtom(L));
  else
    return clause_LiteralSignedAtom(L);
}


static __inline__ SYMBOL clause_LiteralPredicate(LITERAL L)
{
  return term_TopSymbol(clause_LiteralAtom(L));
}

static __inline__ BOOL clause_LiteralIsPredicate(LITERAL L)
{
  return !fol_IsEquality(clause_LiteralAtom(L));
}

static __inline__ BOOL clause_LiteralIsEquality(LITERAL L)
{
  return fol_IsEquality(clause_LiteralAtom(L));
}

static __inline__ BOOL clause_LiteralIsSort(LITERAL L)
{
  SYMBOL S;
  S = clause_LiteralPredicate(L);
  return (symbol_IsPredicate(S) &&
	  (symbol_Arity(S) == 1));
}


static __inline__ void clause_LiteralSetAtom(LITERAL L, TERM A)
{
  if (clause_LiteralIsNegative(L))
    list_Rplaca(term_ArgumentList(clause_LiteralSignedAtom(L)),A);
  else
    L->atomWithSign = A;
}

static __inline__ void clause_LiteralSetNegAtom(LITERAL L, TERM A)
{
  list_Rplaca(term_ArgumentList(clause_LiteralSignedAtom(L)), A);
}

static __inline__ void clause_LiteralSetPosAtom(LITERAL L, TERM A)
{
  L->atomWithSign = A;
}

static __inline__ void clause_NLiteralSetLiteral(LITERAL L, TERM LIT)
{
  L->atomWithSign = LIT;
}

/**************************************************************/
/* Memory management                                          */
/**************************************************************/

static __inline__ void clause_LiteralFree(LITERAL L)
{
  memory_Free(L, sizeof(LITERAL_NODE));
}


/**************************************************************/
/* Functions to access literals.                                 */
/**************************************************************/

static __inline__ LITERAL clause_GetLiteral(CLAUSE C, int Index)
{
  return C->literals[Index];
}

static __inline__ void clause_SetLiteral(CLAUSE C, int Index, LITERAL L)
{
  C->literals[Index]= L;
}

static __inline__ TERM clause_GetLiteralTerm(CLAUSE C, int Index)
{
  return clause_LiteralSignedAtom(clause_GetLiteral(C, Index));
}

static __inline__ TERM clause_GetLiteralAtom(CLAUSE C, int Index)
{
  return clause_LiteralAtom(clause_GetLiteral(C, Index));
}

static __inline__ int clause_NumOfConsLits(CLAUSE Clause)
{
  return Clause->c;
}

static __inline__ int clause_NumOfAnteLits(CLAUSE Clause)
{
  return Clause->a;
}

static __inline__ int clause_NumOfSuccLits(CLAUSE Clause)
{
  return Clause->s;
}

static __inline__ void clause_SetNumOfConsLits(CLAUSE Clause, int Number)
{
  Clause->c = Number;
}

static __inline__ void clause_SetNumOfAnteLits(CLAUSE Clause, int Number)
{
  Clause->a = Number;
}

static __inline__ void clause_SetNumOfSuccLits(CLAUSE Clause, int Number)
{
  Clause->s = Number;
}

static __inline__ int clause_Length(CLAUSE Clause)
{
  return (clause_NumOfConsLits(Clause) +
	  clause_NumOfAnteLits(Clause) +
	  clause_NumOfSuccLits(Clause));
}


static __inline__ int clause_LastLitIndex(CLAUSE Clause)
{
  return clause_Length(Clause) - 1;
}

static __inline__ int clause_FirstLitIndex(void)
{
  return 0;
}

static __inline__ int clause_FirstConstraintLitIndex(CLAUSE Clause)
{
  return 0;
}

static __inline__ int clause_FirstAntecedentLitIndex(CLAUSE Clause)
{
  return clause_NumOfConsLits(Clause);
}

static __inline__ int clause_FirstSuccedentLitIndex(CLAUSE Clause)
{
  return (clause_NumOfAnteLits(Clause) + clause_NumOfConsLits(Clause));
}


static __inline__ int clause_LastConstraintLitIndex(CLAUSE Clause)
{
  return clause_NumOfConsLits(Clause) - 1;
}

static __inline__ int clause_LastAntecedentLitIndex(CLAUSE Clause)
{
  return clause_FirstSuccedentLitIndex(Clause) - 1;
}

static __inline__ int clause_LastSuccedentLitIndex(CLAUSE Clause)
{
  return clause_Length(Clause) - 1;
}

static __inline__ LIST clause_GetLiteralList(CLAUSE Clause)
/**************************************************************
  INPUT:   A clause.
  RETURNS: A new list is created containing all literals of the
           clause. The list contains pointers, not literal indexes.
***************************************************************/
{
  LIST Result;
  int  i;

  Result = list_Nil();
  for (i=clause_FirstLitIndex(); i<=clause_LastLitIndex(Clause); i++)
    Result = list_Cons(clause_GetLiteral(Clause, i), Result);
  return Result;
}


static __inline__ LIST clause_GetLiteralListExcept(CLAUSE Clause, int Index)
/**************************************************************
  INPUT:   A clause.
  RETURNS: A new list is created containing all literals of the
           clause except the literal at <Index>. The list contains
	   pointers, not literal indexes.
***************************************************************/
{
  LIST Result;
  int  i;

  Result = list_Nil();
  for (i=clause_FirstLitIndex(); i<=clause_LastLitIndex(Clause); i++)
    if (i != Index)
      Result = list_Cons(clause_GetLiteral(Clause, i), Result);
  return Result;
}


/**************************************************************/
/* Clause Access Macros                                       */
/**************************************************************/

static __inline__ int clause_Counter(void)
{
  return clause_CLAUSECOUNTER;
}

static __inline__ void clause_SetCounter(int Value)
{
#ifdef CHECK
  if (Value < 0) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_SetCounter: new counter value is negative.");
    misc_FinishErrorReport();
  }
#endif
  clause_CLAUSECOUNTER = Value;
}

static __inline__ int clause_IncreaseCounter(void)
{
#ifdef CHECK
  if (clause_CLAUSECOUNTER == INT_MAX) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_IncreaseCounter: counter overflow.");
    misc_FinishErrorReport();
  }
#endif
  return clause_CLAUSECOUNTER++;
}

static __inline__ void clause_DecreaseCounter(void)
{
#ifdef CHECK
  if (clause_CLAUSECOUNTER == 0) {
    misc_FinishErrorReport();
    misc_ErrorReport("\n In clause_DecreaseCounter: counter underflow.");
    misc_FinishErrorReport();
  }
#endif
  clause_CLAUSECOUNTER--;
}

static __inline__ NAT clause_Depth(CLAUSE Clause)
{
  return Clause->depth;
}

static __inline__ void clause_SetDepth(CLAUSE Clause, NAT NewDepth)
{
  Clause->depth = NewDepth;
}


static __inline__ NAT clause_Weight(CLAUSE Clause)
{
#ifdef CHECK
  if (Clause->weight == clause_WEIGHTUNDEFINED) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_Weight: Tried to access undefined weight.");
    misc_FinishErrorReport();
  }
#endif
  return Clause->weight;
}

static __inline__ void clause_UpdateWeight(CLAUSE Clause, FLAGSTORE Flags)
{
  Clause->weight = clause_ComputeWeight(Clause, Flags);
}


static __inline__ int clause_Number(const CLAUSE Clause)
{
  return Clause->clausenumber;
}

static __inline__ void clause_SetNumber(CLAUSE Clause, int Number)
{
  Clause->clausenumber = Number;
}

static __inline__ void clause_NewNumber(CLAUSE Clause)
{
  Clause->clausenumber = clause_IncreaseCounter();
}


static __inline__ NAT clause_SplitLevel(CLAUSE Clause)
{
  return Clause->validlevel;
}

static __inline__ BOOL clause_CheckSplitLevel(CLAUSE Clause)
/**************************************************************
  INPUT:   A clause.
  RETURNS: TRUE, if the splitlevel invariant for the clause is fulfilled.
  EFFECT:  Checks, if the validlevel of the clause is the order
           of the highest set bit in the SPLITFIELD entry
           of the clause.
***************************************************************/
{
  if (Clause->validlevel == 0)
    return (Clause->splitfield == NULL);
  else {
    int i, j;
    for (i = Clause->splitfield_length-1; i >= 0; i--)
      if (Clause->splitfield[i] != 0)
	break;
    for (j = sizeof(SPLITFIELDENTRY)*CHAR_BIT-1; j >= 0; j--)
      if (Clause->splitfield[i] & ((SPLITFIELDENTRY)1 << j))
	break;
    return (Clause->validlevel == (i*sizeof(SPLITFIELDENTRY)*CHAR_BIT+j));
  }
}

static __inline__ LIST clause_ParentClauses(CLAUSE Clause)
{
  return Clause->parentCls;
}

static __inline__ LIST clause_ParentLiterals(CLAUSE Clause)
{
  return Clause->parentLits;
}


static __inline__ SYMBOL clause_MaxVar(CLAUSE Clause)
{
  return Clause->maxVar;
}

static __inline__ void clause_SetMaxVar(CLAUSE Clause, SYMBOL Variable)
{
  Clause->maxVar = Variable;
}


static __inline__ RULE clause_Origin(CLAUSE Clause)
{
  return Clause->origin;
}

static __inline__ BOOL clause_Exists(CLAUSE Clause)
{
  return (Clause != (CLAUSE)NULL);
}

static __inline__ BOOL clause_LiteralExists(LITERAL L)
{
  return (L != (LITERAL)NULL);
}

static __inline__ CLAUSE clause_Null(void)
{
  return (CLAUSE) NULL;
}

static __inline__ void clause_SetSplitLevel(CLAUSE Clause, NAT Level)
{
  Clause->validlevel = Level;
}

static __inline__ void clause_InitSplitData(CLAUSE C)
{
  C->splitfield = NULL;
  C->splitfield_length = 0;
  clause_SetSplitLevel(C, 0);
}

static __inline__ void clause_SetSplitField(CLAUSE Clause, SPLITFIELD B,
					    unsigned Length)
{
  unsigned i;
  if (Clause->splitfield_length != Length) {
    if (Clause->splitfield != NULL) {
      memory_Free(Clause->splitfield,
		  sizeof(SPLITFIELDENTRY) * Clause->splitfield_length);
    }
    if (Length != 0) {
      Clause->splitfield = memory_Malloc(sizeof(SPLITFIELDENTRY) * Length);
    }
    else
      Clause->splitfield = NULL;
    Clause->splitfield_length = Length;
  }
  for (i=0; i < Length; i++)
    Clause->splitfield[i] = B[i];
}


static __inline__ NAT  clause_ComputeSplitFieldAddress(NAT n, NAT* field)
{
  *field = 0;
  while (n >= (sizeof(SPLITFIELDENTRY) * CHAR_BIT)) {
    (*field)++;
    n -= sizeof(SPLITFIELDENTRY) * CHAR_BIT;
  }
  return n;
}

static __inline__ void clause_ExpandSplitField(CLAUSE C, NAT Length)
{
  SPLITFIELD NewField;
  NAT i;
  if (C->splitfield_length < Length) {
    NewField = memory_Malloc(sizeof(SPLITFIELDENTRY) * Length);
    for (i=0; i < C->splitfield_length; i++)
      NewField[i] = C->splitfield[i];
    for (i=C->splitfield_length; i < Length; i++)
      NewField[i] = 0;
    if (C->splitfield != NULL) {
      memory_Free(C->splitfield,
		  sizeof(SPLITFIELDENTRY) * C->splitfield_length);
    }
    C->splitfield = NewField;
    C->splitfield_length = Length;
  }
}

static __inline__ void clause_UpdateSplitField(CLAUSE C1, CLAUSE C2)
  /* Add the split data of <C2> to <C1> */
{
  unsigned i;
  if (C1->splitfield_length < C2->splitfield_length)
    clause_ExpandSplitField(C1, C2->splitfield_length);
  for (i=0; i < C2->splitfield_length; i++)
    C1->splitfield[i] = C1->splitfield[i] | C2->splitfield[i];
}

static __inline__ void clause_ClearSplitField(CLAUSE C)
{
  int i;

  for (i=C->splitfield_length-1; i >=0; i--)
    C->splitfield[i] = 0;
}
	
static __inline__ void clause_SetSplitFieldBit(CLAUSE Clause, NAT n)
{
  unsigned field;
  
  n = clause_ComputeSplitFieldAddress(n, &field);
  if (field >= Clause->splitfield_length)
    clause_ExpandSplitField(Clause, field + 1);
  Clause->splitfield[field] = (Clause->splitfield[field]) |
    ((SPLITFIELDENTRY)1 << n);
}

static __inline__ BOOL clause_GetFlag(CLAUSE Clause, CLAUSE_FLAGS Flag)
{
  return (Clause->flags & Flag) != 0;
}

static __inline__ void clause_SetFlag(CLAUSE Clause, CLAUSE_FLAGS Flag)
{
  Clause->flags = Clause->flags | Flag;
}

static __inline__ void clause_RemoveFlag(CLAUSE Clause, CLAUSE_FLAGS Flag)
{
  if (Clause->flags & Flag)
    Clause->flags = Clause->flags - Flag;
}

static __inline__ void clause_ClearFlags(CLAUSE Clause)
{
  Clause->flags = 0;
}


static __inline__ BOOL clause_DependsOnSplitLevel(CLAUSE C, NAT N)
{
  if (N==0)
    return TRUE;
  else {
    unsigned field;
    N = clause_ComputeSplitFieldAddress(N, &field);
    if (field >= C->splitfield_length)
      return FALSE;
    else
      return (C->splitfield[field] & ((SPLITFIELDENTRY)1 << N)) != 0;
  }
}

static __inline__ void clause_SetSplitDataFromFather(CLAUSE Result,
						     CLAUSE Father)
{
  if (clause_GetFlag(Father, CONCLAUSE))
    clause_SetFlag(Result, CONCLAUSE);
  clause_SetSplitLevel(Result, clause_SplitLevel(Father));
  clause_SetSplitField(Result, Father->splitfield, Father->splitfield_length);
}

static __inline__ void clause_UpdateSplitDataFromNewSplitting(CLAUSE Result,
							      CLAUSE Father,
							      NAT Level)
{
  unsigned field;
  NAT i;
  
  clause_SetSplitLevel(Result, Level);
  Level = clause_ComputeSplitFieldAddress(Level, &field);

  if (field >= Result->splitfield_length) {
    if (Result->splitfield != NULL)
      memory_Free(Result->splitfield,
		  sizeof(SPLITFIELDENTRY) * Result->splitfield_length);
    Result->splitfield = memory_Malloc((field + 1) * sizeof(SPLITFIELDENTRY));
    Result->splitfield_length = field + 1;
  }
  if (clause_GetFlag(Father, CONCLAUSE))
    clause_SetFlag(Result, CONCLAUSE);
  for (i=0; i < Father->splitfield_length; i++)
    Result->splitfield[i] = Father->splitfield[i];
  for (i=Father->splitfield_length; i < Result->splitfield_length; i++)
    Result->splitfield[i] = 0;
  Result->splitfield[field] = (Result->splitfield[field] | ((SPLITFIELDENTRY)1 << Level));
}

static __inline__ void clause_UpdateSplitDataFromPartner(CLAUSE Result,
							 CLAUSE Partner)
{
  if (clause_GetFlag(Partner, CONCLAUSE))
    clause_SetFlag(Result, CONCLAUSE);
  if (clause_SplitLevel(Partner) == 0)
    return;
  /* Set Split level to misc_Max(Partner, Result) */
  clause_SetSplitLevel(Result, clause_SplitLevel(Partner) > clause_SplitLevel(Result)
		       ? clause_SplitLevel(Partner)
		       : clause_SplitLevel(Result));
  clause_UpdateSplitField(Result, Partner);
}

static __inline__ void clause_SetSplitDataFromList(CLAUSE Result, LIST List)
{
  CLAUSE TempClause;
  LIST Scan;
  NAT  l;
  Scan = List;
  l = Result->splitfield_length;
  while (!list_Empty(Scan)) {
    TempClause = (CLAUSE) list_Top(Scan);
    if (clause_GetFlag(TempClause, CONCLAUSE))
      clause_SetFlag(Result, CONCLAUSE);
    clause_SetSplitLevel(Result,
			 clause_SplitLevel(TempClause) > clause_SplitLevel(Result)
			 ? clause_SplitLevel(TempClause)
			 : clause_SplitLevel(Result));
    if (l < TempClause->splitfield_length)
      l = TempClause->splitfield_length;
    Scan = list_Cdr(Scan);
  }
  if (l > Result->splitfield_length) {
    if (Result->splitfield != NULL)
      memory_Free(Result->splitfield,
		  sizeof(SPLITFIELDENTRY) * Result->splitfield_length);
    Result->splitfield = memory_Malloc(sizeof(SPLITFIELDENTRY) * l);
    Result->splitfield_length = l;
  }
  
  for (l=0; l < Result->splitfield_length; l++)
    Result->splitfield[l] = 0;
  
  while (!list_Empty(List)) {
    TempClause= (CLAUSE) list_Top(List);
    List = list_Cdr(List);
    for (l=0; l < TempClause->splitfield_length; l++)
      Result->splitfield[l] = Result->splitfield[l] | TempClause->splitfield[l];
  }
}


static __inline__ void clause_SetSplitDataFromParents(CLAUSE Result,
						      CLAUSE Mother,
						      CLAUSE Father)
{
  NAT i;
  if (clause_GetFlag(Father, CONCLAUSE) || clause_GetFlag(Mother, CONCLAUSE))
    clause_SetFlag(Result, CONCLAUSE);
  if ((clause_SplitLevel(Father) == 0) && (clause_SplitLevel(Mother) == 0))
    return;
  clause_SetSplitLevel(Result, clause_SplitLevel(Mother) > clause_SplitLevel(Father)
		       ? clause_SplitLevel(Mother)
		       : clause_SplitLevel(Father));
  
  if (Mother->splitfield_length > Father->splitfield_length) {
    if (Result->splitfield != NULL)
      memory_Free(Result->splitfield,
		  sizeof(SPLITFIELDENTRY) * Result->splitfield_length);
    Result->splitfield = memory_Malloc(sizeof(SPLITFIELDENTRY) *
				       Mother->splitfield_length);
    Result->splitfield_length = Mother->splitfield_length;
    for (i=0; i < Father->splitfield_length; i++)
      Result->splitfield[i] =
	Mother->splitfield[i] | Father->splitfield[i];
    for (i=Father->splitfield_length; i < Mother->splitfield_length; i++)
      Result->splitfield[i] = Mother->splitfield[i];
  }
  else {
    if (Result->splitfield != NULL)
      memory_Free(Result->splitfield,
		  sizeof(SPLITFIELDENTRY) * Result->splitfield_length);
    Result->splitfield = memory_Malloc(sizeof(SPLITFIELDENTRY) *
				       Father->splitfield_length);
    Result->splitfield_length = Father->splitfield_length;
    for (i=0; i < Mother->splitfield_length; i++)
      Result->splitfield[i] =
	Mother->splitfield[i] | Father->splitfield[i];
    for (i=Mother->splitfield_length; i < Father->splitfield_length; i++)
      Result->splitfield[i] = Father->splitfield[i];
  }
}

static __inline__ void clause_SetParentClauses(CLAUSE Clause, LIST PClauses)
{
  Clause->parentCls = PClauses;
}

static __inline__ void clause_AddParentClause(CLAUSE Clause, int PClause)
{
  Clause->parentCls = list_Cons((POINTER) PClause, Clause->parentCls);
}

static __inline__ void clause_SetParentLiterals(CLAUSE Clause, LIST PLits)
{
  Clause->parentLits = PLits;
}

static __inline__ void clause_AddParentLiteral(CLAUSE Clause, int PLit)
{
  Clause->parentLits = list_Cons((POINTER) PLit, Clause->parentLits);
}


static __inline__ BOOL clause_ValidityIsNotSmaller(CLAUSE C1, CLAUSE C2)
{
  return (C1->validlevel <= C2->validlevel);
}

static __inline__ BOOL clause_IsMoreValid(CLAUSE C1, CLAUSE C2)
{
  return (C1->validlevel < C2->validlevel);
}


static __inline__ BOOL  clause_CompareAbstractLEQ (CLAUSE Left, CLAUSE Right) 
/**************************************************************
  INPUT:   Two clauses.
  RETURNS: TRUE if left <= right, FALSE otherwise.
  EFFECTS: Internal function used to compare clauses for
           sorting.
  CAUTION: Expects clause literal order to be fixed.
***************************************************************/
{
  return (BOOL) (clause_CompareAbstract(Left, Right) <= 0);
}


static __inline__ BOOL clause_IsFromRewriting(CLAUSE Clause)
{
  return Clause->origin == REWRITING;
}

static __inline__ BOOL clause_IsFromCondensing(CLAUSE Clause)
{
  return Clause->origin == CONDENSING;
}

static __inline__ BOOL clause_IsFromObviousReductions(CLAUSE Clause)
{
  return Clause->origin == OBVIOUS_REDUCTIONS;
}

static __inline__ BOOL clause_IsFromSortSimplification(CLAUSE Clause)
{
  return Clause->origin == SORT_SIMPLIFICATION;
}

static __inline__ BOOL clause_IsFromMatchingReplacementResolution(CLAUSE Clause)
{
  return Clause->origin == MATCHING_REPLACEMENT_RESOLUTION;
}

static __inline__  BOOL clause_IsFromClauseDeletion(CLAUSE Clause)
{
  return Clause->origin == CLAUSE_DELETION;
}

static __inline__ BOOL clause_IsFromEmptySort(CLAUSE Clause)
{
  return Clause->origin == EMPTY_SORT;
}

static __inline__ BOOL clause_IsFromSortResolution(CLAUSE Clause)
{
  return Clause->origin == SORT_RESOLUTION;
}

static __inline__ BOOL clause_IsFromUnitConflict(CLAUSE Clause)
{
  return Clause->origin == UNIT_CONFLICT;
}

static __inline__ BOOL clause_IsFromEqualityResolution(CLAUSE Clause)
{
  return Clause->origin == EQUALITY_RESOLUTION;
}

static __inline__ BOOL clause_IsFromEqualityFactoring(CLAUSE Clause)
{
  return Clause->origin == EQUALITY_FACTORING;
}

static __inline__ BOOL clause_IsFromMergingParamodulation(CLAUSE Clause)
{
  return Clause->origin == MERGING_PARAMODULATION;
}

static __inline__ BOOL clause_IsFromSuperpositionRight(CLAUSE Clause)
{
  return Clause->origin == SUPERPOSITION_RIGHT;
}

static __inline__ BOOL clause_IsFromSuperpositionLeft(CLAUSE Clause)
{
  return Clause->origin == SUPERPOSITION_LEFT;
}

static __inline__ BOOL clause_IsFromGeneralResolution(CLAUSE Clause)
{
  return Clause->origin == GENERAL_RESOLUTION;
}

static __inline__ BOOL clause_IsFromGeneralFactoring(CLAUSE Clause)
{
  return Clause->origin == GENERAL_FACTORING;
}

static __inline__ BOOL clause_IsFromSplitting(CLAUSE Clause)
{
  return Clause->origin == SPLITTING;
}

static __inline__ BOOL clause_IsFromDefApplication(CLAUSE Clause)
{
  return Clause->origin == DEFAPPLICATION;
}

static __inline__ BOOL clause_IsFromTerminator(CLAUSE Clause)
{
  return Clause->origin == TERMINATOR;
}

static __inline__ BOOL clause_IsTemporary(CLAUSE Clause)
{
  return Clause->origin == TEMPORARY;
}

static __inline__ BOOL clause_IsFromInput(CLAUSE Clause)
{
  return Clause->origin == INPUT;
}


static __inline__ BOOL clause_HasReducedPredecessor(CLAUSE Clause)
{
  RULE origin = clause_Origin(Clause);

  return (origin == CONDENSING                   ||
	  origin == REWRITING                    ||
	  origin == SPLITTING                    ||
	  origin == ASSIGNMENT_EQUATION_DELETION ||
	  origin == SORT_SIMPLIFICATION          ||
	  origin == OBVIOUS_REDUCTIONS);
}

static __inline__ BOOL clause_IsSplitFather(CLAUSE C1, CLAUSE C2)
{
  return (C1->clausenumber == (int)list_Car(C2->parentCls));
}


static __inline__ void clause_SetFromRewriting(CLAUSE Clause)
{
  Clause->origin = REWRITING;
}

static __inline__ void clause_SetFromContextualRewriting(CLAUSE Clause)
{
  Clause->origin = CONTEXTUAL_REWRITING;
}

static __inline__ void clause_SetFromUnitConflict(CLAUSE Clause)
{
  Clause->origin = UNIT_CONFLICT;
}

static __inline__ void clause_SetFromCondensing(CLAUSE Clause)
{
  Clause->origin = CONDENSING;
}

static __inline__ void clause_SetFromAssignmentEquationDeletion(CLAUSE Clause)
{
  Clause->origin = ASSIGNMENT_EQUATION_DELETION;
}

static __inline__ void clause_SetFromObviousReductions(CLAUSE Clause)
{
  Clause->origin = OBVIOUS_REDUCTIONS;
}

static __inline__ void clause_SetFromSortSimplification(CLAUSE Clause)
{
  Clause->origin = SORT_SIMPLIFICATION;
}

static __inline__ void clause_SetFromMatchingReplacementResolution(CLAUSE Clause)
{
  Clause->origin = MATCHING_REPLACEMENT_RESOLUTION;
}

static __inline__ void clause_SetFromClauseDeletion(CLAUSE Clause)
{
  Clause->origin = CLAUSE_DELETION;
}

static __inline__ void clause_SetFromEmptySort(CLAUSE Clause)
{
  Clause->origin = EMPTY_SORT;
}

static __inline__ void clause_SetFromSortResolution(CLAUSE Clause)
{
  Clause->origin = SORT_RESOLUTION;
}

static __inline__ void clause_SetFromEqualityResolution(CLAUSE Clause)
{
  Clause->origin = EQUALITY_RESOLUTION;
}

static __inline__ void clause_SetFromEqualityFactoring(CLAUSE Clause)
{
  Clause->origin = EQUALITY_FACTORING;
}

static __inline__ void clause_SetFromMergingParamodulation(CLAUSE Clause)
{
  Clause->origin = MERGING_PARAMODULATION;
}

static __inline__ void clause_SetFromParamodulation(CLAUSE Clause)
{
  Clause->origin = PARAMODULATION;
}
static __inline__ void clause_SetFromOrderedParamodulation(CLAUSE Clause)
{
  Clause->origin = ORDERED_PARAMODULATION;
}
static __inline__ void clause_SetFromSuperpositionRight(CLAUSE Clause)
{
  Clause->origin = SUPERPOSITION_RIGHT;
}

static __inline__ void clause_SetFromSuperpositionLeft(CLAUSE Clause)
{
  Clause->origin = SUPERPOSITION_LEFT;
}

static __inline__ void clause_SetFromGeneralResolution(CLAUSE Clause)
{
  Clause->origin = GENERAL_RESOLUTION;
}

static __inline__ void clause_SetFromOrderedHyperResolution(CLAUSE Clause)
{
  Clause->origin = ORDERED_HYPER;
}

static __inline__ void clause_SetFromSimpleHyperResolution(CLAUSE Clause)
{
  Clause->origin = SIMPLE_HYPER;
}

static __inline__ void clause_SetFromURResolution(CLAUSE Clause)
{
  Clause->origin = UR_RESOLUTION;
}

static __inline__ void clause_SetFromGeneralFactoring(CLAUSE Clause)
{
  Clause->origin = GENERAL_FACTORING;
}

static __inline__ void clause_SetFromSplitting(CLAUSE Clause)
{
  Clause->origin = SPLITTING;
}

static __inline__ void clause_SetFromDefApplication(CLAUSE Clause)
{
  Clause->origin = DEFAPPLICATION;
}

static __inline__ void clause_SetFromTerminator(CLAUSE Clause)
{
  Clause->origin = TERMINATOR;
}

static __inline__ void clause_SetTemporary(CLAUSE Clause)
{
  Clause->origin = TEMPORARY;
}


static __inline__ void clause_SetFromInput(CLAUSE Clause)
{
  Clause->origin = INPUT;
}


static __inline__ LITERAL clause_FirstConstraintLit(CLAUSE Clause)
{
  return Clause->literals[0];
}

static __inline__ LITERAL clause_FirstAntecedentLit(CLAUSE Clause)
{
  return Clause->literals[clause_FirstAntecedentLitIndex(Clause)];
}

static __inline__ LITERAL clause_FirstSuccedentLit(CLAUSE Clause)
{
  return Clause->literals[clause_FirstSuccedentLitIndex(Clause)];
}

static __inline__ LITERAL clause_LastConstraintLit(CLAUSE Clause)
{
  return Clause->literals[clause_LastConstraintLitIndex(Clause)];
}

static __inline__ LITERAL clause_LastAntecedentLit(CLAUSE Clause)
{
  return Clause->literals[clause_LastAntecedentLitIndex(Clause)];
}

static __inline__ LITERAL clause_LastSuccedentLit(CLAUSE Clause)
{
  return Clause->literals[clause_LastSuccedentLitIndex(Clause)];
}


static __inline__ BOOL clause_HasEmptyConstraint(CLAUSE Clause)
{
  return clause_NumOfConsLits(Clause) == 0;
}

static __inline__ BOOL clause_HasEmptyAntecedent(CLAUSE Clause)
{
  return clause_NumOfAnteLits(Clause) == 0;
}

static __inline__ BOOL clause_HasEmptySuccedent(CLAUSE Clause)
{
  return clause_NumOfSuccLits(Clause) == 0;
}


static __inline__ BOOL clause_IsGround(CLAUSE Clause)
{
#ifdef CHECK
  if (!symbol_Equal(clause_MaxVar(Clause), clause_SearchMaxVar(Clause))) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In clause_IsGround: Clause is corrupted.");
    misc_FinishErrorReport();
  }
#endif
  return (symbol_VarIndex(clause_MaxVar(Clause)) ==
	  symbol_GetInitialStandardVarCounter());
}

static __inline__ BOOL clause_IsEmptyClause(CLAUSE C)
{
  return (C != (CLAUSE)NULL &&
	  clause_HasEmptyAntecedent(C) &&
	  clause_HasEmptySuccedent(C)  &&
	  clause_HasEmptyConstraint(C));
}

static __inline__ int clause_LiteralGetIndex(LITERAL L)
{
  int j = 0;

  while (clause_GetLiteral(clause_LiteralOwningClause(L), j) != L)
    j++;

  return j;
}

static __inline__ BOOL clause_LiteralIsFromConstraint(LITERAL Literal)
{
  int    index  = clause_LiteralGetIndex(Literal);
  CLAUSE clause = clause_LiteralOwningClause(Literal);

  return (index <= clause_LastConstraintLitIndex(clause) &&
	  index >= clause_FirstConstraintLitIndex(clause));
}

static __inline__ BOOL clause_LiteralIsFromAntecedent(LITERAL Literal)
{
  int    index  = clause_LiteralGetIndex(Literal);
  CLAUSE clause = clause_LiteralOwningClause(Literal);

  return (index <= clause_LastAntecedentLitIndex(clause) &&
	  index >= clause_FirstAntecedentLitIndex(clause));
}

static __inline__ BOOL clause_LiteralIsFromSuccedent(LITERAL Literal)
{
   int    index;
   CLAUSE clause;
   index  = clause_LiteralGetIndex(Literal);
   clause = clause_LiteralOwningClause(Literal);
   return (index <= clause_LastSuccedentLitIndex(clause) &&
	   index >= clause_FirstSuccedentLitIndex(clause));
}

static __inline__ BOOL clause_IsSimpleSortClause(CLAUSE Clause)
{
  return (clause_HasEmptyAntecedent(Clause) &&
	  (clause_NumOfSuccLits(Clause) == 1) &&
	  clause_LiteralIsSort(clause_GetLiteral(Clause,
				clause_NumOfConsLits(Clause))) &&
	  clause_HasSolvedConstraint(Clause));
}

static __inline__ BOOL clause_IsSubsortClause(CLAUSE Clause)
{
  return (clause_IsSimpleSortClause(Clause) &&
	  term_IsVariable(term_FirstArgument(
            clause_LiteralSignedAtom(
	      clause_GetLiteral(Clause, clause_NumOfConsLits(Clause))))));
}


static __inline__ BOOL clause_HasSuccLits(CLAUSE Clause)
{
  return (clause_NumOfSuccLits(Clause) > 1);
}

static __inline__ BOOL clause_HasGroundSuccLit(CLAUSE Clause)
{
  int  i, l;

  l = clause_Length(Clause);
  for (i = clause_FirstSuccedentLitIndex(Clause); i < l; i++)
    if (term_IsGround(Clause->literals[i]->atomWithSign))
      return TRUE;
  
  return FALSE;
}

static __inline__ LITERAL clause_GetGroundSuccLit(CLAUSE Clause)
{
  int  i, l;

  l = clause_Length(Clause);
  for (i = clause_FirstSuccedentLitIndex(Clause); i < l; i++)
    if (term_IsGround(Clause->literals[i]->atomWithSign))
      return Clause->literals[i];

  return (LITERAL)NULL;
}


static __inline__ void clause_Free(CLAUSE Clause)
{
  memory_Free(Clause, sizeof(CLAUSE_NODE));
}


static __inline__ void clause_ReInit(CLAUSE Clause,
				     FLAGSTORE Flags,
				     PRECEDENCE Precedence)
{
  clause_Normalize(Clause);
  clause_SetMaxLitFlags(Clause, Flags, Precedence);
  clause_UpdateWeight(Clause, Flags);
  clause_UpdateMaxVar(Clause);
}

static __inline__ void clause_OrientAndReInit(CLAUSE Clause, FLAGSTORE Flags,
					      PRECEDENCE Precedence)
{
  clause_OrientEqualities(Clause, Flags, Precedence);
  clause_ReInit(Clause, Flags, Precedence);
}

static __inline__ void clause_SetDataFromFather(CLAUSE Result, CLAUSE Father,
						int i, FLAGSTORE Flags,
						PRECEDENCE Precedence)
{
  clause_OrientAndReInit(Result, Flags, Precedence);
  clause_SetSplitDataFromFather(Result, Father);
  clause_SetDepth(Result, clause_Depth(Father) + 1);
  clause_AddParentClause(Result, clause_Number(Father));
  clause_AddParentLiteral(Result, i);
}


static __inline__ void clause_SetDataFromParents(CLAUSE Result, CLAUSE Father,
						 int i, CLAUSE Mother, int j,
						 FLAGSTORE Flags,
						 PRECEDENCE Precedence)
{
  clause_OrientAndReInit(Result, Flags, Precedence);
  clause_SetSplitDataFromParents(Result, Father, Mother);
  clause_SetDepth(Result,
		  misc_Max(clause_Depth(Father), clause_Depth(Mother)) +1);
  clause_AddParentClause(Result, clause_Number(Father));
  clause_AddParentLiteral(Result, i);
  clause_AddParentClause(Result, clause_Number(Mother));
  clause_AddParentLiteral(Result, j);
}


#endif

