/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                     SYMBOLS                            * */
/* *                                                        * */
/* *  $Module:   SYMBOL                                     * */ 
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
/* $Revision: 35442 $                                        * */
/* $State$                                            * */
/* $Date: 2007-03-28 17:24:40 -0700 (Wed, 28 Mar 2007) $                             * */
/* $Author: jeffc $                                       * */
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


#ifndef _SYMBOL_
#define _SYMBOL_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "list.h"
#include "stringsx.h"

/**************************************************************/
/* Data Structures and Constants                              */
/**************************************************************/

/* Critical values: the maximum length of a symbol string and the */
/* maximum number of different variables (in one term, clause)    */
/* CAUTION: symbol__MAXVARIABLES is the overall number of         */
/*          variables + 1 to provide safe allocation of contexts  */
/*          ... because the first var begins with 1 instead of 0. */

#define symbol__SYMBOLMAXLEN   64

#define symbol__NOOFSTANDARDVAR 2000
#define symbol__NOOFINDEXVAR    1000

#define symbol__MAXSTANDARDVAR  symbol__NOOFSTANDARDVAR
#define symbol__MAXINDEXVAR     (symbol__NOOFSTANDARDVAR + symbol__NOOFINDEXVAR)

#define symbol__NOOFVARIABLES (symbol__NOOFSTANDARDVAR + symbol__NOOFINDEXVAR)
#define symbol__MAXVARIABLES  (symbol__NOOFVARIABLES + 1)

/* Symbol Types, Symbols are represented as integers. In case of */
/* constants, functions, predicates, junctors, the two least     */
/* significant bits encode the type. Variables are just          */
/* positive integers, all other symbols negative integers        */
/* The third least significant bit encodes the status of         */
/* function symbols (lexicographic or multiset)                  */

extern const int symbol_MASK;
extern const int symbol_TYPEMASK;
extern const int symbol_STATMASK;
extern const int symbol_TYPESTATMASK;

extern const int symbol_ARBITRARYARITY;

extern const int symbol_TYPEBITS;
extern const int symbol_STATBITS;
extern const int symbol_TYPESTATBITS;

extern const int symbol_SIGTYPES;

#define symbol_CONSTANT  0 
#define symbol_FUNCTION  1
#define symbol_PREDICATE 2
#define symbol_JUNCTOR   3

#define symbol_STATLEX   0 
#define symbol_STATMUL   1

/* For constants, functions, predicates, junctors, is a special */
/* symbol table available, containing the arity, status and the */
/* print name.                                                  */

typedef int SYMBOL;
typedef int *PRECEDENCE;

typedef struct signature {
  char   *name;         /* The name of the symbol as a string */
  NAT    length;        /* The length of the name. Needed for efficient printing */
  int    weight;        /* The weight of the symbol for ordering purposes */
  int    arity;         /* The arity of the symbol */
  NAT    props;         /* Special Properties of the symbol, e.g. AC, Skolem,... */
  SYMBOL info;          /* 2 LSB denote Type and 3rd LSB denotes status */
  LIST   generatedBy;
} SIGNATURE_NODE, *SIGNATURE;

typedef enum {SKOLEM=1,    CUMMUTATIVE=2, ASSOCIATIVE=4, ORDRIGHT=8, ORDMUL=16,
	      DECLSORT=32, DOMPRED=64, ISDEF=128, FREELY=256, GENERATED=512
} SPROPERTY;


#define symbol__MAXSIGNATURE 4000

extern SIGNATURE *symbol_SIGNATURE;

extern SYMBOL symbol_STANDARDVARCOUNTER;
extern SYMBOL symbol_INDEXVARCOUNTER;

extern int symbol_ACTINDEX;
extern int symbol_ACTSKOLEMFINDEX;
extern int symbol_ACTSKOLEMCINDEX;
extern int symbol_ACTSKOLEMPINDEX;
extern int symbol_ACTSKOLEMAINDEX;

/* For matching of signature symbols */
extern SYMBOL symbol_CONTEXT[symbol__MAXSIGNATURE];


/**************************************************************/
/* Specials                                                   */
/**************************************************************/

NAT             symbol_MaxStringLength(void);

void            symbol_ReinitGenericNameCounters(void);

int             symbol_GetIncreasedOrderingCounter(void);

void            symbol_Delete(SYMBOL);
BOOL            symbol_IsSymbol(SYMBOL);
void            symbol_Dump(PRECEDENCE);

LIST            symbol_SortByPrecedence(LIST, PRECEDENCE);
void            symbol_RearrangePrecedence(PRECEDENCE, LIST);

void            symbol_LowerSignature(void);

LIST            symbol_GetAllSymbols(void);
LIST            symbol_GetAllPredicates(void);
LIST            symbol_GetAllFunctions(void);

void            symbol_SetCount(SYMBOL, unsigned long);
unsigned long   symbol_GetCount(SYMBOL);
/**************************************************************/
/* Symbol Comparisons                                         */
/**************************************************************/

static __inline__ BOOL symbol_Equal(SYMBOL A, SYMBOL B)
{
  return A==B;
}

static __inline__ BOOL symbol_IsSignature(SYMBOL S)
{
  return S < 0;
}

static __inline__ void symbol_CheckNoVariable(SYMBOL S)
{
#ifdef CHECK
  if (!symbol_IsSignature(S)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In symbol_CheckNoVariable: illegal input\n");
    misc_FinishErrorReport();
  }
#endif
}

static __inline__ int symbol_Type(SYMBOL ActSymbol)
{
  symbol_CheckNoVariable(ActSymbol);
  return (-ActSymbol) & symbol_TYPEMASK;
}

static __inline__ BOOL symbol_IsJunctor(SYMBOL S)
{
  return (symbol_IsSignature(S) && symbol_Type(S) == symbol_JUNCTOR);
}

static __inline__ BOOL symbol_IsFunction(SYMBOL S)
{
  return (symbol_IsSignature(S) &&
	  (symbol_Type(S) == symbol_FUNCTION ||
	   symbol_Type(S) == symbol_CONSTANT));
}

static __inline__ BOOL symbol_IsConstant(SYMBOL S)
{
  return (symbol_IsSignature(S) && symbol_Type(S) == symbol_CONSTANT);
}

static __inline__ BOOL symbol_IsPredicate(SYMBOL S)
{
  return (symbol_IsSignature(S) && symbol_Type(S) == symbol_PREDICATE);
}

static __inline__ BOOL symbol_IsVariable(SYMBOL S)
{
  return S > 0;
}

static __inline__ BOOL symbol_IsStandardVariable(SYMBOL S)
{
  return symbol_IsVariable(S) && (S <= symbol__MAXSTANDARDVAR);
}

static __inline__ BOOL symbol_IsIndexVariable(SYMBOL S)
{
  return (S > symbol__MAXSTANDARDVAR) && (S <= symbol__MAXINDEXVAR);
}

static __inline__ BOOL symbol_IsComplex(SYMBOL S)
{
  return (!symbol_IsVariable(S) && !symbol_IsConstant(S));
}

static __inline__ BOOL symbol_IsSuccessor(SYMBOL S, SYMBOL P)
{
  return S > P;
}


/**************************************************************/
/* Symbol Manipulation                                        */
/**************************************************************/

static __inline__ int symbol_GetInitialStandardVarCounter(void)
{
  return 0;
}

static __inline__ int symbol_GetInitialIndexVarCounter(void)
{
  return symbol__MAXSTANDARDVAR;
}

static __inline__ int symbol_FirstIndexVariable(void)
{
  return symbol__MAXSTANDARDVAR + 1;
}

static __inline__ int symbol_LastIndexVariable(void)
{
  return symbol_INDEXVARCOUNTER;
}

/* Special predefined symbols            */

#define symbol__NULL 0

static __inline__ int symbol_MaxVars(void)
{
  return symbol__MAXVARIABLES;
}

static __inline__ int symbol_MaxConsts(void)
{
  return symbol__MAXSIGNATURE;
}

static __inline__ int symbol_MaxBaseSorts(void)
{
  return symbol__MAXSIGNATURE;
}

static __inline__ int symbol_TypeBits(void)
{
  return symbol_TYPEBITS;
}

static __inline__ int symbol_Null(void)
{
  return 0;
}

static __inline__ int symbol_ActIndex(void)
{
  return symbol_ACTINDEX;
}

static __inline__ void symbol_ResetSkolemIndex(void)
{
  symbol_ACTSKOLEMFINDEX = 0;
  symbol_ACTSKOLEMCINDEX = 0;
  symbol_ACTSKOLEMPINDEX = 0;
  symbol_ACTSKOLEMAINDEX = 0;
}


/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  MEMORY MANAGEMENT                                     * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/

static __inline__ void symbol_FreeSignature(SIGNATURE Sig)
/***************************************************************
  INPUT:   A signature datum.
  RETURNS: void
  EFFECTS: The datum is deleted and its memory freed.
****************************************************************/
{
  memory_Free(Sig->name, symbol__SYMBOLMAXLEN);
  list_Delete(Sig->generatedBy);
  memory_Free(Sig, sizeof(SIGNATURE_NODE));
}

static __inline__ SIGNATURE symbol_GetSignature(void)
{
  return (SIGNATURE) memory_Malloc(sizeof(SIGNATURE_NODE));
} 


/**************************************************************/
/* Symbol Creation                                            */
/**************************************************************/

static __inline__ SYMBOL symbol_CreateStandardVariable(void)
/***************************************************************
  INPUT:   None
  RETURNS: A new symbol for a new standard variable numbered according to
           symbol_STANDARDVARCOUNTER
  SUMMARY: Creates a new standard variable symbol.
  EFFECTS: None
****************************************************************/
{
#ifdef CHECK
  if (symbol_STANDARDVARCOUNTER >= symbol__MAXSTANDARDVAR) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In symbol_CreateStandardVariable: Number of standard variables exceeded.\n");
    misc_FinishErrorReport();
   }
#endif

  return (++symbol_STANDARDVARCOUNTER);
}


static __inline__ SYMBOL symbol_CreateIndexVariable(void)
/***************************************************************
  INPUT:   None
  RETURNS: A new symbol for a new index variable numbered according to
           symbol_INDEXVARCOUNTER
  SUMMARY: Creates a new index variable symbol.
  EFFECTS: None
****************************************************************/
{
#ifdef CHECK
  if (symbol_INDEXVARCOUNTER >= symbol__MAXINDEXVAR) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In symbol_CreateIndexVariable: Number of index variables exceeded.\n");
    misc_FinishErrorReport();
  }
#endif

  return (++symbol_INDEXVARCOUNTER);
}


static __inline__ SYMBOL symbol_NextIndexVariable(SYMBOL Variable)
{
#ifdef CHECK
  if ((Variable != symbol_GetInitialIndexVarCounter() &&
       !symbol_IsIndexVariable(Variable)) ||
      Variable == symbol__MAXINDEXVAR) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In symbol_NextVariable: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  return (Variable + 1);
}


static __inline__ void symbol_SetStandardVarCounter(SYMBOL Variable)
{
#ifdef CHECK
  if (Variable != symbol_GetInitialStandardVarCounter() &&
      !symbol_IsStandardVariable(Variable)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In symbol_SetStandardVarCounter: Illegal input.\n");
    misc_FinishErrorReport();
  } 
  else 
    if (Variable >= symbol__MAXSTANDARDVAR) {
      misc_StartErrorReport();
      misc_ErrorReport("\n In symbol_SetStandardVarCounter: Number of standard variables exceeded.\n");
      misc_FinishErrorReport();
    }
#endif

  symbol_STANDARDVARCOUNTER = Variable;
}

static __inline__ SYMBOL symbol_FirstVariable(void)
{
  return 1;
}

static __inline__ BOOL symbol_GreaterVariable(SYMBOL Var1, SYMBOL Var2)
{
  return Var1 > Var2;
}

static __inline__ void symbol_ResetStandardVarCounter(void)
{
  symbol_STANDARDVARCOUNTER = symbol_GetInitialStandardVarCounter();
}

void   symbol_Init(BOOL);
BOOL   symbol_SignatureExists(void);
void   symbol_FreeAllSymbols(void);
SYMBOL symbol_CreateFunction(const char*, int, int, PRECEDENCE);
SYMBOL symbol_CreateSkolemFunction(int, PRECEDENCE);
SYMBOL symbol_CreateSkolemPredicate(int, PRECEDENCE);
SYMBOL symbol_CreatePredicate(const char*, int, int, PRECEDENCE);
SYMBOL symbol_CreateJunctor(const char*, int, int, PRECEDENCE);

/**************************************************************/
/* Symbol Access                                              */
/**************************************************************/

SYMBOL symbol_Lookup(const char*);

static __inline__ int symbol_VarIndex(SYMBOL ActSymbol)
{
  return ActSymbol;
}

static __inline__ int symbol_NormVar(SYMBOL ActSymbol)
{
  /* Normalization of variables s.t. the index of the variable
     is normalized starting always with 1:
     Standard variables are already normalized.
     Index variables are decreased by the number of the
     underlying standard variables. */
  return (ActSymbol <= symbol__MAXSTANDARDVAR) ? ActSymbol : (ActSymbol - symbol__MAXSTANDARDVAR);
}

/* The name, index and arity macros are only defined for signature   */
/* elements not for variables. The type of the symbol is not checked */
/* by the macros.                                                    */

static __inline__ int symbol_Index(SYMBOL ActSymbol)
{
  symbol_CheckNoVariable(ActSymbol);
  return (-ActSymbol) >> symbol_TYPESTATBITS;
}

static __inline__ void symbol_CheckIndexInRange(int Index)
{
#ifdef CHECK
  if (Index < 0 || Index >= symbol__MAXSIGNATURE) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In symbol_CheckIndexInRange: Symbol index is out of range.\n");
    misc_FinishErrorReport();
  }
#endif
}

static __inline__ SYMBOL symbol_SignatureSymbol(int ActIndex, int Type, int Status)
{
  return -((ActIndex << symbol_TYPESTATBITS)
	   | (Status << symbol_TYPEBITS)
	   | Type);
}

static __inline__ SIGNATURE symbol_Signature(int Index)
  /* Returns the signature of the symbol with <Index> or NULL */
  /* if the symbol was deleted */
{
  symbol_CheckIndexInRange(Index);
  return symbol_SIGNATURE[Index];
}

static __inline__ void symbol_SetSignature(int ActIndex, SIGNATURE Sig)
{
  symbol_CheckIndexInRange(ActIndex);
  symbol_SIGNATURE[ActIndex] = Sig;
}

static __inline__ SYMBOL symbol_GetSigSymbol(int Index)
{
  return symbol_Signature(Index)->info;
}

static __inline__ int symbol_Stat(SYMBOL ActSymbol)
{
  symbol_CheckNoVariable(ActSymbol);
  return ((-ActSymbol) & symbol_STATMASK) >> symbol_TYPEBITS;
}

static __inline__ SYMBOL symbol_ChangeType(SYMBOL S, int Type)
/**************************************************************
  INPUT:   A symbol and a new type for that symbols.
  RETURNS: A new symbol that is the old symbol with type changed to <Type>,
           therefore the return value is different from <S>.
  EFFECT:  Uses the signature memory of the input symbol.
  CAUTION: Usage only allowed by the parsing modules!!!
***************************************************************/
{
  SIGNATURE Sig;
  symbol_CheckNoVariable(S);
  Sig = symbol_Signature(symbol_Index(S));
  S   = symbol_SignatureSymbol(symbol_Index(S), Type, symbol_Stat(S));
  Sig->info = S;
  return S;
}

static __inline__ int symbol_Arity(SYMBOL ActSymbol)
{
  return symbol_Signature(symbol_Index(ActSymbol))->arity;
}

static __inline__ NAT symbol_PositiveArity(SYMBOL ActSymbol)
{
  int arity = symbol_Arity(ActSymbol);
  if (arity < 0)
    return NAT_MAX;
  else
    return arity;
}

static __inline__ void symbol_SetArity(SYMBOL ActSymbol, int Arity)
{
  symbol_Signature(symbol_Index(ActSymbol))->arity = Arity;
}
  
static __inline__ int symbol_ArbitraryArity(void)
{
  return -1;
}

static __inline__ char* symbol_Name(SYMBOL ActSymbol)
{
  return symbol_Signature(symbol_Index(ActSymbol))->name;
}

static __inline__ NAT symbol_NameLength(SYMBOL ActSymbol)
{
  return symbol_Signature(symbol_Index(ActSymbol))->length;
}

static __inline__ int symbol_Info(SYMBOL ActSymbol)
{
  return symbol_Signature(symbol_Index(ActSymbol))->info;
}

static __inline__ int symbol_Weight(SYMBOL ActSymbol)
{
  return symbol_Signature(symbol_Index(ActSymbol))->weight;
}

static __inline__ int symbol_Ordering(PRECEDENCE P, SYMBOL ActSymbol)
{
  int Index;
  
  Index = symbol_Index(ActSymbol);
#ifdef CHECK
  symbol_CheckIndexInRange(Index);
  if (P[Index] < 0) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In symbol_Ordering: Ordering of symbol %s is invalid\n",
		     symbol_Name(ActSymbol));
    misc_FinishErrorReport();
  }
#endif
  return P[Index];
}

static __inline__ void symbol_SetWeight(SYMBOL ActSymbol, int Weight)
{
  symbol_Signature(symbol_Index(ActSymbol))->weight = Weight;
}

static __inline__ void symbol_SetName(SYMBOL ActSymbol, char* Name)
{
  symbol_Signature(symbol_Index(ActSymbol))->name = Name;
}

static __inline__ LIST symbol_GeneratedBy(SYMBOL S)
{
  return symbol_Signature(symbol_Index(S))->generatedBy;
}

static __inline__ BOOL symbol_IsGeneratedBy(SYMBOL S1, SYMBOL S2)
{
  return list_PointerMember(symbol_GeneratedBy(S1), (POINTER)S2);
}

static __inline__ void symbol_SetGeneratedBy(SYMBOL S, LIST SymbolList)
{
  symbol_Signature(symbol_Index(S))->generatedBy = SymbolList;
}

static __inline__ void symbol_SetOrdering(PRECEDENCE P, SYMBOL ActSymbol,
					  int Ordering)
{
  int Index;

  Index = symbol_Index(ActSymbol);
  symbol_CheckIndexInRange(Index);
  P[Index] = Ordering;
}

static __inline__ void symbol_SetIncreasedOrdering(PRECEDENCE P, SYMBOL S)
{
  symbol_SetOrdering(P, S, symbol_GetIncreasedOrderingCounter());
}


static __inline__ BOOL symbol_PrecedenceGreater(PRECEDENCE P, SYMBOL S1, SYMBOL S2)
{
  return symbol_Ordering(P, S1) < symbol_Ordering(P, S2);
}

static __inline__ BOOL symbol_HasProperty(SYMBOL ActSymbol, SPROPERTY Property)
{
  return (symbol_Signature(symbol_Index(ActSymbol))->props & Property);
}

static __inline__ void symbol_AddProperty(SYMBOL ActSymbol, SPROPERTY Property)
{
  SIGNATURE S = symbol_Signature(symbol_Index(ActSymbol));
  S->props    = S->props | Property;
}

static __inline__ void symbol_RemoveProperty(SYMBOL ActSymbol, SPROPERTY Property)
{
  SIGNATURE S = symbol_Signature(symbol_Index(ActSymbol));
  if (S->props & Property)
    S->props = S->props - Property;
}

static __inline__ BOOL symbol_IsBaseSort(SYMBOL Symbol)
{
  return (symbol_Arity(Symbol) == 1);
}

static __inline__ void symbol_ClearPrecedence(PRECEDENCE P)
{
  int i;
  const int clear = -42; /* Some negative number */

  for (i = 0; i < symbol__MAXSIGNATURE; i++)
    P[i] = clear;        
}

static __inline__ PRECEDENCE symbol_CreatePrecedence(void)
{
  PRECEDENCE P;

  P = memory_Malloc(sizeof(int[symbol__MAXSIGNATURE]));
  symbol_ClearPrecedence(P);
  return P;
}

static __inline__ void symbol_DeletePrecedence(PRECEDENCE P)
{
  memory_Free(P, sizeof(int[symbol__MAXSIGNATURE]));
}

static __inline__ void symbol_TransferPrecedence(PRECEDENCE Source,
						 PRECEDENCE Target)
  /* Copy settings from one precedence object to another */
{
  int i;

  for (i = 0; i < symbol__MAXSIGNATURE; i++)
    Target[i] = Source[i];
}

static __inline__ LIST symbol_DeleteSymbolFromList(LIST Symbols, SYMBOL S)
  /* Deletes all occurrences of <S> from the list */
{
  return list_DeleteElement(Symbols, (POINTER) S, 
			    (BOOL (*)(POINTER, POINTER)) symbol_Equal);
}

static __inline__ void symbol_DeleteSymbolList(LIST Symbols)
  /* The list AND the symbols within are deleted */
{
  list_DeleteWithElement(Symbols, (void (*)(POINTER))symbol_Delete);
}

/**************************************************************/
/* Symbol CONTEXT                                             */
/**************************************************************/

static __inline__ BOOL symbol_ContextIsClean(void)
{
  int i;
  for (i = 0; i < symbol__MAXSIGNATURE; i++)
    if (symbol_CONTEXT[i] != (SYMBOL)0)
      return FALSE;
  return TRUE;
}

static __inline__ void symbol_ContextClean(void)
{
  int i;
  for (i = 0; i < symbol__MAXSIGNATURE; i++)
    symbol_CONTEXT[i] = (SYMBOL)0;
}

static __inline__ BOOL symbol_ContextIsMapped(SYMBOL Symbol)
{
  int i;
  for (i = 0; i < symbol__MAXSIGNATURE; i++)
    if (symbol_Equal(symbol_CONTEXT[i],Symbol))
      return TRUE;
  return FALSE;
}

static __inline__ SYMBOL symbol_ContextGetValue(SYMBOL Symbol)
{
  int Index;

  Index = symbol_Index(Symbol);
  symbol_CheckIndexInRange(Index);
  return symbol_CONTEXT[Index];
}

static __inline__ void symbol_ContextSetValue(SYMBOL Symbol, SYMBOL Value)
{
  int Index;

  Index = symbol_Index(Symbol);
  symbol_CheckIndexInRange(Index);
  symbol_CONTEXT[Index] = Value;
}

static __inline__ void symbol_ContextClearValue(SYMBOL Symbol)
{
  symbol_ContextSetValue(Symbol, (SYMBOL)0);
}

static __inline__ BOOL symbol_ContextIsBound(SYMBOL Symbol)
{
  return (symbol_ContextGetValue(Symbol) != (SYMBOL)0);
}

/**************************************************************/
/* Symbol Output                                              */
/**************************************************************/

void   symbol_Print(SYMBOL);
void   symbol_PrintPrecedence(PRECEDENCE);
void   symbol_FPrintPrecedence(FILE*, PRECEDENCE);
void   symbol_FPrint(FILE*, SYMBOL);
void   symbol_FPrintOtter(FILE*, SYMBOL);
void   symbol_PrintLn(SYMBOL);
void   symbol_PrintAll(void);

#endif
