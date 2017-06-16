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


#ifndef _TERM_
#define _TERM_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "symbol.h"
#include "stack.h"

/**************************************************************/
/* Structures                                                 */
/**************************************************************/

/* In CHECK mode you can block the stamp for all terms,
   so no other function can use the macro term_IncStamp(),
   which must be used for initialization at the beginning
   of a new traversal */

typedef struct term {
  SYMBOL symbol;
  union {
    LIST termlist;
    struct term* term;
  } super;
  LIST   args;
  NAT    stamp;
  NAT    size;
} *TERM, TERM_NODE;


/* Data Structures and Macros for Marking of variables, used in */
/* all functions extracting variables from terms.               */

extern NAT      term_MARK;
extern POINTER  term_BIND[symbol__MAXVARIABLES][2];

#ifdef CHECK
extern BOOL term_BINDPHASE;
static  __inline__ void term_StartBinding(void)   { term_BINDPHASE=TRUE; }
static  __inline__ void term_StopBinding(void)    { term_BINDPHASE=FALSE; }
static  __inline__ BOOL term_InBindingPhase(void) { return term_BINDPHASE; }
#else
static  __inline__ void term_StartBinding(void)   { }
static  __inline__ void term_StopBinding(void)    { }
#endif

static __inline__ NAT term_NullMark(void)
{
  return 0;
}


static __inline__ NAT term_BindingMark(SYMBOL Var)
{
  return (NAT) term_BIND[symbol_VarIndex(Var)][0];
}


static __inline__ void term_SetBindingMark(SYMBOL Var, NAT Mark)
{
  term_BIND[symbol_VarIndex(Var)][0] = (POINTER) Mark;
}


static __inline__ POINTER term_BindingValue(SYMBOL Var)
{
  return term_BIND[symbol_VarIndex(Var)][1];
}


static __inline__ void term_SetBindingValue(SYMBOL Var, POINTER Value)
{
  term_BIND[symbol_VarIndex(Var)][1] = Value;
}

static __inline__ void term_CreateBinding(SYMBOL Var, NAT Mark)
{
  term_SetBindingMark(Var, Mark);
}

static __inline__ void term_ClearBinding(SYMBOL Var)
{
  term_SetBindingMark(Var, term_NullMark());
}

static __inline__ void term_CreateValueBinding(SYMBOL Var, NAT Mark, POINTER Value)
{
  term_SetBindingMark(Var, Mark);
  term_SetBindingValue(Var, Value);
}


static __inline__ BOOL term_VarIsMarked(SYMBOL Var, NAT Mark)
{
  return term_BindingMark(Var) >= Mark;
}


static __inline__ NAT term_ActMark(void)
{
  NAT MarkVar;
  if (term_MARK == NAT_MAX) {
    int i;
    for (i = 0; i < symbol_MaxVars(); i++)
      term_BIND[i][0] = (POINTER) term_NullMark();
    term_MARK = 1;
  }
  MarkVar = term_MARK++;
  return MarkVar;
}


static __inline__ void term_NewMark(void)
{
  if (term_MARK == NAT_MAX) {
    int i;
    for (i = 0; i < symbol_MaxVars(); i++)
      term_BIND[i][0] = (POINTER) term_NullMark();
    term_MARK = 1;
  }
  term_MARK++;
}


static __inline__ NAT term_OldMark(void)
{
  return term_MARK - 1;
}


/**************************************************************/
/* Macros                                                     */
/**************************************************************/

static __inline__ TERM term_Null(void)
{
 return (TERM)NULL;
}

static __inline__ SYMBOL term_TopSymbol(TERM T)
{
  return T->symbol;
}


static __inline__ void term_RplacTop(TERM T, SYMBOL S)
{
  T->symbol = S;
}


static __inline__ LIST term_SupertermList(TERM T)
{
  return T->super.termlist;
}


static __inline__ void term_RplacSupertermList(TERM T, LIST L)
{
  T->super.termlist = L;
}


static __inline__ LIST term_AtomsLiterals(TERM T)
{
  return T->super.termlist;
}


static __inline__ TERM term_Superterm(TERM T)
{
  return T->super.term;
}


static __inline__ void term_RplacSuperterm(TERM T1, TERM T2)
{
  T1->super.term = T2;
}


static __inline__ BOOL term_IsVariable(TERM T)
{
  return symbol_IsVariable(term_TopSymbol(T));
}


static __inline__ BOOL term_IsStandardVariable(TERM T)
{
  return symbol_IsStandardVariable(term_TopSymbol(T));
}


static __inline__ BOOL term_IsIndexVariable(TERM T)
{
  return symbol_IsIndexVariable(term_TopSymbol(T));
}


static __inline__ LIST term_ArgumentList(TERM T)
{
  return T->args;
}


static __inline__ void term_RplacArgumentList(TERM T, LIST A)
{
  T->args = A;
}


static __inline__ BOOL term_IsComplex(TERM T)
{
  return term_ArgumentList(T) != NULL;
}


static __inline__ BOOL term_IsConstant(TERM T)
{
  return !term_IsComplex(T) && !term_IsVariable(T);
}


static __inline__ BOOL term_IsAtom(TERM T)
{
  return symbol_IsPredicate(term_TopSymbol(T));
}

static __inline__ BOOL term_IsDeclaration(TERM Term)
/**************************************************************
  INPUT:   A term.
  RETURNS: TRUE, if the term is a monadic atom, FALSE otherwise.
***************************************************************/
{
  return (term_IsAtom(Term) && symbol_IsBaseSort(term_TopSymbol(Term)));
}


static __inline__ TERM term_FirstArgument(TERM T)
{
  return (TERM) list_First(T->args);
}


static __inline__ void term_RplacFirstArgument(TERM T1, TERM T2)
{
  list_Rplaca(T1->args, T2);
}


static __inline__ TERM term_SecondArgument(TERM T)
{
  return (TERM) list_Second(T->args);
}


static __inline__ void term_RplacSecondArgument(TERM T1, TERM T2)
{
  list_RplacSecond(T1->args, T2);
}


static __inline__ void term_Free(TERM T)
{
  memory_Free((char*) T, sizeof(TERM_NODE));
}


static __inline__ BOOL term_EqualTopSymbols(TERM T, TERM S)
{
  return symbol_Equal(term_TopSymbol(T), term_TopSymbol(S));
}


static __inline__ void term_EqualitySwap(TERM T)
{
  TERM Aux;
  Aux = term_FirstArgument(T);
  list_Rplaca(term_ArgumentList(T), (POINTER) term_SecondArgument(T));
  list_Rplaca(list_Cdr(term_ArgumentList(T)), (POINTER) Aux);
}


/**************************************************************/
/* Macros and Variables for the term's stamp                  */
/**************************************************************/

/* Maximum number of modules that use the term module's stamp */
#define term_MAXSTAMPUSERS  20

extern NAT  term_STAMP;
extern BOOL term_STAMPBLOCKED;

static __inline__ NAT term_Stamp(void)
{
  return term_STAMP;
}

static __inline__ BOOL term_StampBlocked(void)
{
  return term_STAMPBLOCKED;
}


#ifdef CHECK

/* In CHECK mode 'term_StartStamp' is a real function defined in    */
/* 'term.c'.                                                        */

static __inline__ void term_StopStamp(void)
{
  term_STAMPBLOCKED = FALSE;
}

#else

/* Attention:                                                       */
/* You should check for Overflow before calling this function !!!!! */
/* Use "term_StampOverflow" to do this.                             */
/* If an overflow occurred, you have to reset the stamp of all terms */
/* you're using.                                                    */
static __inline__ void term_StartStamp(void)
{
  term_STAMP++;
}

static __inline__ void term_StopStamp(void)
{ }

#endif


static __inline__ NAT term_TermStamp(TERM T)
{
  return T->stamp;
}

static __inline__ void term_SetTermStamp(TERM T)
{
  T->stamp = term_STAMP;
}

static __inline__ NAT term_Size(TERM T)
{
  return T->size;
}

static __inline__ void term_SetSize(TERM T, NAT s)
{
  T->size = s;
}

static __inline__ BOOL term_AlreadyVisited(TERM T)
{
  return T->stamp == term_STAMP;
}

static __inline__ BOOL term_HasTermStamp(TERM T)
{
  return T->stamp == term_STAMP;
}

static __inline__ void  term_ResetTermStamp(TERM T)
{
  T->stamp = 0;
}

static __inline__ BOOL term_StampAlreadyReset(TERM T)
{
  return T->stamp == 0;
}


/**************************************************************/
/* Functions on Term Creation And Deletion                    */
/**************************************************************/

void  term_Init(void);

TERM  term_Create(SYMBOL, LIST);
TERM  term_CreateAddFather(SYMBOL, LIST);
TERM  term_CreateStandardVariable(void);
void  term_Delete(TERM);
void  term_DeleteIterative(TERM);

/**************************************************************/
/* Term Comparisons                                           */
/**************************************************************/

BOOL  term_Equal(TERM, TERM);
BOOL  term_EqualIterative(TERM, TERM);               /* Unused */
BOOL  term_VariableEqual(TERM, TERM);
BOOL  term_IsGround(TERM);
BOOL  term_IsTerm(TERM);
BOOL  term_IsTermList(LIST);
BOOL  term_AllArgsAreVar(TERM);
int   term_CompareBySymbolOccurences(TERM, TERM);
int   term_CompareAbstract(TERM, TERM);
BOOL  term_CompareAbstractLEQ(TERM, TERM);


/**************************************************************/
/* Low Level Term Functions                                   */
/**************************************************************/

TERM  term_Copy(TERM);
TERM  term_CopyIterative(TERM);                     /* Unused */
TERM  term_CopyWithEmptyArgListNode(TERM, LIST, LIST*);
void  term_PrintWithEmptyArgListNode(TERM);
BOOL  term_ReplaceSubtermBy(TERM, TERM, TERM);
void  term_ReplaceVariable(TERM, SYMBOL, TERM);
void  term_ExchangeVariable(TERM, SYMBOL, SYMBOL);
BOOL  term_SubstituteVariable(SYMBOL, TERM, TERM*);
NAT   term_ComputeSize(TERM);
void  term_InstallSize(TERM);
NAT   term_Depth(TERM);
BOOL  term_ContainsSymbol(TERM, SYMBOL);
BOOL  term_Sharing(TERM);
void  term_AddFatherLinks(TERM);
BOOL  term_FatherLinksEstablished(TERM);
TERM  term_TopLevelTerm(TERM);
BOOL  term_HasPointerSubterm(TERM, TERM);
BOOL  term_HasSubterm(TERM, TERM);
BOOL  term_HasProperSuperterm(TERM, TERM);
TERM  term_FindSubterm(TERM, SYMBOL);
LIST  term_FindAllAtoms(TERM, SYMBOL);
BOOL  term_CheckTerm(TERM);
NAT   term_RootDistance(TERM);
BOOL  term_RootDistanceSmaller(TERM,TERM);

static __inline__ LIST term_CopyTermList(LIST List)
/**************************************************************
  INPUT:   A list of TERMs.
  RETURNS: A deep copy of the list, i.e. the terms are copied, too.
***************************************************************/
{
  return list_CopyWithElement(List, (POINTER (*)(POINTER))term_Copy);
}

static __inline__ void term_CopyTermsInList(LIST List)
/**************************************************************
  INPUT:   A list of TERMs.
  EFFECT:  Replaces every term in the list with its copy. 
***************************************************************/
{
  list_NMapCar(List, (POINTER (*)(POINTER)) term_Copy);
}

static __inline__ void term_DeleteTermList(LIST List)
/**************************************************************
  INPUT:   A list of TERMs.
  RETURNS: Nothing.
  EFFECT:  The list is freed together with its elements.
***************************************************************/
{
  list_DeleteWithElement(List, (void (*)(POINTER))term_Delete);
}

static __inline__ BOOL term_ListContainsTerm(LIST List, TERM Term)
/**************************************************************
  INPUT:   A list of TERMs.
  RETURNS: TRUE, if <List> contains <Term>, FALSE otherwise.
           Terms are compared with respect to the term_Equal function.
***************************************************************/
{
  return list_Member(List, Term, (BOOL (*)(POINTER,POINTER))term_Equal);
}

static __inline__ LIST term_DeleteDuplicatesFromList(LIST List)
/**************************************************************
  INPUT:   A list of TERMs.
  RETURNS: The list where duplicate terms are removed.
  EFFECT:  Terms are compared with respect to the term_Equal function.
           The duplicate terms are not deleted.
***************************************************************/
{
  return list_DeleteDuplicates(List, (BOOL (*)(POINTER, POINTER))term_Equal);
}


static __inline__ LIST term_DestroyDuplicatesInList(LIST Terms)
/**************************************************************
  INPUT:   A list of terms.
  RETURNS: The list where all duplicate terms are removed.
  EFFECTS: The terms are compared with respect to the term_Equal function.
           The duplicate terms are deleted, too.
***************************************************************/
{
  return list_DeleteDuplicatesFree(Terms, (BOOL (*)(POINTER,POINTER))term_Equal,
				   (void (*)(POINTER))term_Delete);
}



/**************************************************************/
/* Term Input and Output Functions                            */
/**************************************************************/

void   term_Print(TERM);
void   term_PrettyPrint(TERM);
void   term_FPrint(FILE*, TERM);
void   term_TermListPrint(LIST);
void   term_TermListFPrint(FILE*, LIST);


void   term_PrintPrefix(TERM);
void   term_FPrintPrefix(FILE*, TERM);
void   term_TermListPrintPrefix(LIST);
void   term_TermListFPrintPrefix(FILE*, LIST);

void   term_FPrintOtterPrefix(FILE*, TERM);
void   term_TermListFPrintOtterPrefix(FILE*, LIST);

void   term_FPrintPosition(FILE*,TERM,TERM);

static __inline__ void term_PrintPosition(TERM TopTerm, TERM Subterm)
{
  term_FPrintPosition(stdout, TopTerm, Subterm);
}

/**************************************************************/
/* High Level Term Functions                                  */
/**************************************************************/

void   term_ToCoVariables(TERM);
NAT    term_Bytes(TERM);

void   term_MarkVariables(TERM, NAT);
void   term_CountSymbols(TERM);
LIST   term_ListOfVariables(TERM);
LIST   term_VariableSymbols(TERM);
LIST   term_ListOfAtoms(TERM,SYMBOL);
LIST   term_ListOfConstants(TERM);
LIST   term_ListOfFunctions(TERM);
NAT    term_NumberOfVarOccs(TERM);
NAT    term_NumberOfSymbolOccurrences(TERM, SYMBOL);
BOOL   term_ContainsFunctions(TERM);
BOOL   term_ContainsVariable(TERM,SYMBOL);
SYMBOL term_MaxVar(TERM);

void   term_StartMinRenaming(void);
void   term_StartMaxRenaming(SYMBOL);
TERM   term_Rename(TERM);
SYMBOL term_GetRenamedVarSymbol(SYMBOL);

LIST   term_RenamePseudoLinear(TERM, SYMBOL);

/**************************************************************/
/* Stamp Functions                                            */
/**************************************************************/

/* Currently only in CHECK mode */
#ifdef CHECK
void   term_StartStamp(void);
#endif

void   term_SetTermSubtermStamp(TERM T);

NAT    term_GetStampID(void);
BOOL   term_StampOverflow(NAT);


#endif
