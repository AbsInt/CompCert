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


#define SHOWBINDINGS 0

#ifndef _CONTEXT_
#define _CONTEXT_


/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "term.h"
#include "symbol.h"
#include "list.h"

/**************************************************************/
/* Structures                                                 */
/**************************************************************/

/* Set 'SHOWBINDINGS' to non-zero value to enable debug output. */
/* #define SHOWBINDINGS 1 */

#define cont__SIZE symbol__MAXVARIABLES

extern int  cont_NOOFCONTEXTS;
extern LIST cont_LISTOFCONTEXTS;
extern int  cont_BINDINGS;

/* An array to remember bindings for the variables. The array     */
/* is indexed by the variable index and holds the binding term.   */

typedef struct binding {
  SYMBOL         symbol;
  SYMBOL         renaming;
  TERM           term;
  struct binding *context;
  struct binding *link;
} *CONTEXT, CONTEXT_NODE;

extern CONTEXT cont_LASTBINDING;     /* The last binding made. */
extern CONTEXT cont_CURRENTBINDING;  /* Help variable. */

extern SYMBOL cont_INDEXVARSCANNER;

/* Two contexts are allocated by default */

extern CONTEXT cont_LEFTCONTEXT;
extern CONTEXT cont_RIGHTCONTEXT;
extern CONTEXT cont_INSTANCECONTEXT; /* This context is used as a label only (dummy context) */


static __inline__ CONTEXT cont_LeftContext(void)
{
  return cont_LEFTCONTEXT;
}

static __inline__ CONTEXT cont_RightContext(void)
{
  return cont_RIGHTCONTEXT;
}

static __inline__ CONTEXT cont_InstanceContext(void)
{
  return cont_INSTANCECONTEXT;
}

/**************************************************************/
/* A stack for the number of established bindings             */
/**************************************************************/

#define cont__STACKSIZE 1000

typedef int cont_STACK_TYPE[cont__STACKSIZE];

extern cont_STACK_TYPE cont_STACK;
extern int             cont_STACKPOINTER;

/* Stack operations */

static __inline__ void cont_StackInit(void)
{
  cont_STACKPOINTER = 1;
}

static __inline__ void cont_StackPush(int Entry)
{
#ifdef CHECK
  if (cont_STACKPOINTER >= cont__STACKSIZE) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cont_StackPush: Context stack overflow!\n");
    misc_FinishErrorReport();
  }
#endif
  
  cont_STACK[cont_STACKPOINTER++] = Entry;
}

static __inline__ void cont_StackPop(void)
{
  --cont_STACKPOINTER;
}

static __inline__ int cont_StackPopResult(void)
{
  return cont_STACK[--cont_STACKPOINTER];
}

static __inline__ void cont_StackNPop(int N)
{
  cont_STACKPOINTER -= N;
}

static __inline__ int cont_StackTop(void)
{
  return cont_STACK[cont_STACKPOINTER - 1];
}

static __inline__ int cont_StackNthTop(int N)
{
  return cont_STACK[cont_STACKPOINTER - (1 + N)];
}

static __inline__ void cont_StackRplacTop(int Entry)
{
  cont_STACK[cont_STACKPOINTER - 1] = Entry;
}

static __inline__ void cont_StackRplacNthTop(int N, int Entry)
{
  cont_STACK[cont_STACKPOINTER - (1 + N)] = Entry;
}

static __inline__ void cont_StackRplacNth(int N, int Entry)
{
  cont_STACK[N] = Entry;
}

static __inline__ int cont_StackBottom(void)
{
  return cont_STACKPOINTER;
}

static __inline__ void cont_StackSetBottom(int Pointer)
{
  cont_STACKPOINTER = Pointer;
}

static __inline__ BOOL cont_StackEmpty(int Pointer)
{
  return cont_STACKPOINTER == Pointer;
}


static __inline__ void cont_StartBinding(void)
{
  cont_StackPush(cont_BINDINGS);

  cont_BINDINGS = 0;
}

static __inline__ int cont_BindingsSinceLastStart(void)
{
  return cont_BINDINGS;
}

static __inline__ void cont_StopAndStartBinding(void)
{
  cont_StackRplacTop(cont_StackTop() + cont_BINDINGS);

  cont_BINDINGS = 0;
}

/**************************************************************/
/* Access                                                     */
/**************************************************************/

static __inline__ CONTEXT cont_Binding(CONTEXT C, SYMBOL Var)
{
  return &(C)[Var];
}

static __inline__ CONTEXT cont_BindingLink(CONTEXT B)
{
  return B->link;
}

static __inline__ void cont_SetBindingLink(CONTEXT B, CONTEXT L)
{
  B->link = L;
}

static __inline__ TERM cont_BindingTerm(CONTEXT B)
{
  return B->term;
}

static __inline__ void cont_SetBindingTerm(CONTEXT B, TERM T)
{
  B->term = T;
}

static __inline__ SYMBOL cont_BindingSymbol(CONTEXT B)
{
  return B->symbol;
}

static __inline__ void cont_SetBindingSymbol(CONTEXT B, SYMBOL S)
{
  B->symbol = S;
}

static __inline__ SYMBOL cont_BindingRenaming(CONTEXT B)
{
  return B->renaming;
}

static __inline__ void cont_SetBindingRenaming(CONTEXT B, SYMBOL S)
{
  B->renaming = S;
}

static __inline__ CONTEXT cont_BindingContext(CONTEXT B)
{
  return B->context;
}

static __inline__ void cont_SetBindingContext(CONTEXT B, CONTEXT C)
{
  B->context = C;
}

static __inline__ CONTEXT cont_ContextBindingLink(CONTEXT C,SYMBOL Var)
{
  return C[Var].link;
}

static __inline__ TERM cont_ContextBindingTerm(CONTEXT C,SYMBOL Var)
{
  return C[Var].term;
}

static __inline__ void cont_SetContextBindingTerm(CONTEXT C, SYMBOL Var, TERM t)
{
  C[Var].term = t;
}

static __inline__ SYMBOL cont_ContextBindingSymbol(CONTEXT C,SYMBOL Var)
{
  return C[Var].symbol;
}

static __inline__ SYMBOL cont_ContextBindingRenaming(CONTEXT C,SYMBOL Var)
{
  return C[Var].renaming;
}

static __inline__ void cont_SetContextBindingRenaming(CONTEXT C, SYMBOL Var,
						       SYMBOL R)
{
  C[Var].renaming = R;
}

static __inline__ CONTEXT cont_ContextBindingContext(CONTEXT C,SYMBOL Var)
{
  return C[Var].context;
}

/**************************************************************/
/* Predicates                                                 */
/**************************************************************/

static __inline__ BOOL cont_VarIsBound(CONTEXT C, SYMBOL Var)
{
  return cont_ContextBindingTerm(C,Var) != (TERM) NULL;
}

static __inline__ BOOL cont_VarIsUsed(CONTEXT C, SYMBOL Var)
{
  return cont_ContextBindingContext(C,Var) != (CONTEXT) NULL;
}

static __inline__ BOOL cont_VarIsLinked(CONTEXT C, SYMBOL Var)
{
  return cont_ContextBindingLink(C,Var) != (CONTEXT) NULL;
}

static __inline__ BOOL cont_VarIsRenamed(CONTEXT C, SYMBOL Var)
{
  return cont_ContextBindingRenaming(C, Var) != symbol_Null();
}

static __inline__ BOOL cont_VarIsClosed(CONTEXT C,SYMBOL Var)
{
  return !cont_VarIsBound(C,Var) && cont_VarIsUsed(C,Var);
}

static __inline__ BOOL cont_BindingIsBound(CONTEXT B)
{
  return cont_BindingTerm(B) != (TERM) NULL;
}

static __inline__ BOOL cont_BindingIsUsed(CONTEXT B)
{
  return cont_BindingContext(B) != (CONTEXT) NULL;
}

/**************************************************************/
/* Aux functions for backtracking                             */
/**************************************************************/

static __inline__ CONTEXT cont_LastBinding(void)
{
  return cont_LASTBINDING;
}

static __inline__ void cont_SetLastBinding(CONTEXT B)
{
  cont_LASTBINDING = B;
}

static __inline__ TERM cont_LastBindingTerm(void)
{
  return cont_BindingTerm(cont_LastBinding());
}

static __inline__ SYMBOL cont_LastBindingSymbol(void)
{
  return cont_BindingSymbol(cont_LastBinding());
}

static __inline__ CONTEXT cont_LastBindingContext(void)
{
  return cont_BindingContext(cont_LastBinding());
}

static __inline__ BOOL cont_LastIsBound(void)
{
  return cont_BindingIsBound(cont_LastBinding());
}

static __inline__ BOOL cont_LastIsUsed(void)
{
  return cont_LastBindingContext() != (CONTEXT) NULL;
}

static __inline__ BOOL cont_LastIsClosed(void)
{
  return !cont_LastIsBound() && cont_LastIsUsed();
}

static __inline__ BOOL cont_IsInContext(CONTEXT C, SYMBOL Var, CONTEXT B)
{
  return cont_Binding(C, Var) == B;
}

static __inline__ CONTEXT cont_ContextOfBinding(CONTEXT B)
{
  CONTEXT Result;
  LIST    Scan;

  for (Result = NULL, Scan = cont_LISTOFCONTEXTS;
       list_Exist(Scan);
       Scan = list_Cdr(Scan)) {
    if (cont_IsInContext(list_Car(Scan), cont_BindingSymbol(B), B)) {
      Result = list_Car(Scan);
      break;
    }
  }

#ifdef CHECK
  if (Result == NULL) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cont_ContextOfBinding: Unknown context.\n");
    misc_FinishErrorReport();
  }
#endif

  return Result;
}

/**************************************************************/
/* Initialization                                             */
/**************************************************************/

static __inline__ void cont_InitBinding(CONTEXT C, SYMBOL Var)
{
  cont_CURRENTBINDING = cont_Binding(C, Var);
  cont_SetBindingLink(cont_CURRENTBINDING, (CONTEXT)NULL);
  cont_SetBindingTerm(cont_CURRENTBINDING, (TERM)NULL);
  cont_SetBindingSymbol(cont_CURRENTBINDING, Var);
  cont_SetBindingRenaming(cont_CURRENTBINDING, symbol_Null());
  cont_SetBindingContext(cont_CURRENTBINDING, (CONTEXT)NULL);
}

static __inline__ void cont_InitContext(CONTEXT C)
{
  int i;

  for (i = 0; i < cont__SIZE; i++)
    cont_InitBinding(C, i);
}

/**************************************************************/
/* Creation and deletion of contexts                          */
/**************************************************************/

static __inline__ CONTEXT cont_Create(void)
{
  CONTEXT Result;

  Result = (CONTEXT)memory_Malloc(cont__SIZE*sizeof(CONTEXT_NODE));

  cont_InitContext(Result);

  cont_LISTOFCONTEXTS = list_Cons(Result, cont_LISTOFCONTEXTS);
  cont_NOOFCONTEXTS++;

  return Result;
}
    
static __inline__ void cont_Delete(CONTEXT C)
{
#ifdef CHECK
  if ((cont_NOOFCONTEXTS == 0) ||
      !list_PointerMember(cont_LISTOFCONTEXTS, C)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cont_Delete: Context %ld not registered.\n",
		     (unsigned long)C);
    misc_FinishErrorReport();
  }
#endif

  cont_LISTOFCONTEXTS = list_PointerDeleteOneElement(cont_LISTOFCONTEXTS, C);

  cont_NOOFCONTEXTS--;

  memory_Free(C, cont__SIZE*sizeof(CONTEXT_NODE));
}

static __inline__ void cont_ResetIndexVarScanner(void)
{
  cont_INDEXVARSCANNER = symbol_GetInitialIndexVarCounter();
}

/**************************************************************/
/* Output bindings                                            */
/**************************************************************/

static __inline__ void cont_BindingOutput(CONTEXT C, SYMBOL Var)
{
  symbol_Print(cont_ContextBindingSymbol(C, Var));
  putchar(':');
  symbol_Print(Var);

  fputs(" -> ", stdout);

  if (cont_VarIsBound(C, Var)) {
    term_PrintPrefix(cont_ContextBindingTerm(C, Var));
  } else
    fputs("unbound", stdout);

  fputs(" in ", stdout);

  if (cont_VarIsUsed(C, Var)) {
    printf("%ld", (unsigned long)cont_ContextBindingContext(C, Var));
  } else
    fputs("NULL (unused)", stdout);

  fputs(". ", stdout);

  if (cont_VarIsClosed(C, Var)) {
    fputs("(closed)", stdout);
  }

  if (!cont_VarIsBound(C, Var) &&
      !cont_VarIsUsed(C, Var)) {
    fputs(",(free)", stdout);
  }

  if (cont_VarIsRenamed(C, Var)) {
    fputs(",(renamed): ", stdout);
    symbol_Print(Var);
    fputs(" -> ", stdout);
    symbol_Print(cont_ContextBindingRenaming(C, Var));
  } 
  
  fflush(stdout);
}

static __inline__ void cont_PrintCurrentTrail(void)
{
  fputs("\nPrint bindings:", stdout);
  cont_CURRENTBINDING = cont_LastBinding();
  while (cont_CURRENTBINDING) {
    cont_BindingOutput(cont_ContextOfBinding(cont_CURRENTBINDING),
		       cont_BindingSymbol(cont_CURRENTBINDING));
    cont_CURRENTBINDING = cont_BindingLink(cont_CURRENTBINDING);
    if (cont_CURRENTBINDING)
      putchar('\n');
  }
  fflush(stdout);
}

/**************************************************************/
/* Close bindings                                             */
/**************************************************************/

static __inline__ void cont_CloseBindingHelp(CONTEXT C, SYMBOL Var)
{
  cont_SetContextBindingTerm(C, Var, NULL);
}

static __inline__ void cont_CloseBindingBindingHelp(CONTEXT B)
{
  cont_SetBindingTerm(B, NULL);
}

#if SHOWBINDINGS
static __inline__ void cont_CloseBinding(CONTEXT C, SYMBOL Var)
{
  fputs("\nClose binding from ", stdout);
  cont_BindingOutput(C, Var);
  cont_CloseBindingHelp(C, Var);
}
#else
static __inline__ void cont_CloseBinding(CONTEXT C, SYMBOL Var)
{
  cont_CloseBindingHelp(C, Var);
}
#endif

static __inline__ void cont_CloseBindingBinding(CONTEXT B) {
  cont_CloseBindingBindingHelp(B);
}

/**************************************************************/
/* Establish bindings                                         */
/**************************************************************/

static __inline__ void cont_CreateBindingHelp(CONTEXT C, SYMBOL Var,
					      CONTEXT CTerm, TERM Term)
{
#ifdef CHECK
  if (cont_VarIsBound(C, Var)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cont_CreateBindingHelp: Variable already bound.\n");
    misc_FinishErrorReport();
  }
#endif

  cont_CURRENTBINDING = cont_Binding(C,Var);
  cont_SetBindingTerm(cont_CURRENTBINDING, Term);
  cont_SetBindingContext(cont_CURRENTBINDING, CTerm);
  cont_SetBindingLink(cont_CURRENTBINDING, cont_LastBinding());
  cont_SetLastBinding(cont_CURRENTBINDING);
}

#if SHOWBINDINGS

static __inline__ int cont_CreateBinding(CONTEXT C, SYMBOL Var, CONTEXT CTerm, TERM Term)
{
  cont_CreateBindingHelp(C,Var,CTerm,Term);
  fputs("\nEstablish binding from ", stdout);
  cont_BindingOutput(C, Var);
  return ++cont_BINDINGS;
}

static __inline__ int cont_CreateClosedBinding(CONTEXT C, SYMBOL Var)
{
  cont_CreateBindingHelp(C, Var, C, NULL);
  fputs("\nEstablish closed binding from ", stdout);
  cont_BindingOutput(C,Var);
  return ++cont_BINDINGS;
}

#else

static __inline__ int cont_CreateBinding(CONTEXT C, SYMBOL Var, CONTEXT CTerm, TERM Term)
{
  cont_CreateBindingHelp(C,Var,CTerm,Term);
  return ++cont_BINDINGS;
}

static __inline__ int cont_CreateClosedBinding(CONTEXT C, SYMBOL Var)
{
  cont_CreateBindingHelp(C, Var, C, NULL);
  return ++cont_BINDINGS;
}

#endif

/**************************************************************/
/* Backtracking                                               */
/**************************************************************/

static __inline__ void cont_BackTrackLastBindingHelp(void)
{
  cont_CURRENTBINDING = cont_LastBinding();
  cont_SetLastBinding(cont_BindingLink(cont_CURRENTBINDING));
  cont_SetBindingTerm(cont_CURRENTBINDING, NULL);
  cont_SetBindingContext(cont_CURRENTBINDING, NULL);
  cont_SetBindingRenaming(cont_CURRENTBINDING, symbol_Null());
  cont_SetBindingLink(cont_CURRENTBINDING, NULL);

  cont_BINDINGS--;
}

#if SHOWBINDINGS

static __inline__ void cont_BackTrackLastBinding(void)
{
  CONTEXT LastContext;
  SYMBOL  LastSymbol;

  LastContext = cont_ContextOfBinding(cont_LastBinding());
  LastSymbol  = cont_LastBindingSymbol();
  fputs("\nBacktrack binding from ", stdout);
  cont_BindingOutput(LastContext, LastSymbol);
  cont_BackTrackLastBindingHelp();
}

static __inline__ int cont_BackTrack(void)
{
  printf("\nBacktrack %d bindings:", cont_BINDINGS);

  while (cont_BINDINGS > 0)
    cont_BackTrackLastBinding();

  if (!cont_StackEmpty(0))
    cont_BINDINGS = cont_StackPopResult();

  fflush(stdout);
  return 0;
}

static __inline__ int cont_StopAndBackTrack(void)
{
#ifdef CHECK
  if (cont_BINDINGS > 0) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cont_StopAndBackTrack: Bindings not reset!\n");
    misc_FinishErrorReport();
  } else if (cont_StackEmpty(0)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cont_StopAndBackTrack: No bindings on stack!\n");
    misc_FinishErrorReport();
  }
#endif
  cont_BINDINGS = cont_StackPopResult();

  printf("\nStop and Backtrack %d bindings:", cont_BINDINGS);

  while (cont_BINDINGS > 0)
    cont_BackTrackLastBinding();

  fflush(stdout);
  return 0;
}

static __inline__ int cont_BackTrackAndStart(void)
{
  printf("\nBacktrack %d bindings:", cont_BINDINGS);

  while (cont_BINDINGS > 0)
    cont_BackTrackLastBinding();

  fflush(stdout);
  return 0;
}

static __inline__ void cont_Reset(void)
{
  fputs("\nReset bindings:", stdout);
  while (cont_LastBinding())
    cont_BackTrackLastBinding();

  cont_BINDINGS = 0;
  cont_StackInit();
  cont_ResetIndexVarScanner();
  fflush(stdout);
}

#else

static __inline__ void cont_BackTrackLastBinding(void)
{
  cont_BackTrackLastBindingHelp();
}

static __inline__ int cont_BackTrack(void)
{
  while (cont_BINDINGS > 0)
    cont_BackTrackLastBinding();

  if (!cont_StackEmpty(0))
    cont_BINDINGS = cont_StackPopResult();

  return 0;
}

static __inline__ int cont_StopAndBackTrack(void)
{
#ifdef CHECK
  if (cont_BINDINGS > 0) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cont_StopAndBackTrack: Bindings not reset!\n");
    misc_FinishErrorReport();
  } else if (cont_StackEmpty(0)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cont_StopAndBackTrack: No bindings on stack!\n");
    misc_FinishErrorReport();
  }
#endif
  cont_BINDINGS = cont_StackPopResult();

  while (cont_BINDINGS > 0)
    cont_BackTrackLastBinding();

  return 0;
}

static __inline__ int cont_BackTrackAndStart(void)
{
  while (cont_BINDINGS > 0)
    cont_BackTrackLastBinding();

  return 0;
}

static __inline__ void cont_Reset(void)
{
  while (cont_LastBinding())
    cont_BackTrackLastBinding();

  cont_BINDINGS = 0;
  cont_StackInit();
  cont_ResetIndexVarScanner();
}

#endif

/**************************************************************/
/* Check state of bindings                                    */
/**************************************************************/

#define cont__CHECKSTACKSIZE  1000
#define cont__CHECKSTACKEMPTY 0

typedef POINTER cont_CHECKSTACK_TYPE[cont__CHECKSTACKSIZE];

extern cont_CHECKSTACK_TYPE cont_CHECKSTACK;
extern int                  cont_CHECKSTACKPOINTER;

/* Stack operations */

static __inline__ void cont_CheckStackInit(void)
{
  cont_CHECKSTACKPOINTER = cont__CHECKSTACKEMPTY;
}

static __inline__ void cont_CheckStackPush(POINTER Entry)
{
#ifdef CHECK
  if (cont_CHECKSTACKPOINTER >= cont__STACKSIZE) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cont_CheckStackPush: Context check stack overflow!\n");
    misc_FinishErrorReport();
  }
#endif
  
  cont_CHECKSTACK[cont_CHECKSTACKPOINTER++] = Entry;
}

static __inline__ void cont_CheckStackPop(void)
{
  --cont_CHECKSTACKPOINTER;
}

static __inline__ POINTER cont_CheckStackPopResult(void)
{
  return cont_CHECKSTACK[--cont_CHECKSTACKPOINTER];
}

static __inline__ void cont_CheckStackNPop(int N)
{
  cont_CHECKSTACKPOINTER -= N;
}

static __inline__ POINTER cont_CheckStackTop(void)
{
  return cont_CHECKSTACK[cont_CHECKSTACKPOINTER - 1];
}

static __inline__ POINTER cont_CheckStackNthTop(int N)
{
  return cont_CHECKSTACK[cont_CHECKSTACKPOINTER - (1 + N)];
}

static __inline__ void cont_CheckStackRplacTop(POINTER Entry)
{
  cont_CHECKSTACK[cont_CHECKSTACKPOINTER - 1] = Entry;
}

static __inline__ void cont_CheckStackRplacNthTop(int N, POINTER Entry)
{
  cont_CHECKSTACK[cont_CHECKSTACKPOINTER - (1 + N)] = Entry;
}

static __inline__ void cont_CheckStackRplacNth(int N, POINTER Entry)
{
  cont_CHECKSTACK[N] = Entry;
}

static __inline__ int cont_CheckStackBottom(void)
{
  return cont_CHECKSTACKPOINTER;
}

static __inline__ void cont_CheckStackSetBottom(int Pointer)
{
  cont_CHECKSTACKPOINTER = Pointer;
}

static __inline__ BOOL cont_CheckStackEmpty(int Pointer)
{
  return cont_CHECKSTACKPOINTER == Pointer;
}

extern CONTEXT cont_STATELASTBINDING; /* Storage to save state of trails. */
extern int     cont_STATEBINDINGS;    /* Storage to save number of current bindings. */
extern int     cont_STATESTACK;       /* Storage to save state of stack. */
extern int     cont_STATETOPSTACK;    /* Storage to save state of the top element of the stack. */

static __inline__ BOOL cont_CheckLastBinding(CONTEXT Check, int Bindings)
{
  CONTEXT Scan;
  BOOL    Result;

  Scan = cont_LastBinding();

  while (Bindings > 0) {
    Scan = cont_BindingLink(Scan);
    Bindings--;
  }
  if (Check == Scan)
    Result = TRUE;
  else
    Result = FALSE;

  return Result;
}

static __inline__ void cont_CheckState(void)
{
  if (cont_CheckStackEmpty(cont__CHECKSTACKEMPTY)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cont_CheckState: No states saved.\n");
    misc_FinishErrorReport();
  }

  cont_STATETOPSTACK    = (int)cont_CheckStackPopResult();
  cont_STATESTACK       = (int)cont_CheckStackPopResult();
  cont_STATEBINDINGS    = (int)cont_CheckStackPopResult();
  cont_STATELASTBINDING = (CONTEXT)cont_CheckStackPopResult();

  if ((cont_STATELASTBINDING != cont_LastBinding()) ||
      (cont_STATEBINDINGS != cont_BINDINGS) ||
      (!cont_StackEmpty(cont_STATESTACK)) ||
      (cont_STATETOPSTACK != cont_StackTop())) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cont_CheckState: State of contexts does not match saved state.");
    misc_ErrorReport("\nTrail: Saved state: %ld; current state: %ld.",
		     (long)cont_STATELASTBINDING, (long)cont_LastBinding());
    misc_ErrorReport("\nNumber of bindings: Saved state: %d; current state: %d.",
		     cont_STATEBINDINGS, cont_BINDINGS);
    misc_ErrorReport("\nBinding stack pointer: Saved state: %d; current state: %d.",
		     cont_STATESTACK, cont_StackBottom());
    misc_ErrorReport("\nNumber of bindings on top of stack: Saved state: %d; current state: %d.\n\n",
		     cont_STATETOPSTACK, cont_StackTop());
    misc_FinishErrorReport();
  }
}

static __inline__ void cont_SaveState(void)
{
  cont_CheckStackPush((POINTER)cont_LastBinding());
  cont_CheckStackPush((POINTER)cont_BINDINGS);
  cont_CheckStackPush((POINTER)cont_StackBottom());
  cont_CheckStackPush((POINTER)cont_StackTop());
}

static __inline__ BOOL cont_IsContextEmpty(const CONTEXT Check)
{
  int i;

  for (i = 0; i < cont__SIZE; i++)
    if (cont_VarIsBound(Check, i) ||
	cont_VarIsUsed(Check, i) ||
	cont_VarIsLinked(Check, i) ||
	cont_VarIsRenamed(Check, i))
      return FALSE;

  return TRUE;
}

/**************************************************************/
/* Generation of index variables                              */
/**************************************************************/

static __inline__ SYMBOL cont_NextIndexVariable(const CONTEXT IndexContext)
{
  if (symbol_Equal(cont_INDEXVARSCANNER, symbol_LastIndexVariable()))
    cont_INDEXVARSCANNER = symbol_CreateIndexVariable();
  else
    for (;;) {
      cont_INDEXVARSCANNER = symbol_NextIndexVariable(cont_INDEXVARSCANNER);
      if (!cont_VarIsUsed(IndexContext, cont_INDEXVARSCANNER)) 
	break;
      else 
	if (symbol_Equal(cont_INDEXVARSCANNER, symbol_LastIndexVariable())) {
	  cont_INDEXVARSCANNER = symbol_CreateIndexVariable();
	  break;
	}
    }
  return cont_INDEXVARSCANNER;
}

/**************************************************************/
/* Dereferencing of terms wrt. contexts                       */
/**************************************************************/

static __inline__ TERM cont_Deref(CONTEXT* Context, TERM Term)
/**************************************************************
  INPUT:   A call-by-ref context and a term.
  RETURNS: The dereferenced term and the corresponding context.
  SUMMARY: Dereferences bindings of variables.
  CAUTION: In general, the context of the returned term
           is different to the input context.
***************************************************************/
{

  while (term_IsVariable(Term) && *Context != cont_InstanceContext()) {
    SYMBOL TermTop;

    TermTop = term_TopSymbol(Term);

    if (cont_VarIsBound(*Context, TermTop)) {
      CONTEXT HelpContext;

      HelpContext = cont_ContextBindingContext(*Context, TermTop);
      Term        = cont_ContextBindingTerm(*Context, TermTop);
      *Context    = HelpContext;
    } 
    else
      return Term;
  }

  return Term;
}

/**************************************************************/
/* Functions for Initialization and Controlling               */
/**************************************************************/
           
void cont_Init(void);
void cont_Check(void);
void cont_Free(void);

/**************************************************************/
/* Functions for Term Equality Test with respect to Bindings  */
/**************************************************************/

BOOL cont_TermEqual(CONTEXT, TERM, CONTEXT, TERM);
BOOL cont_TermEqualModuloBindings(CONTEXT, CONTEXT, TERM, CONTEXT, TERM);

/**************************************************************/
/* Functions for Applying Bindings                            */
/**************************************************************/

TERM   cont_CopyAndApplyBindings(CONTEXT, TERM);
TERM   cont_CopyAndApplyBindingsCom(const CONTEXT, TERM);

TERM   cont_ApplyBindingsModuloMatching(const CONTEXT, TERM, BOOL);
TERM   cont_ApplyBindingsModuloMatchingReverse(const CONTEXT, TERM);

BOOL   cont_BindingsAreRenamingModuloMatching(const CONTEXT);

/**************************************************************/
/* Misc Functions                                             */
/**************************************************************/

SYMBOL cont_TermMaxVar(CONTEXT, TERM);
NAT    cont_TermSize(CONTEXT, TERM);
BOOL   cont_TermContainsSymbol(CONTEXT, TERM, SYMBOL);

/**************************************************************/
/* Functions for Output                                       */
/**************************************************************/

void cont_TermPrintPrefix(CONTEXT, TERM);

#endif
