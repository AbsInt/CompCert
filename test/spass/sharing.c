/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                  STRUCTURE SHARING                     * */
/* *                                                        * */
/* *  $Module:   SHARING                                    * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1997, 1998, 1999, 2000            * */
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

#include "sharing.h"

/**************************************************************/
/* Static Variables                                           */
/**************************************************************/

#ifdef CHECK
static BOOL sharing_DATABLOCKED;
#endif

static LIST sharing_DATALIST = (LIST) NULL;

#define sharing_STACKSIZE      500
static LIST sharing_STACK[sharing_STACKSIZE];
static LIST* sharing_STACKPOINTER = sharing_STACK;

/**************************************************************/
/* Prototypes for static functions used only in this module   */
/**************************************************************/

static BOOL sharing_IsNoMoreUsed(TERM);
static LIST sharing_InternGetDataList(TERM);

static TERM sharing_InsertIntoSharing(TERM, SHARED_INDEX);
static void sharing_DeleteFromSharing(TERM, SHARED_INDEX);

static void sharing_ResetTermStamp(TERM);

static void sharing_PrintWithSuperterms(TERM);


/**************************************************************/
/* ********************************************************** */
/* *			                                    * */
/* *  PRIMITIVE SHARING FUNCTIONS                           * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/


SHARED_INDEX sharing_IndexCreate(void)
/**********************************************************
  INPUT:   None.
  RETURNS: A shared index, consisting of an Index, a Consttable
           and a Vartable.
  EFFECTS: Initializes the shared Index for the sharing_Vartable and the
           sharing_Consttable with NULL-Pointers and an empty st_index.
**********************************************************/
{
  SHARED_INDEX Result;
  int          i;

  Result = (SHARED_INDEX)memory_Malloc(sizeof(SHARED_INDEX_NODE));
  sharing_SetIndex(Result, st_IndexCreate());

  for (i=0; (i < symbol_MaxVars()); i++)
    sharing_SetVartableEntry(Result, i, NULL);

  for (i=0; (i < symbol_MaxConsts()); i++)
    sharing_SetConsttableEntry(Result, i, NULL);

  sharing_SetStampID(Result, term_GetStampID());
  return Result;
}


void sharing_IndexDelete(SHARED_INDEX ShIndex)
/**********************************************************
  INPUT:   A shared Index.
  RETURNS: None.
  EFFECTS: Deletes the Index and frees the memory for the
           structure including the Const- and Vartable.
**********************************************************/
{
  st_IndexDelete(sharing_Index(ShIndex));

  memory_Free(ShIndex, sizeof(SHARED_INDEX_NODE));
}


void sharing_PushOnStack(TERM Term)
/**********************************************************
  INPUT:   A term.
  RETURNS: None.
  EFFECTS: Creates a Stack of Pointers to the 
           term and all of its subterms in their order in
	   the arglist (thus ordered by depth).
	   top of the stack is bottom term
**********************************************************/
{
  LIST ArgList;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In sharing_PushOnStack: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  stack_Push(Term);

  ArgList = term_ArgumentList(Term);

  while (!list_Empty(ArgList)){
    sharing_PushOnStack(list_Car(ArgList));
    ArgList = list_Cdr(ArgList);
  }
}


void sharing_PushReverseOnStack(TERM Term)
/**********************************************************
  INPUT:   A term.
  RETURNS: None.
  EFFECTS: Creates a Stack of Pointers to the 
           term and all of its subterms, except variables in their order in
	   the arglist (thus ordered by depth).
	   top of the stack is top term
**********************************************************/
{
  LIST ArgList;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In sharing_PushReverseOnStack: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  if (!term_IsVariable(Term)) {

    ArgList = term_ArgumentList(Term);

    while (!list_Empty(ArgList)){
      sharing_PushReverseOnStack(list_Car(ArgList));
      ArgList = list_Cdr(ArgList);
    }

    stack_Push(Term);
  }
}

void sharing_PushReverseOnStackExcept(TERM Term, LIST DontTermList)
/**********************************************************
  INPUT:   A term and an exception list.
  RETURNS: None.
  EFFECTS: Creates a Stack of Pointers to the 
           term and all of its subterms that are not contained
	   or below the terms in DontTermList in their order in
	   the arglist (thus ordered by depth).
	   top of the stack is top term
**********************************************************/
{
  LIST ArgList;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In sharing_PushReverseOnStack: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  if (!term_IsVariable(Term) && !term_ListContainsTerm(DontTermList, Term)) {
    ArgList = term_ArgumentList(Term);

    while (!list_Empty(ArgList)){
      sharing_PushReverseOnStackExcept(list_Car(ArgList), DontTermList);
      ArgList = list_Cdr(ArgList);
    }

    stack_Push(Term);
  }
}

void sharing_PushOnStackNoStamps(TERM Term)
/**********************************************************
  INPUT:   A term.
  RETURNS: None.
  EFFECTS: Creates a Stack of Pointers to the 
           term and all of its subterms that are not stamped
	   or below stamped terms.
	   top of the stack is top term.
**********************************************************/
{
  LIST ArgList;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In sharing_PushReverseOnStackNoStamps: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  if (!term_IsVariable(Term) && !term_HasTermStamp(Term)) {

    stack_Push(Term);

    ArgList = term_ArgumentList(Term);

    while (!list_Empty(ArgList)){
      sharing_PushOnStackNoStamps(list_Car(ArgList));
      ArgList = list_Cdr(ArgList);
    }
  }
}


void sharing_PushListOnStack(LIST TermList)
/**********************************************************
  INPUT:   A list of terms.
  RETURNS: None.
  EFFECTS: Creates a Stack of Pointers to the 
           terms in <TermList>  and all of subterms in their order in
	   the arglist (thus ordered by depth).
**********************************************************/
{
  while (!list_Empty(TermList)) {
    sharing_PushOnStack(list_Car(TermList));
    TermList = list_Cdr(TermList);
  }
}


void sharing_PushListReverseOnStack(LIST TermList)
/**********************************************************
  INPUT:   A list of terms.
  RETURNS: None.
  EFFECTS: Puts all terms in Termlist and their superterms
           in their order in the arglist (thus ordered by depth)
	   on the stack.
	   On top of the stack are subterms.
**********************************************************/
{
  while (!list_Empty(TermList)) {
    sharing_PushReverseOnStack(list_Car(TermList));
    TermList = list_Cdr(TermList);
  }
}

void sharing_PushListReverseOnStackExcept(LIST TermList, LIST DontPushList)
/**********************************************************
  INPUT:   Two lists of terms.
  RETURNS: None.
  EFFECTS: Puts all terms in Termlist except those contained in
           DontPushList and their superterms
           in their order in the arglist (thus ordered by depth)
	   on the stack.
	   On top of the stack are subterms.
**********************************************************/
{
  while (!list_Empty(TermList)) {
    sharing_PushReverseOnStackExcept(list_Car(TermList), DontPushList);
    TermList = list_Cdr(TermList);
  }
}

void sharing_PushListOnStackNoStamps(LIST TermList)
/**********************************************************
  INPUT:   A list of terms.
  RETURNS: None.
  EFFECTS: Puts all terms in Termlist on the stack.
	   On top of the stack are subterms.
**********************************************************/
{
  while (!list_Empty(TermList)) {
    sharing_PushOnStackNoStamps(list_Car(TermList));
    TermList = list_Cdr(TermList);
  }
}


static BOOL sharing_IsNoMoreUsed(TERM Term)
/**********************************************************
  INPUT:   A term.
  RETURNS: TRUE,  if the Term has no superterms,
           FALSE, else.
**********************************************************/
{
#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In sharing_IsNoMoreUsed: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  return (list_Empty(term_SupertermList(Term)));
}


/**************************************************************/
/* ********************************************************** */
/* *			                                    * */
/* *  FUNCTIONS FOR INSERTION AND DELETION                  * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/

/**************************************************************/
/* ********************************************************** */
/* *			                                    * */
/* *  1) FUNCTIONS FOR INSERTION                            * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/

TERM sharing_Insert(POINTER Data, TERM Atom, SHARED_INDEX SharedIndex)
/**********************************************************
  INPUT:   A data element, it's unshared atom and a SharedIndex.
  RETURNS: The shared term inserted into the SharedIndex.
  CAUTION: The superterm slot of <Atom> is destructively used!
  MEMORY:  The term 'Atom' still exists, memory needed for
           the shared version is allocated. 
**********************************************************/
{
#ifdef CHECK
  if (!term_IsTerm(Atom) || (!sharing_IsNoMoreUsed(Atom))){
    misc_StartErrorReport();
    misc_ErrorReport("\n In sharing_Insert: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  Atom = sharing_InsertIntoSharing(Atom, SharedIndex);

  term_RplacSupertermList(Atom, list_Cons(Data, term_SupertermList(Atom)));

  return(Atom);
}


static TERM sharing_InsertIntoSharing(TERM Term, SHARED_INDEX SharedIndex)
/**********************************************************
  INPUT:   A term and a shared index.
  RETURNS: A copy of 'Term' which is inserted into the Sharing
           and the "SharedIndex".
  MEMORY:  The unshared version isn't freed, needed memory
           is allocated.
**********************************************************/
{
  int B_Stack;
  TERM InsTerm;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In sharing_InsertIntoSharing: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  B_Stack = stack_Bottom();
  sharing_PushOnStack(Term);
  InsTerm = stack_Top();      /* not necessary initialization ... */

  while (! stack_Empty(B_Stack)){
    InsTerm = stack_PopResult();

    if (term_IsVariable(InsTerm)){
      if (!sharing_IsSharedVar(InsTerm, SharedIndex)) {

	sharing_SetVartableEntry(SharedIndex, sharing_VariableIndex(InsTerm),
				 term_Create(term_TopSymbol(InsTerm),
					     list_Nil()));

	st_EntryCreate(sharing_Index(SharedIndex),
		       sharing_VartableEntry(SharedIndex,
					     sharing_VariableIndex(InsTerm)),
		       sharing_VartableEntry(SharedIndex,
					     sharing_VariableIndex(InsTerm)),
		       cont_LeftContext());
      }

	/* The NULL-Pointer in the Vartable is replaced by a copy of the */
	/* InsTerm, which is referenced by the InsTerms SharedTermCopy.  */
	/* A complex T still has to be insert. into its Args superlists. */
	/* The unshared Term isn't yet in the 'SharedIndex' and thus is  */
	/* inserted, too.                                                */
    

      sharing_RememberSharedTermCopy(InsTerm,
				     sharing_VartableEntry(SharedIndex, sharing_VariableIndex(InsTerm)));

    }else if (term_IsConstant(InsTerm)){ 
      if (!sharing_IsSharedConst(InsTerm, SharedIndex)) { 
	sharing_SetConsttableEntry(SharedIndex, sharing_ConstantIndex(InsTerm),
				   term_Create(term_TopSymbol(InsTerm),
					       list_Nil()));

	st_EntryCreate(sharing_Index(SharedIndex),
		       sharing_ConsttableEntry(SharedIndex, sharing_ConstantIndex(InsTerm)),
		       sharing_ConsttableEntry(SharedIndex, sharing_ConstantIndex(InsTerm)),
		       cont_LeftContext());
      }

	/* The NULL-Pointer in the Consttable is replaced by a copy of the */
	/* InsTerm, which is referenced by the InsTerms SharedTermCopy.    */
	/* A complex T still has to be insert. into its Args superlists.   */
	/* The unshared Term isn't yet in the 'SharedIndex' and thus is    */
	/* inserted, too.                                                  */

      sharing_RememberSharedTermCopy(InsTerm,
				     sharing_ConsttableEntry(SharedIndex, sharing_ConstantIndex(InsTerm)));

    }else{  /* term_IsComplex(InsTerm) */
            /* -> owns subterms which now have copies in Sharing.  */

      TERM SharedDuplicate;
      LIST HelpList;
      BOOL DuplCandHasSameArgs;

      SharedDuplicate = (TERM)NULL;
      HelpList =
        term_SupertermList(sharing_SharedTermCopy(term_FirstArgument(InsTerm)));
      if (list_Empty(HelpList)){
	  SharedDuplicate = term_Create(term_TopSymbol(InsTerm), list_Nil());
	  DuplCandHasSameArgs = FALSE;
	}
      else{
	DuplCandHasSameArgs = FALSE;
	while (!DuplCandHasSameArgs && !list_Empty(HelpList)){
	  SharedDuplicate = (TERM) list_First(HelpList);

	  if (term_TopSymbol(SharedDuplicate) == term_TopSymbol(InsTerm)){
	    LIST OrigHelpArgList, DuplHelpArgList;

	    OrigHelpArgList = term_ArgumentList(InsTerm);
	    DuplHelpArgList = term_ArgumentList(SharedDuplicate);
	    while (!list_Empty(OrigHelpArgList) &&
		   (DuplCandHasSameArgs = 
                   (sharing_SharedTermCopy(list_First(OrigHelpArgList)) ==
		    list_First(DuplHelpArgList)))){
	      DuplHelpArgList = list_Cdr(DuplHelpArgList);
	      OrigHelpArgList = list_Cdr(OrigHelpArgList);
	    }
	  }
	  HelpList = list_Cdr(HelpList);
	}
	if (!DuplCandHasSameArgs)
	  SharedDuplicate = term_Create(term_TopSymbol(InsTerm), list_Nil());
      } /* end of else fuer Behandlung von InsTerm mit shared FirstArg. */

      if (!DuplCandHasSameArgs){
      /* Falls neue Kopie gemacht wurde, wird diese hier "eingeshared": */

	for (HelpList = term_ArgumentList(InsTerm); !list_Empty(HelpList);
	     HelpList = list_Cdr(HelpList)){
	  TERM SharedArg;
	
	  SharedArg = sharing_SharedTermCopy((TERM)list_First(HelpList));

	  term_RplacArgumentList(SharedDuplicate, 
				 list_Cons(SharedArg,
					   term_ArgumentList(SharedDuplicate)));

	  term_RplacSupertermList(SharedArg,
	    list_Cons(SharedDuplicate,
		      term_SupertermList(SharedArg)));
	}
	term_RplacArgumentList(SharedDuplicate, 
	  list_NReverse(term_ArgumentList(SharedDuplicate)));
	
	/* Now a newly generated term can be inserted into the 'SharedIndex' !  */
	
	st_EntryCreate(sharing_Index(SharedIndex),
		       SharedDuplicate,
		       SharedDuplicate,
		       cont_LeftContext());

      }
      sharing_RememberSharedTermCopy(InsTerm,
				      SharedDuplicate);
    } 
  } 

  return(sharing_SharedTermCopy(InsTerm));
}

/**************************************************************/
/* ********************************************************** */
/* *			                                    * */
/* *  2) FUNCTIONS FOR DELETION                             * */
/* *							    * */
/* ********************************************************** */
/**************************************************************/

void sharing_Delete(POINTER Data, TERM Atom, SHARED_INDEX SharedIndex)
/**********************************************************
  INPUT:   A data element, its atom and an index.
  RETURNS: Nothing.
  MEMORY:  Destructive, deletes 'Atom' from Sharing and frees
           memory that's no more needed.
***********************************************************/
{
#ifdef CHECK
  if (!term_IsTerm(Atom)){
    misc_StartErrorReport();
    misc_ErrorReport("\n In sharing_Delete: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  term_RplacSupertermList(Atom,
    list_PointerDeleteElement(term_SupertermList(Atom), Data));

  if (sharing_IsNoMoreUsed(Atom))
    sharing_DeleteFromSharing(Atom, SharedIndex);

}


static void sharing_DeleteFromSharing(TERM Term, SHARED_INDEX SharedIndex)
/**********************************************************
  INPUT:   A term and a SharedIndex
  RETURNS: Nothing 
  MEMORY:  'Term' is removed from the Sharing, only correct
           if 'Term' is unshared in sharing (real subterms
	   may be shared, off course).
***********************************************************/
{
  BOOL IsIndexed;
#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In sharing_DeleteFromSharing: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  IsIndexed = st_EntryDelete(sharing_Index(SharedIndex), Term, Term, cont_LeftContext());

#ifdef CHECK
  if (!IsIndexed) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In sharing_DeleteFromSharing: Input not indexed.\n");
    misc_FinishErrorReport();
  }
#endif

  if (term_IsComplex(Term)){
    LIST Args;

    Args = term_ArgumentList(Term);

    while (!list_Empty(Args)){
      TERM NextArg;
      LIST Help;

      /* This block frees the terms arglists memory. */
      Help = Args;
      NextArg = (TERM) list_First(Args);
      Args = list_Cdr(Args);
      list_Free(Help);

      term_RplacSupertermList(NextArg, 
	list_PointerDeleteOneElement(term_SupertermList(NextArg), Term));
      if (sharing_IsNoMoreUsed(NextArg))
	sharing_DeleteFromSharing(NextArg, SharedIndex);
    }

  } else if (term_IsConstant(Term)) {
    sharing_SetConsttableEntry(SharedIndex, sharing_ConstantIndex(Term), NULL);
  } else {
    sharing_SetVartableEntry(SharedIndex, sharing_VariableIndex(Term), NULL);
  }
  list_Delete(term_SupertermList(Term));
  term_Free(Term);
}


/**************************************************************/
/* Functions to access unshared data via the shared term.     */
/**************************************************************/

LIST sharing_GetDataList(TERM Term, SHARED_INDEX SharedIndex)
/**********************************************************
  INPUT:   A shared term and the shared index it belongs to.
  RETURNS: The list of data connected to all superterms of Term,
           e.g. the list of all literals containing Term.
  EFFECT:  Allocates memory for the returned list.
  CAUTION: Works recursive!
**********************************************************/
{
  LIST Result = list_Nil();
#ifdef CHECK
  if (!term_IsTerm(Term) || (SharedIndex == NULL)){
    misc_StartErrorReport();
    misc_ErrorReport("\n In sharing_GetDataList: Illegal input.\n");
    misc_FinishErrorReport();
  }
  /* What if the term doesn't belong to this shared index ?????? */

#endif

  if (term_StampOverflow(sharing_StampID(SharedIndex)))
    sharing_ResetAllTermStamps(SharedIndex);
    
  term_StartStamp();

  Result = sharing_InternGetDataList(Term);

  term_StopStamp();

  return Result;
}


static LIST sharing_InternGetDataList(TERM Term)
/**********************************************************
  INPUT:   A shared term.
  RETURNS: The list of data connected to all superterms of Term
  EFFECT:  Allocates memory for the returned list.
********************************************************/
{
  if (term_IsAtom(Term))
    /* We are at top level of the superterm "tree",  */
    /* so the recursion stops here                   */ 
    return list_Copy(term_AtomsLiterals(Term));
  else{
    LIST SuperList;
    LIST DataList = list_Nil();

    for (SuperList = term_SupertermList(Term); !list_Empty(SuperList);
	 SuperList = list_Cdr(SuperList)) {
      TERM superterm = (TERM) list_Car(SuperList);
      if (!term_AlreadyVisited(superterm)) {
	DataList = list_Nconc(sharing_InternGetDataList(superterm), DataList);
	term_SetTermStamp(superterm);
      }
    }
    return DataList;
  }
}


void sharing_StartDataIterator(TERM Term, SHARED_INDEX SharedIndex)
/**********************************************************
  INPUT:   A shared term and the shared index it belongs to.
  RETURNS: Nothing.
  EFFECT:  Prepares the data iterator for Term.
           After this call you can access single data items
	   for Term with function sharing_GetNextData.
********************************************************/
{
#ifdef CHECK
  if (!term_IsTerm(Term) || (SharedIndex == NULL)){
    misc_StartErrorReport();
    misc_ErrorReport("\n In sharing_StartDataIterator: Illegal input.\n");
    misc_FinishErrorReport();
  }
  if (sharing_DATABLOCKED) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In sharing_StartDataIterator: Data iterator already used.\n");
    misc_FinishErrorReport();
  }
  sharing_DATABLOCKED = TRUE;
#endif

  if (term_StampOverflow(sharing_StampID(SharedIndex)))
    sharing_ResetAllTermStamps(SharedIndex);
  term_StartStamp();

  /* Init stack */
  sharing_STACKPOINTER = sharing_STACK;  /* Pop all items */
  while (!term_IsAtom(Term)) {
    /* Push superterm list on stack */
    *(sharing_STACKPOINTER++) = term_SupertermList(Term);
    Term                      = list_Car(term_SupertermList(Term));
  }
    
  sharing_DATALIST = term_AtomsLiterals(Term);
}


POINTER sharing_GetNextData(void)
/**********************************************************
  INPUT:   None
  RETURNS: A single data item connected to the term specified
           in the previous call of sharing_StartDataIterator.
	   NULL is returned, if all data items were accessed before.
  EFFECT:  In contrast to function sharing_GetDataList
           no memory is allocated.
********************************************************/
{
  POINTER Result = NULL;
  LIST superlist;

#ifdef CHECK
  if (!sharing_DATABLOCKED) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In sharing_GetNextData: Iterator wasn't started.\n");
    misc_FinishErrorReport();
  }
#endif

  if (!list_Empty(sharing_DATALIST)) {
    Result = list_Car(sharing_DATALIST);
    sharing_DATALIST = list_Cdr(sharing_DATALIST);
  } else {
    superlist = NULL;
    while ((sharing_STACKPOINTER > sharing_STACK) && /* stack not empty */
	   list_Empty(superlist)) {
      /* change between backtracking and expansion */
      do { /* Backtracking */
	superlist = *(--sharing_STACKPOINTER); /* PopResult */
	term_SetTermStamp(list_Car(superlist));
	do
	  superlist = list_Cdr(superlist);
	while (!list_Empty(superlist) &&
	       term_AlreadyVisited(list_Car(superlist)));
      } while ((sharing_STACKPOINTER>sharing_STACK) && list_Empty(superlist));
      while (!list_Empty(superlist) &&
	     !term_IsAtom(list_Car(superlist))) { /* Expansion */
	*(sharing_STACKPOINTER++) = superlist;
	superlist = term_SupertermList(list_Car(superlist));
	/* Search next unvisited term */
	while (!list_Empty(superlist) &&
	       term_AlreadyVisited(list_Car(superlist)))
	  superlist = list_Cdr(superlist);
      }
    }
    if (!list_Empty(superlist)) {
      *(sharing_STACKPOINTER++) = superlist;
      sharing_DATALIST          = term_AtomsLiterals(list_Car(superlist));
      Result                    = list_Car(sharing_DATALIST);
      sharing_DATALIST          = list_Cdr(sharing_DATALIST);
    }
  } /* else */
  return Result;
}


void sharing_StopDataIterator(void)
/**********************************************************
  INPUT:   None.
  RETURNS: Nothing.
  EFFECT:  The data iterator is stopped for the term you specified
           in the corresponding call of sharing_StartDataIterator.
********************************************************/
{
#ifdef CHECK
  if (!sharing_DATABLOCKED) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In sharing_StopDataIterator: Iterator wasn't started.\n");
    misc_FinishErrorReport();
  }
  sharing_DATABLOCKED = FALSE;
#endif
  sharing_DATALIST = list_Nil();
  term_StopStamp();
}


LIST sharing_NAtomDataList(TERM Atom)
/**********************************************************
  INPUT:   A shared term.
  RETURNS: A List of data connected with 'Term' or superterms.
  EFFECT:  No memory Allocation
  CAUTION: THE RETURNED LIST MUST NOT CHANGE
**********************************************************/
{
#ifdef CHECK
  if (!term_IsTerm(Atom) || !term_IsAtom(Atom)){
    misc_StartErrorReport();
    misc_ErrorReport("\n In sharing_NAtomDataList: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif
  
  return(term_AtomsLiterals(Atom));
}


LIST sharing_GetAllSuperTerms(SHARED_INDEX Index)
/**********************************************************
  INPUT:   A shared Index.
  RETURNS: A List of all Data in the shared Index.
  EFFECT:  The term stamp is used.
**********************************************************/
{
  int  i;
  LIST Result = list_Nil();
  TERM term;

  if (term_StampOverflow(sharing_StampID(Index)))
    sharing_ResetAllTermStamps(Index);
  term_StartStamp();
  
  for (i = 0; i < symbol_MaxVars(); i++) {
    term = sharing_VartableEntry(Index,i);
    if (term != NULL)
      Result = list_Nconc(sharing_InternGetDataList(term), Result);
  }

  for (i = 0; i < symbol_MaxConsts(); i++) {
    term = sharing_ConsttableEntry(Index,i);
    if (term != NULL)
      Result = list_Nconc(sharing_InternGetDataList(term), Result);
  }
  
  term_StopStamp();

  return Result;
}


void sharing_ResetAllTermStamps(SHARED_INDEX SharedIndex)
/**********************************************************
  INPUT:   A shared index.
  RETURNS: Nothing.
  EFFECT:  The stamps of all terms in the shared index are reset.
**********************************************************/
{
  TERM term;
  int i;
     
  /* Reset stamp for all variables and their superterms */
  for (i = 0; i < symbol_MaxVars(); i++) {
    term = sharing_VartableEntry(SharedIndex, i);
    if (term != NULL)
      sharing_ResetTermStamp(term);
  }

  /* Reset stamp for all constants and their superterms */
  for (i = 0; i < symbol_MaxConsts(); i++){
    term = sharing_ConsttableEntry(SharedIndex, i);
    if (term != NULL)
      sharing_ResetTermStamp(term);
  }
}


static void sharing_ResetTermStamp(TERM Term)
/**********************************************************
  INPUT:   A term.
  RETURNS: Nothing.
  EFFECT:  The stamps of Term and all its superterms are reset.
**********************************************************/
{
  LIST SuperList;
  TERM SuperTerm;

  if (!term_IsAtom(Term)) {
    for (SuperList = term_SupertermList(Term); !list_Empty(SuperList);
	 SuperList = list_Cdr(SuperList)) {
      SuperTerm = (TERM) list_Car(SuperList);
      if (!term_StampAlreadyReset(SuperTerm)) {
	sharing_ResetTermStamp(SuperTerm);
	term_ResetTermStamp(SuperTerm);
      }
    }
  }
}


NAT sharing_GetNumberOfOccurances(TERM Term)
/**************************************************************
  INPUT:   A shared (!) term.
  RETURNS: How many literals contain <Term>.
           Note that literals containing <Term> <n> times are counted
	   <n> times.
***************************************************************/
{
  if (term_IsAtom(Term))
    /* Stop recursion */
    return list_Length(term_AtomsLiterals(Term));
  else {
    LIST Scan;
    NAT  Result;

    Result = 0;
    for (Scan = term_SupertermList(Term); !list_Empty(Scan); Scan = list_Cdr(Scan))
      Result += sharing_GetNumberOfOccurances(list_Car(Scan));

    return Result;
  }
}


NAT sharing_GetNumberOfInstances(TERM Term, SHARED_INDEX Index)
/**************************************************************
  INPUT:   A (!) shared term and a shared index. The term has to be
           part of the index.
  RETURNS: How many literals within the index contain an instance of <Term>.
           Note that literals containing <n> instances of <Term>
	   are counted <n> times.
***************************************************************/
{
  NAT  Result;
  TERM Instance;

  Result   = 0;
  Instance = st_ExistInstance(cont_LeftContext(), sharing_Index(Index), Term);
  while (Instance != NULL) {
    Result += sharing_GetNumberOfOccurances(Instance);
    Instance = st_NextCandidate();
  }
  return Result;
}


/**************************************************************/
/* Output functions for the sharing structure.                  */
/**************************************************************/

void sharing_PrintVartable(SHARED_INDEX SharedIndex)
/**********************************************************
  INPUT:   A shared index.
  RETURNS: Nothing.
  EFFECT:  Prints the Vartable entries to stdout
**********************************************************/
{
  int i;
     
  for (i = 0; i < symbol_MaxVars(); i++){
    if (sharing_VartableEntry(SharedIndex, i) != NULL){
      printf("\n X%d   :  ", i);
      
      term_Print(sharing_VartableEntry(SharedIndex, i));
    }
  }
}


void sharing_PrintConsttable(SHARED_INDEX SharedIndex)
/**********************************************************
  INPUT: A shared index.  
  RETURNS: Nothing.
  EFFECT:  Prints the Consttable entries to stdout
**********************************************************/
{
  int i;
     
  for (i = 0; i < symbol_MaxConsts(); i++){
    if (sharing_ConsttableEntry(SharedIndex, i) != NULL){
      printf("\n c%d   :  ", i);
      
      term_Print(sharing_ConsttableEntry(SharedIndex, i));
    }
  }
}


void sharing_PrintSharingConstterms1(SHARED_INDEX SharedIndex)
/**********************************************************
  INPUT:   A shared index.
  RETURNS: Nothing.
  EFFECT:  Prints all terms from the Consttable and their
           direct superterms to stdout
**********************************************************/
{
  TERM term;
  int i;
     
  for (i = 0; i < symbol_MaxConsts(); i++) {
    term = sharing_ConsttableEntry(SharedIndex, i);
    if (term != NULL){
      printf("\n c%d   :  ", i);
      term_Print(term);
      puts("   has the direct superterms : ");
      term_TermListPrint(term_SupertermList(term));
    }
  }
}


void sharing_PrintSharingVarterms1(SHARED_INDEX SharedIndex)
/**********************************************************
  INPUT:   A shared index.
  RETURNS: Nothing.
  EFFECT:  Prints all terms from the Vartable and their
           superterms to stdout
**********************************************************/
{
  TERM term;
  int i;
     
  for (i = 0; i < symbol_MaxVars(); i++) {
    term = sharing_VartableEntry(SharedIndex, i);
    if (term != NULL){
      printf("\n x%d   :  ", i);
      term_Print(term);
      puts("   has the direct superterms : ");
      term_TermListPrint(term_SupertermList(term));
    }
  }
}


static void sharing_PrintWithSuperterms(TERM Term)
/**********************************************************
  INPUT:   A Term
  RETURNS: Nothing.
  EFFECT:  Prints all Superterms of 'Term' from the sharing
           to stdout.
**********************************************************/
{

  LIST HelpList;

#ifdef CHECK
  if (!term_IsTerm(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In sharing_PrintWithSuperterms: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  if (term_IsAtom(Term)) {
    term_Print(Term);
    putchar('\n');
  }
  else{
    term_Print(Term);
    HelpList = term_SupertermList(Term);
    if (!list_Empty(HelpList)){
      putchar('[');
      term_TermListPrint(HelpList);
      puts("]");
      while (!list_Empty(HelpList)){
	sharing_PrintWithSuperterms(list_Car(HelpList));
	HelpList = list_Cdr(HelpList);
      }
    }
  }
}


void sharing_PrintSharing(SHARED_INDEX SharedIndex)
/**********************************************************
  INPUT:   A shared Index.
  EFFECT:  Prints the sharing to standard.out.
**********************************************************/
{
  int i;
     
  for (i = 0; i < symbol_MaxConsts(); i++){
    if (sharing_ConsttableEntry(SharedIndex, i) != NULL){
      sharing_PrintWithSuperterms(sharing_ConsttableEntry(SharedIndex, i));
      puts("\n");
    }
  }
  puts("------------------------");
  for (i = 0; i < symbol_MaxVars(); i++){
    if (sharing_VartableEntry(SharedIndex, i) != NULL){
      sharing_PrintWithSuperterms(sharing_VartableEntry(SharedIndex, i));
      puts("\n");
    }
  }
}


void sharing_PrintSameLevelTerms(TERM Term)
/**********************************************************
  INPUT:   A term.
  RETURNS: Nothing.
  EFFECT:  Prints all terms, that share any of 'Term's args to 
           standard.out.
**********************************************************/
{
  LIST HelpList;

  HelpList = term_ArgumentList(Term);

  while (!list_Empty(HelpList)){
    if (!list_Empty(term_SupertermList(list_First(HelpList))))
      term_TermListPrint(term_SupertermList(list_First(HelpList)));

    HelpList = list_Cdr(HelpList);
  }
}

void sharing_PrintStack(void)
/**********************************************************
  INPUT:   None.
  RETURNS: Nothing.
  EFFECT:  Prints the internal sharing stack for iterative
           queries. Only for debugging purposes.
**********************************************************/
{
  TERM term;
  LIST* ptr = sharing_STACKPOINTER;

  while (ptr > sharing_STACK) {
    ptr--;
    term = list_Car(*ptr);
    term_Print(term);
    putchar('\n');
  }
}


