/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                    ST INDEXING                         * */
/* *                                                        * */
/* *  $Module:   ST                                         * */ 
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

#ifndef _ST_
#define _ST_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "foldfg.h"
#include "term.h"
#include "symbol.h"
#include "list.h"

#include "subst.h"
#include "unify.h"

/**************************************************************/
/* Data Structures                                            */
/**************************************************************/

typedef enum {st_NOP,             st_UNIFIER,    st_GEN,
	      st_GENPRETEST,      st_INSTANCE,   st_INSTANCEPRETEST
}  st_RETRIEVAL_TYPE;

typedef enum {st_STANDARD, st_NOC} st_WHERE_TYPE;

typedef unsigned short int st_MINMAX;


/**************************************************************/
/* Type st_INDEX and Inline Functions                         */
/**************************************************************/

typedef struct st {
  SUBST     subst;
  LIST      subnodes;
  LIST      entries;
  st_MINMAX max, min;
} st_INDEX_NODE, *st_INDEX;


static __inline__ st_INDEX st_Get(void)
{
  return (st_INDEX) memory_Malloc(sizeof(st_INDEX_NODE));
}

static __inline__ void st_Free(st_INDEX ST)
{
  memory_Free(ST, sizeof(st_INDEX_NODE));
}

static __inline__ SUBST st_Subst(st_INDEX ST)
{
  return ST->subst;
}

static __inline__ LIST st_Entries(st_INDEX ST)
{
  return ST->entries;
}

static __inline__ LIST st_Subnodes(st_INDEX ST)
{
  return ST->subnodes;
}

static __inline__ st_MINMAX st_Max(st_INDEX ST)
{
  return ST->max;
}

static __inline__ void st_SetMax(st_INDEX ST, st_MINMAX Value)
{
  ST->max = Value;
}

static __inline__ st_MINMAX st_Min(st_INDEX ST)
{
  return ST->min;
}

static __inline__ void st_SetMin(st_INDEX ST, st_MINMAX Value)
{
  ST->min = Value;
}

static __inline__ BOOL st_IsLeaf(st_INDEX ST)
{
  return !list_Empty(st_Entries(ST));
}

static __inline__ BOOL st_IsInner(st_INDEX ST)
{
  return !list_Empty(st_Subnodes(ST));
}

static __inline__ BOOL st_Empty(st_INDEX ST)
{
  return (ST == NULL || (!st_IsLeaf(ST) && !st_IsInner(ST)));
}

static __inline__ BOOL st_Exist(st_INDEX ST)
{
  return (ST != NULL && (st_IsLeaf(ST) || st_IsInner(ST)));
}

static __inline__ void st_SetNode(st_INDEX Index, SUBST Subst,
				  LIST Subnodes, LIST Entries)
{
  Index->subst    = Subst;
  Index->subnodes = Subnodes;
  Index->entries  = Entries;
}

static __inline__ st_INDEX st_CreateNode(SUBST Subst, LIST Subnodes,
					 LIST Entries)
{
  st_INDEX index;

  index = st_Get();
  st_SetNode(index, Subst, Subnodes, Entries);

  return index;
}


typedef enum {st_EMPTY = 1, st_FCT, st_CONST, st_VAR,
	      st_STAR, st_FIRST} NODETYPE;


/**************************************************************/
/* A special ST-Stack for sequential retrieval operations     */
/**************************************************************/

#define st_STACKSIZE 1000

typedef POINTER ST_STACK[st_STACKSIZE];

extern ST_STACK st_STACK;
extern int      st_STACKPOINTER;
extern int      st_STACKSAVE;

/* Stack operations */

static __inline__ void st_StackInit(void)
{
  st_STACKPOINTER = 0;
}

static __inline__ void st_StackPush(POINTER Entry)
{
#ifdef CHECK
  if (st_STACKPOINTER >= st_STACKSIZE) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In st_StackPush: ST-Stack Overflow!\n");
    misc_FinishErrorReport();
  }
#endif
  
  st_STACK[st_STACKPOINTER++] = Entry;
}

static __inline__ void st_StackPop(void)
{
  --st_STACKPOINTER;
}

static __inline__ POINTER st_StackPopResult(void)
{
  return st_STACK[--st_STACKPOINTER];
}

static __inline__ void st_StackNPop(int N)
{
  st_STACKPOINTER -= N;
}

static __inline__ POINTER st_StackTop(void)
{
  return st_STACK[st_STACKPOINTER - 1];
}

static __inline__ POINTER st_StackNthTop(int N)
{
  return st_STACK[st_STACKPOINTER - (1 + N)];
}

static __inline__ void st_StackRplacTop(POINTER Entry)
{
  st_STACK[st_STACKPOINTER - 1] = Entry;
}

static __inline__ void st_StackRplacNthTop(int N, POINTER Entry)
{
  st_STACK[st_STACKPOINTER - (1 + N)] = Entry;
}

static __inline__ void st_StackRplacNth(int N, POINTER Entry)
{
  st_STACK[N] = Entry;
}

static __inline__ int st_StackBottom(void)
{
  return st_STACKPOINTER;
}

static __inline__ void st_StackSetBottom(int Pointer)
{
  st_STACKPOINTER = Pointer;
}

static __inline__ BOOL st_StackEmpty(int Pointer)
{
  return st_STACKPOINTER == Pointer;
}


/**************************************************************/
/* Functions for Creation and Deletion of an st_INDEX         */
/**************************************************************/

st_INDEX st_IndexCreate(void); 
void     st_IndexDelete(st_INDEX);

/**************************************************************/
/* Add and Remove Entries to an st_INDEX                      */
/**************************************************************/

void     st_EntryCreate(st_INDEX, POINTER, TERM, const CONTEXT);
BOOL     st_EntryDelete(st_INDEX, POINTER, TERM, const CONTEXT);

/**************************************************************/
/* Functions for Retrieval in the Index                       */
/**************************************************************/

LIST     st_GetUnifier(CONTEXT, st_INDEX, CONTEXT, TERM);
LIST     st_GetGen(CONTEXT, st_INDEX, TERM);
LIST     st_GetGenPreTest(CONTEXT, st_INDEX, TERM);
LIST     st_GetInstance(CONTEXT, st_INDEX, TERM);
LIST     st_GetInstancePreTest(CONTEXT, st_INDEX, TERM);

void     st_CancelExistRetrieval(void);

POINTER  st_ExistUnifier(CONTEXT, st_INDEX, CONTEXT, TERM);
POINTER  st_ExistGen(CONTEXT, st_INDEX, TERM);
POINTER  st_ExistGenPreTest(CONTEXT, st_INDEX, TERM);
POINTER  st_ExistInstance(CONTEXT, st_INDEX, TERM);
POINTER  st_ExistInstancePreTest(CONTEXT, st_INDEX, TERM);

POINTER  st_NextCandidate(void);

/**************************************************************/
/* Function for Output                                        */
/**************************************************************/

void     st_Print(st_INDEX, void (*)(POINTER));

#endif
