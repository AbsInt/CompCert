/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                     LISTS                              * */
/* *                                                        * */
/* *  $Module:   LIST                                       * */ 
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

#ifndef _LIST_
#define _LIST_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "memory.h"
#include "misc.h"

/**************************************************************/
/* Structures                                                 */
/**************************************************************/

typedef struct LIST_HELP {
  struct LIST_HELP *cdr;
  POINTER           car;
} LIST_NODE;

typedef LIST_NODE *LIST;

/**************************************************************/
/* Macros                                                     */
/**************************************************************/

static __inline__ void list_Free(LIST L)
{
  memory_Free(L, sizeof(LIST_NODE));
}

static __inline__ LIST list_Nil(void)
{
  return NULL;
}

static __inline__ BOOL list_Empty(LIST L)
{
  return L == NULL;
}

static __inline__ BOOL list_Exist(LIST L)
{
  return L != NULL;
}

static __inline__ POINTER list_Car(LIST L)
{
  return L->car;
}

static __inline__ POINTER list_NCar(LIST *L)
{
  POINTER Result;
  LIST    Help;

  Result = (*L)->car;
  Help   = (*L)->cdr;
  list_Free(*L);
  *L     = Help;
  return Result;
}

static __inline__ LIST list_Cdr(LIST L)
{
  return L->cdr;
}

static __inline__ POINTER list_First(LIST L)
{
  return list_Car(L);
}

static __inline__ POINTER list_Second(LIST L)
{
  return list_Car(list_Cdr(L));
}

static __inline__ POINTER list_Third(LIST L)
{
  return list_Car(list_Cdr(list_Cdr(L)));
}

static __inline__ POINTER list_Fourth(LIST L) 
{
  return(list_Third(list_Cdr(L)));
}

static __inline__ POINTER list_Fifth(LIST L) 
{
  return(list_Fourth(list_Cdr(L)));
}

static __inline__ void list_Rplacd(LIST L1, LIST L2)
{
  L1->cdr = L2;
}

static __inline__ void list_Rplaca(LIST L, POINTER P)
{
  L->car = P;
}

static __inline__ void list_RplacSecond(LIST L, POINTER P)
{
  list_Rplaca(list_Cdr(L), P);
}


/**************************************************************/
/* Functions                                                  */
/**************************************************************/

LIST    list_Copy(const LIST);
LIST    list_CopyWithElement(const LIST, POINTER (*)(POINTER));
void    list_InsertNext(LIST, POINTER);

void    list_NMapCar(LIST, POINTER (*)(POINTER));
void    list_Apply(void (*)(POINTER), LIST);

LIST    list_Reverse(const LIST);
LIST    list_NReverse(LIST);

void    list_Split(LIST, LIST *, LIST *); 
LIST    list_PointerSort(LIST);
LIST    list_Merge(LIST, LIST, BOOL (*)(POINTER, POINTER));
LIST    list_MergeSort(LIST, BOOL (*)(POINTER, POINTER));
LIST    list_InsertionSort(LIST, BOOL (*)(POINTER, POINTER));
LIST    list_Sort(LIST, BOOL (*)(POINTER, POINTER));
BOOL    list_SortedInOrder(LIST, BOOL (*)(POINTER, POINTER));
LIST    list_NumberSort(LIST , NAT (*)(POINTER));
LIST    list_GreaterNumberSort(LIST , NAT (*)(POINTER));
LIST    list_NNumberMerge(LIST , LIST, NAT (*)(POINTER));

POINTER list_DequeueNext(LIST);
POINTER list_NthElement(LIST, NAT);
void    list_DeleteWithElement(LIST, void (*)(POINTER));
NAT     list_DeleteWithElementCount(LIST, void (*)(POINTER));
LIST    list_DeleteElement(LIST, POINTER, BOOL (*)(POINTER, POINTER));
LIST    list_DeleteElementIf(LIST, BOOL (*)(POINTER));
LIST    list_DeleteElementIfFree(LIST, BOOL (*)(POINTER), void (*)(POINTER));
LIST    list_DeleteElementFree(LIST, POINTER, BOOL (*)(POINTER, POINTER), void (*)(POINTER));
LIST    list_DeleteOneElement(LIST, POINTER, BOOL (*)(POINTER, POINTER));
LIST    list_PointerDeleteElement(LIST, POINTER);
LIST    list_PointerDeleteElementFree(LIST, POINTER, void (*)(POINTER));
LIST    list_PointerDeleteOneElement(LIST, POINTER);
BOOL    list_DeleteFromList(LIST*, POINTER);
BOOL    list_DeleteOneFromList(LIST*, POINTER);
LIST    list_DeleteDuplicates(LIST, BOOL (*)(POINTER, POINTER));
LIST    list_DeleteDuplicatesFree(LIST, BOOL (*)(POINTER, POINTER), void (*)(POINTER));
LIST    list_PointerDeleteDuplicates(LIST);

BOOL    list_IsSetOfPointers(LIST);
LIST    list_NPointerUnion(LIST, LIST);
LIST    list_NUnion(LIST, LIST, BOOL (*)(POINTER, POINTER));
LIST    list_NListTimes(LIST, LIST);
LIST    list_NIntersect(LIST, LIST, BOOL (*)(POINTER, POINTER));
void    list_NInsert(LIST, LIST);
LIST    list_NPointerIntersect(LIST, LIST);
BOOL    list_HasIntersection(LIST, LIST);
LIST    list_NPointerDifference(LIST, LIST);
LIST    list_NDifference(LIST, LIST, BOOL (*)(POINTER, POINTER));
LIST    list_NMultisetDifference(LIST, LIST, BOOL (*)(POINTER, POINTER));
BOOL    list_PointerReplaceMember(LIST, POINTER, POINTER);

void    list_DeleteAssocListWithValues(LIST, void (*)(POINTER));
POINTER list_AssocListValue(LIST, POINTER);
LIST    list_AssocListPair(LIST, POINTER);

LIST    list_MultisetDistribution(LIST);
int     list_CompareMultisetsByElementDistribution(LIST, LIST);

NAT     list_Length(LIST);
NAT     list_Bytes(LIST);

/**************************************************************/
/* Functional Inline Functions                                */
/**************************************************************/

static __inline__ LIST list_Cons(POINTER Ptr, const LIST List)
{
  LIST Cell;

  Cell = (LIST)memory_Malloc(sizeof(LIST_NODE));
  Cell->car = Ptr;
  Cell->cdr = List;
  return Cell;
}


static __inline__ LIST list_Nconc(LIST List1, LIST List2)
{
  LIST Result;

  if (list_Empty(List1))
    return List2;

  if (list_Empty(List2))
    return List1;

  Result = List1;
  for (List1 = Result; !list_Empty(list_Cdr(List1)); List1 = list_Cdr(List1))
    /* empty */;
  List1->cdr = List2;
  return Result;
}


static __inline__ LIST list_List(POINTER P)
{
  return list_Cons(P,list_Nil());
}


static __inline__ LIST list_Append(LIST List1, LIST List2)
{
  LIST Result;

  if (list_Empty(List1))
    return List2;
  if (list_Empty(List2))
    return list_Copy(List1);

  Result = list_Copy(List1);
  for (List1 = Result; !list_Empty(list_Cdr(List1)); List1 = list_Cdr(List1))
    /* empty */;
  List1->cdr = List2;
  return Result;
}


static __inline__ void list_Delete(LIST L)
{
  LIST Current;

  Current = L;
  while (!list_Empty(Current)) {
    L = list_Cdr(L);
    list_Free(Current);
    Current = L;
  }
}

static __inline__ BOOL list_Member(LIST List, POINTER Element,
				   BOOL (*Test)(POINTER, POINTER))
/**************************************************************
  INPUT:   A list and an element pointer and an equality test for two elements.
  RETURNS: TRUE iff Element is in List with respect to Test
***************************************************************/
{
  while (!list_Empty(List)) {
    if (Test(Element, list_Car(List)))
      return TRUE;
    List = list_Cdr(List);
  }
  
  return FALSE;
}


static __inline__ BOOL list_PointerMember(LIST List, POINTER Element)
/**************************************************************
  INPUT:   A list and an element pointer.
  RETURNS: TRUE iff Element is in List with respect to pointer equality.
***************************************************************/
{
  while (!list_Empty(List)) {
    if (Element == list_Car(List))
      return TRUE;
    List = list_Cdr(List);
  }
  
  return FALSE;
}

/**************************************************************/
/* Stack Macros                                               */
/**************************************************************/

static __inline__ LIST list_StackBottom(void)
{
  return list_Nil();
}


static __inline__ BOOL list_StackEmpty(LIST S)
{
  return list_Empty(S);
}


static __inline__ LIST list_Push(POINTER I, LIST L)
{
  return list_Cons(I, L);
}


static __inline__ POINTER list_Top(LIST L)
{
  return list_Car(L);
}


static __inline__ LIST list_Pop(LIST L)
{
  LIST Aux = L; 

  L = list_Cdr(L);
  list_Free(Aux);
  return L;
}


static __inline__ void list_RplacTop(LIST L, POINTER P)
{
  list_Rplaca(L, P);
}


static __inline__ LIST list_StackFree(LIST L)
{
  while (!list_StackEmpty(L))
    L = list_Pop(L);
  return list_Nil();
}


/**************************************************************/
/* Pair Macros                                                */
/**************************************************************/

static __inline__ LIST list_PairNull(void)
{
  return list_Nil();
}


static __inline__ LIST list_PairCreate(POINTER P1, POINTER P2)
{
  return list_Cons(P1, P2);
}


static __inline__ void list_PairFree(LIST L)
{
  list_Free(L);
}


static __inline__ POINTER list_PairFirst(LIST L)
{
  return list_Car(L);
}


static __inline__ POINTER list_PairSecond(LIST L)
{
  return (POINTER)list_Cdr(L);
}

static __inline__ void list_PairRplacSecond(LIST L, POINTER P)
{
  list_Rplacd(L,P);
}

static __inline__ void list_DeletePairList(LIST L)
  /* Delete a list of pairs */
{
  list_DeleteWithElement(L, (void (*)(POINTER))list_PairFree);
}

static __inline__ void list_DeleteDistribution(LIST L)
{
  list_DeletePairList(L);
}

/**************************************************************/
/* Assoc Lists                                                */
/**************************************************************/


static __inline__ LIST list_AssocCons(LIST L, POINTER Key, POINTER Value)
{
  return list_Cons(list_PairCreate(Key, Value), L);
} 

#endif
