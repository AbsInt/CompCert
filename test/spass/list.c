/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                     LISTS                              * */
/* *                                                        * */
/* *  $Module:   LIST                                       * */ 
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

#include "list.h"

/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  MEMORY MANAGEMENT                                     * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/

LIST list_Copy(const LIST List)
/**************************************************************
  INPUT:   A List.
  RETURNS: The copy of the list.
  CAUTION: The entries of the list are NOT copied !
           the function needs time O(n), where <n> is the length
	   of the list.
***************************************************************/
{
  LIST Copy;
  LIST Scan1,Scan2;

 
  if (list_Empty(List))
    return list_Nil();

  Copy  = list_List(list_Car(List));
  Scan1 = Copy;
  Scan2 = list_Cdr(List);

  while (!list_Empty(Scan2)) {
    list_Rplacd(Scan1, list_List(list_Car(Scan2)));
    Scan1 = list_Cdr(Scan1);
    Scan2 = list_Cdr(Scan2);
  }
  return Copy;
}


LIST list_CopyWithElement(const LIST List, POINTER (*CopyElement)(POINTER))
/**************************************************************
  INPUT:   A List and a copy function for the elements.
  RETURNS: The copy of the list.
  CAUTION: The entries of the list are NOT copied !
           The function needs time O(n*c), where <n> is the length
	   of the list and <c> is the time for a call of the
	   element copy function.
***************************************************************/
{
  LIST Copy;
  LIST Scan1,Scan2;

  if (list_Empty(List))
    return list_Nil();

  Copy  = list_List(CopyElement(list_Car(List)));
  Scan1 = Copy;
  Scan2 = list_Cdr(List);

  while (!list_Empty(Scan2)) {
    list_Rplacd(Scan1, list_List(CopyElement(list_Car(Scan2))));
    Scan1 = list_Cdr(Scan1);
    Scan2 = list_Cdr(Scan2);
  }
  return Copy;
}


void list_InsertNext(LIST List, POINTER Pointer)
/**************************************************************
  INPUT:   A list and a pointer to anything.
  RETURNS: A list with Pointer being added at the position that
           follows List.
  SUMMARY: We enqueue the element at position list_Cdr(List);
           The function needs time O(1).
***************************************************************/
{
#ifdef CHECK
  if (Pointer == NULL) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In list_InsertNext: NULL Pointer. ");
    misc_FinishErrorReport();
  }
#endif

  list_Rplacd(List, list_Cons(Pointer, list_Cdr(List)));
}


void list_NMapCar(LIST List, POINTER (*ElementFunc)(POINTER))
/**************************************************************
  INPUT:   A List and a function for the elements.
  RETURNS: The List where all elements are replaced by the result of 
           the function calls of <ElementFunc> to the elements
  CAUTION: The List is not copied !
           The function needs time O(n*f), where <n> is the length
	   of the list and <f> is the time for a call of the
	   element function.
***************************************************************/
{
  LIST Scan;

  for (Scan = List; !list_Empty(Scan); Scan = list_Cdr(Scan))
    list_Rplaca(Scan, ElementFunc(list_Car(Scan)));
}


void list_Apply(void (*Function)(POINTER),  LIST List)
/**************************************************************
  INPUT:   A non-resulting function and a list.
  SUMMARY: Apply the function to all members of the list.
           The function needs time O(n*f), where <n> is the length
	   of the list and <f> is the time for a call of the
	   element function.
***************************************************************/
{
  while (!list_Empty(List)) {
    Function(list_Car(List));
    List = list_Cdr(List);
  }
}


LIST list_Reverse(const LIST List)
/**************************************************************
  INPUT:   A list.
  RETURNS: A new list where the order of the elements is reversed.
  EFFECT:  The function needs time O(n), where <n> is the length
           of the list.
***************************************************************/
{
  LIST ReverseList;
  LIST Scan;
  
  ReverseList = list_Nil();

  for (Scan=List;!list_Empty(Scan);Scan=list_Cdr(Scan)) 
    ReverseList = list_Cons(list_Car(Scan), ReverseList);

  return ReverseList;
}


LIST list_NReverse(LIST List)
/**************************************************************
  INPUT:   A list
  RETURNS: The same list with reversed order of items.
  CAUTION: Destructive.
           The function needs time O(n), where <n> is the length
           of the list.
***************************************************************/
{
  LIST ReverseList;
  LIST Scan1;
  LIST Scan2;
  
  ReverseList = list_Nil();

  for (Scan1=List; !list_Empty(Scan1); Scan1=list_Cdr(Scan1)) 
    ReverseList = list_Cons(list_Car(Scan1),ReverseList);

  for (Scan1=List, Scan2=ReverseList;
       !list_Empty(Scan1);
       Scan1=list_Cdr(Scan1), Scan2=list_Cdr(Scan2)) 
    list_Rplaca(Scan1, list_Car(Scan2));

  list_Delete(ReverseList);
  return List;
}


static __inline__ BOOL list_PointerLower (POINTER A, POINTER B)
{
  return (NAT) A < (NAT) B;
}

LIST list_PointerSort(LIST List)
/**************************************************************
  INPUT:   A list
  RETURNS: The same list where the elements are sorted as pointers.
  EFFECT:  The function needs time O(n log n), where <n> is the length
           of the list.
  CAUTION: Destructive.
***************************************************************/
{
  return list_Sort(List, list_PointerLower);
}


BOOL list_SortedInOrder(LIST L, BOOL (*Test)(POINTER, POINTER)) 
/**************************************************************
  INPUT:   A list, and an ordering function.
  RETURNS: TRUE, if the list is ordered with respect to the
           ordering function, FALSE otherwise.
  EFFECT:  The function needs time O(n), where <n> is the 
           length of the list.
***************************************************************/
{
  LIST Scan1, Scan2;

  if (!(list_Empty(L) || list_Empty(list_Cdr(L)))) {
    Scan1 = L;
    Scan2 = list_Cdr(Scan1);

    /* Scan the list. */
    do {
      /* If all elements are ordered, then every element  */
      /* is <= its successor with respect to the ordering */
      /* function.                                        */
      /* We might have a strictly ordering Test function, */
      /* which implements < instead of <=, so let's test  */
      /* for equality first. */
      if (!Test(list_Car(Scan1), list_Car(Scan2)) &&
	  Test(list_Car(Scan2), list_Car(Scan1)))
	/* It is really strictly greater, so return FALSE. */
	return FALSE;

      Scan1 = list_Cdr(Scan1);
      Scan2 = list_Cdr(Scan1);
    } while (!list_Empty(Scan2));
  }

  return TRUE;
}


LIST list_Merge(LIST List1, LIST List2, BOOL (*Test)(POINTER, POINTER)) 
/**************************************************************
  INPUT:   Two sorted lists List1 and List2, and an ordering function.
  RETURNS: The merged list ordered with respect to the ordering function.
  EFFECT:  The function needs time O(n), where <n> is the length of the list.
***************************************************************/
{

  LIST Scan1, Scan2, Result, ResultStart;

#ifdef CHECK
  if (!list_SortedInOrder(List1, Test)) {
    /* print an error message and exit */
    misc_StartErrorReport();
    misc_ErrorReport("\n In list_Merge: First argument is not sorted.");
    misc_FinishErrorReport();
  }
  else if (!list_SortedInOrder (List2, Test)) {
    /* print an error message and exit */
    misc_StartErrorReport();
    misc_ErrorReport("\n In list_Merge: Second argument is not sorted.");
    misc_FinishErrorReport();
  }
#endif

  if (list_Empty(List1))
    return List2;

  if (list_Empty(List2))
    return List1;

  /* This version is derived from list_NNumberMerge, but it doesn't need */
  /* to allocate and deallocate memory, so it should be more efficient.  */

  /* Use the list with the least element as result list. */
  if (Test(list_Car(List1), list_Car(List2))) {
    ResultStart = List1;
    Scan1       = list_Cdr(List1);
    Scan2       = List2;
  }
  else {
    ResultStart = List2;
    Scan1       = List1;
    Scan2       = list_Cdr(List2);
  }

  /* Result is the last element of the merged list. */

  Result = ResultStart;

  while (!list_Empty(Scan1) && !list_Empty(Scan2)) {
    /* This function doesn't implement stable merging. */
    /* Add another test if you need it.                */

    if (Test(list_Car(Scan1), list_Car(Scan2))) {
      list_Rplacd(Result,Scan1);
      Scan1  = list_Cdr(Scan1);
    }
    else {
      list_Rplacd(Result,Scan2);
      Scan2  = list_Cdr(Scan2);
    }
    Result = list_Cdr(Result);
  }

  if (list_Empty(Scan1))
    list_Rplacd(Result, Scan2);
  else
    list_Rplacd(Result, Scan1);

  return ResultStart;
}


void list_Split(LIST L, LIST *Half1, LIST *Half2) 
/**************************************************************
  INPUT:   A list, and two pointers to lists.
  RETURNS: Nothing.
  EFFECT:  The input list is split in two. <Half1> and 
           <Half2> point to the resulting halves.
	   The input list is destructively changed!
	   If the list length is odd, <Half2> is assigned the
	   bigger part. 
	   The function needs time O(n), where <n> is the 
           length of the input list.
***************************************************************/
{
  /* Adapted code from proofcheck ... MergeSort. */

  LIST SingleStep, DoubleStep, Prev;

  if (list_Empty(L) || list_Empty(list_Cdr(L))) {
    *Half1 = list_Nil();
    *Half2 = L;
  }
  else {
    /* divide list in two halves */
    Prev = L;
    SingleStep = list_Cdr(L);
    DoubleStep = list_Cdr(SingleStep);
    
    while (!list_Empty(DoubleStep) && !list_Empty(list_Cdr(DoubleStep))) {
      Prev       = SingleStep;
      SingleStep = list_Cdr(SingleStep);
      DoubleStep = list_Cdr(list_Cdr(DoubleStep));
    }
    
    *Half1 = L;
    *Half2 = SingleStep;
    list_Rplacd(Prev, list_Nil());
  }
}


LIST list_MergeSort (LIST L, BOOL (*Test) (POINTER, POINTER)) 
/**************************************************************
  INPUT:   A list, and an ordering function.
  RETURNS: The list sorted with respect to the ordering function.
  EFFECT:  The function needs time O((n log n) * t), where 
	   <n> is the length of the input list and <t> is the
	   execution time of the ordering function.
***************************************************************/
{
  LIST Result; 
#ifdef CHECK
  NAT  originallength;

  originallength = list_Length(L);
#endif

  /* Only sort if list has more than one element */
  if (!list_Empty(L) && !list_Empty(list_Cdr(L))) {
    LIST  lowerhalf;
    LIST  greaterhalf;

    LIST *lowerhalfptr;
    LIST *greaterhalfptr;

    lowerhalfptr = &lowerhalf;
    greaterhalfptr = &greaterhalf;

    list_Split(L, lowerhalfptr, greaterhalfptr);

#ifdef CHECK
    if((list_Length(lowerhalf) + list_Length(greaterhalf)) 
       != originallength) {
      /* output an error message and exit */
      misc_StartErrorReport();
      misc_ErrorReport("\n In list_MergeSort: Split lists' total sizes");
      misc_ErrorReport("\n don't match original list's size.");
      misc_FinishErrorReport();
    }
#endif

    lowerhalf   = list_MergeSort(lowerhalf, Test);

    greaterhalf = list_MergeSort(greaterhalf, Test);

#ifdef CHECK
    if((list_Length(lowerhalf) + list_Length(greaterhalf)) 
       != originallength) {
      /* output an error message and exit */
      misc_StartErrorReport();
      misc_ErrorReport("\n In list_MergeSort: Mergesorted lists' total sizes");
      misc_ErrorReport("\n don't match original list's size.");
      misc_FinishErrorReport();
    }
#endif

    Result = list_Merge(lowerhalf, greaterhalf, Test);
    
#ifdef CHECK
    if(list_Length(Result) != originallength) {
      /* output an error message and exit */
      misc_StartErrorReport();
      misc_ErrorReport("\n In list_MergeSort: Merged list's size doesn't match ");
      misc_ErrorReport("\n original list's size.");
      misc_FinishErrorReport();
    }
#endif

  }
  else {
    Result = L;
  }

  return Result;
}


LIST list_InsertionSort(LIST List, BOOL (*Test)(POINTER, POINTER))
/**************************************************************
  INPUT:   A list and a 'less' function on the elements.
  RETURNS: The same list where the elements are sorted with
           respect to Test.
  EFFECT:  The function needs time O(n^2*t), where <n> is the
           length of the list and <t> is the time for the test
	   function.
  CAUTION: Destructive.
***************************************************************/
{
  LIST Scan1,Scan2,Min;
  POINTER Exchange;

  for (Scan1=List; !list_Empty(Scan1); Scan1=list_Cdr(Scan1)) {
    Min = Scan1;
    for (Scan2 = list_Cdr(Scan1); !list_Empty(Scan2); Scan2 = list_Cdr(Scan2))
      if (Test(list_Car(Scan2), list_Car(Min))) {
	Exchange = list_Car(Min);
	list_Rplaca(Min, list_Car(Scan2));
	list_Rplaca(Scan2, Exchange);
      }
  }

  return List;
}


LIST list_Sort(LIST List, BOOL (*Test)(POINTER, POINTER))
/**************************************************************
  INPUT:   A list and a 'less' function on the elements.
  RETURNS: The same list where the elements are sorted with
           respect to Test.
  EFFECT:  The function needs time O((n log n) *t), where <n> 
           is the length of the list and <t> is the time for 
	   the test function.
  CAUTION: Destructive.
***************************************************************/
{
  LIST Result;

#ifdef CHECK
  NAT  originallength;

  originallength = list_Length(List);
#endif

  Result = list_MergeSort(List, Test);

#ifdef CHECK
  if (!list_SortedInOrder(Result, Test)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In list_Sort: list_MergeSort did not sort properly.");
    misc_FinishErrorReport();
  }
  if (list_Length(Result) != originallength) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In list_Sort: list_MergeSort lost elements. ");
    misc_FinishErrorReport();
  }
#endif

  return Result;
}


/* Help Variable used to store a pointer to the numbering function to use
   in element comparisons.
*/
static NAT (*NumberFunction)(POINTER) = NULL;

static __inline__ BOOL list_PointerNumberedLower(POINTER A, POINTER B) 
{
  return (BOOL) (NumberFunction(A) < NumberFunction(B));
}

static __inline__ BOOL list_PointerNumberedLowerOrEqual(POINTER A, POINTER B) 
{
  return (BOOL) (NumberFunction(A) <= NumberFunction(B));
}

static __inline__ BOOL list_PointerNumberedGreater(POINTER A, POINTER B) 
{
  return (BOOL) (NumberFunction(A) > NumberFunction(B));
}

LIST list_NumberSort(LIST List, NAT (*Number)(POINTER))
/**************************************************************
  INPUT:   A list and function mapping elements to numbers.
  RETURNS: The same list where the elements are sorted with
           respect to < and the Number function.
  EFFECT:  The function needs time O((n log n) * f), where <n> 
           is the length of the list and <f> is the time for a 
	   call of the <Number> function.
  CAUTION: Destructive.
***************************************************************/
{
  /* Use number function as temporary variable. It is used as 
     an implicit parameter in list_PointerLower.
     We can't make it an explicit parameter, because of the
     prototype of list_Sort.
  */

  NumberFunction = Number;

  return list_Sort(List, list_PointerNumberedLower);

}


LIST list_GreaterNumberSort(LIST List, NAT (*Number)(POINTER))
/**************************************************************
  INPUT:   A list and function mapping elements to numbers.
  RETURNS: The same list where the elements are sorted with 
           respect to > and the Number function.
  EFFECT:  The function needs time O((n log n) * f), where <n> 
           is the length of the list and <f> is the time for a 
	   call of the <Number> function.
  CAUTION: Destructive.
***************************************************************/
{
  /* Use number function as temporary variable. It is used as 
     an implicit parameter in list_PointerLower.
     We can't make it an explicit parameter, because of the
     prototype of list_Sort.
  */

  NumberFunction = Number;

  return list_Sort(List, list_PointerNumberedGreater);
}


LIST list_NNumberMerge(LIST List1, LIST List2, NAT (*Number)(POINTER))
/**************************************************************
  INPUT:   Two sorted lists and function mapping elements to
           numbers.
  RETURNS: The merge of the lists where the elements are sorted
           with respect to < and the Number function.
  CAUTION: Destructive on both lists.
***************************************************************/
{
  NumberFunction = Number;

  return list_Merge(List1, List2, list_PointerNumberedLowerOrEqual);
}
      

POINTER list_DequeueNext(LIST List)
/**************************************************************
  INPUT:   A list
  RETURNS: A pointer to a dequeued element.
  SUMMARY: We dequeue the element pointed to by list_Cdr(List).
           The function needs time O(1).
***************************************************************/
{
  POINTER Pointer;
  LIST    Memo;

  if (list_Empty(List))
    return NULL;

  Memo = list_Cdr(List);
  if (list_Empty(Memo))
    return NULL;
      
  Pointer = list_Car(Memo);
  list_Rplacd(List, Memo->cdr);
  list_Free(Memo);
  return Pointer;
}


POINTER list_NthElement(LIST List, NAT Number)
/**************************************************************
  INPUT:   A List and a natural number.
  RETURNS: The <Number>th element of the list, NULL otherwise.
  EFFECT:  The function needs time O(Number).
***************************************************************/
{
  while (!list_Empty(List) && --Number > 0)
    List = list_Cdr(List);
  
  if (list_Empty(List))
    return NULL;
  else
    return list_Car(List);
}


void list_DeleteWithElement(LIST List, void (*ElementDelete)(POINTER))
/**************************************************************
  INPUT:   A list and a delete function for the elements.
  RETURNS: Nothing.
  EFFECT:  The list and all its elements are deleted.
           The function needs time O(n*d), where <n> is the length
	   of the list and <d> is the time for the delete function.
***************************************************************/
{
  LIST Scan;

  while (!list_Empty(List)) {
    Scan = list_Cdr(List);
    ElementDelete(list_Car(List));
    list_Free(List);
    List = Scan;
  }
}


NAT list_DeleteWithElementCount(LIST List, void (*ElementDelete)(POINTER))
/**************************************************************
  INPUT:   A List and a delete function for the elements.
  RETURNS: The number of deleted elements.
  EFFECT:  The List and all its elements are deleted.
           The function needs time O(n*d), where <n> is the length
	   of the list and <d> is the time for the delete function.
***************************************************************/
{
  int  Result;
  LIST Scan;

  Result = 0;

  while (!list_Empty(List)) {
    Scan = list_Cdr(List);
    ElementDelete(list_Car(List));
    list_Free(List);
    List = Scan;
    Result++;
  }

  return Result;
}


LIST list_DeleteElement(LIST List, POINTER Element, BOOL (*Test)(POINTER, POINTER))
/**************************************************************
  INPUT:   A list, an element pointer, an equality test for 
           elements
  RETURNS: The list where Element is deleted from List with 
           respect to Test.
  EFFECTS: If List contains Element with respect to EqualityTest,
           Element is deleted from List
  CAUTION: Destructive. Be careful, the first element of a
           list cannot be changed destructively by call by
	   reference.
***************************************************************/
{
  LIST   Scan1,Scan2;

  while (!list_Empty(List) && Test(Element, list_Car(List))) {
    Scan1 = list_Cdr(List);
    list_Free(List);
    List = Scan1;
  }

  if (list_Empty(List))
    return list_Nil();
  
  Scan2 = List;
  Scan1 = list_Cdr(List);

  while (!list_Empty(Scan1)) {
    if (Test(Element, list_Car(Scan1))) {
      list_Rplacd(Scan2, list_Cdr(Scan1));
      list_Free(Scan1);
      Scan1 = list_Cdr(Scan2);
    }
    else {
      Scan2 = Scan1;
      Scan1 = list_Cdr(Scan1);
    }
  }
  return List;
}


LIST list_DeleteElementIf(LIST List, BOOL (*Test)(POINTER))
/**************************************************************
  INPUT:   A list and a test for elements.
  RETURNS: The list where an element is deleted if <Test> on it
           succeeds.
  CAUTION: Destructive. Be careful, the first element of a list
           cannot be changed destructively by call by
	   reference.
***************************************************************/
{
  LIST   Scan1,Scan2;

  while (!list_Empty(List) && Test(list_Car(List))) {
    Scan1 = list_Cdr(List);
    list_Free(List);
    List = Scan1;
  }

  if (list_Empty(List)) 
    return list_Nil();
  
  Scan2 = List;
  Scan1 = list_Cdr(List);

  while (!list_Empty(Scan1)) {
    if (Test(list_Car(Scan1))) {
      list_Rplacd(Scan2, list_Cdr(Scan1));
      list_Free(Scan1);
      Scan1 = list_Cdr(Scan2);
    }
    else {
      Scan2 = Scan1;
      Scan1 = list_Cdr(Scan1);
    }
  }
  return List;
}


LIST list_DeleteElementIfFree(LIST List, BOOL (*Test)(POINTER),
			      void (*Delete)(POINTER))
/**************************************************************
  INPUT:   A list, a test for elements and a delete function
           for elements.
  RETURNS: The list where an element is deleted if <Test> on it
           succeeds.
           The element is deleted with <Delete>.
  CAUTION: Destructive. Be careful, the first element of a list
           cannot be changed destructively by call by reference.
***************************************************************/
{
  LIST   Scan1,Scan2;

  while (!list_Empty(List) && Test(list_Car(List))) {
    Scan1 = list_Cdr(List);
    Delete(list_Car(List));
    list_Free(List);
    List = Scan1;
  }

  if (list_Empty(List))
    return list_Nil();
  
  Scan2 = List;
  Scan1 = list_Cdr(List);

  while (!list_Empty(Scan1)) {
    if (Test(list_Car(Scan1))) {
      Delete(list_Car(Scan1));
      list_Rplacd(Scan2, list_Cdr(Scan1));
      list_Free(Scan1);
      Scan1 = list_Cdr(Scan2);
    }
    else {
      Scan2 = Scan1;
      Scan1 = list_Cdr(Scan1);
    }
  }
  return List;
}



LIST list_DeleteElementFree(LIST List, POINTER Element,
			    BOOL (*Test)(POINTER, POINTER),
			    void (*Free)(POINTER))
/**************************************************************
  INPUT:   A list, an element pointer, an equality test for
           elements and a free function for elements.
  RETURNS: The list where Element is deleted from List with
           respect to Test.
  EFFECTS: If the list contains <Element> with respect to  <Test>,
           <Element> is deleted from the list and freed.
  CAUTION: Destructive. Be careful, the first element of a list
           cannot be changed destructively by call by reference.
***************************************************************/
{
  LIST   Scan1,Scan2;

  while (!list_Empty(List) && Test(Element, list_Car(List))) {
    Scan1 = list_Cdr(List);
    Free(list_Car(List));
    list_Free(List);
    List = Scan1;
  }

  if (list_Empty(List))
    return list_Nil();
  
  Scan2 = List;
  Scan1 = list_Cdr(List);

  while (!list_Empty(Scan1)) {
    if (Test(Element, list_Car(Scan1))) {
      list_Rplacd(Scan2, list_Cdr(Scan1));
      Free(list_Car(Scan1));
      list_Free(Scan1);
      Scan1 = list_Cdr(Scan2);
    }
    else {
      Scan2 = Scan1;
      Scan1 = list_Cdr(Scan1);
    }
  }
  return List;
}


LIST list_DeleteOneElement(LIST List, POINTER Element, BOOL (*Test)(POINTER, POINTER))
/**************************************************************
  INPUT:   A list, an element pointer and an equality test for
           elements.
  RETURNS: The list where at most one element was deleted from
           <List> if the Test between <Element> and the element
	   succeeds.
  EFFECT:  The function needs time O(n*t) in the worst case, and
           time O(t) in the best case, where <n> is the length of
	   the list and t is the time for a call of the test function.
  CAUTION: Destructive. Be careful, the first element of a list
           cannot be changed destructively by call by
	   reference.
	   The memory of the deleted element is not freed.
***************************************************************/
{
  LIST scan1, scan2;

  if (list_Empty(List))
    return List;
  else {
    if (Test(Element, list_Car(List)))
      return list_Pop(List);
  }
  
  for (scan2 = List, scan1 = list_Cdr(List); !list_Empty(scan1);
       scan2 = scan1, scan1 = list_Cdr(scan1)) {
    if (Test(Element, list_Car(scan1))) {
      list_Rplacd(scan2, list_Cdr(scan1));
      list_Free(scan1);
      scan1 = list_Cdr(scan2);
      return List;
    }
  }
  return List;
}


LIST list_PointerDeleteElement(LIST List, POINTER Element)
/**************************************************************
  INPUT:   A list and an element pointer
  RETURNS: The list where Element is deleted from List with respect to
           pointer equality.
  EFFECTS: If <List> contains <Element> with respect to pointer equality,
           <Element> is deleted from <List>.
	   This function needs time O(n), where <n> is the length of the list.
  CAUTION: Destructive. Be careful, the first element of a list cannot
           be changed destructively by call by reference.
***************************************************************/
{
  LIST   Scan1,Scan2;

  while (!list_Empty(List) && Element == list_Car(List)) {
    Scan1 = list_Cdr(List);
    list_Free(List);
    List = Scan1;
  }

  if (list_Empty(List))
    return list_Nil();
  
  Scan2 = List;
  Scan1 = list_Cdr(List);

  while (!list_Empty(Scan1)) {
    if (Element == list_Car(Scan1)) {
      list_Rplacd(Scan2, list_Cdr(Scan1));
      list_Free(Scan1);
      Scan1 = list_Cdr(Scan2);
    }
    else {
      Scan2 = Scan1;
      Scan1 = list_Cdr(Scan1);
    }
  }
  return List;
}

LIST list_PointerDeleteElementFree(LIST List, POINTER Element,
				   void (*Free)(POINTER))
/**************************************************************
  INPUT:   A list, an element pointer and a free function for
           elements.
  RETURNS: The list where Element is deleted from List with
           respect to pointer equality and freed.
  EFFECTS: If List contains Element with respect to pointer
           equality, Element is deleted from List
  CAUTION: Destructive. Be careful, the first element of a list
           cannot be changed destructively by call by 
	   reference.
***************************************************************/
{
  LIST   Scan1,Scan2;
  
  while (!list_Empty(List) && Element == list_Car(List)) {
    Scan1 = list_Cdr(List);
    Free(list_Car(List));
    list_Free(List);
    List = Scan1;
  }

  if (list_Empty(List))
    return list_Nil();
  
  Scan2 = List;
  Scan1 = list_Cdr(List);

  while (!list_Empty(Scan1)) {
    if (Element == list_Car(Scan1)) {
      list_Rplacd(Scan2, list_Cdr(Scan1));
      Free(list_Car(Scan1));
      list_Free(Scan1);
      Scan1 = list_Cdr(Scan2);
    }
    else {
      Scan2 = Scan1;
      Scan1 = list_Cdr(Scan1);
    }
  }
  return List;
}
 

LIST list_PointerDeleteOneElement(LIST List, POINTER Element)
/**************************************************************
  INPUT:   A list and an element pointer.
  RETURNS: The list where one occurrence of Element is deleted from List 
           with respect to pointer equality.
  EFFECTS: If List contains Element with respect to pointer equality,
           Element is deleted from List.
  CAUTION: Destructive. Be careful, the first element of a list cannot
           be changed destructively by call by reference.
***************************************************************/
{
  LIST   Scan1,Scan2;

  if (list_Empty(List))
    return List;
  else {
    if (Element == list_Car(List))
      return list_Pop(List);
  }
  
  Scan2 = List;
  Scan1 = list_Cdr(List);

  while (!list_Empty(Scan1)) {
    if (Element == list_Car(Scan1)) {
      list_Rplacd(Scan2, list_Cdr(Scan1));
      list_Free(Scan1);
      Scan1 = list_Cdr(Scan2);
      return List;
    }
    else {
      Scan2 = Scan1;
      Scan1 = list_Cdr(Scan1);
    }
  }
  return List;     
}


BOOL list_DeleteFromList(LIST* List, POINTER Element)
/**************************************************************
  INPUT:   A list and an element pointer
  RETURNS: TRUE, if Element was deleted; FALSE, otherwise.
  EFFECTS: If List contains Element with respect to pointer equality,
           all occurrences of Element are deleted from List.
  CAUTION: Destructive. Be careful, the first element of a list cannot
           be changed destructively by call by reference.
***************************************************************/
{
  BOOL Found;
  LIST Scan1;

  Found = FALSE;

  while (list_Exist(*List) && Element == list_Car(*List)) {
    Scan1 = list_Cdr(*List);
    list_Free(*List);
    *List = Scan1;
    Found = TRUE;
  }

  if (list_Exist(*List)) {
    LIST Scan2;

    Scan2 = *List;
    Scan1 = list_Cdr(*List);

    while (list_Exist(Scan1)) {
      if (Element == list_Car(Scan1)) {
	list_Rplacd(Scan2, list_Cdr(Scan1));
	list_Free(Scan1);
	Scan1 = list_Cdr(Scan2);
	Found = TRUE;
      } else {
	Scan2 = Scan1;
	Scan1 = list_Cdr(Scan1);
      }
    }
  }

  return Found;
}


BOOL list_DeleteOneFromList(LIST* List, POINTER Element)
/**************************************************************
  INPUT:   A list and an element pointer
  RETURNS: TRUE, if <Element> was deleted; FALSE, otherwise.
  EFFECTS: If <List> contains <Element> with respect to pointer equality,
           the first occurrence of <Element> is deleted from <List>.
  CAUTION: Destructive.
***************************************************************/
{
  if (list_Exist(*List)) {
    LIST Scan1;

    /* special treatment for the first element */
    if (Element == list_Car(*List)) {
      Scan1 = list_Cdr(*List);
      list_Free(*List);
      *List = Scan1;
      return TRUE;
    } else {
      LIST Scan2;

      for (Scan2 = *List, Scan1 = list_Cdr(*List); list_Exist(Scan1); ) {
	if (Element == list_Car(Scan1)) {
	  list_Rplacd(Scan2, list_Cdr(Scan1));
	  list_Free(Scan1);
	  Scan1 = list_Cdr(Scan2);
	  return TRUE;
	} else {
	  Scan2 = Scan1;
	  Scan1 = list_Cdr(Scan1);
	}
      }
    }
  }
  return FALSE;
}


BOOL list_IsSetOfPointers(LIST L)
/**************************************************************
  INPUT:   A list.
  RETURNS: TRUE, if <L> is a set of pointers (without duplicates),
           FALSE, otherwise.
  EFFECT:  The function needs n(n-1)/2 comparisons in the worst case,
           where n is the length of the list. So its time complexity
	   is O(n^2).
***************************************************************/
{
  for ( ; !list_Empty(L); L = list_Cdr(L)) {
    if (list_PointerMember(list_Cdr(L), list_Car(L)))
      return FALSE;
  }
  return TRUE;
}


LIST list_DeleteDuplicates(LIST List, BOOL (*Test)(POINTER, POINTER))
/**************************************************************
  INPUT:   A list, an equality test for elements
  RETURNS: The list where multiple occurrences are deleted.
  CAUTION: Destructive.
***************************************************************/
{
  LIST Scan;
  
  Scan = List;

  while (!list_Empty(Scan)) {
    list_Rplacd(Scan,
		list_DeleteElement(list_Cdr(Scan), list_Car(Scan), Test));
    Scan = list_Cdr(Scan);
  }
  return List;
}


LIST list_DeleteDuplicatesFree(LIST List, BOOL (*Test)(POINTER, POINTER), 
			       void (*Free)(POINTER))
/**************************************************************
  INPUT:   A list, an equality test for elements, and a free
           function for elements.
  RETURNS: The list where multiple occurrences are deleted.
  CAUTION: Destructive and frees all duplicates.
***************************************************************/
{
  LIST Scan;
  
  Scan = List;

  while (!list_Empty(Scan)) {
    list_Rplacd(Scan, list_DeleteElementFree(list_Cdr(Scan), list_Car(Scan), Test, Free));
    Scan = list_Cdr(Scan);
  }
  return List;
}


LIST list_PointerDeleteDuplicates(LIST List)
/**************************************************************
  INPUT:   A list
  RETURNS: The list where multiple occurrences are deleted.
  CAUTION: Destructive.
  EFFECT:  The function needs 
***************************************************************/
{
  LIST Scan;
  
  Scan = List;

  while (!list_Empty(Scan)) {
    list_Rplacd(Scan, list_PointerDeleteElement(list_Cdr(Scan),
						list_Car(Scan)));
    Scan = list_Cdr(Scan);
  }
  return List;
}


LIST list_NPointerUnion(LIST List1, LIST List2)
/**************************************************************
  INPUT:   Two lists.
  RETURNS: Regarding both lists as sets, the union of the sets.
  CAUTION: Destructive.
***************************************************************/
{
  return list_PointerDeleteDuplicates(list_Nconc(List1,List2));
}


LIST list_NUnion(LIST List1, LIST List2, BOOL (*Test)(POINTER, POINTER))
/**************************************************************
  INPUT:   Two lists and an equality test for the elements.
  RETURNS: Regarding both lists as sets, the union of the sets.
  CAUTION: Destructive.
***************************************************************/
{
  return list_DeleteDuplicates(list_Nconc(List1,List2), Test);
}


LIST list_NListTimes(LIST List1, LIST List2)
/**************************************************************
  INPUT:   Two lists of lists.
  RETURNS: The list of combinations of element lists.
  CAUTION: Destroys List1 and List2.
***************************************************************/
{
  LIST Result, Scan1, Scan2;

  Result = list_Nil();

  if (!list_Empty(List2)) {
    for (Scan1=List1; !list_Empty(Scan1); Scan1=list_Cdr(Scan1))
      for (Scan2=List2; !list_Empty(Scan2); Scan2=list_Cdr(Scan2))
	Result = list_Cons(list_Append(((LIST)list_Car(Scan1)),
				       list_Copy((LIST)list_Car(Scan2))),
			   Result);
  }
  list_DeleteWithElement(List1, (void (*)(POINTER))list_Delete);
  list_DeleteWithElement(List2, (void (*)(POINTER))list_Delete);

  return Result;
}


LIST list_NIntersect(LIST List1, LIST List2, BOOL (*Test)(POINTER, POINTER))
/**************************************************************
  INPUT:   Two lists and an equality test for the elements.
  RETURNS: Regarding both lists as sets, the intersection of the sets.
  CAUTION: Destructive on List1
***************************************************************/
{
  LIST Scan1, Scan2;
  
  while (!list_Empty(List1) && !list_Member(List2, list_Car(List1), Test)) {
    Scan1 = list_Cdr(List1);
    list_Free(List1);
    List1 = Scan1;
  }

  if (list_Empty(List1))
    return List1;

  Scan1 = List1;
  Scan2 = list_Cdr(List1);

  while (!list_Empty(Scan2)) {
    if (list_Member(List2, list_Car(Scan2), Test)) {
      Scan2 = list_Cdr(Scan2);
      Scan1 = list_Cdr(Scan1);
    }
    else {
      list_Rplacd(Scan1, list_Cdr(Scan2));
      list_Free(Scan2);
      Scan2 = list_Cdr(Scan1);
    }
  }
  return List1;
}


LIST list_NPointerIntersect(LIST List1, LIST List2)
/**************************************************************
  INPUT:   Two lists.
  RETURNS: Regarding both lists as sets, the intersection of the sets.
  CAUTION: Destructive on List1
***************************************************************/
{
  LIST Scan1, Scan2;
  
  while (!list_Empty(List1) && !list_PointerMember(List2, list_Car(List1))) {
    Scan1 = list_Cdr(List1);
    list_Free(List1);
    List1 = Scan1;
  }

  if (list_Empty(List1))
    return List1;

  Scan1 = List1;
  Scan2 = list_Cdr(List1);

  while (!list_Empty(Scan2)) {
    if (list_PointerMember(List2, list_Car(Scan2))) {
      Scan2 = list_Cdr(Scan2);
      Scan1 = list_Cdr(Scan1);
    }
    else {
      list_Rplacd(Scan1, list_Cdr(Scan2));
      list_Free(Scan2);
      Scan2 = list_Cdr(Scan1);
    }
  }
  return List1;
}


void list_NInsert(LIST List1, LIST List2)
/**************************************************************
  INPUT:   Two lists where <List1> must not be empty.
  EFFECT:  <List2> is destructively concatenated after
           the first element of <List1>.
  RETURNS: void.
  CAUTION: Destructive on List1 and List2.
***************************************************************/
{
  LIST Help;

#ifdef CHECK
  if (list_Empty(List1)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In list_NInsert: Empty list argument.");
    misc_FinishErrorReport();
  }
#endif

  Help = list_Cdr(List1);
  list_Rplacd(List1,List2);
  List2 = List1;

  while (!list_Empty(list_Cdr(List2)))
    List2 = list_Cdr(List2);

  list_Rplacd(List2,Help);
}

      
BOOL list_HasIntersection(LIST List1, LIST List2)
/**************************************************************
  INPUT:   Two lists .
  RETURNS: TRUE iff List1 and List2 have a common element.
  EFFECT:  The function needs time O(n*m), where n and m are the
           lengths of the lists.
***************************************************************/
{ 
  LIST Scan;

  if (!list_Empty(List2)) {
    for (Scan=List1; !list_Empty(Scan); Scan=list_Cdr(Scan))
      if (list_PointerMember(List2, list_Car(Scan)))
	return TRUE;
  }
  return FALSE;
}


LIST list_NPointerDifference(LIST List1, LIST List2)
/**************************************************************
  INPUT:   Two lists.
  RETURNS: The list List1-List2.
  CAUTION: Destructive on List1.
***************************************************************/
{ 
  LIST Scan;

  if (!list_Empty(List1)) {
    for (Scan=List2; !list_Empty(Scan); Scan=list_Cdr(Scan))
      List1 = list_PointerDeleteElement(List1, list_Car(Scan));
  }
  return List1;
}


LIST list_NDifference(LIST List1, LIST List2, BOOL (*Test)(POINTER, POINTER))
/**************************************************************
  INPUT:   Two lists and an equality test for elements.
  RETURNS: The list List1-List2 wrt. <Test>.
  CAUTION: Destructive on List1.
***************************************************************/
{ 
  LIST Scan;
  
  if (!list_Empty(List1)) {
    for (Scan=List2; !list_Empty(Scan); Scan=list_Cdr(Scan))
      List1 = list_DeleteElement(List1, list_Car(Scan), Test);
  }
  return List1;
}


LIST list_NMultisetDifference(LIST List1, LIST List2, BOOL (*Test)(POINTER, POINTER))
/**************************************************************
  INPUT:   Two lists representing multisets and an equality
           test for elements.
  RETURNS: The multiset difference List1-List2 wrt. <Test>.
  CAUTION: Destructive on List1. The memory of deleted
           elements is not freed.
***************************************************************/
{
  LIST scan;
  /* Delete equal arguments */
  if (!list_Empty(List1)) {
    for (scan = List2; !list_Empty(scan); scan = list_Cdr(scan))
      /* Delete at most one element from List1 equal to */
      /* the actual element of List2. */
      List1 = list_DeleteOneElement(List1, list_Car(scan), Test);
  }
  return List1;
}

    
BOOL list_PointerReplaceMember(LIST List, POINTER Old, POINTER New)
/**************************************************************
  INPUT:   A list, a pointer to an old element, a pointer to a new element
  RETURNS: TRUE iff <Old> was replaced.
  EFFECT:  The first occurrence of <Old> in the list is replaced by <New>.
***************************************************************/
{
  while (!list_Empty(List)) {
    if (Old == list_Car(List)) {
      list_Rplaca(List, New);
      return TRUE;
    }
    List = list_Cdr(List);
  }
  return FALSE;
}   

  
void list_DeleteAssocListWithValues(LIST List, void (*ValueDelete)(POINTER))
/**************************************************************
  INPUT:   An association list and a delete function for the values.
  RETURNS: void.
  EFFECT:  The assoc list and its values are deleted.
***************************************************************/
{
  LIST Scan;

  for (Scan=List;!list_Empty(Scan);Scan = list_Cdr(Scan)) {
    ValueDelete(list_PairSecond(list_Car(Scan)));
    list_PairFree(list_Car(Scan));
  }

  list_Delete(List);
}


POINTER list_AssocListValue(LIST List, POINTER Key)
/**************************************************************
  INPUT:   An association list and a key.
  RETURNS: The value for <key> in the list. If <key> is not
           contained, NULL.
***************************************************************/
{
  LIST Scan;

  for (Scan=List;!list_Empty(Scan);Scan = list_Cdr(Scan))
    if (Key == list_PairFirst(list_Car(Scan)))
      return list_PairSecond(list_Car(Scan));

  return NULL;
}


LIST list_AssocListPair(LIST List, POINTER Key)
/**************************************************************
  INPUT:   An association list and a key.
  RETURNS: The  (<key>.<value) in the list. If <key> is not
           contained, the NULL pair.
***************************************************************/
{
  LIST Scan;

  for (Scan=List;!list_Empty(Scan);Scan = list_Cdr(Scan))
    if (Key == list_PairFirst(list_Car(Scan)))
      return list_Car(Scan);

  return list_PairNull();
}


LIST list_MultisetDistribution(LIST Multiset) 
/**************************************************************
  INPUT:   A list representing a multiset.
  RETURNS: The associative list of pairs (<element>.<occurrences>) 
           representing the distribution of elements in the list.
	   If the input multiset is empty, the NULL pair.
***************************************************************/
{
  LIST Distribution;
  LIST Scan;

  Distribution = list_PairNull();

  for (Scan = Multiset; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    LIST    Count;
    POINTER Element;
    int     Occurences;

    Element = list_Car(Scan);
    Count   = list_AssocListPair(Distribution, Element);

    if (Count != list_PairNull()) {
      Occurences = (int) list_PairSecond(Count);
      list_PairRplacSecond(Count, (POINTER) (Occurences + 1));
    }
    else {
      Distribution = list_AssocCons(Distribution, Element, (POINTER) 1);
    }
  }

  return Distribution;
}


int list_CompareElementDistribution(LIST LeftPair, LIST RightPair) 
/**************************************************************
  INPUT:   Two lists, representing single element frequency 
           counts.
  RETURNS: 1 if left > right, -1 if left < right, 0 otherwise.
  EFFECT:  Compares two element frequencies.
***************************************************************/
{
  if ((int) list_PairSecond(LeftPair) < (int) list_PairSecond(RightPair)) {
    return -1;
  }
  else if ((int) list_PairSecond(LeftPair) > (int) list_PairSecond(RightPair)) {
    return 1;
  }

  return 0;
}


BOOL list_CompareElementDistributionLEQ(LIST LeftPair, LIST RightPair) {
/**************************************************************
  INPUT:   Two lists, representing single element frequency 
           counts.
  RETURNS: TRUE if left <= right, FALSE otherwise.
  EFFECT:  Compares two element frequencies.
***************************************************************/
  return (list_CompareElementDistribution(LeftPair, RightPair) <= 0);
}


static int list_CompareDistributions(LIST Left, LIST Right) 
/**************************************************************
  INPUT:   Two lists, representing element distributions.
  RETURNS: 1 if left > right, -1 if left < right, 0 otherwise.
  EFFECT:  Compares the two distributions by comparing the 
           element frequencies from left to right.
  CAUTION: Expects the distributions to be sorted.
***************************************************************/
{
  LIST scan, scan2;
  int result;

  result = 0;

  scan  = Left;
  scan2 = Right;

  /* Compare distributions. */

  while ( !(list_Empty(scan) || list_Empty(scan2))) {
    result = list_CompareElementDistribution(list_Car(scan), list_Car(scan2));
    if (result != 0) {
      break;
    }
    
    scan  = list_Cdr(scan);
    scan2 = list_Cdr(scan2);
  }

  /* If the result is 0, and a distribution still
     has elements left, it is declared to be greater.
  */
  if (result == 0) {
    if (list_Empty(scan) && !list_Empty(scan2))
      result = -1;
    else if (!list_Empty(scan) && list_Empty(scan2))
      result = 1;
  }

  return result;
}


int list_CompareMultisetsByElementDistribution(LIST Left, LIST Right) 
/**************************************************************
  INPUT:   Two lists, representing multisets.
  RETURNS: 1 if left > right, -1 if left < right, 0 otherwise.
  EFFECT:  Compares two multisets by counting their element 
           frequencies, sorting them, and comparing the 
	   resulting multisets over natural numbers.
***************************************************************/
{
  LIST lmsd, rmsd; /* multiset distributions. */
  int result;

  /* Convert multiset of elements into a
     multiset of pairs (element, occurrences).
  */

  lmsd = list_MultisetDistribution(Left);
  rmsd = list_MultisetDistribution(Right);

  /* Sort multiset distributions in order 
     to make them comparable. 
   */

  lmsd = list_Sort(lmsd, (BOOL (*) (POINTER, POINTER)) list_CompareElementDistributionLEQ);
  rmsd = list_Sort(rmsd, (BOOL (*) (POINTER, POINTER)) list_CompareElementDistributionLEQ);

  result = list_CompareDistributions(lmsd, rmsd);

  list_DeleteDistribution(lmsd);
  list_DeleteDistribution(rmsd);

  return result;
}


NAT list_Length(LIST List)
/**************************************************************
  INPUT:   A List.
  RETURNS: The number of elements..
  EFFECT:  The function needs time O(n), where <n> is the length
           of the list.
***************************************************************/
{
  NAT Result;

  Result = 0;

  while (!list_Empty(List)) {
    Result++;
    List = list_Cdr(List);
  }

  return Result;
}


NAT list_Bytes(LIST List)
/**************************************************************
  INPUT:   A List.
  RETURNS: The number of Bytes occupied by the list structure of <List>
  EFFECT:  the function needs time O(n), where <n> is the length
           of the list.
***************************************************************/
{
  return (list_Length(List)*sizeof(LIST_NODE));
}
