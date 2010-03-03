/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                       HASHING                          * */
/* *                                                        * */
/* *  $Module:   HASHARRAY                                  * */ 
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

#ifndef _HASHARRAY_
#define _HASHARRAY_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "list.h"

/**************************************************************/
/* Structures                                                 */
/**************************************************************/

#define hsh__SIZE 29            /* a prime */

/* Each Entry is a list of pairs <key,list of values> */

typedef LIST* HASH;

void hsh_Check(HASH H);

/**************************************************************/
/* Inline Functions                                           */
/**************************************************************/

static __inline__ unsigned long hsh_Index(POINTER Key)
/**************************************************************
  INPUT:   A pointer
  RETURNS: A key for the hasharray
***************************************************************/
{
  return (unsigned long)Key % hsh__SIZE;
}

static __inline__ void hsh_Put(HASH H, POINTER Key, POINTER Value)
/**************************************************************
  INPUT:   A hasharray, a pointer used as key and a pointer to a data item
  EFFECT:  Add Value to the list of data items associated with the key,
           if it isn't a member already
***************************************************************/
{
  LIST Scan, Pair;
  unsigned long HashKey;
  HashKey = hsh_Index(Key);
  for (Scan = H[HashKey]; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    Pair = list_Car(Scan);
    if (list_PairFirst(Pair) == Key) {
      if (!list_PointerMember(list_PairSecond(Pair), Value))
	list_Rplacd(Pair, list_Cons(Value, list_PairSecond(Pair)));
#ifdef CHECK
      hsh_Check(H);
#endif
      return;
    }
  }
  H[HashKey] = list_Cons(list_PairCreate(Key, list_List(Value)), H[HashKey]);
#ifdef CHECK
  hsh_Check(H);
#endif
}

static __inline__ void hsh_PutList(HASH H, POINTER Key, LIST List)
/**************************************************************
  INPUT:   A hasharray, a pointer used as key and a list of data items
  EFFECT:  Add the list to the list of data items associated with the key,
           and delete all duplicates.
***************************************************************/
{
  LIST Scan, Pair;
  unsigned long HashKey;

  HashKey = hsh_Index(Key);
  for (Scan = H[HashKey]; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    Pair = list_Car(Scan);
    if (list_PairFirst(Pair) == Key) {
      list_Rplacd(Pair, list_Nconc(list_PairSecond(Pair), List));
#ifdef CHECK
      hsh_Check(H);
#endif
      return;
    }
  }
  H[HashKey] = list_Cons(list_PairCreate(Key, List), H[HashKey]);
#ifdef CHECK
  hsh_Check(H);
#endif
}

static __inline__ void hsh_PutListWithCompareFunc(HASH H, POINTER Key, 
						  LIST List,
						  BOOL (*Test)(POINTER, POINTER), 
						  unsigned long (*HashFunc)(POINTER))
/**************************************************************
  INPUT:   A hasharray, a pointer used as key, a list of data
           items, a test function for key equality and a
	   hashing function.
  EFFECT:  Add the list to the list of data items associated
           with the key, and delete all duplicates.
***************************************************************/
{
  LIST Scan, Pair;
  unsigned long HashKey;

  HashKey = (unsigned long) HashFunc(Key);
  for (Scan = H[HashKey]; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    Pair = (LIST) list_Car(Scan);
    if (Test(list_PairFirst(Pair), Key)) {
      list_Rplacd(Pair, list_Nconc(list_PairSecond(Pair), List));
#ifdef CHECK
      hsh_Check(H);
#endif
      return;
    }
  }
  H[HashKey] = list_Cons(list_PairCreate(Key, List), H[HashKey]);
#ifdef CHECK
  hsh_Check(H);
#endif
}

static __inline__ LIST hsh_Get(HASH H, POINTER Key)
/**************************************************************
  INPUT:   A hasharray and a pointer used as key
  RETURNS: The list of data items associated with the key
***************************************************************/
{
  LIST Scan, Pair;

  for (Scan = H[hsh_Index(Key)]; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    Pair = list_Car(Scan);
    if (list_PairFirst(Pair) == Key)
      return list_PairSecond(Pair);
  }
  return NULL;
}

static __inline__ void hsh_DelItem(HASH H, POINTER Key)
/**************************************************************
  INPUT:   A hasharray and a pointer used as key
  RETURNS: The information associated with the key is deleted
***************************************************************/
{
  LIST Scan, Pair;
  unsigned long k;

  k = hsh_Index(Key);
  for (Scan = H[k]; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    Pair = list_Car(Scan);
    if (list_PairFirst(Pair) == Key) {
      list_Delete(list_PairSecond(Pair));
      list_PairFree(Pair);
      H[k] = list_PointerDeleteElement(H[k], Pair);
      return;
    }
  }
}

static __inline__ LIST hsh_GetWithCompareFunc(HASH H, POINTER Key,
					      BOOL (*Test)(POINTER, POINTER),
					      unsigned long (*HashFunc)(POINTER))
/**************************************************************
  INPUT:   A hasharray, a pointer used as key, a compare function
           for keys and a hash function for keys.
  RETURNS: The list of data items associated with the key
***************************************************************/
{
  LIST Scan, Pair;

  for (Scan = H[HashFunc(Key)]; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    Pair = list_Car(Scan);
    if (Test(list_PairFirst(Pair), Key))
      return list_PairSecond(Pair);
  }
  return NULL;
}


static __inline__ unsigned long hsh_StringHashKey(const char* Label)
{
  unsigned long i, s;
  s = 0;
  for (i = 0; i <= strlen(Label); i++)
    s += Label[i];
  s = s % hsh__SIZE;
  return s;
}

/**************************************************************/
/* Functions                                                  */
/**************************************************************/

HASH hsh_Create(void);
void hsh_Reset(HASH H);
void hsh_Delete(HASH H);
LIST hsh_GetAllEntries(HASH H);

#endif


