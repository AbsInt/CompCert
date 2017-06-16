/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                 SIMPLE HASHING                         * */
/* *                                                        * */
/* *  $Module:   HASH                                       * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1999, 2000, 2001                  * */
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

#include "hash.h"

/**************************************************************/
/* Global Variables                                           */
/**************************************************************/

LIST hash_TABLE[hash__SIZE];


/**************************************************************/
/* Functions                                                  */
/**************************************************************/

void hash_Init(void)
{
  int i;
  
  for (i = 0; i < hash__SIZE; i++)
    hash_PutList(i, list_Nil());
}

void hash_Reset(void)
{
  int  i;
  LIST Scan;
  
  for (i = 0; i < hash__SIZE; i++) {
    Scan = hash_List(i);
    while (!list_Empty(Scan)) {
      list_Free(list_Car(Scan));
      Scan = list_Cdr(Scan);
    }
    list_Delete(hash_List(i));
    hash_PutList(i, list_Nil());
  }
}

void hash_ResetWithValue(void (*ValueDelete)(POINTER))
{
  int  i;
  LIST Scan;
  
  for (i = 0; i < hash__SIZE; i++) {
    Scan = hash_List(i);
    while (!list_Empty(Scan)) {
      ValueDelete(list_PairSecond(list_Car(Scan)));
      list_Free(list_Car(Scan));
      Scan = list_Cdr(Scan);
    }
    list_Delete(hash_List(i));
    hash_PutList(i, list_Nil());
  }
}

POINTER hash_Get(POINTER key)
{
  LIST Scan;

  Scan = hash_List(hash_Index(key));
  
  while (!list_Empty(Scan)) {
    if (list_PairFirst(list_Car(Scan)) == key)
      return list_PairSecond(list_Car(Scan));
    Scan = list_Cdr(Scan);
  }

  return NULL;
}
