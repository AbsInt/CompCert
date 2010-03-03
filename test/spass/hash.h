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

#ifndef _HASH_
#define _HASH_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "list.h"


/**************************************************************/
/* Structures                                                 */
/**************************************************************/

#define hash__SIZE 29            /* a prime */

/* Each Entry is a list of pairs <key,value> */
extern LIST hash_TABLE[hash__SIZE];


/**************************************************************/
/* Inline Functions                                           */
/**************************************************************/

static __inline__ NAT hash_Index(POINTER Key)
{
  return (NAT)Key % hash__SIZE;
}

static __inline__ LIST hash_List(NAT Index)
{
  return hash_TABLE[Index];
}

static __inline__ void hash_PutList(NAT Index, LIST List)
{
  hash_TABLE[Index] = List;
}

static __inline__ void hash_Put(POINTER Key, POINTER Value)
{
  hash_PutList(hash_Index(Key), list_Cons(list_PairCreate((POINTER)Key, Value),
					  hash_List(hash_Index(Key))));
}


/**************************************************************/
/* Functions                                                  */
/**************************************************************/

void    hash_Init(void);
void    hash_Reset(void);
void    hash_ResetWithValue(void (*)(POINTER));

POINTER hash_Get(POINTER);


#endif


