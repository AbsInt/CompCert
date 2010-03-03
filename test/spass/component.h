/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *               COMPONENTS OF CLAUSES                    * */
/* *                                                        * */
/* *  $Module:   COMPONENT                                  * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 2000, 2001 MPI fuer Informatik    * */
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

#ifndef _COMPONENT_
#define _COMPONENT_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "list.h"

/**************************************************************/
/* Structures                                                 */
/**************************************************************/

typedef struct cliteral {
  BOOL  used;              /* Flag if the index is already used            */
  int   litindex;          /* Index of the literal in the original clause  */ 
  LIST  litvarlist;        /* List of variables of the literal             */
} *CLITERAL, CLITERAL_NODE;


typedef struct litptr {
  CLITERAL *litptr;             /* Array of Pointer to literals           */
  int     length;              /* Number of literal in the array *litptr */
} *LITPTR, LITPTR_NODE;

/**************************************************************/
/* Macros                                                     */
/**************************************************************/

static __inline__ BOOL literal_GetUsed(CLITERAL C)
{
  return C->used;
}

static __inline__ int literal_GetLitIndex(CLITERAL C)
{
  return C->litindex;
}

static __inline__ LIST literal_GetLitVarList(CLITERAL C)
{
  return C->litvarlist;
}

static __inline__ void literal_PutUsed(CLITERAL C,BOOL Bool)
{
  C->used = Bool;
}

static __inline__ void literal_PutLitIndex(CLITERAL C, int I)
{
  C->litindex = I;
}

static __inline__ void literal_PutLitVarList(CLITERAL C, LIST L)
{
  C->litvarlist = L;
}

static __inline__ CLITERAL litptr_Literal(LITPTR C, int I)
{
  return C->litptr[I];
}

static __inline__ void litptr_SetLiteral(LITPTR LP, int I, CLITERAL CL)
{
  LP->litptr[I] = CL;
}


static __inline__ int litptr_Length(LITPTR C)
{
  return C->length;
}

static __inline__ void litptr_SetLength(LITPTR C, int n)
{
  C->length = n;
}

static __inline__ void litptr_IncLength(LITPTR C)
{
  (C->length)++;
}

static __inline__ void literal_Free(CLITERAL Lit)
{
  memory_Free(Lit, sizeof(CLITERAL_NODE));
}


/**************************************************************/
/* Functions on a Component and on a Literal                  */
/**************************************************************/

CLITERAL literal_Create(BOOL, int, LIST);
void     literal_Delete(CLITERAL);

LITPTR   litptr_Create(LIST, LIST);
void     litptr_Delete(LITPTR);
void     litptr_Print(LITPTR);
BOOL     litptr_AllUsed(LITPTR);


#endif
