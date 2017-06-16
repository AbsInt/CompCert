/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *             SIGNATURE TABLE                            * */
/* *                                                        * */
/* *  $Module:   TABLE                                      * */ 
/* *                                                        * */
/* *  Copyright (C) 1999, 2000, 2001 MPI fuer Informatik    * */
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
/* $Revision: 21527 $                                         * */
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

/* module manages signature tables i. e. tables of terms (including the empty */
/* term NULL) where the lookup key is the tuple of top symbol index and       */
/* arguments' equivalence classes with respect to a partition p, the          */
/* _p-signature_ (sigtab_Index(top symbol), [arg 1] , ..., [arg n] )          */
/*                                                 p              p           */

#ifndef _TABLE_
#define _TABLE_


/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "term.h"
#include "partition.h"


/**************************************************************/
/* Basic types                                                */
/**************************************************************/

typedef struct termarray {
  TERM term;
  int stamp;
  struct termarray *child;
} *TERMARRAY;

typedef struct table {
  TERMARRAY ta, *pos;
  int *posstamp, stampcounter, opbound, varbound, termbound;
}
*TABLE;

/* a signature table is an "array of terms allocated by need" (i. e. a tree   */
/* where the nodes of the same layer represent array entries with the same    */
/* dimension), an array of positions in this "array", stamps for the          */
/* positions, the stamp counter and bounds for the operator symbol, variable   */
/* and term indices of the terms to be stored in the signature table (i. e.   */
/* for every such term its top symbol index has to be in [1, opbound] and the */
/* term numbers of its arguments in [0, termbound] - or its variable index in */
/* [1, varbound] if it is a variable)                                         */


/**************************************************************/
/* Prototypes                                                 */
/**************************************************************/

TABLE table_Null(void);
TABLE table_Create(int, int, int);
void  table_Free(TABLE);
TABLE table_Init(TABLE, int, int, int);
TERM  table_QueryAndEnter(TABLE, PARTITION, TERM);
TABLE table_Delete(TABLE, TERM);


#endif

