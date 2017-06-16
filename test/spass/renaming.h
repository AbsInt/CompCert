/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                   RENAMING                             * */
/* *                                                        * */
/* *  $Module:   REN                                        * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1997, 1998, 2000, 2001            * */
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


#ifndef _SPASS_RENAMING_
#define _SPASS_RENAMING_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "misc.h"
#include "foldfg.h"
#include "unify.h"
#include "vector.h"

/**************************************************************/
/* Data Structures and Constants                              */
/**************************************************************/

typedef struct {
  TERM   hit;
  LIST   matches;
  BOOL   general;
  int    polarity;
} *RENAMING, RENAMING_NODE;

/* <hit>       is the formula that has a positive benefit              */
/* <matches>   are further matches of <hit> in the overall formula     */
/* <general>   is TRUE iff the <hit> formula must not be replaced but  */
/*             is a generalzation of the matches formulae that are to  */
/*             be replaced                                             */
/* <polarity>  is the most general polarity of <hit> and all <matches> */

 
/**************************************************************/
/* Functions                                                 */
/**************************************************************/


static __inline__ int ren_OverallPolarity(RENAMING ren)
{
  return ren->polarity;
}

static __inline__ TERM ren_Hit(RENAMING ren)
{
  return ren->hit;
}

static __inline__ LIST ren_Matches(RENAMING ren)
{
  return ren->matches;
}

static __inline__ BOOL ren_General(RENAMING ren)
{
  return ren->general;
}

static __inline__ void ren_SetMatches(RENAMING ren, LIST matches)
{
  ren->matches = matches;
}

static __inline__ void ren_SetHit(RENAMING ren, TERM hit)
{
  ren->hit = hit;
}

static __inline__ void ren_SetOverallPolarity(RENAMING ren, int polarity)
{
  ren->polarity = polarity;
}

static __inline__ void ren_SetGeneral(RENAMING ren, BOOL general)
{
  ren->general = general;
}



static __inline__ RENAMING ren_Create(TERM hit, LIST matches, int polarity)
/**************************************************************
  INPUT:   A formula, a list of further matching formulae
           and the overall polarity of the <hit> and the further <matches>.
  RETURNS: A new renaming object, which is initialized.
           General is set to false.
  MEMORY:  Allocates memory for the RENAMING.
***************************************************************/
{
  RENAMING Result;

  Result           = (RENAMING)memory_Malloc(sizeof(RENAMING_NODE));
  Result->hit      = hit;
  Result->matches  = matches;
  Result->polarity = polarity;
  Result->general  = FALSE;

  return Result;
}

static __inline__ void ren_Delete(RENAMING ren)
/**************************************************************
  INPUT:   A renaming.
  RETURNS: void.
  MEMORY:  Frees memory for the RENAMING and the matches list.
           Formulae are not deleted.
***************************************************************/
{
  list_Delete(ren->matches);
  memory_Free(ren,sizeof(RENAMING_NODE));
}


/**************************************************************/
/* Function Prototypes                                        */
/**************************************************************/

void ren_Init(void);
TERM ren_Rename(TERM, PRECEDENCE, LIST*,BOOL, BOOL);
void ren_PrettyPrint(RENAMING);

#endif
