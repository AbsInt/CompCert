/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *             PARTITION                                  * */
/* *                                                        * */
/* *  $Module:   PARTITION                                  * */ 
/* *                                                        * */
/* *  Copyright (C) 1999, 2001 MPI fuer Informatik          * */
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


/**************************************************************/
/* Include                                                    */
/**************************************************************/

#include "partition.h"


/**************************************************************/
/* Inline functions                                           */
/**************************************************************/

static __inline__ ECLASS part_GetClass(PARTITION p, ELEMENT e)
{
  return p[e];
}


static __inline__ PARTITION part_SetClass(PARTITION p, ELEMENT e, ECLASS c)
{
  p[e] = c;
  return p;
}


static __inline__ int part_GetClassSize(PARTITION p, ELEMENT e)
{
  return p[p[part_CARD] + e];
}


static __inline__ PARTITION part_SetClassSize(PARTITION p, ELEMENT e, int
    classsize)
{
  p[p[part_CARD] + e] = classsize;
  return p;
}


static __inline__ int part_GetStamp(PARTITION p, ELEMENT e)
{
  return p[-part_HEAD - 1 - e];
}


static __inline__ PARTITION part_SetStamp(PARTITION p, ELEMENT e, int stamp)
{
  p[-part_HEAD - 1 - e] = stamp;
  return p;
}


static __inline__ BOOL part_Stamped(PARTITION p, ELEMENT e)
{
  return part_GetStamp(p, e) == p[part_STAMPCOUNTER];
}


static __inline__ ELEMENT part_DelayedInit(PARTITION p, ELEMENT e)
/***************************************************************
  RETURNS: the (now stamped) element
  EFFECT:  establishes the equivalence class {e} in p, thus
	   partially initializing p
***************************************************************/
{
  if (!part_Stamped(p, e)) {
    part_SetClass(p, e, -e - 1);  /* representative e (>= 0) of {e} is coded */
				  /* as -e - 1 (< 0)                         */
    part_SetClassSize(p, e, 1);
    part_SetStamp(p, e, p[part_STAMPCOUNTER]);
  }
  return e;
}


/**************************************************************/
/* Functions                                                  */
/**************************************************************/

PARTITION part_Create(int size)
/****************************************************************
  RETURNS: the initial partition {{0}, {1}, {2}, ..., {size - 1}}
	   of the set {0, 1, 2, ..., size - 1}
****************************************************************/
{
  PARTITION result;

#ifdef CHECK
  if (size < 0) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In part_Create: negative size %d.", size);
    misc_FinishErrorReport();
  }
#endif

  result = (PARTITION) memory_Calloc(size * 3 + part_HEAD, sizeof(int))
             + size + part_HEAD;  /* move pointer to the middle of the array */
				  /* to allow negative indices               */
  result[part_CARD]         = size;
  result[part_ALLOC]        = size * 3 + part_HEAD;
  result[part_STAMPCOUNTER] = 1;
  return result;
}


PARTITION part_Init(PARTITION p, int size)
/****************************************************************
  RETURNS: the initial partition {{0}, {1}, {2}, ..., {size - 1}}
           of the set {0, 1, 2, ..., size - 1}
  EFFECT:  stores the initial partition to p if it's big enough,
           otherwise creates a new partition, therefore
  CAUTION: must be called inside an assignment like:
             p = part_Init(p, ...)
****************************************************************/
{
  int alloc, i;

#ifdef CHECK
  if (size < 0) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In part_Init: negative size %d.", size);
    misc_FinishErrorReport();
  }
#endif

  alloc = (p[part_ALLOC] - part_HEAD) / 3;
  if (size > alloc) {
    part_Free(p);
    p = part_Create(size);
  }
  else {
    p[part_CARD] = size;
    p[part_STAMPCOUNTER]++;

    /* if a stamp overflow occurs, reinit stamps: */
    if (p[part_STAMPCOUNTER] <= 0) {
      for (i = 0; i < alloc; i++)
        part_SetStamp(p, i, 0);
      p[part_STAMPCOUNTER] = 1;
    }

  }
  return p;
}


static ELEMENT part_NF(PARTITION p, ELEMENT e)
/***************************************************************
  RETURNS: the normal form element of the class [e]; this is an 
           element of [e] that sometimes differ from the
           representative
  EFFECT:  makes the normal form to the direct parent of all
	   elements visited on the search path from e to this
	   normal form ("path compression")
***************************************************************/
{
  ELEMENT nf, aux;

#ifdef CHECK
  if (!part_Element(p, e)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In part_NF: %d not in partitioned set.", e);
    misc_FinishErrorReport();
  }
#endif

  nf = e;
  while (part_GetClass(p, part_DelayedInit(p, nf)) >= 0)
    nf = part_GetClass(p, nf);

  /* path compression: */
  while (e != nf) {
    aux = part_GetClass(p, e);
    part_SetClass(p, e, nf);
    e = aux;
  }

  return nf;
}


ECLASS part_Find(PARTITION p, ELEMENT e)
/***************************************************************
  RETURNS: (the representative of) class [e]
***************************************************************/
{

#ifdef CHECK
  if (!part_Element(p, e)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In part_Find: %d not in partitioned set.", e);
    misc_FinishErrorReport();
  }
#endif

  return -part_GetClass(p, part_NF(p, e)) - 1;
    /* representative e is coded as -e - 1 (cf. part_DelayedInit) */
}


PARTITION part_Union(PARTITION p, ECLASS c1, ECLASS c2)
/***************************************************************
  RETURNS: the union of the classes
  EFFECT:  the representative of c1 is the representative of the
           union
***************************************************************/
{
  ELEMENT nf1, nf2, aux;

#ifdef CHECK
  if (!part_Element(p, c1)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In part_Union: first class %d not in partitioned set.",
      c1);
    misc_FinishErrorReport();
  }
  if (!part_Element(p, c2)) {
    misc_StartErrorReport();
    misc_ErrorReport
      ("\n In part_Union: second class %d not in partitioned set.", c2);
    misc_FinishErrorReport();
  }
#endif

  nf1 = part_NF(p, c1);
  nf2 = part_NF(p, c2);
  if (nf1 != nf2) {

    /* make [nf1] the bigger (or at least not smaller) class: */
    if (part_GetClassSize(p, nf1) < part_GetClassSize(p, nf2)) {
      aux = nf1;
      nf1 = nf2;
      nf2 = aux;
      part_SetClass(p, nf1, part_GetClass(p, nf2));
      part_SetClass(p, -part_GetClass(p, nf2) - 1, nf1);
    }

    part_SetClass(p, nf2, nf1);
    part_SetClassSize(p, nf1,
		      part_GetClassSize(p, nf1) + part_GetClassSize(p, nf2));
  }
  return p;
}

