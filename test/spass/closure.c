/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *             CONGRUENCE CLOSURE ALGORITHM               * */
/* *                                                        * */
/* *  $Module:   CLOSURE                                    * */
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


/**************************************************************/
/* Include                                                    */
/**************************************************************/

#include "closure.h"


/**************************************************************/
/* Global constants and variable                              */
/**************************************************************/

/* standard initial size of a closure's stacks */
static const int cc_RASSTDSIZE = 64;
/* cc_RASSTDSIZE * ld(cc_RASSTDSIZE) */
static const int cc_SIZELDSIZE = 384;
/* the virtual term "true" has number 0 */
static const ELEMENT cc_NOOFTRUE = 0;


static struct {
  PARTITION partition;
  TABLE table;
  RAS car, cdr, size, pending, combine;
} cc_CLOSURE;

/* the closure consists of a partition, a signature table, stacks for         */
/* (circularly linked) lists of predecessors of equivalence classes (i. e.    */
/* terms with direct subterms from this class), for the sizes of these lists, */
/* for pending terms (the ones to be worked off) and for terms to be combined */
/* in the same equivalence class                                              */


/**************************************************************/
/* Inline functions                                           */
/**************************************************************/

static __inline__ PARTITION cc_GetPartition(void)
{
  return cc_CLOSURE.partition;
}


static __inline__ void cc_SetPartition(PARTITION partition)
{
  cc_CLOSURE.partition = partition;
}


static __inline__ TABLE cc_GetTable(void)
{
  return cc_CLOSURE.table;
}


static __inline__ void cc_SetTable(TABLE table)
{
  cc_CLOSURE.table = table;
}


static __inline__ RAS cc_GetCars(void)
{
  return cc_CLOSURE.car;
}


static __inline__ TERM cc_GetCar(int index)
{
  return (TERM) ras_Get(cc_GetCars(), index);
}


static __inline__ void cc_SetCars(RAS car)
{
  cc_CLOSURE.car = car;
}


static __inline__ RAS cc_GetCdrs(void)
{
  return cc_CLOSURE.cdr;
}


static __inline__ int cc_GetCdr(int index)
{
  return (int) ras_Get(cc_GetCdrs(), index);
}


static __inline__ void cc_SetCdrs(RAS cdr)
{
  cc_CLOSURE.cdr = cdr;
}


static __inline__ void cc_SetCdr(int index, int cdr)
{
  ras_Set(cc_GetCdrs(), index, (POINTER) cdr);
}


static __inline__ RAS cc_GetSizes(void)
{
  return cc_CLOSURE.size;
}


static __inline__ int cc_GetSize(int index)
{
  return (int) ras_Get(cc_GetSizes(), index);
}


static __inline__ void cc_SetSizes(RAS size)
{
  cc_CLOSURE.size = size;
}


static __inline__ void cc_SetSize(int index, int size)
{
  ras_Set(cc_GetSizes(), index, (POINTER) size);
}


static __inline__ RAS cc_GetPending(void)
{
  return cc_CLOSURE.pending;
}


static __inline__ void cc_SetPending(RAS pending)
{
  cc_CLOSURE.pending = pending;
}


static __inline__ RAS cc_GetCombine(void)
{
  return cc_CLOSURE.combine;
}


static __inline__ void cc_SetCombine(RAS combine)
{
  cc_CLOSURE.combine = combine;
}


/**************************************************************/
/* Functions                                                  */
/**************************************************************/

static int cc_Number(int actno, TERM term, TERM pred)
/***************************************************************
  INPUT:   the actual number of terms, the term to be numbered
           and its predecessor (may be the empty term
           term_Null())
  RETURNS: the new number of terms after recursively numbering
           the term and its subterms
  EFFECT:  stores a term's number as its size, partially
           initializes its predecessor list and pushes all
           subterms to the pending stack
***************************************************************/
{
  LIST terms;

#ifdef CHECK
  if (actno < 0) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cc_Number: negative actual number of terms.");
    misc_FinishErrorReport();
  }
#endif

  term_SetSize(term, actno++);
  cc_SetCars(ras_Push(cc_GetCars(), pred));
  cc_SetPending(ras_Push(cc_GetPending(), term));
  for (terms = term_ArgumentList(term); !list_Empty(terms); terms =
      list_Cdr(terms))
    actno = cc_Number(actno, list_Car(terms), term);
  return actno;
}


static void cc_Union(ECLASS c1, ECLASS c2)
/***************************************************************
  EFFECT:  unions c1 and c2, therefore the signatures of the
           predecessors of one class change, so these
           predecessors have to be deleted from the signature
           table and become pending again; sets new class's
           predecessor list and its size to the concatenation of
           the old lists resp. the sum of the old sizes
***************************************************************/
{
  int aux, size;
  TERM term;

#ifdef CHECK
  if (part_Find(cc_GetPartition(), c1) != c1) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cc_Union: first class corrupted, i. e. is not ");
    misc_ErrorReport("the representative.");
    misc_FinishErrorReport();
  }
  if (part_Find(cc_GetPartition(), c2) != c2) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cc_Union: second class corrupted, i. e. is not ");
    misc_ErrorReport("the representative.");
    misc_FinishErrorReport();
  }
#endif

  if (c1 != c2) {

    /* make c1 the class with the bigger (or at least not smaller) list: */
    if (cc_GetSize(c1) < cc_GetSize(c2)) {
      aux = c1;
      c1  = c2;
      c2  = aux;
    }

    /* delete c2's predecessors from signature table and add them to pending: */
    for (size = cc_GetSize(c2), aux = c2; size > 0; size--) {
      term = cc_GetCar(aux);
      aux  = cc_GetCdr(aux);
      table_Delete(cc_GetTable(), term);
      cc_SetPending(ras_Push(cc_GetPending(), term));
    }

    if (cc_GetSize(c2) > 0) {  /* then GetSize(c1) ( >= GetSize(c2) ) > 0 too */

      /* union circularly linked lists by exchanging cdrs: */
      aux = cc_GetCdr(c1);
      cc_SetCdr(c1, cc_GetCdr(c2));
      cc_SetCdr(c2, aux);

      cc_SetSize(c1, cc_GetSize(c1) + cc_GetSize(c2));
    }
    part_Union(cc_GetPartition(), c1, c2);
  }
}


static void cc_InitData(CLAUSE clause)
/***************************************************************
  INPUT:  the clause to investigate
  EFFECT: pushes clause's atoms and their subterms on the
          pending stack, initializes each predecessor list with
          the list containing only a term's father, and unions
          the equivalence classes of the terms of the same
          antecedent equation
***************************************************************/
{
  int last, actno, i, ld;
  TERM atom;
  RAS cdr, size;

  cc_SetCars(ras_InitWithSize(cc_GetCars(), cc_RASSTDSIZE));
  cc_SetPending(ras_InitWithSize(cc_GetPending(), cc_RASSTDSIZE));
  ras_FastPush(cc_GetCars(), term_Null());  /* "true" has no predecessors */
  actno = 1;
  last  = clause_LastLitIndex(clause);
  for (i = clause_FirstLitIndex(); i <= last; i++) {
    atom = clause_GetLiteralAtom(clause, i);
    if (fol_IsEquality(atom)) {
      actno = cc_Number(actno, term_FirstArgument(atom), term_Null());
      actno = cc_Number(actno, term_SecondArgument(atom), term_Null());
    }
    else
      actno = cc_Number(actno, atom, term_Null());
  }
  cc_SetPartition(part_Init(cc_GetPartition(), actno));
  cc_SetTable(table_Init(cc_GetTable(), symbol_ActIndex() - 1,
                         clause_MaxVar(clause), actno - 1));
  cdr  = ras_InitWithSize(cc_GetCdrs(), actno);
  size = ras_InitWithSize(cc_GetSizes(), actno);
  for (i = 0; i < actno; i++) {
    ras_FastPush(cdr, (POINTER) i);  /* form a cycle */
    ras_FastPush(size, (POINTER) (cc_GetCar(i) == term_Null()? 0 : 1));
  }
  cc_SetCdrs(cdr);
  cc_SetSizes(size);

  /* compute ceil(ld(actno)) avoiding mathbib-logarithm's rounding errors: */
  for (ld = 0, i = actno - 1; i > 0; i >>= 1)
    ld++;

  cc_SetCombine(ras_InitWithSize(cc_GetCombine(), actno * ld + 1));

  /* for every antecedent equation union equivalence classes of its terms  */
  /* (a non-equational atom is represented as the equation atom = "true"): */
  last = clause_LastAntecedentLitIndex(clause);
  for (i = clause_FirstLitIndex(); i <= last; i++) {
    atom = clause_GetLiteralAtom(clause, i);
    if (fol_IsEquality(atom))
      cc_Union(term_Size(term_FirstArgument(atom)),  /* clause not shared, therefore */
	       term_Size(term_SecondArgument(atom))); /* here no cc_Find needed */
    else
      cc_Union(term_Size(atom), part_Find(cc_GetPartition(), cc_NOOFTRUE));
  }

}


static BOOL cc_Outit(CLAUSE clause)
/***************************************************************
  RETURNS: the decision, if the clause is a tautology
***************************************************************/
{
  int last, i;
  BOOL result;
  TERM atom;

#ifdef CHECK
  if (!ras_Empty(cc_GetPending())) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cc_Outit: there are terms left to work off.");
    misc_FinishErrorReport();
  }
#endif

  last   = clause_LastLitIndex(clause);
  for (i = clause_FirstSuccedentLitIndex(clause), result = FALSE;
       i <= last && !result; i++) {
    atom = clause_GetLiteralAtom(clause, i);
    if (fol_IsEquality(atom))
      result = part_Equivalent(cc_GetPartition(),
			       term_Size(term_FirstArgument(atom)),
			       term_Size(term_SecondArgument(atom)));
    else
      result = part_Equivalent(cc_GetPartition(), term_Size(atom), cc_NOOFTRUE);
  }
  return result;
}


/**************************************************************/
/* Main functions                                             */
/**************************************************************/

void cc_Init(void)
{
  cc_SetPartition(part_Create(cc_RASSTDSIZE));
  cc_SetTable(table_Create(cc_RASSTDSIZE, cc_RASSTDSIZE, cc_RASSTDSIZE));
  cc_SetCars(ras_CreateWithSize(cc_RASSTDSIZE));
  cc_SetCdrs(ras_CreateWithSize(cc_RASSTDSIZE));
  cc_SetSizes(ras_CreateWithSize(cc_RASSTDSIZE));
  cc_SetPending(ras_CreateWithSize(cc_RASSTDSIZE));
  cc_SetCombine(ras_CreateWithSize(cc_SIZELDSIZE));
}


void cc_Free(void)
{
  part_Free(cc_GetPartition());
  table_Free(cc_GetTable());
  ras_Free(cc_GetCars());
  ras_Free(cc_GetCdrs());
  ras_Free(cc_GetSizes());
  ras_Free(cc_GetPending());
  ras_Free(cc_GetCombine());
}


BOOL cc_Tautology(CLAUSE clause)
/***************************************************************
  INPUT:   the clause to test
  RETURNS: the decision, if the clause - where all variables are
           regarded as skolem constants - is a tautology, using
           the congruence closure algorithm of Downey, Sethi and
           Tarjan
  CAUTION: overrides the sizes of the clause's terms
***************************************************************/
{
  TERM term, query;

  cc_InitData(clause);
  while (!ras_Empty(cc_GetPending())) {

    /* propagate the closure: */
    while (!ras_Empty(cc_GetPending())) {
      term  = ras_Pop(cc_GetPending());
      query = table_QueryAndEnter(cc_GetTable(), cc_GetPartition(), term);
      if (query != term_Null()) {
        ras_FastPush(cc_GetCombine(), term);
        ras_FastPush(cc_GetCombine(), query);
      }
    }
    while (!ras_Empty(cc_GetCombine()))
      cc_Union(part_Find(cc_GetPartition(), term_Size(ras_Pop(cc_GetCombine()))),
	       part_Find(cc_GetPartition(), term_Size(ras_Pop(cc_GetCombine()))));
  }
  return cc_Outit(clause);
}

