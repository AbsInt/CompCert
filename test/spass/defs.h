/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                     Definitions                        * */
/* *                                                        * */
/* *  $Module:   DEFS                                       * */ 
/* *                                                        * */
/* *  Copyright (C) 1998, 1999, 2000, 2001                  * */
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

#ifndef _DEFS_
#define _DEFS_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/


#include "clause.h"
#include "term.h"
#include "list.h"
#include "search.h"

/**************************************************************/
/* Structures                                                 */
/**************************************************************/
typedef enum { PREDOCCURONCE = 1, /* whether predicate occurs only once */
               ISEQUALITY    = 2  /* whether predicate is equality */
} DEF_ATTRIBUTES;

typedef struct DEF_HELP {
  TERM   expansion;        /* The definition of the predicate term*/
  TERM   predicate;        /* The predicate which is defined*/
  TERM   toprove;
  LIST   parentclauses;    /* List of clause numbers plus list of literal indices */
  const char *label;            /* The label of the predicate term*/
  BOOL   conjecture;
  NAT    attributes;       /* The attributes of the predicate*/
} *DEF, DEF_NODE;

/**************************************************************/
/* Inline functions                                           */
/**************************************************************/
static __inline__ TERM def_Expansion(DEF D)
{
  return D->expansion;
}

static __inline__ void def_RplacExp(DEF D, TERM E)
{
  D->expansion = E;
}

static __inline__ TERM def_Predicate(DEF D)
{
  return D->predicate;
}

static __inline__ void def_RplacPred(DEF D, TERM Pred)
{
  D->predicate = Pred;
}

static __inline__ TERM def_ToProve(DEF D)
{
  return D->toprove;
}

static __inline__ void def_RplacToProve(DEF D, TERM ToProve)
{
  D->toprove = ToProve;
}

static __inline__ LIST def_ClauseNumberList(DEF D)
{
  return list_PairFirst(D->parentclauses);
}

static __inline__ void def_RplacClauseNumberList(DEF D, LIST L)
{
  list_Rplaca(D->parentclauses, L);
}

static __inline__ LIST def_ClauseLitsList(DEF D)
{
  return list_PairSecond(D->parentclauses);
}

static __inline__ void def_RplacClauseLitsList(DEF D, LIST L)
{
  list_Rplacd(D->parentclauses, L);
}

static __inline__ const char* def_Label(DEF D)
{
  return D->label;
}

static __inline__ void def_RplacLabel(DEF D, const char* L)
{
  D->label = L;
}

static __inline__ BOOL def_Conjecture(DEF D)
{
  return D->conjecture;
}

static __inline__ void def_SetConjecture(DEF D)
{
  D->conjecture = TRUE;
}

static __inline__ void def_AddAttribute(DEF D, DEF_ATTRIBUTES Attribute)
{
  D->attributes = D->attributes | Attribute;
}

static __inline__ NAT def_HasAttribute(DEF D, DEF_ATTRIBUTES Attribute)
{
  return (D->attributes & Attribute);
}

static __inline__ void def_RemoveAttribute(DEF D, DEF_ATTRIBUTES Attribute)
{
  if (D->attributes & Attribute)
    D->attributes = D->attributes - Attribute;
}

static __inline__ BOOL def_HasGuard(DEF D)
{
  return (def_ToProve(D)!=term_Null());
}

/**************************************************************/
/* Functions                                                  */
/**************************************************************/

DEF  def_CreateFromClauses(TERM, TERM, LIST, LIST, BOOL);
DEF  def_CreateFromTerm(TERM, TERM, TERM, const char*);

LIST def_ExtractDefsFromTerm(TERM, const char*);
void def_ExtractDefsFromTermlist(PROOFSEARCH, LIST, LIST);
void def_ExtractDefsFromClauselist(PROOFSEARCH, LIST);

TERM def_ApplyDefToTermOnce(DEF, TERM, FLAGSTORE, PRECEDENCE, BOOL*);
TERM def_ApplyDefToTermExhaustive(PROOFSEARCH, TERM);
LIST def_ApplyDefToTermlist(DEF, LIST, FLAGSTORE, PRECEDENCE, BOOL*, BOOL);
LIST def_ApplyDefinitionToTermList(LIST, LIST, FLAGSTORE, PRECEDENCE);
/*
LIST def_GetTermsForProof(TERM, TERM, int);
BOOL def_FindProofForGuard(TERM, TERM, TERM, FLAGSTORE);
*/

LIST def_ApplyDefToClauseOnce(DEF, CLAUSE, FLAGSTORE, PRECEDENCE);
LIST def_ApplyDefToClauseExhaustive(PROOFSEARCH, CLAUSE);
LIST def_ApplyDefToClauselist(PROOFSEARCH, DEF, LIST, BOOL);

LIST def_FlattenWithOneDefinition(PROOFSEARCH, DEF);
void def_FlattenWithOneDefinitionSemiDestructive(PROOFSEARCH, DEF);
void def_FlattenWithOneDefinitionDestructive(PROOFSEARCH, DEF);
void def_FlattenDefinitionsDestructive(PROOFSEARCH);

void def_Delete(DEF);
void def_Print(DEF);

int  def_PredicateOccurrences(TERM, SYMBOL);
#endif
