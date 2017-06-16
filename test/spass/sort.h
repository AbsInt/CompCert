/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                  SORTED REASONING                      * */
/* *                                                        * */
/* *  $Module:   SORT                                       * */ 
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

#ifndef _SORT_
#define _SORT_

#include "clause.h"
#include "unify.h"
#include "hash.h"
#include "subsumption.h"


/**************************************************************/
/* Data Structures and Constants                              */
/**************************************************************/

/* Objects of type SORT are used to store the sort information */
/* for terms. SORT is a list of NODE's                        */

typedef LIST SORT;
/* List of sort nodes */

typedef LIST SOJU;
/* Pair: First Component Sort, Second Component Condition */

typedef enum {SORTEQNONE=1, SORTEQDECR=2, SORTEQMANY=3} STR;
/* The overall result of an sort theory analysis with respect to equations */

typedef struct CONDITION_HELP {
  SYMBOL var;
  LIST   constraint;
  LIST   antecedent;
  LIST   succedent;
  LIST   clauses;
} CONDITION_NODE,*CONDITION;

/* This data structure collects the conditions from conditioned subsort clauses */
/* The constraint, antecedent, succedent lists contain lists of atoms used to  */
/* derive the subsort relationship that come from clauses.                     */


typedef struct NODE_HELP {
  LIST   links;
  NAT    mark;
  NAT    start;
  NAT    extra;
  LIST   conditions;
  SYMBOL symbol;
} NODE_NODE,*NODE;

/* This is a node from the subsort graph with outgoing links the represented   */
/* sort symbol and a mark indicating whether the node is already visited,i.e,  */
/* it is TRUE. Whereas start indicates whether the node was put true right     */
/* from the beginning. Conditions contains a list of conditions needed to set  */
/* the node true.                                                              */

typedef struct SLINK_HELP {
  LIST   input;                    
  NODE   output;                   
  int    card;                     
  int    fire;
  LIST   constraint;
  LIST   antecedent;
  LIST   succedent;
  SYMBOL var;
  CLAUSE clause;                   
} SLINK_NODE,*SLINK;

/* This is a link in the subsort graph, with a list of input nodes that have   */
/* to become true in order to fire the link and set the output node TRUE       */
/* constraint, antecedent, succedent literals are the extra literals of        */
/* <clause> and <var> is the subsort variable. It is always assumed that the   */
/* subsort variable is the maximal variable with respect to the constraint,    */
/* antecedent and succedent literals.                                          */

typedef struct SORTTHEORY_HELP {
  st_INDEX index;                                 
  NODE     basesorttable[symbol__MAXSIGNATURE];   
  LIST     suborigcls;
  LIST     termorigcls;
  NAT      mark;        
} SORTTHEORY_NODE,*SORTTHEORY;

/* The index contains the term declarations mapped to their possibly           */
/* approximated term declarations of inserted clauses. The subsort declarations*/
/* are handled by a specific graph initiated over the base sorts. There is     */
/* one node in the graph for every base sort (basesorttable) and links         */
/* correspond to subsort declaration clauses                                   */
/* The mark is used in the subsort graph to detect already visited nodes.      */
/* The lists suborigcls and termorigcls map original clauses to sort theory    */
/* clauses to links/terms respectively. They contain triples of this kind      */



/**************************************************************/
/* Extern                                                     */
/**************************************************************/

void      sort_ConditionDelete(CONDITION);
CONDITION sort_ConditionCopy(CONDITION);


/**************************************************************/
/* Macros                                                     */
/**************************************************************/

static __inline__ SORT sort_TopSort(void)
{
  return list_Nil();
}

static __inline__ BOOL sort_IsTopSort(SORT S)
{
  return list_Empty(S);
}

static __inline__ SORT sort_Copy(SORT S)
{
  return list_Copy(S);
}

static __inline__ void sort_DeleteOne(SORT S)
{
  list_Delete(S);
}

static __inline__ SORT sort_Intersect(SORT S1, SORT S2)
{
  return list_Nconc(S1, S2);
}

static __inline__ SORT sort_DeleteBaseNode(SORT S, NODE N)
{
  return list_PointerDeleteElement(S,N);
}

static __inline__ SORT sort_AddBaseNode(SORT S, NODE N)
{
  return list_Cons(N,S);
}

static __inline__ void sort_NodeFree(NODE N)
{
  memory_Free(N,sizeof(NODE_NODE));
}

static __inline__ BOOL sort_NodeEqual(NODE N1, NODE N2)
{
  return (N1 == N2);
}

static __inline__ void sort_DeleteConditionList(LIST List)
{
  list_DeleteWithElement(List, (void (*)(POINTER)) sort_ConditionDelete);
}

static __inline__ void sort_NodeDelete(NODE N)
{
  list_Delete(N->links);
  N->links = list_Nil();
  sort_DeleteConditionList(N->conditions);
  N->conditions = list_Nil();
  sort_NodeFree(N);
}

static __inline__ LIST sort_NodeLinks(NODE N)
{
  return N->links;
}

static __inline__ BOOL sort_NodeValue(SORTTHEORY S, NODE N)
{
  return (N->mark == S->mark);
}

static __inline__ BOOL sort_NodeExtraValue(SORTTHEORY S, NODE N)
{
  return (N->extra == S->mark);
}

static __inline__ BOOL sort_NodeStartValue(SORTTHEORY S, NODE N)
{
  return (N->start == S->mark);
}

static __inline__ NAT sort_NodeMark(NODE N)
{
  return N->mark;
}

static __inline__ NAT sort_NodeStart(NODE N)
{
  return N->start;
}

static __inline__ SYMBOL sort_NodeSymbol(NODE N)
{
  return N->symbol;
}

static __inline__ LIST sort_NodeConditions(NODE N)
{
  return N->conditions;
}

static __inline__ void sort_PutNodeMark(NODE N, NAT M)
{
  N->mark = M;
}

static __inline__ void sort_PutNodeExtra(NODE N, NAT M)
{
  N->extra = M;
}

static __inline__ void sort_PutNodeStart(NODE N, NAT S)
{
  N->start = S;
}

static __inline__ void sort_PutNodeSymbol(NODE N, SYMBOL S)
{
  N->symbol = S;
}

static __inline__ void sort_PutNodeLinks(NODE N, LIST C)
{
  N->links = C;
}

static __inline__ void sort_PutNodeConditions(NODE N, LIST C)
{
  N->conditions = C;
}

static __inline__ void sort_PutNodeTrue(SORTTHEORY S, NODE N)
{
  N->mark = S->mark;
}

static __inline__ void sort_PutNodeExtraTrue(SORTTHEORY S, NODE N)
{
  N->extra = S->mark;
}

static __inline__ void sort_PutNodeStartTrue(SORTTHEORY S, NODE N)
{
  N->start = S->mark;
}

static __inline__ LIST sort_LinkInput(SLINK S)
{
  return S->input;
}

static __inline__ NODE sort_LinkOutput(SLINK S)
{
  return S->output;
}

static __inline__ int sort_LinkFire(SLINK S)
{
  return S->fire;
}

static __inline__ int sort_LinkVar(SLINK S)
{
  return S->var;
}

static __inline__ LIST sort_LinkConstraint(SLINK S)
{
  return S->constraint;
}

static __inline__ LIST sort_LinkAntecedent(SLINK S)
{
  return S->antecedent;
}

static __inline__ LIST sort_LinkSuccedent(SLINK S)
{
  return S->succedent;
}

static __inline__ CLAUSE sort_LinkClause(SLINK S)
{
  return S->clause;
}

static __inline__ int sort_LinkCard(SLINK S)
{
  return S->card;
}

static __inline__ void sort_PutLinkInput(SLINK S, LIST T)
{
  S->input = T;
}

static __inline__ void sort_PutLinkVar(SLINK S, SYMBOL V)
{
  S->var = V;
}

static __inline__ void sort_PutLinkConstraint(SLINK S, LIST T)
{
  S->constraint = T;
}

static __inline__ void sort_PutLinkAntecedent(SLINK S, LIST T)
{
  S->antecedent = T;
}

static __inline__ void sort_PutLinkSuccedent(SLINK S, LIST T)
{
  S->succedent = T;
}

static __inline__ void sort_PutLinkOutput(SLINK S,NODE H)
{
  S->output = H;
}

static __inline__ void sort_PutLinkClause(SLINK S, CLAUSE C)
{
  S->clause = C;
}

static __inline__ void sort_PutLinkCard(SLINK S,int L)
{
  S->card = L;
}

static __inline__ void sort_LinkResetFire(SLINK S) {
  S->fire = S->card;
}

static __inline__ int sort_LinkDecrementFire(SLINK S)
{
  --(S->fire);
  return S->fire;
}

static __inline__ void sort_LinkFree(SLINK S)
{
  memory_Free(S,sizeof(SLINK_NODE));
}

static __inline__ void sort_LinkDelete(SLINK S)
{
  LIST Scan;
  for (Scan=sort_LinkInput(S); !list_Empty(Scan); Scan=list_Cdr(Scan))
    sort_PutNodeLinks(list_Car(Scan),list_PointerDeleteElement(sort_NodeLinks(list_Car(Scan)),S));
  list_Delete(sort_LinkInput(S));
  term_DeleteTermList(sort_LinkConstraint(S));
  term_DeleteTermList(sort_LinkAntecedent(S));
  term_DeleteTermList(sort_LinkSuccedent(S));
  sort_LinkFree(S);
}

static __inline__ SYMBOL sort_ConditionVar(CONDITION C)
{
  return C->var;
}

static __inline__ LIST sort_ConditionConstraint(CONDITION C)
{
  return C->constraint;
}

static __inline__ LIST sort_ConditionAntecedent(CONDITION C)
{
  return C->antecedent;
}

static __inline__ LIST sort_ConditionSuccedent(CONDITION C)
{
  return C->succedent;
}

static __inline__ LIST sort_ConditionClauses(CONDITION C)
{
  return C->clauses;
}

static __inline__ void sort_ConditionPutVar(CONDITION C, SYMBOL Var)
{
   C->var = Var;
}

static __inline__ void sort_ConditionPutConstraint(CONDITION C, LIST Constr)
{
   C->constraint = Constr;
}

static __inline__ void sort_ConditionPutAntecedent(CONDITION C, LIST Ante)
{
   C->antecedent = Ante;
}

static __inline__ void sort_ConditionPutSuccedent(CONDITION C, LIST Succ)
{
   C->succedent = Succ;
}

static __inline__ void sort_ConditionPutClauses(CONDITION C, LIST Clauses)
{
   C->clauses = Clauses;
}

static __inline__ void sort_ConditionFree(CONDITION C)
{
  memory_Free(C, sizeof(CONDITION_NODE));
}

static __inline__ BOOL sort_ConditionNoResidues(CONDITION C)
{
  return (list_Empty(sort_ConditionConstraint(C)) &&
	  list_Empty(sort_ConditionAntecedent(C)) &&
	  list_Empty(sort_ConditionSuccedent(C)));
}



static __inline__ BOOL sort_LinkNoResidues(SLINK S)
{
  return (list_Empty(sort_LinkConstraint(S)) &&
	  list_Empty(sort_LinkAntecedent(S)) &&
	  list_Empty(sort_LinkSuccedent(S)));
}

static __inline__ BOOL sort_HasEqualSort(SORT S1, SORT S2)
{
  return S1 == S2;
}


static __inline__ POINTER sort_PairSort(LIST Pair)
{
  return list_PairFirst(Pair);
}

static __inline__ POINTER sort_PairCondition(LIST Pair)
{
  return list_PairSecond(Pair);
}

static __inline__ LIST sort_PairCreate(SORT S , CONDITION Just)
{
  return list_PairCreate((POINTER)S, Just);
}

static __inline__ void sort_PairFree(LIST Pair)
{
  list_PairFree(Pair);
}

static __inline__ void sort_PairDelete(LIST Pair)
{
  sort_DeleteOne(sort_PairSort(Pair));
  sort_ConditionDelete(sort_PairCondition(Pair));
  list_PairFree(Pair);
}

static __inline__ LIST sort_PairCopy(LIST Pair)
{
  return sort_PairCreate(sort_Copy(sort_PairSort(Pair)),
			 sort_ConditionCopy(sort_PairCondition(Pair)));
}

static __inline__ NODE sort_TheoryNode(SORTTHEORY Theory, SYMBOL S)
{
  return Theory->basesorttable[symbol_Index(S)];
}

static __inline__ NAT sort_TheoryMark(SORTTHEORY Theory)
{
  return Theory->mark;
}

static __inline__ LIST sort_TheorySuborigcls(SORTTHEORY Theory)
{
  return Theory->suborigcls;
}

static __inline__ LIST sort_TheoryTermorigcls(SORTTHEORY Theory)
{
  return Theory->termorigcls;
}

static __inline__ void sort_TheoryIncrementMark(SORTTHEORY Theory)
{
  if (Theory->mark == NAT_MAX) {
    int  i;   
    NODE Node;
    for (i = 0; i < symbol__MAXSIGNATURE; i++) {
      Node = Theory->basesorttable[i];
      Node->mark  = 0;
      Node->extra = 0;
      Node->start = 0;
    }
    Theory->mark = 0;      
  } 
  ++(Theory->mark);
}

static __inline__ st_INDEX sort_TheoryIndex(SORTTHEORY Theory)
{
  return Theory->index;
}


/**************************************************************/
/* Functions                                                  */
/**************************************************************/

void sort_Init(void);
void sort_Free(void);

void sort_Delete(SORT);
BOOL sort_Eq(SORT, SORT);
void sort_DeleteSortPair(SOJU);

void sort_Print(SORT);
void sort_PairPrint(SOJU);

LIST sort_GetSymbolsFromSort(SORT);
BOOL sort_ContainsSymbol(SORT, SYMBOL);
BOOL sort_IsSort(SORT);


SORTTHEORY sort_ApproxStaticSortTheory(LIST, FLAGSTORE, PRECEDENCE);
SORTTHEORY sort_ApproxDynamicSortTheory(LIST);


SORTTHEORY sort_TheoryCreate(void);
void       sort_TheoryDelete(SORTTHEORY);
void       sort_TheoryPrint(SORTTHEORY);
void       sort_TheoryInsertClause(SORTTHEORY, CLAUSE, CLAUSE, LITERAL);
void       sort_TheoryDeleteClause(SORTTHEORY, CLAUSE);
SORT       sort_TheorySortOfSymbol(SORTTHEORY, SYMBOL);
BOOL       sort_TheorySortEqual(SORTTHEORY,SORT,SORT);
CONDITION  sort_TheoryIsSubsortOfNoResidues(SORTTHEORY, SORT, SORT);
BOOL       sort_TheoryIsSubsortOf(SORTTHEORY, SORT, SORT);
BOOL       sort_TheoryIsSubsortOfExtra(SORTTHEORY , SORT , SORT , SORT);
LIST       sort_TheoryComputeAllSubsortHits(SORTTHEORY, SORT, SORT);
SOJU       sort_ComputeSortNoResidues(SORTTHEORY,TERM, CLAUSE, int, FLAGSTORE, PRECEDENCE);
LIST       sort_ApproxMaxDeclClauses(CLAUSE, FLAGSTORE, PRECEDENCE);
STR        sort_AnalyzeSortStructure(LIST, FLAGSTORE, PRECEDENCE);


#endif
