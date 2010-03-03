/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                ANALYSIS OF CLAUSE SETS                 * */
/* *                                                        * */
/* *  $Module:   ANALYZE                                    * */ 
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

#include <stdio.h>

#include "analyze.h"

static LIST ana_CalculatePredicatePrecedence(LIST, LIST);
static LIST ana_CalculateFunctionPrecedence(LIST, LIST, FLAGSTORE);

/**************************************************************/
/* Global Variables                                           */
/**************************************************************/

LIST ana_FINITEMONADICPREDICATES;  /* List of monadic predicates with finite extension */

BOOL ana_EQUATIONS;                /* Problem contains any equations at all */
static BOOL ana_PEQUATIONS;        /* Problem contains positive equations */
static BOOL ana_NEQUATIONS;        /* Problem contains negative equations */
static BOOL ana_FUNCTIONS;         /* Problem contains non-constant function symbols */
static BOOL ana_PROP;              /* Problem contains propositional variables */
static BOOL ana_GROUND;            /* Problem contains non-propositional, non-equational ground atoms */
static BOOL ana_NONUNIT;           /* Problem contains non-unit clauses */
static BOOL ana_MONADIC;           /* Problem contains non-ground monadic predicates */
static BOOL ana_NONMONADIC;        /* Problem contains non-ground n-place predicates, n>1, not equality */
BOOL ana_SORTRES;                  /* Problem contains literal not(S(x)) for some S */
BOOL ana_USORTRES;                 /* Problem contains literal not(S(t)) for some S */
static BOOL ana_FINDOMAIN;         /* Problem contains clause implying a finite domain */
static BOOL ana_NONTRIVDOMAIN;     /* Problem contains clause implying a domain of size greater one */
static BOOL ana_CONGROUND;         /* Conjecture is ground */

static BOOL ana_PUREEQUATIONAL;    /* Problem is purely equational */
static BOOL ana_PUREPROPOSITIONAL; /* Problem is purely propositional */

BOOL ana_SORTDECEQUATIONS;         /* True if all positive equations are sort decreasing with respect to
                                      the static sort theory contained in the problem */
static BOOL ana_SORTMANYEQUATIONS;  /* True if all positive equations have the
				       same sort on left and right hand side with
				       respect to the static sort theory
				       contained in the problem */

static NAT  ana_AXIOMCLAUSES;      /* Number of axiom clauses */
static NAT  ana_CONCLAUSES;        /* Number of conjecture clauses */
static NAT  ana_NONHORNCLAUSES;    /* Number of Non-Horn clauses */


/**************************************************************/
/* Functions                                                  */
/**************************************************************/

void ana_AnalyzeProblem(PROOFSEARCH Search, LIST Clauses)
/**************************************************************
  INPUT:   A proofsearch object and a list of clauses.
  RETURNS: Void.
  EFFECT:  Analyzes the clauses and sets the analyze variables.
           Recomputes the weight for the clauses.
	   <Search> is modified according to clauses: non trivial domain number
	   is set
***************************************************************/
{
  CLAUSE Clause;

  ana_EQUATIONS       = FALSE;  
  ana_PEQUATIONS      = FALSE;             /* Defaults for properties */
  ana_NEQUATIONS      = FALSE; 
  ana_FUNCTIONS       = FALSE;
  ana_FINDOMAIN       = FALSE;
  ana_NONTRIVDOMAIN   = FALSE;
  ana_MONADIC         = FALSE;
  ana_NONMONADIC      = FALSE;
  ana_PROP            = FALSE;
  ana_GROUND          = FALSE;
  ana_SORTRES         = FALSE;
  ana_USORTRES        = FALSE;
  ana_NONUNIT         = FALSE;
  ana_CONGROUND       = TRUE;

  ana_AXIOMCLAUSES    = 0; 
  ana_CONCLAUSES      = 0;
  ana_NONHORNCLAUSES  = 0;

  list_Delete(ana_FINITEMONADICPREDICATES);
  ana_FINITEMONADICPREDICATES = list_Nil();

  if (list_Empty(Clauses))
    return;

  ana_FINITEMONADICPREDICATES = clause_FiniteMonadicPredicates(Clauses);

  while (!list_Empty(Clauses)) {
    Clause = (CLAUSE)list_Car(Clauses);
    clause_UpdateWeight(Clause, prfs_Store(Search));

    if (clause_GetFlag(Clause,CONCLAUSE))
      ana_CONCLAUSES++;
    else
      ana_AXIOMCLAUSES++;

    if (clause_NumOfSuccLits(Clause) > 1)
      ana_NONHORNCLAUSES++;

    if (ana_CONGROUND && clause_GetFlag(Clause,CONCLAUSE) &&
	clause_MaxVar(Clause) != symbol_GetInitialStandardVarCounter())
      ana_CONGROUND = FALSE;
    if (!ana_PEQUATIONS && clause_ContainsPositiveEquations(Clause)) {
      ana_PEQUATIONS = TRUE;
    }
    if (!ana_NEQUATIONS && clause_ContainsNegativeEquations(Clause)) {
      ana_NEQUATIONS = TRUE;
    }
    if (!ana_MONADIC || !ana_NONMONADIC || !ana_PROP || !ana_GROUND)
      clause_ContainsFolAtom(Clause,&ana_PROP,&ana_GROUND,&ana_MONADIC,&ana_NONMONADIC);

    if (!ana_FUNCTIONS && clause_ContainsFunctions(Clause)) {
      ana_FUNCTIONS = TRUE;
    }
    if (!ana_FINDOMAIN && clause_ImpliesFiniteDomain(Clause)) {
      ana_FINDOMAIN = TRUE;
    }
    if (!ana_NONTRIVDOMAIN && clause_ImpliesNonTrivialDomain(Clause)) {
      prfs_SetNonTrivClauseNumber(Search, clause_Number(Clause));
      ana_NONTRIVDOMAIN =  TRUE;
    }
    if (!ana_NONUNIT && clause_Length(Clause) > 1) {
      ana_NONUNIT = TRUE;
    }
    if (!ana_SORTRES || !ana_USORTRES) 
      clause_ContainsSortRestriction(Clause,&ana_SORTRES,&ana_USORTRES);
    
    Clauses = list_Cdr(Clauses);
  }

  ana_PUREEQUATIONAL    = ((ana_PEQUATIONS || ana_NEQUATIONS) && !ana_MONADIC &&
			   !ana_NONMONADIC && !ana_PROP && !ana_GROUND);
  ana_EQUATIONS         = (ana_PEQUATIONS || ana_NEQUATIONS);
  ana_PUREPROPOSITIONAL = (!ana_PEQUATIONS && !ana_NEQUATIONS &&!ana_MONADIC &&
			   !ana_NONMONADIC && ana_PROP);
}


void ana_AnalyzeSortStructure(LIST Clauses, FLAGSTORE Flags,
			      PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A list of clauses, a flag store and a precedence.
  RETURNS: Nothing.
  EFFECT:  The sort structure with respect to equations is analyzed.
           It is detected whether all equations are many sorted or
	   sort decreasing.
***************************************************************/
{
  if (ana_PEQUATIONS && ana_SORTRES) {
    STR Result;
    Result                = sort_AnalyzeSortStructure(Clauses,Flags,Precedence);
    ana_SORTMANYEQUATIONS = (Result == SORTEQMANY);
    ana_SORTDECEQUATIONS  = (Result == SORTEQMANY || Result == SORTEQDECR);
  }
}


void ana_Print(FLAGSTORE Flags, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A flag store and a precedence.
  RETURNS: Nothing.
  EFFECT:  The results of an analysis stored in the module variables
           is printed to stdout.
***************************************************************/
{
  const char* Horn;

  if (ana_NONHORNCLAUSES == 0)
    Horn = "Horn";
  else
    Horn = "Non-Horn";
  
  if (ana_MONADIC && !ana_NONMONADIC) {
    printf("\n This is a monadic %s problem",Horn);
    if (ana_PEQUATIONS || ana_NEQUATIONS)
      fputs(" with equality.", stdout);
    else
      fputs(" without equality.", stdout);
  }
  else
    if (ana_PEQUATIONS || ana_NEQUATIONS) {
      if (ana_NONMONADIC || ana_MONADIC || ana_PROP)
	printf("\n This is a first-order %s problem containing equality.",Horn);
      else
	if (ana_NONUNIT)
	  printf("\n This is a pure equality %s problem.",Horn);
	else
	  fputs("\n This is a unit equality problem.", stdout);
    }
    else
      if (ana_NONMONADIC || ana_MONADIC)
	printf("\n This is a first-order %s problem without equality.",Horn);

  if (ana_PUREPROPOSITIONAL)
    printf("\n This is a propositional %s problem.",Horn);
  else
    if (ana_FINDOMAIN || !ana_FUNCTIONS) {
      fputs("\n This is a problem that has, if any, a finite domain model.",
	    stdout);
      if (ana_FINDOMAIN)
	fputs("\n There is a finite domain clause.", stdout);
      if (!ana_FUNCTIONS)
	fputs("\n There are no function symbols.", stdout);
    }

  if (ana_NONTRIVDOMAIN)
    fputs("\n This is a problem that has, if any, a non-trivial domain model.",
	  stdout);
      
  
  if (ana_SORTRES) {
    fputs("\n This is a problem that contains sort information.", stdout);
    if (ana_PEQUATIONS) {
      if (ana_SORTMANYEQUATIONS)
	fputs("\n All equations are many sorted.", stdout);
      else {
	if (ana_SORTDECEQUATIONS)
	  fputs("\n All equations are sort-decreasing.", stdout);
      }
    }
  }

  if (ana_CONCLAUSES > 0 && ana_CONGROUND && !ana_PUREPROPOSITIONAL)
    fputs("\n The conjecture is ground.", stdout);

  if (!list_Empty(ana_FINITEMONADICPREDICATES)) {
    LIST Scan;
    fputs("\n The following monadic predicates have finite extensions: ", stdout);
    for (Scan=ana_FINITEMONADICPREDICATES;!list_Empty(Scan);Scan=list_Cdr(Scan)) {
      symbol_Print((SYMBOL)list_Car(Scan));
      if (!list_Empty(list_Cdr(Scan)))
	fputs(", ", stdout);
    }
    putchar('.');
  }

  printf("\n Axiom clauses: %d Conjecture clauses: %d",ana_AXIOMCLAUSES,ana_CONCLAUSES);

  flag_PrintInferenceRules(Flags);
  flag_PrintReductionRules(Flags);
  fputs("\n Extras    : ", stdout);
  if (flag_GetFlagValue(Flags, flag_SATINPUT))
    fputs("Input Saturation, ", stdout);
  else
    fputs("No Input Saturation, ", stdout);
  if (flag_GetFlagValue(Flags, flag_SELECT) == flag_SELECTOFF)
    fputs("No Selection, ", stdout);
  else
    if (flag_GetFlagValue(Flags, flag_SELECT) == flag_SELECTIFSEVERALMAXIMAL)
      fputs("Dynamic Selection, ", stdout);
    else
      fputs("Always Selection, ", stdout);
  if (flag_GetFlagValue(Flags, flag_SPLITS) == flag_SPLITSUNLIMITED)
    fputs("Full Splitting, ", stdout);
  else
    if (flag_GetFlagValue(Flags, flag_SPLITS) == flag_SPLITSOFF)
      fputs("No Splitting, ", stdout);
    else
      printf("Maximum of %d Splits, ",flag_GetFlagValue(Flags, flag_SPLITS));
  if (flag_GetFlagValue(Flags, flag_FULLRED))
    fputs("Full Reduction, ", stdout);
  else
    fputs("Lazy Reduction, ", stdout);
  printf(" Ratio: %d, FuncWeight: %d, VarWeight: %d",
	 flag_GetFlagValue(Flags, flag_WDRATIO),
	 flag_GetFlagValue(Flags, flag_FUNCWEIGHT),
	 flag_GetFlagValue(Flags, flag_VARWEIGHT));
  fputs("\n Precedence: ", stdout);
  fol_PrintPrecedence(Precedence);
  fputs("\n Ordering  : ", stdout);
  fputs(flag_GetFlagValue(Flags, flag_ORD) == flag_ORDKBO ? "KBO" : "RPOS",
	stdout);
}


void ana_AutoConfiguration(LIST Clauses, FLAGSTORE Flags,
			   PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A list of clauses, a flag store and a precedence.
  RETURNS: Nothing.
  EFFECT:  Based on the values of the ana analysis module, an appropriate
           complete configuration of inference, reduction rules and other
	   settings is established.
***************************************************************/
{
  LIST Scan, Functions, Predicates, Constants;

  Functions  = symbol_GetAllFunctions();
  Predicates = fol_GetNonFOLPredicates();

  /* Set precedence */
  Predicates = ana_CalculatePredicatePrecedence(Predicates, Clauses);
  Functions  = ana_CalculateFunctionPrecedence(Functions, Clauses, Flags);
  Constants  = list_Nil();

  for (Scan=Functions; !list_Empty(Scan); Scan=list_Cdr(Scan))
    if (symbol_IsConstant((SYMBOL)list_Car(Scan)))
      Constants = list_Cons(list_Car(Scan),Constants);
  Functions = list_NPointerDifference(Functions,Constants);
  Constants = list_NReverse(Constants);

  for ( ; !list_Empty(Functions); Functions = list_Pop(Functions))
    symbol_SetIncreasedOrdering(Precedence, (SYMBOL)list_Car(Functions));
  /* Predicates < Functions */
  for ( ; !list_Empty(Predicates); Predicates = list_Pop(Predicates))
    symbol_SetIncreasedOrdering(Precedence, (SYMBOL)list_Car(Predicates));
  /* Constants < Predicates */
  /* Predicates < Functions */
  for ( ; !list_Empty(Constants); Constants = list_Pop(Constants))
    symbol_SetIncreasedOrdering(Precedence, (SYMBOL)list_Car(Constants));

  flag_ClearInferenceRules(Flags);
  flag_ClearReductionRules(Flags);

  flag_SetFlagValue(Flags, flag_ROBV,    flag_ROBVON);
  flag_SetFlagValue(Flags, flag_RTAUT,   flag_RTAUTSYNTACTIC);
  flag_SetFlagValue(Flags, flag_RFSUB,   flag_RFSUBON);
  flag_SetFlagValue(Flags, flag_RBSUB,   flag_RBSUBON);
  flag_SetFlagValue(Flags, flag_RFMRR,   flag_RFMRRON);
  flag_SetFlagValue(Flags, flag_RBMRR,   flag_RBMRRON);
  flag_SetFlagValue(Flags, flag_RUNC,    flag_RUNCON);
  flag_SetFlagValue(Flags, flag_FULLRED, flag_FULLREDON);
  /*flag_SetFlagValue(Flags, flag_FUNCWEIGHT,1);
  flag_SetFlagValue(Flags, flag_VARWEIGHT,1);*/
  flag_SetFlagValue(Flags, flag_WDRATIO,5);

  if (ana_NEQUATIONS) {
    flag_SetFlagValue(Flags, flag_IEQR, flag_EQUALITYRESOLUTIONON);
    if (ana_NONUNIT) {
      if (ana_NONTRIVDOMAIN)
	flag_SetFlagValue(Flags, flag_RAED, flag_RAEDPOTUNSOUND);
      else
	flag_SetFlagValue(Flags, flag_RAED, flag_RAEDSOUND);
    }
  }

  if (ana_PEQUATIONS) {
    flag_SetFlagValue(Flags, flag_ISPR, flag_SUPERPOSITIONRIGHTON);
    flag_SetFlagValue(Flags, flag_ISPL, flag_SUPERPOSITIONLEFTON);
    if (ana_NONHORNCLAUSES > 0)
      flag_SetFlagValue(Flags, flag_IEQF, flag_EQUALITYFACTORINGON);
    if (ana_NONUNIT) 
      flag_SetFlagValue(Flags, flag_RCON, flag_RCONON);
    flag_SetFlagValue(Flags, flag_RFREW, flag_RFREWON);
    flag_SetFlagValue(Flags, flag_RBREW, flag_RBREWON);
    flag_SetFlagValue(Flags, flag_RFCRW, flag_RFCRWOFF); /* Here we could activate contextual rewriting */
    flag_SetFlagValue(Flags, flag_RBCRW, flag_RBCRWOFF);
  }
  
  if (ana_SORTRES) {
    flag_SetFlagValue(Flags, flag_SORTS, flag_SORTSMONADICWITHVARIABLE);
    flag_SetFlagValue(Flags, flag_IEMS,  flag_EMPTYSORTON);
    flag_SetFlagValue(Flags, flag_ISOR,  flag_SORTRESOLUTIONON);
    flag_SetFlagValue(Flags, flag_RSSI, flag_RSSION);
    if (!ana_PEQUATIONS || ana_SORTMANYEQUATIONS)
      flag_SetFlagValue(Flags, flag_RSST, flag_RSSTON);
  }
  else
    flag_SetFlagValue(Flags, flag_SORTS, flag_SORTSOFF);

  if (ana_MONADIC || ana_NONMONADIC) { /* Problem contains real predicates */
    flag_SetFlagValue(Flags, flag_IORE, flag_ORDEREDRESOLUTIONNOEQUATIONS);
    if (ana_NONHORNCLAUSES > 0)
      flag_SetFlagValue(Flags, flag_IOFC, flag_FACTORINGONLYRIGHT);
    if (ana_NONUNIT) 
      flag_SetFlagValue(Flags, flag_RCON, flag_RCONON);
  }


  if (!ana_FUNCTIONS)
    flag_SetFlagValue(Flags, flag_SELECT, flag_SELECTALWAYS);
  else
    if (ana_NONUNIT)
      flag_SetFlagValue(Flags, flag_SELECT, flag_SELECTIFSEVERALMAXIMAL);
    else
      flag_SetFlagValue(Flags, flag_SELECT, flag_SELECTOFF);

  if (ana_CONCLAUSES < ana_AXIOMCLAUSES || (ana_CONGROUND && !ana_PUREPROPOSITIONAL))
    flag_SetFlagValue(Flags, flag_SATINPUT, flag_SATINPUTON);
  else
    flag_SetFlagValue(Flags, flag_SATINPUT, flag_SATINPUTOFF);

  if (ana_NONHORNCLAUSES > 0)
    flag_SetFlagValue(Flags, flag_SPLITS, flag_SPLITSUNLIMITED);
  else
    flag_SetFlagValue(Flags, flag_SPLITS, flag_SPLITSOFF);
}


void ana_ExploitSortAnalysis(FLAGSTORE Flags)
/**************************************************************
  INPUT:   A flag store.
  EFFECT:  If all equations are many sorted and or no positive
           equations occur at all and the problem contains sort
	   information, static soft typing is activated.
***************************************************************/
{
  if (ana_SORTRES && (!ana_PEQUATIONS || ana_SORTMANYEQUATIONS))
    flag_SetFlagValue(Flags, flag_RSST, flag_RSSTON);
}


static LIST ana_CalculatePredicatePrecedence(LIST Predicates, LIST Clauses)
/**************************************************************
  INPUT:   A list of predicates and a list of clauses.
  RETURNS: A list of predicate symbols, which should be used
           for setting the symbol precedence. The list is sorted
           in descending order, that means predicates with highest
           precedence come first.
  EFFECT:  Analyze the clause list to build a directed graph G where
           the predicates are vertices. There's an edge (P,Q) in
           G iff a clause exists where P is a negative literal
           and Q is a positive literal and P != Q. Apply DFS to
           find the strongly connected components of this graph.
	   The <Predicates> list is deleted.
  CAUTION: The predicate list must contain ALL predicates
           occurring in the clause list!
***************************************************************/
{
  GRAPH  graph;
  LIST   result, scan;
  int    i, j;
  NAT    count;
  SYMBOL s;

  /* clause_ListPrint(Clauses); DBG */

  if (list_Empty(Predicates)) {
    return Predicates;
  }

  graph = graph_Create();

  /* First create the nodes: one node for every predicate symbol. */
  for ( ; !list_Empty(Predicates); Predicates = list_Pop(Predicates))
    graph_AddNode(graph, symbol_Index((SYMBOL)list_Car(Predicates)));

  /* Now scan the clause clause list to create the edges */
  /* An edge (P,Q) means P is smaller than Q */
  for (scan = Clauses; !list_Empty(scan); scan = list_Cdr(scan)) {
    CLAUSE c = list_Car(scan);

    for (i = clause_FirstLitIndex(); i < clause_FirstSuccedentLitIndex(c); i++) {
      SYMBOL negPred = term_TopSymbol(clause_GetLiteralAtom(c, i));
      if (!symbol_Equal(negPred, fol_Equality())) { /* negative predicate */
	for (j = clause_FirstSuccedentLitIndex(c); j < clause_Length(c); j++) {
	  SYMBOL posPred = term_TopSymbol(clause_GetLiteralAtom(c, j));
	  if (!symbol_Equal(posPred, fol_Equality()) && /* positive predicate */
	      negPred != posPred) {  /* No self loops! */
	    graph_AddEdge(graph_GetNode(graph, symbol_Index(negPred)),
			  graph_GetNode(graph, symbol_Index(posPred)));
	  }
	}
      }
    }
  }

  /* graph_Print(graph); fflush(stdout); DBG */

  /* Calculate the strongly connected components of the graph */
  count = graph_StronglyConnectedComponents(graph);

  /* Now create the precedence list by scanning the nodes.        */
  /* If there's a link between two strongly connected components  */
  /* c1 and c2 then component_num(c1) > component_num(c2), so the */
  /* following code creates a valid precedence list in descending */
  /* order.                                                       */
  result = list_Nil();
  for (i = count - 1; i >= 0; i--) {
    for (scan = graph_Nodes(graph); !list_Empty(scan); scan = list_Cdr(scan)) {
      GRAPHNODE n = list_Car(scan);
      if (graph_NodeCompNum(n) == i) {
	/* The symbol represented by the node <<n> belongs to component <i> */
	s = symbol_GetSigSymbol(graph_NodeNumber(n));
	result = list_Cons((POINTER)s, result);
      }
    }
  }

  /* putchar('\n');
     for (scan = result; !list_Empty(scan); scan = list_Cdr(scan)) {
     s = (SYMBOL) list_Car(scan);
     symbol_Print(s);
     putchar(' ');
     }
     putchar('\n'); fflush(stdout); DBG */

  graph_Delete(graph);

  return result;
}


/* We use the node info to store the degree of the node */
static __inline__ NAT ana_NodeDegree(GRAPHNODE Node)
{
  return (NAT)graph_NodeInfo(Node);
}


static __inline__ void ana_IncNodeDegree(GRAPHNODE Node)
{
  graph_NodeSetInfo(Node, (POINTER)(ana_NodeDegree(Node)+1));
}

static BOOL ana_NodeGreater(GRAPHNODE N1, GRAPHNODE N2)
/**************************************************************
  INPUT:   Two graph nodes.
  RETURNS: TRUE, if N1 is greater than N2.
  EFFECT:  This function is used to sort the node list
           of the graph in ana_CalculateFunctionPrecedence.
***************************************************************/
{
  return (symbol_Arity(symbol_GetSigSymbol(graph_NodeNumber(N1))) >
	  symbol_Arity(symbol_GetSigSymbol(graph_NodeNumber(N2))));
}


static BOOL ana_BidirectionalDistributivity(LIST SymbolPairs)
/**************************************************************
  INPUT:   A list of symbol pairs defining distributivity.
  RETURNS: TRUE, if the list contains two pairs (s1, s2) and (s2, s1)
           FALSE otherwise.
  EFFECT:  This function is used to detect symbols that are distributive
           in both directions, logical OR and AND for example.
***************************************************************/
{
  LIST scan, actPair, nextPair;

  for ( ; !list_Empty(SymbolPairs); SymbolPairs = list_Cdr(SymbolPairs)) {
    actPair = list_Car(SymbolPairs);
    /* If actPair = (s1, s2), check whether there's a pair (s2, s1) in list */
    for (scan = list_Cdr(SymbolPairs); !list_Empty(scan); scan = list_Cdr(scan)) {
      nextPair = list_Car(scan);
      if (symbol_Equal((SYMBOL)list_PairFirst(actPair),(SYMBOL)list_PairSecond(nextPair)) &&
	  symbol_Equal((SYMBOL)list_PairSecond(actPair),(SYMBOL)list_PairFirst(nextPair)))
	return TRUE;
    }
  }
  return FALSE;
}


static LIST ana_CalculateFunctionPrecedence(LIST Functions, LIST Clauses,
					    FLAGSTORE Flags)
/**************************************************************
  INPUT:   A list of functions, a list of clauses and 
           a flag store.
  RETURNS: A list of function symbols, which should be used
           for setting the symbol precedence. The list is sorted
           in descending order, that means function with highest
           precedence come first.
  EFFECT:  Analyzes the clauses to build a directed graph G with
           function symbol as nodes. An edge (f,g) or in G means
           f should have lower precedence than g.
           An edge (f,g) or (g,f) is created if there's an equation
           equal(f(...), g(...)) in the clause list.
	   The direction of the edge depends on the degree of the
           nodes and the symbol arity.
	   Then find the strongly connected components of this
           graph.
           The "Ordering" flag will be set in the flag store.
  CAUTION: The value of "ana_PEQUATIONS" must be up to date.
***************************************************************/
{
  GRAPH     graph;
  GRAPHNODE n1, n2;
  LIST      result, scan, scan2, distrPairs;
  NAT       i, j;
  SYMBOL    s, Add, Mult;

  if (list_Empty(Functions))
    return Functions;   /* Problem contains no functions */
  else if (!ana_PEQUATIONS) {
    Functions = list_NumberSort(Functions, (NAT (*)(POINTER)) symbol_PositiveArity);
    return Functions;
  }

  graph = graph_Create();
  /* First create the nodes: one node for every function symbol. */
  for (; !list_Empty(Functions); Functions = list_Pop(Functions))
    graph_AddNode(graph, symbol_Index((SYMBOL)list_Car(Functions)));

  /* Now sort the node list wrt descending symbol arity. */
  graph_SortNodes(graph, ana_NodeGreater);

  /* A list of pairs (add, multiply) of distributive symbols */
  distrPairs = list_Nil();

  /* Now add undirected edges: there's an undirected edge between  */
  /* two nodes if the symbols occur as top symbols in a positive   */
  /* equation. */
  for (scan = Clauses; !list_Empty(scan); scan = list_Cdr(scan)) {
    CLAUSE c = list_Car(scan);
    for (i = clause_FirstSuccedentLitIndex(c);
	 i <= clause_LastSuccedentLitIndex(c); i++) {
      if (clause_LiteralIsEquality(clause_GetLiteral(c, i))) {
	/* Consider only positive equations */
	TERM t1, t2;

	if (fol_DistributiveEquation(clause_GetLiteralAtom(c,i), &Add, &Mult)) {
	  /* Add a pair (Add, Mult) to <distrTerms> */
	  distrPairs = list_Cons(list_PairCreate((POINTER)Add, (POINTER)Mult),
				 distrPairs);
	  /*fputs("\nDISTRIBUTIVITY: ", stdout);
	    term_PrintPrefix(clause_GetLiteralAtom(c,i));
	    fputs(" Add=", stdout); symbol_Print(Add);
	    fputs(" Mult=", stdout); symbol_Print(Mult); fflush(stdout); DBG */
	}

	t1 = term_FirstArgument(clause_GetLiteralAtom(c, i));
	t2 = term_SecondArgument(clause_GetLiteralAtom(c, i));

	if  (!term_IsVariable(t1) && !term_IsVariable(t2) &&
	     !term_EqualTopSymbols(t1, t2) &&  /* No self loops! */
	     !term_HasSubterm(t1, t2) &&       /* No subterm property */
	     !term_HasSubterm(t2, t1)) {
	  n1 = graph_GetNode(graph, symbol_Index(term_TopSymbol(t1)));
	  n2 = graph_GetNode(graph, symbol_Index(term_TopSymbol(t2)));
	  /* Create an undirected edge by adding two directed edges */
	  graph_AddEdge(n1, n2);
	  graph_AddEdge(n2, n1);
	  /* Use the node info for the degree of the node */
	  ana_IncNodeDegree(n1);
	  ana_IncNodeDegree(n2);
	}
      }
    }
  }
  
  /* putchar('\n');
     for (scan = graph_Nodes(graph); !list_Empty(scan); scan = list_Cdr(scan)) {
     n1 = list_Car(scan);
     printf("(%s,%d,%u), ",
     symbol_Name(symbol_GetSigSymbol(graph_NodeNumber(n1))),
     graph_NodeNumber(n1), ana_NodeDegree(n1));
     }
     graph_Print(graph); fflush(stdout); DBG */

  graph_DeleteDuplicateEdges(graph);
  
  /* Transform the undirected graph into a directed graph. */
  for (scan = graph_Nodes(graph); !list_Empty(scan); scan = list_Cdr(scan)) {
    n1 = list_Car(scan);
    result = list_Nil(); /* Collect edges from n1 that shall be deleted */ 
    for (scan2 = graph_NodeNeighbors(n1); !list_Empty(scan2);
	 scan2 = list_Cdr(scan2)) {
      int a1, a2;
      n2 = list_Car(scan2);
      /* Get the node degrees in the undirected graph with multiple edges */
      i  = ana_NodeDegree(n1);
      j  = ana_NodeDegree(n2);
      a1 = symbol_Arity(symbol_GetSigSymbol(graph_NodeNumber(n1)));
      a2 = symbol_Arity(symbol_GetSigSymbol(graph_NodeNumber(n2)));

      if (i > j || (i==j && a1 >= a2)) {
	/* symbol2 <= symbol1, so remove edge n1 -> n2 */
	result = list_Cons(n2, result);
      }
      if (i < j || (i==j && a1 <= a2)) {
	/* symbol1 <= symbol2, so remove edge n2 -> n1 */
	graph_DeleteEdge(n2, n1);
      }
      /* NOTE: If (i==j && a1==a2) both edges are deleted! */
    }
    /* Now delete edges from n1 */
    for ( ; !list_Empty(result); result = list_Pop(result))
      graph_DeleteEdge(n1, list_Car(result));
  }

  if (!list_Empty(distrPairs) && !ana_BidirectionalDistributivity(distrPairs)) {
    /* Enable RPO ordering, otherwise the default KBO will be used. */
    flag_SetFlagValue(Flags, flag_ORD, flag_ORDRPOS);
  }

  /* Now examine the list of distribute symbols */
  /* since they've highest priority.                  */
  for ( ; !list_Empty(distrPairs); distrPairs = list_Pop(distrPairs)) {
    scan = list_Car(distrPairs); /* A pair (Add, Mult) */
    /* Addition */
    n1 = graph_GetNode(graph,
		       symbol_Index((SYMBOL)list_PairFirst(scan)));
    /* Multiplication */
    n2 = graph_GetNode(graph, 
		       symbol_Index((SYMBOL)list_PairSecond(scan)));
    /* Remove any edges between n1 and n2 */
    graph_DeleteEdge(n1, n2);
    graph_DeleteEdge(n2, n1);
    /* Add one edge Addition -> Multiplication */
    graph_AddEdge(n1, n2);
    list_PairFree(scan);
  }

  /* fputs("\n------------------------",stdout);
     graph_Print(graph); fflush(stdout); DBG */

  /* Calculate the strongly connected components of the graph. */
  /* <i> is the number of SCCs. */
  i = graph_StronglyConnectedComponents(graph);

  /* Now create the precedence list by scanning the nodes.        */
  /* If there's a link between two strongly connected components  */
  /* c1 and c2 then component_num(c1) > component_num(c2), so the */
  /* following code creates a valid precedence list in descending */
  /* order.                                                       */
  result = list_Nil();
  while (i-- > 0) {   /* for i = numberOfSCCs -1 dowto 0 */
    for (scan = graph_Nodes(graph); !list_Empty(scan); scan = list_Cdr(scan)) {
      n1 = list_Car(scan);
      if (graph_NodeCompNum(n1) == i) {
	/* The symbol represented by the node <n> belongs to component <i> */
	s = symbol_GetSigSymbol(graph_NodeNumber(n1));
	result = list_Cons((POINTER)s, result);
      }
    }
  }

  /* putchar('\n');
     for (scan = result; !list_Empty(scan); scan = list_Cdr(scan)) {
     s = (SYMBOL) list_Car(scan);
     symbol_Print(s);
     fputs(" > ", stdout);
     }
     putchar('\n'); fflush(stdout); DBG */

  graph_Delete(graph);

  return result;
}
