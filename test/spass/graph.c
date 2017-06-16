/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                       GRAPHS                           * */
/* *                                                        * */
/* *  $Module:   GRAPH                                      * */ 
/* *                                                        * */
/* *  Copyright (C) 1998, 2000, 2001 MPI fuer Informatik    * */
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

#include "graph.h"


static LIST graph_ROOTS;      /* used as stack by SCC algorithm */
static LIST graph_UNFINISHED; /* used as stack by SCC algorithm */


void graph_NodePrint(GRAPHNODE Node)
/**************************************************************
  INPUT:   A graph node.
  RETURNS: Nothing.
  EFFECT:  Prints some node information to stdout.
***************************************************************/
{
  printf("(%d,%d,%d) ", graph_NodeNumber(Node), graph_NodeDfsNum(Node),
	 graph_NodeCompNum(Node));
}


GRAPH graph_Create(void)
/**************************************************************
  INPUT:   None.
  RETURNS: A new graph without nodes and edges.
***************************************************************/
{
  GRAPH result;

  result = memory_Malloc(sizeof(GRAPH_STRUCT));
  result->size      = 0;
  result->dfscount  = 0;
  result->compcount = 0;
  result->nodes     = list_Nil();
  return result;
}


void graph_Delete(GRAPH Graph)
/**************************************************************
  INPUT:   A graph.
  RETURNS: Nothing.
  EFFECT:  All memory required by the graph and its nodes
           is freed.
***************************************************************/
{
  for ( ; !list_Empty(Graph->nodes); Graph->nodes = list_Pop(Graph->nodes)) {
    list_Delete(graph_NodeNeighbors(list_Car(Graph->nodes)));
    memory_Free(list_Car(Graph->nodes), sizeof(GRAPHNODE_STRUCT));
  }
  memory_Free(Graph, sizeof(GRAPH_STRUCT));
}


GRAPHNODE graph_GetNode(GRAPH Graph, NAT Number)
/**************************************************************
  INPUT:   A graph and the ID of a node.
  RETURNS: The node with the requested number or NULL
           if such a node doesn't exist.
***************************************************************/
{
  LIST scan;

  for (scan = Graph->nodes; !list_Empty(scan); scan= list_Cdr(scan)) {
    if (graph_NodeNumber(list_Car(scan)) == Number)
      return list_Car(scan);
  }

  return NULL;
}


GRAPHNODE graph_AddNode(GRAPH Graph, NAT Number)
/**************************************************************
  INPUT:   A graph and the ID of a node.
  RETURNS: A node with the requested number.
  EFFECT:  If the graph has no such node, a new node is created.
***************************************************************/
{
  GRAPHNODE result;

  result = graph_GetNode(Graph, Number);
  if (result == NULL) {
    result = memory_Malloc(sizeof(GRAPHNODE_STRUCT));
    Graph->nodes      = list_Cons(result, Graph->nodes);
    result->number    = Number;
    result->dfs_num   = -1;
    result->comp_num  = -1;
    result->info      = NULL;
    result->neighbors = list_Nil();
  }
  return result;
}


void graph_AddEdge(GRAPHNODE From, GRAPHNODE To)
/**************************************************************
  INPUT:   Two graph nodes.
  RETURNS: Nothing.
  EFFECT:  Adds a single (directed) edge (From, To).
***************************************************************/
{
  From->neighbors = list_Cons(To, From->neighbors);
}


void graph_DeleteEdge(GRAPHNODE From, GRAPHNODE To)
/**************************************************************
  INPUT:   Two graph nodes.
  RETURNS: Nothing.
  EFFECT:  Removes ALL edges (From, To) from a graph.
***************************************************************/
{
  From->neighbors = list_PointerDeleteElement(From->neighbors, To);
}


void graph_DeleteDuplicateEdges(GRAPH Graph)
/**************************************************************
  INPUT:   A graph.
  RETURNS: Nothing.
  EFFECT:  Removes duplicate edges between all nodes.
***************************************************************/
{
  LIST scan;

  for (scan = graph_Nodes(Graph); !list_Empty(scan); scan = list_Cdr(scan)) {
    GRAPHNODE n = list_Car(scan);
    n->neighbors = list_PointerDeleteDuplicates(n->neighbors);
  }
}


void graph_SortNodes(GRAPH Graph, BOOL (*SortFunction)(GRAPHNODE, GRAPHNODE))
/**************************************************************
  INPUT:   A graph and a sorting function for graph nodes.
  RETURNS: Nothing.
  EFFECT:  The node list is sorted with respect to the
           sorting function.
***************************************************************/
{
  Graph->nodes = list_Sort(graph_Nodes(Graph),
			   (BOOL (*) (POINTER, POINTER)) SortFunction);  
}


static void graph_ReinitDFS(GRAPH Graph)
/**************************************************************
  INPUT:   A graph.
  RETURNS: Nothing.
  EFFECT:  Prepares the graph and its nodes for a new DFS run.
           The DFS and COMP numbers are reset.
***************************************************************/
{
  LIST scan;

  Graph->dfscount  = 0;
  Graph->compcount = 0;

  for (scan = graph_Nodes(Graph); !list_Empty(scan); scan = list_Cdr(scan)) {
    graph_NodeSetDfsNum(list_Car(scan), -1);
    graph_NodeSetCompNum(list_Car(scan), -1);
  }
}


static void graph_InternSCC(GRAPH Graph, GRAPHNODE Node)
/**************************************************************
  INPUT:   A graph and a node of the graph.
  RETURNS: Nothing.
  EFFECT:  This is an internal function used by
           graph_StronglyConnnectedComponents.
	   It sets information in the graph structure which
           specifies the strongly connected components of
           the graph.
***************************************************************/
{
  GRAPHNODE n;
  LIST      scan;
  NAT       act_dfs;

  act_dfs = (Graph->dfscount)++;
  graph_NodeSetDfsNum(Node, act_dfs);

  graph_UNFINISHED = list_Push(Node, graph_UNFINISHED);
  graph_ROOTS      = list_Push(Node, graph_ROOTS);

  /* putchar('\n'); list_Apply(graph_NodePrint, graph_UNFINISHED);
     putchar('\n'); list_Apply(graph_NodePrint, graph_ROOTS);
     fflush(stdout); DBG */

  for (scan = graph_NodeNeighbors(Node);
       !list_Empty(scan); scan = list_Cdr(scan)) {
    n = list_Car(scan);
    if (!graph_NodeVisited(n)) {
      graph_InternSCC(Graph, n);  /* Visit <n> */
    } else if (!graph_NodeCompleted(n)) {
      /* <n> was visited but is not yet in a permanent component */
      NAT dfs_num_of_n = graph_NodeDfsNum(n);
      while (!list_StackEmpty(graph_ROOTS) &&
	     graph_NodeDfsNum(list_Top(graph_ROOTS)) > dfs_num_of_n)
	graph_ROOTS = list_Pop(graph_ROOTS);
      /* putchar('\n'); list_Apply(symbol_Print, graph_UNFINISHED);
	 putchar('\n'); list_Apply(symbol_Print, graph_ROOTS);
	 fflush(stdout); DBG */
    }
  }

  /* printf("\nDFS(%u) complete.", graph_NodeNumber(Node)); DBG */

  if (Node == list_Top(graph_ROOTS)) {
    /* Node is root of a component, so make this component permanent */
    while (!list_StackEmpty(graph_UNFINISHED) &&
	   graph_NodeDfsNum(list_Top(graph_UNFINISHED)) >= act_dfs) {
      n = list_Top(graph_UNFINISHED);
      graph_UNFINISHED = list_Pop(graph_UNFINISHED);
      graph_NodeSetCompNum(n, Graph->compcount);
    }
    Graph->compcount++;
    graph_ROOTS = list_Pop(graph_ROOTS);
  }

  /* putchar('\n'); list_Apply(graph_NodePrint, graph_UNFINISHED);
     putchar('\n'); list_Apply(graph_NodePrint, graph_ROOTS); fflush(stdout); DBG */
}


NAT graph_StronglyConnectedComponents(GRAPH Graph)
/**************************************************************
  INPUT:   A graph.
  RETURNS: The number of strongly connected components
           in the graph.
  EFFECT:  This function sets the component numbers of all nodes.
           Two nodes that belong to the same component will have
           the same component number.
	   The algorithm is taken from the script
           "Datenstrukturen und Algorithmen" by Kurt Mehlhorn
           in winter semester 1997/98, pages 86-92.
***************************************************************/
{
  LIST scan;

  if (Graph->dfscount != 0)
    graph_ReinitDFS(Graph); /* Reinitializations for Depth First Search */

  graph_ROOTS          = list_Nil();
  graph_UNFINISHED     = list_Nil();

  for (scan = graph_Nodes(Graph); !list_Empty(scan); scan = list_Cdr(scan)) {
    if (!graph_NodeVisited(list_Car(scan)))
      graph_InternSCC(Graph, list_Car(scan));
  }
  return Graph->compcount;
}


void graph_Print(GRAPH Graph)
/**************************************************************
  INPUT:   A graph.
  RETURNS: Nothing.
  EFFECT:  The adjacency list representation of the graph
           is printed to stdout.
***************************************************************/
{
  LIST scan1, scan2;
  
  for (scan1 = graph_Nodes(Graph); !list_Empty(scan1); scan1 = list_Cdr(scan1)) {
    printf("\n%u -> ", graph_NodeNumber(list_Car(scan1)));
    for (scan2 = graph_NodeNeighbors(list_Car(scan1)); !list_Empty(scan2);
	 scan2 = list_Cdr(scan2)) {
      printf("%u,", graph_NodeNumber(list_Car(scan2)));
    }
  }
}
