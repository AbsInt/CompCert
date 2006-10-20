/* make_graph.c - Create a graph to be solved for the electromagnetic
 *                problem in 3 dimensions.
 *
 * By:  Martin C. Carlisle
 * Date: Feb 23, 1994
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include "em3d.h"
#include "util.h"

#define NUM_H_NODES  n_nodes
#define H_NODE_DEGREE d_nodes

#define NUM_E_NODES  n_nodes
#define E_NODE_DEGREE d_nodes

int n_nodes;
int d_nodes;

node_t **make_table(int size)
{
  node_t **retval;

  retval = (node_t **) ALLOC(size*sizeof(node_t *));
  assert(retval);
  return retval;
}

// post:
//   all 'next' fields valid or null
//   to_nodes, from_nodes, coefs are dead
void fill_table(node_t **table, int size)
{
  int i;
  
  /* Now we fill the table with allocated nodes */
  for (i=0; i<size; i++)
    {
      table[i] = (node_t *) ALLOC(sizeof(node_t));
      table[i]->value = gen_uniform_double();
      table[i]->from_count = 0;

      if (i > 0) 
	table[i-1]->next = table[i];
    }
  table[size-1]->next = NULL;
}

// post:
//   nodes in 'nodelist' have their 'to_nodes' array created, of
//   size 'degree'; then this array is filled with pointers to
//   randomly-chosen nodes (no duplicates); 'from_count' in the
//   pointed-to node keeps track of its in-degree
void make_neighbors(node_t *nodelist, node_t **table, int tablesz,
		    int degree)
{
  node_t *cur_node;

  for(cur_node = nodelist; cur_node; cur_node=cur_node->next)
    {
      node_t *other_node;
      int j,k;

      cur_node->to_nodes = (node_t **) ALLOC(degree*(sizeof(node_t *)));
      for (j=0; j<degree; j++)
	{
	  /* Make sure no duplicates are generated */
	  do
	    {
	      other_node = table[gen_number(tablesz)];
	      for (k=0; k<j; k++)
		if (other_node == cur_node->to_nodes[k]) break;
	    }
	  while (k<j);
	  cur_node->to_nodes[j]=other_node;
	  other_node->from_count++; /* bad load: 50% */
	}
    }
}

// post:
//   from_nodes and coeffs get allocated, size specified by 'from_count',
//   which is the 'degree' from above; coeff's entries are set randomly,
//   from_nodes' entries left dead; from_count then set to 0
void update_from_coeffs(node_t *nodelist)
{
  node_t *cur_node;

  /* Setup coefficient and from_nodes vectors for h nodes */
  for (cur_node = nodelist; cur_node; cur_node=cur_node->next)
    {
      int from_count = cur_node->from_count;
      int k;

      cur_node->from_nodes = (node_t **) ALLOC(from_count * sizeof(node_t *));
      cur_node->coeffs = (double *) ALLOC(from_count * sizeof(double));
      for (k=0; k<from_count; k++)
	cur_node->coeffs[k] = gen_uniform_double();

      cur_node->from_count = 0;
    }
}

// post:
//   nodes pointed-to by those on 'nodelist' have their from_nodes' 
//   entries filled with back-edges; from_count is used to add
//   information contiguously; global algorithm structure keeps the
//   array access in bounds (we counted in-degree before, and that
//   count was used to allocate, and now we one again enumerate the
//   pointers to a node); perhaps a runtime check is in order here
void fill_from_fields(node_t *nodelist, int degree)
{
  node_t *cur_node;
  for(cur_node = nodelist; cur_node; cur_node = cur_node->next)
    {
      int j;

      for (j=0; j<degree; j++)
	{
	  node_t *other_node = cur_node->to_nodes[j];
	  other_node->from_nodes[other_node->from_count] = cur_node;
	  other_node->from_count++;
	}
    }
}

// post:
//   two arrays of nodes are created; all 'h' nodes are then pointed to
//   H_NODE_DEGREE 'e' nodes, and vice-versa for 'e' nodes; backedge
//   information is also computed; pointers to the first nodes of each 
//   set are stashed in a graph_t and returned (sets are linked together
//   as a linked list)
graph_t initialize_graph()
{
  node_t **h_table;
  node_t **e_table;
  graph_t retval;

  /* We start by creating a table of pointers to the h nodes */
  h_table = make_table(NUM_H_NODES);
  fill_table(h_table,NUM_H_NODES);

  /* We repeat the same for the e nodes */
  e_table = make_table(NUM_E_NODES);
  fill_table(e_table,NUM_E_NODES);

  /* At this point, for each h node, we give it the appropriate number
     of neighbors as defined by the degree */
  make_neighbors(h_table[0],e_table,NUM_E_NODES,H_NODE_DEGREE);
  make_neighbors(e_table[0],h_table,NUM_H_NODES,E_NODE_DEGREE);

  /* We now create from count and initialize coefficients */
  update_from_coeffs(h_table[0]);
  update_from_coeffs(e_table[0]);

  /* Fill the from fields in the nodes */
  fill_from_fields(h_table[0],H_NODE_DEGREE);
  fill_from_fields(e_table[0],E_NODE_DEGREE);

  retval.e_nodes=e_table[0];
  retval.h_nodes=h_table[0];
  
  free(h_table);
  free(e_table);

  return retval;
}

  

