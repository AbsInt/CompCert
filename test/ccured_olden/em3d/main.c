#include <stdio.h>

#include "em3d.h"
#include "make_graph.h"

#define chatting(A)

void print_graph(graph_t graph) 
{
#ifdef GET_OUT
  node_t *cur_node;

  for(cur_node=graph.e_nodes; cur_node; cur_node=cur_node->next)
    {
      chatting(("E: value %f, from_count %d\n",cur_node->value,
	       cur_node->from_count));
    }
  for(cur_node=graph.h_nodes; cur_node; cur_node=cur_node->next)
    {
      chatting(("H: value %f, from_count %d\n",cur_node->value,
	       cur_node->from_count));
    }
#endif GET_OUT 
}

int iters;

int main(int argc, char *argv[])
{
  int i;
  graph_t graph;

  dealwithargs(argc,argv);
  graph=initialize_graph();
  print_graph(graph);

  for (i = 0; i < iters; i++)
    {
      compute_nodes(graph.e_nodes);
      compute_nodes(graph.h_nodes);
      fprintf(stderr, "Completed a computation phase: %d\n", i);
      print_graph(graph);
    }
  return 0;
}
