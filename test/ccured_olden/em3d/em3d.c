#include "em3d.h"

void compute_nodes(node_t *nodelist)
{
  int i;
  
  for (; nodelist; nodelist = nodelist->next)
    for (i=0; i < nodelist->from_count; i++) /* bad load */
      {
	node_t *other_node = nodelist->from_nodes[i]; /* bad load */ 
	double coeff = nodelist->coeffs[i]; /* bad load */
	double value = other_node->value; /* bad load: 50% */ 
	
	nodelist->value -= coeff * value;
      }
}
