/* For copyright information, see olden_v1.0/COPYRIGHT */

/* tree-alloc.c
 */

#ifdef SS_PLAIN
#include "ssplain.h"
#endif SS_PLAIN

#include "tree.h"


tree_t *TreeAlloc (level)
    int		level;
{

  if (level == 0)
    {
      return NULL;
    }
  else 
    {
      struct tree *new, *right, *left;
      
      new = (struct tree *) mymalloc(sizeof(tree_t));
      left = TreeAlloc(level-1);
      right=TreeAlloc(level-1);
      new->val = 1;
      new->left = (struct tree *) left;
      new->right = (struct tree *) right;
      return new;
    }
}
