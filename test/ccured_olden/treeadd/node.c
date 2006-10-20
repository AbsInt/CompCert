/* For copyright information, see olden_v1.0/COPYRIGHT */

/* node.c
 */
#include <stdio.h>
#ifdef SS_PLAIN
#include "ssplain.h"
#endif SS_PLAIN

#include "tree.h"


int dealwithargs(int argc, char *argv[]);

typedef struct {
    long 	level;
} startmsg_t;

int TreeAdd (/* tree_t *t */);
extern tree_t *TreeAlloc (/* int level */);

main (int argc, char *argv[])
{
    tree_t	*root;
    int i, result = 0;

    filestuff();
    (void)dealwithargs(argc, argv);

    chatting("Treeadd with %d levels\n", level);

    chatting("About to enter TreeAlloc\n"); 
    root = TreeAlloc (level);
    chatting("About to enter TreeAdd\n"); 
    
    for (i = 0; i < iters; i++) 
      {
	fprintf(stderr, "Iteration %d...", i);
	result = TreeAdd (root);
	fprintf(stderr, "done\n");
      }

    chatting("Received result of %d\n",result);
    exit(0);
}

/* TreeAdd:
 */
int TreeAdd (t)
     register tree_t	*t;
{
  if (t == NULL)  
    {
      return 0;
    }
  else 
    {
      int leftval;
      int rightval;
      tree_t *tleft, *tright;
      int value;
      
      tleft = t->left;
      leftval = TreeAdd(tleft);
      tright = t->right;
      rightval = TreeAdd(tright);

      value = t->val;
      return leftval + rightval + value;
    }
} /* end of TreeAdd */



