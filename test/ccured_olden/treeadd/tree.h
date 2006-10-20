/* For copyright information, see olden_v1.0/COPYRIGHT */

/* tree.h
 */

typedef struct tree {
    int		val;
    struct tree *left, *right;
} tree_t;

#ifndef SS_PLAIN
#define NULL	0
#endif SS_PLAIN

extern tree_t *TreeAlloc (/*int level*/);

extern int level;
extern int iters;
