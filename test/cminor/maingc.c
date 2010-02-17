/* Test harness for the simple garbage collectors */

#include <stdio.h>
#include <stddef.h>
#include <stdlib.h>
#include <math.h>

extern int init_heap(int hsize);

enum block_kind { RAWDATA = 0, PTRDATA = 1, CLOSURE = 2 };

struct rootblock {
  struct rootblock * next;
  int numroots;
  void * root[8];
};

extern void * alloc_block(struct rootblock * roots,
                          enum block_kind kind,
                          int size);

#ifdef DEBUG
extern void check_heap(void);
#endif

void gc_alarm(int live)
{
  if (live == -1)
    printf("<GC...>\n");
  else
    printf("<GC...%d bytes live>\n", live);
#ifdef DEBUG
  check_heap();
#endif
}

/* Test with binary trees */

typedef struct {
  long i;
} boxedInt;

boxedInt * BoxInt(struct rootblock * r, long n)
{
  boxedInt * new = (boxedInt *) alloc_block(r, RAWDATA, sizeof(long));
  new->i = n;
  return new;
}

typedef struct tn {
    struct tn*    left;
    struct tn*    right;
    boxedInt *    item;
} treeNode;

treeNode* NewTreeNode(struct rootblock * r,
                      treeNode* left, treeNode* right, long item)
{
  struct rootblock nr;
  treeNode* new;
  boxedInt* bitem;
  
  nr.next = r; nr.numroots = 2; nr.root[0] = left; nr.root[1] = right;
  
  bitem = BoxInt(&nr, item);
  
  nr.numroots = 3; nr.root[2] = bitem;
  
  new = (treeNode*) alloc_block(&nr, PTRDATA, sizeof(treeNode));
  
  new->left = (treeNode *) nr.root[0];
  new->right = (treeNode *) nr.root[1];
  new->item = (boxedInt *) nr.root[2];
  
  return new;
}


long ItemCheck(treeNode* tree)
{
  if (tree->left == NULL)
    return tree->item->i;
  else
    return tree->item->i + ItemCheck(tree->left) - ItemCheck(tree->right);
}


treeNode* BottomUpTree(struct rootblock * r, long item, unsigned depth)
{
  struct rootblock nr;

  if (depth > 0) {
    nr.next = r; nr.numroots = 0;
    nr.root[0] = BottomUpTree(&nr, 2 * item - 1, depth - 1);
    nr.numroots = 1;
    nr.root[1] = BottomUpTree(&nr, 2 * item, depth - 1);
    nr.numroots = 2;
    return NewTreeNode(&nr,
                       (treeNode *) nr.root[0],
                       (treeNode *) nr.root[1],
                       item);
  } else {
    return NewTreeNode(r, NULL, NULL, item);
  }
}

treeNode* SkinnyTree(struct rootblock * r, unsigned depth)
{
  struct rootblock nr;

  if (depth > 0) {
    nr.next = r; nr.numroots = 0;
    nr.root[0] = SkinnyTree(&nr, depth - 1);
    nr.numroots = 1;
    return NewTreeNode(&nr,
                       (treeNode *) nr.root[0],
                       (treeNode *) nr.root[0],
                       depth);
  } else {
    return NULL;
  }
}

void test(unsigned N)
{
  unsigned depth, minDepth, maxDepth, stretchDepth;
  struct rootblock r;

  minDepth = 4;

  if ((minDepth + 2) > N)
    maxDepth = minDepth + 2;
  else
    maxDepth = N;

  stretchDepth = maxDepth + 1;

  r.next = NULL; r.numroots = 0;

  r.root[0] = BottomUpTree(&r, 0, stretchDepth);
  printf
    (
     "stretch tree of depth %u\t check: %li\n",
     stretchDepth,
     ItemCheck(r.root[0])
     );

  r.root[0] = SkinnyTree(&r, stretchDepth);

  r.root[0] = BottomUpTree(&r, 0, maxDepth);
  r.numroots = 1;

  r.root[1] = SkinnyTree(&r, stretchDepth);
  r.numroots = 2;

  for (depth = minDepth; depth <= maxDepth; depth += 2) {
    long i, iterations, check;

    iterations = pow(2, maxDepth - depth + minDepth);

    check = 0;

    for (i = 1; i <= iterations; i++) {
      r.root[2] = BottomUpTree(&r, i, depth);
      check += ItemCheck(r.root[2]);
      r.root[2] = BottomUpTree(&r, -i, depth);
      check += ItemCheck(r.root[2]);
    }

    printf
      (
       "%li\t trees of depth %u\t check: %li\n",
       iterations * 2,
       depth,
       check
       );
  }

  printf
    (
     "long lived tree of depth %u\t check: %li\n",
     maxDepth,
     ItemCheck(r.root[0])
     );

  printf
    (
     "skinny tree of depth %u\t\t check: %li\n",
     stretchDepth,
     ItemCheck(r.root[1])
     );
}

int main(int argc, char ** argv)
{
  int N, heapsize;

  N = argc > 1 ? atoi(argv[1]) : 16;
  heapsize = argc > 2 ? atoi(argv[2]) : 8 * 1024 * 1024;

  if (init_heap(heapsize) == -1) {
    fprintf(stderr, "Failed to allocate heap.\n");
    return 2;
  }
  test(N);
}  

/*********************************

PROGRAM OUTPUT
==============
stretch tree of depth 17	 check: -1
131072	 trees of depth 4	 check: -131072
32768	 trees of depth 6	 check: -32768
8192	 trees of depth 8	 check: -8192
2048	 trees of depth 10	 check: -2048
512	 trees of depth 12	 check: -512
128	 trees of depth 14	 check: -128
32	 trees of depth 16	 check: -32
long lived tree of depth 16	 check: -1

***********************************/

