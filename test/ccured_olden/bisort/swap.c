/* For copyright information, see olden_v1.0/COPYRIGHT */

#define COLLECT_SIZE 256
#define DFS_SIZE 20
#include "node.h"

#ifdef SS_PLAIN
#include "ssplain.h"
#endif SS_PLAIN


typedef struct {
  int top;
  HANDLE *handles[DFS_SIZE];
} stack;

#define push(s,v) (s)->handles[++((s)->top)] = v
#define pop(s) (s)->handles[((s)->top)--]
#define stackempty(s) ((s)->top < 0)  
void VisitCollect(HANDLE *t, local int *collect)
{
  register int val;
  val = t->value;
  *collect = val;
}

void VisitCollectReplace(HANDLE *t, local int *collect)
{
  register int temp = *collect;
  register int val = t->value;
  *collect = val;
  t->value = temp;
}

void VisitReplace(HANDLE *t, local int *collect)
{
  register int val = *collect;
  t->value = val;
}

void swapDFS(local stack *s, local int collection[], void visit())
{
  int num=0;
  
  while (!stackempty(s) && num < COLLECT_SIZE) 
    {
      HANDLE *v = pop(s);
      visit(v,&collection[num]);
      num++;
      if (v->left != NULL) 
	{
     HANDLE *child;
     child = v->right;
	  push(s,child);
     child = v->left;
	  push(s,child);
	}
    }
}

void NewSwapSubTree(HANDLE *t1, HANDLE *t2)
{
  local stack c1, r1, s2;
  int collection[COLLECT_SIZE];

  /*chatting("starting swapping\n");*/

  if (t1!=NULL) 
    {
      c1.top = -1;
      r1.top = -1;
      s2.top = -1;
      push(&c1,t1);
      push(&r1,t1);
      push(&s2,t2);
      while (!stackempty(&c1)) 
	{
     MLOCAL(t1);
	  swapDFS(&c1,collection,VisitCollect);
	  MLOCAL(t2);
	  swapDFS(&s2,collection,VisitCollectReplace);
	  MLOCAL(t1);
	  swapDFS(&r1,collection,VisitReplace);
	}
    }
  /*chatting("ending swapping\n");*/

}
  
  
int *Collect(HANDLE *t1, local int collection[])
{
  register int val;
  if (t1==NULL) return collection;
  MLOCAL(t1);
  val = t1->value;
  *collection = val;
  collection += 1;
  collection = Collect(t1->left,collection);
  collection = Collect(t1->right,collection);
  return collection;
}

int *Collect_Replace(HANDLE *t1, local int collection[])
{
  register int temp,val;
  if (t1==NULL) return collection;
  MLOCAL(t1);
  temp = *collection;
  val = t1->value;
  *collection = val;
  t1->value = temp;
  collection += 1;
  collection = Collect_Replace(t1->left,collection);
  collection = Collect_Replace(t1->right,collection);
  return collection;
}

int *Replace(HANDLE *t1, local int collection[])
{
  register int val;
  if (t1==NULL) return collection;
  MLOCAL(t1);
  val = *collection;
  t1->value = val;
  collection +=1;
  collection = Replace(t1->left,collection);
  collection = Replace(t1->right,collection);
  return collection;
}


void SwapSubTree(HANDLE *t1, HANDLE *t2)
{
  int collection[COLLECT_SIZE];
  HANDLE *t1loc, *t2loc;

  MLOCAL(t1);
  Collect(t1,collection);
  MLOCAL(t2);
  Collect_Replace(t2,collection);
  MLOCAL(t1);
  Replace(t1,collection);
}

