#include "tsp.h"

#ifndef PLAIN
#include "mem-ref.h"
#ifdef FUTURES
#include "future-cell.h"
#endif
#endif

#ifndef PLAIN
#define NULL 0
#endif

#ifdef VERIFY_AFFINITIES
#include "affinity.h"
CHECK1_ACCUM(Tree,next,list)
#endif

static Tree conquer(Tree t);
static Tree merge(Tree a, Tree b, Tree t, int nproc);
static Tree makelist(Tree t);
static void reverse(Tree t);
static double distance(Tree a, Tree b);
extern double sqrt(double a);

/* Find Euclidean distance from a to b */
static double distance(Tree a, Tree b) {
  double ax,ay,bx,by;

  ax = a->x; ay = a->y;
  bx = b->x; by = b->y;
  return (sqrt((ax-bx)*(ax-bx)+(ay-by)*(ay-by)));
}

/* sling tree nodes into a list -- requires root to be tail of list */
/* only fills in next field, not prev */
static Tree makelist(Tree t) {
  Tree left, right;
  Tree tleft,tright;
  Tree retval = t;

  if (!t) return NULL;

  /*chatting("makelist\n");*/
  left = makelist(t->left); /* head of left list */
  right = makelist(t->right); /* head of right list */

  if (right) { retval = right; tright = t->right; tright->next = t; }
  if (left) { retval=left; tleft=t->left; tleft->next = (right) ? right : t; }
  t->next = NULL;
  /*chatting("end makelist\n");*/

  return retval;
}

/* reverse orientation of list */
static void reverse(Tree t) {
  Tree prev,back,next,tmp;

  if (!t) return;
  /*chatting("REVERSE\n");*/
  /*print_list(t);*/
  prev = t->prev;
  prev->next = NULL;
  t->prev = NULL;
  back = t;
  tmp = t;
  for (t=t->next; t; back=t,t=next) {
    next = t->next;
    t->next = back;
    back->prev = t;
    }
  tmp->next = prev;
  prev->prev = tmp;
  /*printf("REVERSE result\n");*/
  /*print_list(tmp);*/
  /*printf("End REVERSE\n");*/
}

/* Use closest-point heuristic from Cormen Leiserson and Rivest */
static Tree conquer(Tree t) {
  Tree cycle,tmp,min,prev,next,donext;
  double mindist,test;
  double mintonext, mintoprev, ttonext, ttoprev;

  if (!t) return NULL;
  t=makelist(t);
 
  /*printf("CONQUER\n");*/
  /* Create initial cycle */
  cycle = t;
  t = t->next;
  cycle->next = cycle;
  cycle->prev = cycle;

  for (; t; t=donext) { /* loop over remaining points */
    donext = t->next; /* value won't be around later */
    min = cycle;
    mindist = distance(t,cycle);
    for (tmp=cycle->next; tmp!=cycle; tmp=tmp->next) {
      test = distance(tmp,t);
      if (test < mindist) {
        mindist = test;
        min = tmp;
        } /* if */
      } /* for tmp... */
    next = min->next;
    prev = min->prev;
    mintonext = distance(min,next);
    mintoprev = distance(min,prev);
    ttonext = distance(t,next);
    ttoprev = distance(t,prev);
    if ((ttoprev - mintoprev) < (ttonext - mintonext)) {
      /* insert between min and prev */
      prev->next = t;
      t->next = min;
      t->prev = prev;
      min->prev = t;
      }
    else {
      next->prev = t;
      t->next = next;
      min->next = t;
      t->prev = min;
      }
    } /* for t... */
  /*print_list(cycle);*/
  /*printf("End CONQUER\n");*/
  return cycle;
}

/* Merge two cycles as per Karp */
static Tree merge(Tree a, Tree b, Tree t, int nproc) {
  Tree min,next,prev,tmp;
  double mindist,test,mintonext,mintoprev,ttonext,ttoprev;
  Tree n1,p1,n2,p2;
  double tton1,ttop1,tton2,ttop2;
  double n1ton2,n1top2,p1ton2,p1top2;
  int choice;
  int i;

  /* Compute location for first cycle */
  min = a;
  mindist = distance(t,a);
  tmp = a;
#ifdef VERIFY_AFFINITIES
  Accumulate_list(a,a);
  Accumulate_list(b,b);
#endif
  for (a=a->next; a!=tmp; a=a->next) {
    test = distance(a,t);
    if (test < mindist) {
      mindist = test;
      min = a;
      } /* if */
    } /* for a... */
  next = min->next;
  prev = min->prev;
  mintonext = distance(min,next);
  mintoprev = distance(min,prev);
  ttonext = distance(t,next);
  ttoprev = distance(t,prev);
  if ((ttoprev - mintoprev) < (ttonext - mintonext)) {
    /* would insert between min and prev */
    p1 = prev;
    n1 = min;
    tton1 = mindist;
    ttop1 = ttoprev;
    }
  else { /* would insert between min and next */
    p1 = min;
    n1 = next;
    ttop1 = mindist;
    tton1 = ttonext;
    }
 
  /* Compute location for second cycle */
  min = b;
  mindist = distance(t,b);
  tmp = b;
  for (b=b->next; b!=tmp; b=b->next) {
    test = distance(b,t);
    if (test < mindist) {
      mindist = test;
      min = b;
      } /* if */
    } /* for tmp... */
  next = min->next;
  prev = min->prev;
  mintonext = distance(min,next);
  mintoprev = distance(min,prev);
  ttonext = distance(t,next);
  ttoprev = distance(t,prev);
  if ((ttoprev - mintoprev) < (ttonext - mintonext)) {
    /* would insert between min and prev */
    p2 = prev;
    n2 = min;
    tton2 = mindist;
    ttop2 = ttoprev;
    }
  else { /* would insert between min and next */
    p2 = min;
    n2 = next;
    ttop2 = mindist;
    tton2 = ttonext;
    }

  /* Now we have 4 choices to complete:
     1:t,p1 t,p2 n1,n2
     2:t,p1 t,n2 n1,p2
     3:t,n1 t,p2 p1,n2
     4:t,n1 t,n2 p1,p2 */
  n1ton2 = distance(n1,n2);
  n1top2 = distance(n1,p2);
  p1ton2 = distance(p1,n2);
  p1top2 = distance(p1,p2);

  mindist = ttop1+ttop2+n1ton2; 
  choice = 1;

  test = ttop1+tton2+n1top2;
  if (test<mindist) {
    choice = 2;
    mindist = test;
    }

  test = tton1+ttop2+p1ton2;
  if (test<mindist) {
    choice = 3;
    mindist = test;
    }
  
  test = tton1+tton2+p1top2;
  if (test<mindist) choice = 4;

/*chatting("p1,n1,t,p2,n2 0x%x,0x%x,0x%x,0x%x,0x%x\n",p1,n1,t,p2,n2);*/
  switch (choice) {
    case 1:
      /* 1:p1,t t,p2 n2,n1 -- reverse 2!*/
      /*reverse(b);*/
      reverse(n2);
      p1->next = t;
      t->prev = p1;
      t->next = p2;
      p2->prev = t;
      n2->next = n1;
      n1->prev = n2;
      break;
    case 2:
      /* 2:p1,t t,n2 p2,n1 -- OK*/
      p1->next = t;
      t->prev = p1;
      t->next = n2;
      n2->prev = t;
      p2->next = n1;
      n1->prev = p2;
      break;
    case 3:
      /* 3:p2,t t,n1 p1,n2 -- OK*/
      p2->next = t;
      t->prev = p2;
      t->next = n1;
      n1->prev = t;
      p1->next = n2;
      n2->prev = p1;
      break;
    case 4:
      /* 4:n1,t t,n2 p2,p1 -- reverse 1!*/
      /*reverse(a);*/
      reverse(n1);
      n1->next = t;
      t->prev = n1;
      t->next = n2;
      n2->prev = t;
      p2->next = p1;
      p1->prev = p2;
      break;
    }
  return t;
}

/* Compute TSP for the tree t -- use conquer for problems <= sz */
Tree tsp(Tree t,int sz,int nproc) {
  Tree left,right;
  Tree leftval;
#ifdef FUTURES
  future_cell_pointer fc;
#endif
  Tree rightval;
  int nproc_2 = nproc/2;

  if (t->sz <= sz) return conquer(t);

  left = t->left; right = t->right;
#ifndef FUTURES
  leftval = tsp(left,sz,nproc_2);
#else
  FUTURE(left,sz,nproc_2,tsp,&fc);
#endif
  rightval = tsp(right,sz,nproc_2);
#ifdef FUTURES
  leftval = (Tree) TOUCH(&fc);
  leftval = (Tree) fc.value;
  return merge(leftval,rightval,t,nproc);
#else
  return merge(leftval,rightval,t,nproc);
#endif
}
