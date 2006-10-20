/* For copyright information, see olden_v1.0/COPYRIGHT */

/* build.c
 *
 * By:  Martin C. Carlisle
 * 6/15/94
 * builds the tree for the Power Pricing problem
 *
 * based on code by:  Steve Lumetta, Sherry Li, and Ismail Khalil
 * University of California at Berkeley
 */

#include "power.h"

Root build_tree() 
{
  register int i;
  register Root t;
#ifdef FUTURES
  int j;
  future_cell_int fc[NUM_FEEDERS];
#else
  register Lateral l;
#endif
  
  t = (Root) ALLOC(0,sizeof(*t));
#ifdef FUTURES
  for (i=0,j=0; i<NUM_FEEDERS; i++,j+=LATERALS_PER_FEEDER) {
    FUTURE(j,LATERALS_PER_FEEDER,build_lateral,&fc[i]);
  }
  for (i=0; i<NUM_FEEDERS; i++) {
    TOUCH(&fc[i]);
    t->feeders[i]=(Lateral) fc[i].value;
  }
#else
  for (i=0; i<NUM_FEEDERS; i++) {
    /* Insert future here, split into two loops */
    l = build_lateral(i*LATERALS_PER_FEEDER,LATERALS_PER_FEEDER);
    t->feeders[i]=l;
  }
#endif
  t->theta_R = 0.8;
  t->theta_I = 0.16;
  return t;
}

Lateral build_lateral(int i, int num)
{
  register int j,k;
  register Lateral l;
  register Branch b;
#ifdef FUTURES
  future_cell_int fc;
#else
  register Lateral next;
#endif
 
  if (num == 0) return NULL;

#ifndef PLAIN
  { int x,m,q,proc;
  x = (i+num-1)*BRANCHES_PER_LATERAL+BRANCHES_PER_LATERAL-1;
  m = 1000%__NumNodes;
  q = 1000/__NumNodes;
  if (x<m*(q+1)) proc = x/(q+1);
  else proc = (x-m)/q;
  l = (Lateral) ALLOC(__NumNodes-1-proc,sizeof(*l));
  }
#else
  l = (Lateral) ALLOC(0,sizeof(*l));
#endif

#ifdef FUTURES
  FUTURE(i,num-1,build_lateral,&fc);
  b = build_branch(i*BRANCHES_PER_LATERAL,(num-1)*BRANCHES_PER_LATERAL,
    BRANCHES_PER_LATERAL);
#else
  next = build_lateral(i,num-1);
  b = build_branch(i*BRANCHES_PER_LATERAL,(num-1)*BRANCHES_PER_LATERAL,
    BRANCHES_PER_LATERAL);
#endif

#ifdef FUTURES
  TOUCH(&fc); 
  l->next_lateral = (Lateral) fc.value;
#else
  l->next_lateral = next;
#endif
  l->branch = b;
  l->R = 1/300000.0;
  l->X = 0.000001;
  l->alpha = 0.0;
  l->beta = 0.0;
  return l;
}

Branch build_branch(int i, int j, int num)
{
  register Leaf l;
  register Branch b;
#ifdef FUTURES
  future_cell_int fc;
#endif

  if (num == 0) return NULL;
  /* allocate branch */
#ifndef PLAIN
  { int x,m,q,proc;
  x = i+j+num-1;
  m = 1000%__NumNodes;
  q = 1000/__NumNodes;
  if (x<m*(q+1)) proc = x/(q+1);
  else proc = (x-m)/q;
  b = (Branch) ALLOC(__NumNodes-1-proc,sizeof(*b));
  }
#else
  b = (Branch) ALLOC(0,sizeof(*b));
#endif
  
  /* fill in children */
#ifndef FUTURES
  b->next_branch= build_branch(i,j,num-1);
#else
  FUTURE(i,j,num-1,build_branch,&fc);
#endif

  for (i=0; i<LEAVES_PER_BRANCH; i++) {
    l = build_leaf();
    b->leaves[i] = l;
  }
  
 
#ifdef FUTURES
  TOUCH(&fc);
  b->next_branch = (Branch) fc.value;
#endif
  
  /* fill in values */
  b->R = 0.0001;
  b->X = 0.00002;
  b->alpha = 0.0;
  b->beta = 0.0;
  return b;
}

Leaf build_leaf()
{
  register Leaf l;

  l = (Leaf) mymalloc(sizeof(*l));
  l->D.P = 1.0;
  l->D.Q = 1.0;
  return l;
}
