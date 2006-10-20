#include "tsp.h"
#include <stdio.h>
#include <stdlib.h>

#ifndef PLAIN
#include <cm/cmmd.h>
#include "mem-ref.h"
#endif

#ifdef VERIFY_AFFINITIES
#include "affinity.h"
CHECK2(Tree,left,right,tree)
#endif

int flag;
int __NumNodes, __NDim;

int mylog(int num)
{
  int j=0,k=1;
  
  while(k<num) { k*=2; j++; }
  return j;
} 

int dealwithargs(void)
{
  int num;

  flag = 0;
  __NumNodes = 4;

  __NDim = mylog(__NumNodes);

  num = 150000;

  return num;
}

void print_tree(Tree t)
{
  Tree left,right;
  double x,y;

  if (!t) return;
  x = t->x; y = t->y;
  chatting("x=%f,y=%f\n",x,y);
  left = t->left; right=t->right;
  print_tree(left);
  print_tree(right);
}

void print_list(Tree t)
{
  Tree tmp;
  double x,y;

  if (!t) return;
  x = t->x; y = t->y;
  chatting("%f %f\n",x,y);
  for (tmp=t->next; tmp!=t; tmp=tmp->next) 
    {
    x = tmp->x; y = tmp->y;
    chatting("%f %f\n",x,y);
    }
}

double wallclock;

int main()
{
  Tree t;
  int num;

  num = dealwithargs();
  
  chatting("Building tree of size %d\n",num);
  t=build_tree(num,0,0,__NumNodes,0.0,1.0,0.0,1.0);
#ifdef VERIFY_AFFINITIES
  Docheck_tree(t);
#endif
  if (!flag) chatting("Past build\n");
  if (flag) chatting("newgraph\n");
  if (flag) chatting("newcurve pts\n");


  timer_start(0);
  tsp(t,150,__NumNodes);
  timer_stop(0);
  if (flag) print_list(t);
  if (flag) chatting("linetype solid\n");
  chatting("Time for TSP = %f\n", timer_elapsed(0));
#ifdef VERIFY_AFFINITIES
  Print_Accumulated_list();
#endif

#ifdef FUTURES
  __ShutDown(0);
#endif
  exit(0);
}
