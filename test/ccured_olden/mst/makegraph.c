/* For copyright information, see olden_v1.0/COPYRIGHT */

#include "mst.h"
#include "ssplain.h"

#define CONST_m1 10000
#define CONST_b 31415821
#define RANGE 2048
static int HashRange;

static int mult(int p, int q)
{
   int p1, p0, q1, q0;

   p1=p/CONST_m1; p0=p%CONST_m1;
   q1=q/CONST_m1; q0=q%CONST_m1;
   return (((p0*q1+p1*q0) % CONST_m1)*CONST_m1+p0*q0);
}

static int mst_random(int seed)
{
  int tmp;
  tmp = (mult(seed,CONST_b)+1);
  return tmp;
}

static int compute_dist(int i,int j, int numvert)
{
  int less, gt;
  if (i<j) {less = i; gt = j;} else {less = j; gt = i;}
  return (mst_random(less*numvert+gt) % RANGE)+1;
}

static int hashfunc(unsigned int key)
{
  return ((key>>4) % HashRange);
}

static void AddEdges(Graph retval, int numvert) 
{
  Vertex src, dest;
  Hash hash;
  int i, j, dist, num_inserted = 0;
  
  for (j = 0; j < numvert; j++)
    {
      src = &(retval->vlist[j]); 
      hash = src->edgehash;

      for (i=0; i<numvert; i++) 
        {
          if (i!=j) 
            {
              dist = compute_dist(i,j,numvert);
              dest = &(retval->vlist[i]);
              HashInsert((void *) dist,(unsigned int) dest,hash);
	      num_inserted++;
            }
        } /* for i */
    } /* for j */

  chatting("%d edges inserted\n", num_inserted);
}

Graph MakeGraph(int numvert) 
{
  int i;
  Vertex vf, vt;
  Graph retval;

  retval = (Graph) malloc (sizeof(*retval));

  chatting("Make phase 1: Creating hash tables\n");
  retval->vlist = (Vertex) malloc (numvert*(sizeof(*vf)));
  vt = NULL;

  for (i = numvert - 1; i >= 0; i--) 
    {
      vf = &(retval->vlist[i]);
      HashRange = numvert/4;
      vf->mindist = 9999999;
      vf->edgehash = MakeHash(HashRange,hashfunc);
      vf->next = vt;
      vt=vf;
    }

  chatting("Make phase 3: Creating graph\n");
  AddEdges(retval, numvert);
  chatting("Make returning\n");
  return retval;
}

  
