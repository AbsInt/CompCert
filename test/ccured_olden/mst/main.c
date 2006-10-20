/* For copyright information, see olden_v1.0/COPYRIGHT */

#include <string.h>
#include "mst.h"
#include "ssplain.h"

typedef struct blue_return {
  Vertex vert;
  int dist;
} BlueReturn;

static BlueReturn BlueRule(Vertex inserted, Vertex vlist) 
{
  BlueReturn retval;
  Vertex tmp,prev;
  Hash hash;
  int dist,dist2;
  int count;
  
  if (!vlist) {
    retval.dist = 999999;
    return retval;
  }
  prev = vlist;
  retval.vert = vlist;
  retval.dist = vlist->mindist;
  hash = vlist->edgehash;
  dist = (int) HashLookup((unsigned int) inserted, hash);
  /*chatting("Found %d at 0x%x for 0x%x\n",dist,inserted,vlist);*/
  if (dist) 
    {
      if (dist<retval.dist) 
        {
          vlist->mindist = dist;
          retval.dist = dist;
        }
    }
  else chatting("Not found\n");
  
  count = 0;

  /* We are guaranteed that inserted is not first in list */
  for (tmp=vlist->next; tmp; prev=tmp,tmp=tmp->next) 
    {
      count++;

      /* Splice chosen vertex out of the list */
      if (tmp==inserted) 
        {
          Vertex next;
          next = tmp->next;
          prev->next = next;
        }
      /* Find the shortest distance to any other vertex not in the list */
      else 
        {
          hash = tmp->edgehash;
          dist2 = tmp->mindist;
          dist = (int) HashLookup((unsigned int) inserted, hash);
          /*chatting("Found %d at 0x%x for 0x%x\n",dist,inserted,tmp);*/
          if (dist) 
            {
              if (dist<dist2) 
                {
                  tmp->mindist = dist;
                  dist2 = dist;
                }
            }
          else chatting("Not found\n");
          if (dist2<retval.dist) 
            {
              retval.vert = tmp;
              retval.dist = dist2;
            }
        } /* else */

    } /* for */
  /*chatting("Count was %d\n",count);*/
  return retval;
}

          

static Vertex MyVertexList = NULL;

static int ComputeMst(Graph graph,int numvert) 
{
  Vertex inserted,tmp;
  int cost=0,dist;

  /* make copy of graph */
  chatting("Compute phase 1\n");

  /* Insert first node */
  inserted = graph->vlist;
  tmp = inserted->next;
  graph->vlist = tmp;
  MyVertexList = tmp;
  numvert--;

  /* Announce insertion and find next one */
  chatting("Compute phase 2\n");
  while (numvert) 
    {
      BlueReturn br;

      if (inserted == MyVertexList)
	MyVertexList = MyVertexList->next;
      br = BlueRule(inserted, MyVertexList);
      inserted = br.vert;    
      dist = br.dist;
      numvert--;
      cost = cost+dist;
    }
  return cost;
}

extern int dealwithargs(int argc, char *argv[]);

int main(int argc, char *argv[]) 
{
  Graph graph;
  int dist;
  int size;
 
  chatting("Hash entry size = %d\n", sizeof(struct hash_entry));
  chatting("Hash size = %d\n", sizeof(struct hash));
  chatting("Vertex size = %d\n", sizeof(struct vert_st));
  
  size = dealwithargs(argc,argv);

  chatting("Making graph of size %d\n",size);
  graph = MakeGraph(size);
  chatting("Graph completed\n");

  chatting("About to compute mst \n");
  dist = ComputeMst(graph,size);

  chatting("MST has cost %d\n",dist);
  exit(0);
}

