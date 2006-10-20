#include "perimeter.h"
#ifdef MIGRONLY
#define BLAH MIGRPH()
#else
#define BLAH
#endif

#ifdef VERIFY_AFFINITIES
#include "affinity.h"
CHECK4(QuadTree,nw,ne,sw,se,tree)
#endif

static int adj(Direction d, ChildType ct)
{
  BLAH;
  switch (d) 
    {
    case north:
      return ((ct==northeast) || (ct==northwest));
    case south:
      return ((ct==southeast) || (ct==southwest));
    case east:
      return ((ct==northeast) || (ct==southeast));
    case west:
      return ((ct==southwest) || (ct==northwest));
    }
}

static ChildType reflect(Direction d, ChildType ct) 
{
  BLAH;
  if ((d==west) || (d==east)) 
    {
      switch(ct) 
	{
	case northwest:
	  return northeast;
	case northeast:
	  return northwest;
	case southeast:
	  return southwest;
	case southwest:
	  return southeast;
	}
    }
  switch(ct) 
    {
    case northwest:
      return southwest;
    case northeast:
      return southeast;
    case southeast:
      return northeast;
    case southwest:
      return northwest;
    }
}

int CountTree(QuadTree tree) 
{
  QuadTree nw,ne,sw,se;

  BLAH;
  nw = tree->nw; ne = tree->ne; sw = tree->sw; se = tree->se;
  if (nw==NULL && ne==NULL && sw==NULL && se==NULL)
    return 1;
  else
    return CountTree(nw) + CountTree(ne) + CountTree(sw) +
      CountTree(se);
}

static QuadTree child(QuadTree tree, ChildType ct)
{
  BLAH;
  switch(ct) 
    {
    case northeast:
      return tree->ne;
    case northwest:
      return tree->nw;
    case southeast:
      return tree->se;
    case southwest:
      return tree->sw;
    }
}

static QuadTree gtequal_adj_neighbor(QuadTree tree, Direction d)
{
  QuadTree q,parent;
  ChildType ct;
  
  BLAH;
  parent=tree->parent;
  ct=tree->childtype;
  if ((parent!=NULL) && adj(d,ct))
    q=gtequal_adj_neighbor(parent,d);
  else q=parent;
  if (q && q->color==grey) {
    return child(q,reflect(d,ct));
  }
  else return q;
}

static int sum_adjacent(QuadTree p, ChildType q1, ChildType q2, int size)
{
  BLAH;
  if (p->color==grey) 
    {
      return sum_adjacent(child(p,q1),q1,q2,size/2) +
	sum_adjacent(child(p,q2),q1,q2,size/2);
    }
  else if (p->color==white) 
    {
      return size;
    }
  else return 0;
}

int perimeter(QuadTree tree, int size)
{
  int retval = 0;
  QuadTree neighbor;

  BLAH;
  if (tree->color==grey) 
    {
      QuadTree child;
#ifdef FUTURES
      future_cell_int fc_sw,fc_se,fc_ne;
#endif

#ifndef FUTURES
      child = tree->sw;
      retval += perimeter(child,size/2);
      child = tree->se;
      retval += perimeter(child,size/2);
      child = tree->ne;
      retval += perimeter(child,size/2);
      child = tree->nw;
      retval += perimeter(child,size/2);
#else
      child = tree->sw;
      FUTURE(child,size/2,perimeter,&fc_sw);
      child = tree->se;
      FUTURE(child,size/2,perimeter,&fc_se);
      child = tree->ne;
      FUTURE(child,size/2,perimeter,&fc_ne);
      child = tree->nw;
      retval = perimeter(child,size/2);
      TOUCH(&fc_sw);
      TOUCH(&fc_se);
      TOUCH(&fc_ne);
      retval += fc_sw.value + fc_se.value + fc_ne.value;
#endif
    }
  else if (tree->color==black)
    {
      /* North */
      neighbor=gtequal_adj_neighbor(tree,north);
      if ((neighbor==NULL) || (neighbor->color==white)) retval+=size;
      else if (neighbor->color==grey) 
	retval+=sum_adjacent(neighbor,southeast,southwest,size);
      /* East */
      neighbor=gtequal_adj_neighbor(tree,east);
      if ((neighbor==NULL) || (neighbor->color==white)) retval+=size;
      else if (neighbor->color==grey) 
	retval+=sum_adjacent(neighbor,southwest,northwest,size);
      /* South */
      neighbor=gtequal_adj_neighbor(tree,south);
      if ((neighbor==NULL) || (neighbor->color==white)) retval+=size;
      else if (neighbor->color==grey) 
	retval+=sum_adjacent(neighbor,northwest,northeast,size);
      /* West */
      neighbor=gtequal_adj_neighbor(tree,west);
      if ((neighbor==NULL) || (neighbor->color==white)) retval+=size;
      else if (neighbor->color==grey) 
	retval+=sum_adjacent(neighbor,northeast,southeast,size);
    }
  return retval;
}

#ifdef PLAIN
double wallclock;
int __NumNodes;
#endif

int main()
{
  QuadTree tree;
  int count;
  int level;
  int i;

  BLAH;
  level = 12;
  __NumNodes = 1;

  chatting("Perimeter with %d levels on %d processors\n",level,__NumNodes);
  tree=MakeTree(2048,0,0,0,__NumNodes-1,NULL,southeast,level);
#ifdef VERIFY_AFFINITIES
  Docheck_tree(tree);
#endif
  count=CountTree(tree);
  chatting("# of leaves is %d\n",count);


  timer_start(0);
  for(i=0;i<100;i++) {
    count=perimeter(tree,4096);
  }
  timer_stop(0);

  chatting("perimeter is %d\n",count);
  chatting("Time elapsed = %f milliseconds\n", timer_elapsed(0));
#ifdef FUTURES
  __ShutDown();
#endif
  exit(0);
}

