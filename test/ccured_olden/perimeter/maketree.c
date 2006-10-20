#include "perimeter.h"

static int CheckOutside(int x, int y) 
{
  int euclid = x*x+y*y;

  if (euclid > 4194304) return 1;  
  if (euclid < 1048576) return -1; 
  return 0;
}

static int CheckIntersect(int center_x, int center_y, int size)
{
  int sum;
  
  if (!CheckOutside(center_x+size,center_y+size) &&
      !CheckOutside(center_x+size,center_y-size) &&
      !CheckOutside(center_x-size,center_y-size) &&
      !CheckOutside(center_x-size,center_y+size)) return 2;
  sum=CheckOutside(center_x+size,center_y+size) +
    CheckOutside(center_x+size,center_y-size) +
      CheckOutside(center_x-size,center_y-size) +
	CheckOutside(center_x-size,center_y+size);
  if ((sum==4) || (sum==-4)) return 0;
  return 1;
}  

QuadTree MakeTree(int size, int center_x, int center_y, int lo_proc,
		  int hi_proc, QuadTree parent, ChildType ct, int level) 
{
  int intersect=0;
  QuadTree retval;

#ifdef FUTURES
  retval = (QuadTree) ALLOC(lo_proc,sizeof(*retval));
#else
  retval = (QuadTree) mymalloc(sizeof(*retval));
#endif
  retval->parent = parent;
  retval->childtype = ct;

  intersect = CheckIntersect(center_x,center_y,size);
  size = size/2;
  if ((intersect==0) && (size<512))
      {
      retval->color = white;
      retval->nw = NULL;
      retval->ne = NULL;
      retval->sw = NULL;
      retval->se = NULL;
    }
  else if (intersect==2) 
    {
      retval->color=black;
      retval->nw = NULL;
      retval->ne = NULL;
      retval->sw = NULL;
      retval->se = NULL;
    }
  else 
    {
      if (!level)
	{
	  retval->color = black;
	  retval->nw = NULL;
	  retval->ne = NULL;
	  retval->sw = NULL;
	  retval->se = NULL;
	}
      else 
	{
	  int mid1,mid2;
#ifdef FUTURES 
     future_cell_int fc_sw,fc_se,fc_ne;
#endif

	  mid1 = (lo_proc+hi_proc)/2;
	  mid2 = (lo_proc+hi_proc+1)/2;

#ifndef FUTURES
	  retval->sw = MakeTree(size,center_x-size,center_y-size,
				(mid2+hi_proc+1)/2,hi_proc,retval,
				southwest,level-1);
	  retval->se = MakeTree(size,center_x+size,center_y-size,
				mid2,(mid2+hi_proc)/2,retval,
				southeast,level-1);
	  retval->ne = MakeTree(size,center_x+size,center_y+size,
				(lo_proc+mid1+1)/2,mid1,retval,
				northeast,level-1);
	  retval->nw = MakeTree(size,center_x-size,center_y+size,
				lo_proc,(lo_proc+mid1)/2,retval,
				northwest,level-1);
#else
	  FUTURE(size,center_x-size,center_y-size,
				(mid2+hi_proc+1)/2,hi_proc,retval,
				southwest,level-1,MakeTree,&fc_sw);
	  FUTURE(size,center_x+size,center_y-size,
				mid2,(mid2+hi_proc)/2,retval,
				southeast,level-1,MakeTree,&fc_se);
	  FUTURE(size,center_x+size,center_y+size,
				(lo_proc+mid1+1)/2,mid1,retval,
				northeast,level-1,MakeTree,&fc_ne);
	  retval->nw = MakeTree(size,center_x-size,center_y+size,
				lo_proc,(lo_proc+mid1)/2,retval,
				northwest,level-1);
     TOUCH(&fc_sw);
     retval->sw = (QuadTree) fc_sw.value;
     TOUCH(&fc_se);
     retval->se = (QuadTree) fc_se.value;
     TOUCH(&fc_ne);
     retval->ne = (QuadTree) fc_ne.value;
#endif
	  retval->color = grey;
	}
    }
  return retval;
}



