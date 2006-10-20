/* For copyright information, see olden_v1.0/COPYRIGHT */

#ifdef SS_PLAIN
#include "ssplain.h"
#else SS_PLAIN
#include <cm/cmmd.h>
#include <fcntl.h>
#endif SS_PLAIN

#define DEFINE_GLOBALS
#include "defines.h"
/* WARNING!  Don't use LOCAL on QUAD_EDGE as cache addresses are not aligned */

int flag;

QUAD_EDGE connect_left(a, b)
QUAD_EDGE a,b;
{
  VERTEX_PTR t1,t2;
  QUAD_EDGE ans,lnexta;

  t1=dest(a);
  lnexta=lnext(a); 
  t2=orig(b);
  ans = makeedge(t1,t2/*dest(a), orig(b)*/);
  splice(ans, lnexta);
  splice(sym(ans), b);
  return(ans);
}

QUAD_EDGE connect_right(a, b)
     QUAD_EDGE a,b;
{
  VERTEX_PTR t1,t2;
  QUAD_EDGE ans, oprevb;

  t1=dest(a);
  t2=orig(b);

  oprevb=oprev(b); 
  ans = makeedge(t1,t2);
  splice(ans, sym(a));
  splice(sym(ans), oprevb);
  return(ans);
}

/****************************************************************/
/*	Top-level Delaunay Triangulation Procedure              */
/****************************************************************/

QUAD_EDGE build_delaunay_triangulation(tree,extra)
    /* builds delaunay triangulation.
       va is an array of vertices, from 0 to size.  Each vertex consists of
       a vector and a data pointer.   edge is a pointer to an
       edge on the convex hull of the constructed delaunay triangulation. */

     VERTEX_PTR tree,extra;
{
    EDGE_PAIR retval;

    retval=build_delaunay(tree,extra);
    return retval.left;
}

VERTEX_PTR get_low(tree)
     VERTEX_PTR tree;
{
  VERTEX_PTR temp;
  while((temp=tree->left)) tree=temp;
  return tree;
}

/****************************************************************/
/*	Recursive Delaunay Triangulation Procedure              */
/*	Contains modifications for axis-switching division.     */
/****************************************************************/

EDGE_PAIR build_delaunay(tree,extra)
     VERTEX_PTR tree,extra;
{
    QUAD_EDGE a,b,c,ldo,rdi,ldi,rdo;
    EDGE_PAIR retval;
    VERTEX_PTR maxx, minx;
    VERTEX_PTR s1, s2, s3;

    EDGE_PAIR delleft, delright;

    if (tree && tree->right && tree->left) 
      {
        /* more than three elements; do recursion */
	minx = get_low(tree); maxx = extra;

	delright = build_delaunay(tree->right,extra);
	delleft = build_delaunay(tree->left, tree);
	ldo = delleft.left; ldi=delleft.right;
	rdi=delright.left; rdo=delright.right;

	retval=do_merge(ldo, ldi, rdi, rdo);
	ldo = retval.left;
	rdo = retval.right;
	while (orig(ldo) != minx) { ldo = rprev(ldo); }
	while (orig(rdo) != maxx) { rdo = lprev(rdo); }
	retval.left = ldo;
	retval.right = rdo;
    }
    else if (!tree)
      {
	printf("ERROR: Only 1 point!\n"); 
	exit(-1);
      }
    else if (!tree->left) 
      {	
	/* two points */
	a = makeedge(tree, extra);
	retval.left =  a;
	retval.right = sym(a);
      }
    else 
      { /*  tree->left, !tree->right  */	/* three points */
	/* 3 cases: triangles of 2 orientations, and 3 points on a line. */
	s1 = tree->left;
	s2 = tree;
	s3 = extra;
	a = makeedge(s1, s2);
	b = makeedge(s2, s3);
	splice(sym(a), b);
	c = connect_left(b, a);
	if (ccw(s1, s3, s2)) 
	  {
	    retval.left = sym(c);
	    retval.right = c;
	  }
	else 
	  {
	    retval.left =  a;
	    retval.right = sym(b);
	    if (!ccw(s1, s2, s3)) deleteedge(c);    /* colinear */
	  }
      }
    return retval;
}

/****************************************************************/
/*	Quad-edge storage allocation                            */
/****************************************************************/
QUAD_EDGE next_edge, avail_edge;
#ifndef NEW
#define NYL -1
#else
#define NYL NULL
#endif

void
free_edge(e)
     QUAD_EDGE e;
{
  e = (QUAD_EDGE) ((int) e ^ ((int) e & ANDF));
  onext(e) = avail_edge;
  avail_edge = e;
}

void
deleteedge(e)
     /*disconnects e from the rest of the structure and destroys it. */
     QUAD_EDGE e;
{
  QUAD_EDGE f;
  f=oprev(e);
  splice(e, f);
  f=oprev(sym(e));
  splice(sym(e),f);
  free_edge(e);
}

void
delete_all_edges() 
{ 
  next_edge= 0; 
  avail_edge = NYL;
}

QUAD_EDGE alloc_edge()
{
  QUAD_EDGE ans;

  if (avail_edge == NYL) 
    {
      ans = (QUAD_EDGE) malloc(4*ALLOC_SIZE);
#ifdef OUT
      if ((int) ans & ANDF) 
#else !OUT
      if (!(int) ans & 0xF)
#endif OUT
	{
	  printf("Aborting in alloc_edge, ans = 0x%x\n",(unsigned)ans);
	  exit(-1);
	}
    }
  else ans = (QUAD_EDGE) avail_edge, avail_edge = onext(avail_edge);
  return ans;
}

/****************************************************************/
/*	Geometric primitives                                    */
/****************************************************************/

BOOLEAN incircle(a,b,c,d)
     /* incircle, as in the Guibas-Stolfi paper. */
     VERTEX_PTR a,b,c,d;
{
  double adx, ady, bdx, bdy, cdx, cdy, dx, dy, anorm, bnorm, cnorm, dnorm;
  double dret ;

  dx = X(d); dy = Y(d); dnorm = NORM(d); 
  adx = X(a) - dx; ady = Y(a) - dy; anorm = NORM(a); 
  bdx = X(b) - dx; bdy = Y(b) - dy; bnorm = NORM(b);
  cdx = X(c) - dx; cdy = Y(c) - dy; cnorm = NORM(c); 
  dret =  (anorm - dnorm) * (bdx * cdy - bdy * cdx);
  dret += (bnorm - dnorm) * (cdx * ady - cdy * adx);
  dret += (cnorm - dnorm) * (adx * bdy - ady * bdx);
  return( (0.0 < dret) ? TRUE : FALSE );
}

BOOLEAN ccw(a,b,c)
     /* TRUE iff A, B, C form a counterclockwise oriented triangle */
     VERTEX_PTR a,b,c;
{
  double dret ;
  double xa,ya,xb,yb,xc,yc;
	
  xa=X(a); ya=Y(a);
  xb=X(b); yb=Y(b);
  xc=X(c); yc=Y(c);

  dret = (xa-xc)*(yb-yc) - (xb-xc)*(ya-yc);
  return( (dret  > 0.0)? TRUE : FALSE);
}

/****************************************************************/
/*	Quad-edge manipulation primitives                       */
/****************************************************************/
QUAD_EDGE makeedge(origin, destination)
     VERTEX_PTR origin, destination;
{
  QUAD_EDGE temp, ans;
  temp =  alloc_edge();
  ans = temp;
  
  onext(temp) = ans;
  orig(temp) = origin;
  temp = (QUAD_EDGE) ((int) temp+SIZE);
  onext(temp) = (QUAD_EDGE) ((int) ans + 3*SIZE);
  temp = (QUAD_EDGE) ((int) temp+SIZE);
  onext(temp) = (QUAD_EDGE) ((int) ans + 2*SIZE);
  orig(temp) = destination;
  temp = (QUAD_EDGE) ((int) temp+SIZE);
  onext(temp) = (QUAD_EDGE) ((int) ans + 1*SIZE);
  return(ans);
}

void
splice(a,b)
     QUAD_EDGE a, b;
{
  QUAD_EDGE alpha, beta, temp;
  QUAD_EDGE t1;
  
  alpha = rot(onext(a));
  beta = rot(onext(b));

  t1 = onext(beta);
  temp = onext(alpha);

  onext(alpha) = t1;  
  onext(beta) = temp;

  temp = onext(a); 
  t1 = onext(b); 
  onext(b) = temp; 
  onext(a) = t1;
}

void
swapedge(e)
     QUAD_EDGE e;
{
  QUAD_EDGE a,b,syme,lnexttmp;
  VERTEX_PTR a1,b1;
  
  a = oprev(e);
  syme = sym(e);
  b = oprev(syme); 
  splice(e, a);
  splice(syme, b);
  lnexttmp = lnext(a);
  splice(e, lnexttmp);
  lnexttmp = lnext(b);
  splice(syme, lnexttmp);
  a1 = dest(a);
  b1 = dest(b);
  orig(e) = a1;
  dest(e) = b1; 
}

/****************************************************************/
/*	The Merge Procedure.                                    */
/****************************************************************/

int valid(l,basel)
     QUAD_EDGE l,basel;
{
  VERTEX_PTR t1,t2,t3;

  t1=orig(basel);
  t3=dest(basel);

  t2=dest(l);
  return ccw(t1,t2,t3);
}

void dump_quad(ptr)
     QUAD_EDGE ptr;
{
  int i;
  QUAD_EDGE j;
  VERTEX_PTR v;

  ptr = (QUAD_EDGE) ((int) ptr & ~ANDF);
  chatting("Entered DUMP_QUAD: ptr=0x%x\n",ptr);
  for (i=0; i<4; i++)
   {
    j=onext(((QUAD_EDGE) (ptr+i)));
    v = orig(j);
    chatting("DUMP_QUAD: ptr=0x%x onext=0x%x,v=0x%x\n",ptr+i,j,v);
   }
}


EDGE_PAIR do_merge(ldo, ldi, rdi, rdo)
     QUAD_EDGE ldi, rdi, ldo, rdo;
{
  int rvalid, lvalid;
  QUAD_EDGE basel,lcand,rcand,t;
  VERTEX_PTR t1,t2,t3;
  
  while (TRUE) 
    {
      t3=orig(rdi);

      t1=orig(ldi);
      t2=dest(ldi);

      while (ccw(t1,t2,t3/*orig(ldi), dest(ldi), orig(rdi)*/)) 
	{
	  ldi = lnext(ldi);

	  t1=orig(ldi);
	  t2=dest(ldi);
	}

      t2=dest(rdi);

      if (ccw(t2,t3,t1/*dest(rdi), orig(rdi), orig(ldi)*/)) 
	{  
	  rdi = rprev(rdi); 
	}
      else 
	{ 
	  break; 
	}
    }
  
  basel = connect_left(sym(rdi), ldi);

  lcand = rprev(basel);
  rcand = oprev(basel);
  t1 = orig(basel);
  t2 = dest(basel);

  if (t1/*orig(basel)*/ == orig(rdo)) rdo = basel;
  if (t2/*dest(basel)*/ == orig(ldo)) ldo = sym(basel);
  
  while (TRUE) 
    {
      VERTEX_PTR v1,v2,v3,v4;

      /*chatting("valid site 1,lcand=0x%x,basel=0x%x\n",lcand,basel);*/
      /*dump_quad(lcand);*/
      t=onext(lcand);
      if (valid(t,basel)) 
	{
	  v4=orig(basel);

	  v1=dest(lcand);
	  v3=orig(lcand);

	  v2=dest(t);
	  while (incircle(v1,v2,v3,v4
			  /*dest(lcand), dest(t), orig(lcand), orig(basel)*/))
	    {
	      deleteedge(lcand);
	      lcand = t;

	      t = onext(lcand);
	      v1=dest(lcand);
	      v3=orig(lcand);

	      v2=dest(t);
	    }
	}
      
      /*chatting("valid site 2\n");*/
      t=oprev(rcand);
      if (valid(t,basel)) {
	v4=dest(basel);
	v1=dest(t);
	v2=dest(rcand);
	v3=orig(rcand);
	while (incircle(v1,v2,v3,v4
			/*dest(t), dest(rcand), orig(rcand), dest(basel)*/))
	  {
	    deleteedge(rcand);
	    rcand = t;
	    t = oprev(rcand);
	    v2=dest(rcand);
	    v3=orig(rcand);
	    v1=dest(t);
	  }
      }
      /*chatting("Valid sites 3,4\n");*/
      lvalid = valid(lcand,basel);
      /*chatting("Valid sites 3,4\n");*/
      rvalid = valid(rcand,basel);
      if ((! lvalid) && (! rvalid))
	{
	  EDGE_PAIR retval; 
	  retval.left = ldo; retval.right = rdo; return retval;
	}
      v1=dest(lcand);
      v2=orig(lcand);
      v3=orig(rcand);
      v4=dest(rcand);
      if (!lvalid ||
	  (rvalid && incircle(v1,v2,v3,v4
			      /*dest(lcand), orig(lcand),
				orig(rcand), dest(rcand)*/)))
	{
	  basel = connect_left(rcand, sym(basel));
	  rcand = lnext(sym(basel));
	}
      else
	{
	  basel = sym(connect_right(lcand, basel));
	  lcand = rprev(basel);
	}
    }
}



#define DEFINE_GLOBALS
#define CONST_m1 10000
#define CONST_b 31415821
#define RANGE 100

struct EDGE_STACK *allocate_stack();
struct get_point get_points();
int loop = 0, randum = 1, filein = 0 , fileout = 1, statistics = 0; 

void in_order(tree)
     VERTEX_PTR tree;
{
  VERTEX_PTR tleft, tright;
  double x, y;

  if (!tree) {
    return;
  }

  x = X(tree);
  y = Y(tree);
  chatting("X=%f, Y=%f\n",x, y);
  tleft = tree->left;
  in_order(tleft);
  tright = tree->right;
  in_order(tright);
}

int mult(int p, int q)
{
	int p1, p0, q1, q0;
	
	p1=p/CONST_m1; p0=p%CONST_m1;
	q1=q/CONST_m1; q0=q%CONST_m1;
	return (((p0*q1+p1*q0) % CONST_m1)*CONST_m1+p0*q0);
}

int skiprand(int seed, int n)
/* Generate the nth random # */
{
  for (; n; n--) 
#ifdef SS_PLAIN
    seed = olden_random(seed);
#else SS_PLAIN
    seed=random(seed);
#endif SS_PLAIN
  return seed;
}


#ifdef SS_PLAIN
int olden_random(int seed)
#else SS_PLAIN
int random(int seed)
#endif SS_PLAIN
{
  seed = (mult(seed,CONST_b)+1);
  return seed;
}


void
print_extra(extra)
     VERTEX_PTR extra;
{
  
  double x, y;
  x = X(extra);
  y = Y(extra);
  chatting("X=%f, Y=%f\n",x, y);
}


void
main(argc,argv) 
     int argc;
     char *argv[];
{
  struct EDGE_STACK *my_stack;
  struct get_point point, extra;
  QUAD_EDGE edge;
  int n, retained;
  to_lincoln = to_off = to_3d_out = to_color = 0;
  voronoi = delaunay = 1; interactive = ahost = 0 ;
  retained = 0;
  
  filestuff();
  chatting("argc = %d\n",argc);
  n = dealwithargs(argc, argv);

  chatting("getting %d points\n", n);
  extra=get_points(1,1.0,n,1023);
  point=get_points(n-1,extra.curmax,n-1,extra.seed);
  chatting("Done getting points\n");
  num_vertices = n + 1;
  my_stack=allocate_stack(num_vertices);

//#ifdef SS_PLAIN
//  ssplain_alloc_stats();
//#endif SS_PLAIN

  if (flag) in_order(point.v);
  if (flag) print_extra(extra.v);
  chatting("Doing voronoi on %d nodes\n", n); 

  edge=build_delaunay_triangulation(point.v,extra.v);

  chatting("Elapsed time %f\n", CMMD_node_timer_elapsed(0));
  if (flag) output_voronoi_diagram(edge,n,my_stack);

  exit(0);
}

struct EDGE_STACK *allocate_stack(num_vertices)
     int num_vertices;
{
  struct EDGE_STACK *my_stack;

  num_edgeparts = 12*num_vertices;
  my_alloc(my_stack, struct EDGE_STACK, 1);
  my_alloc(my_stack->elts, QUAD_EDGE , num_edgeparts);
  my_stack->stack_size = num_edgeparts/2;
  return my_stack;
}

void
free_all(cont,my_stack)
     int cont;
     struct EDGE_STACK *my_stack;
{
  free(my_stack->elts);
  free(my_stack);
}

struct get_point get_points(n,curmax,i,seed)
     int n;
     double curmax;
     int i,seed;
{
  VERTEX_PTR node;

  struct get_point point;

  if (n<1 || i<=n/2) {
    point.v = NULL;
    point.curmax=curmax;
	 point.seed = seed;
    return point;
  }
#ifdef OUT
  chatting("Get points: %d, %f, %d\n",n,curmax,i);
#endif OUT

  point = get_points(n/2,curmax,i,seed);
  /*chatting("rec call n=%d\n",n);*/
  i -= n/2;

  node = (VERTEX_PTR) mymalloc(sizeof(struct VERTEX));

  /*chatting("Get points past alloc,n=%d\n",n);*/
  X(node) = point.curmax * exp(log(drand(point.seed))/i);
  Y(node) = drand(point.seed);
  NORM(node) = X(node)*X(node) + Y(node)*Y(node);
  node->right = point.v;
  /*chatting("node = 0x%x\n",node);*/
  point = get_points(n/2,X(node),i-1,point.seed);

  node->left = point.v;
  point.v = node;
  return point;
}


/****************************************************************/
/*	Voronoi Diagram Routines.                               */
/****************************************************************/

/****************************************************************/
/*	Graph Traversal Routines                                */
/****************************************************************/

QUAD_EDGE pop_edge(x)
     struct EDGE_STACK *x;
{
  int a=x->ptr--;
  return (x)->elts[a];
}

void
push_edge(stack,edge)
     struct EDGE_STACK *stack;
     QUAD_EDGE edge;
{
  int a;
  /*chatting("pushing edge \n");*/
  if (stack->ptr == stack->stack_size) {
    printf("cannot push onto stack: stack is too large\n");
  }
  else {
    a = stack->ptr;
    a++;
    stack->ptr = a;
    stack->elts[a] = edge;
  }
}

void
push_ring(stack, edge)
     struct EDGE_STACK *stack;
     QUAD_EDGE edge;
{
  QUAD_EDGE nex;
  nex = onext(edge);
  while (nex != edge) {
    if (seen(nex) == 0) {
      seen(nex) = 1;
      push_edge(stack, nex);
    }
    nex = onext(nex);
  }
}

void
push_nonzero_ring(stack, edge)
     struct EDGE_STACK *stack;
     QUAD_EDGE edge;
{
  QUAD_EDGE nex;
  nex = onext(edge);
  while (nex != edge) {
    if (seen(nex) != 0) {
      seen(nex) = 0;
      push_edge(stack, nex);
    }
    nex = onext(nex);
  }
}

void
zero_seen(my_stack,edge)
     QUAD_EDGE edge;
     struct EDGE_STACK *my_stack;
{
  my_stack->ptr = 0;
  push_nonzero_ring(my_stack, edge);
  while (my_stack->ptr != 0) {
    edge = pop_edge(my_stack);
    push_nonzero_ring(my_stack, sym(edge));
  }
}

