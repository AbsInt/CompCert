/* For copyright information, see olden_v1.0/COPYRIGHT */

extern double sqrt();
extern double exp();
extern double log();
extern double drand();

#include <stdio.h>
#include <stdlib.h>

#ifndef SS_PLAIN
#include "mem-ref.h"
#include "future-cell.h"

#define NULL 0
#endif SS_PLAIN

#define NEW 1
#define EPSILON (1.0e-6)

#define BOOLEAN int
#ifndef TRUE
#define TRUE 1
#endif TRUE
#define FALSE 0

struct edge_rec
{
  struct VERTEX *v;
  struct edge_rec *next;
  int wasseen;
  int more_data; /* 16 byte align this thing */
};

struct get_point
{
  struct VERTEX *v;
  double curmax;
  int seed;
};

#ifdef NEW
typedef struct edge_rec *EDGE_PTR;
typedef struct VERTEX *VERTEX_PTR;
typedef EDGE_PTR QUAD_EDGE;
#else
typedef int EDGE_PTR;
typedef int VERTEX_PTR;
#endif
  
struct VEC2 {
  double x,y;
  double norm;
};

struct VERTEX {
  struct VEC2 v;
  struct VERTEX *left, *right;
};

typedef struct
{
  QUAD_EDGE left, right;
} EDGE_PAIR;

#ifdef NEW
#define onext(a) (a)->next
#else
#define onext(a) next[a]
#endif
#define oprev(a) rot(onext(rot(a)))
#define lnext(a) rot(onext(rotinv(a)))
#define lprev(a) sym(onext(a))
#define rnext(a) rotinv(onext(rot(a)))
#define rprev(a) onext(sym(a))
#define dnext(a) sym(onext(sym(a)))
#define dprev(a) rotinv(onext(rotinv(a)))

#ifdef NEW
#define X(r) r->v.x
#define Y(r) r->v.y
#define NORM(r) r->v.norm
#else
#define X(a) va[a].v.x
#define Y(a) va[a].v.y
#define NORM(a) va[a].norm
#endif  
#ifdef NEW  
#define orig(a) (a)->v
#define dest(a) orig(sym(a))
#define seen(a) (a)->wasseen
#else
#define orig(a) org[a]
#define dest(a) orig(sym(a))
#define seen(a) see[a]
#endif
  
#ifndef NEW
#define origv(a) va[orig(a)].v
#define destv(a) va[dest(a)].v
#else
#define origv(a) orig(a)->v
#define destv(a) dest(a)->v
#endif

#define ALLOC_SIZE (sizeof(struct edge_rec))
#ifndef PLAIN
#define SIZE (sizeof(struct edge_rec) << PN_BITS)  
#define ANDF ((4*sizeof(struct edge_rec) - 1) << PN_BITS)
#else
#define SIZE sizeof(struct edge_rec)
#define ANDF (4*sizeof(struct edge_rec) - 1)
#endif

#define sym(a) ((QUAD_EDGE) (((unsigned int) (a)) ^ 2*SIZE))
#define rot(a) ((QUAD_EDGE) ( (((unsigned int) (a) + 1*SIZE) & ANDF) | ((unsigned int) (a) & ~ANDF) ))
#define rotinv(a) ((QUAD_EDGE) ( (((unsigned int) (a) + 3*SIZE) & ANDF) | ((unsigned int) (a) & ~ANDF) ))
#define base(a) ((QUAD_EDGE) ((unsigned int a) & ~ANDF))

struct EDGE_STACK {
    int ptr;
    QUAD_EDGE *elts ;
    int stack_size;
};

extern QUAD_EDGE alloc_edge();
extern QUAD_EDGE makeedge();
extern void splice();
extern void swapedge();
extern void deleteedge();
extern QUAD_EDGE build_delaunay_triangulation();
extern EDGE_PAIR build_delaunay();
extern EDGE_PAIR do_merge();
extern QUAD_EDGE connect_left();
extern QUAD_EDGE connect_right();

extern void zero_seen();
extern QUAD_EDGE pop_edge();

#ifdef SS_PLAIN
#define drand(seed) (((double) (seed=olden_random(seed))) / (double) 2147483647)
#else SS_PLAIN
#define drand(seed) (((double) (seed=random(seed))) / (double) 2147483647)
#endif SS_PLAIN

#ifdef DEFINE_GLOBALS
#define EXTERN 
#else
#define EXTERN extern
#endif

EXTERN VERTEX_PTR *vp ;
EXTERN struct VERTEX *va ;
EXTERN EDGE_PTR *next ;
EXTERN VERTEX_PTR *org ;
EXTERN int num_vertices, num_edgeparts, stack_size ;
EXTERN int to_lincoln , to_off, to_3d_out, to_color , voronoi , delaunay , interactive , ahost ;
EXTERN char *see;

#ifdef ODEFINE_GLOBALS
#define OEXTERN
#else
#define OEXTERN extern
#endif  

#define my_alloc(str_name, str_type, str_cnt) \
		if (NULL == (str_name = (str_type *) \
		mymalloc((unsigned) (str_cnt ) * (unsigned) (sizeof(str_type)))))\
		exit(printf(" cannot malloc (str_name) \n"))

#define VERTEX_ALLOC 1000

#define RED 123
#define GREEN (RED + 1)

#define CY_SOLID 1
#define CY_DOTTED 2


int ccw(VERTEX_PTR a , VERTEX_PTR b , VERTEX_PTR c );
int olden_random(int seed );
void filestuff(void);
int dealwithargs(int argc , char *  argv[] );
void output_voronoi_diagram(QUAD_EDGE edge , int nv , struct EDGE_STACK * 
                            my_stack );

