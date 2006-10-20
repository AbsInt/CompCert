#define NULL 0

#ifndef PLAIN
#include <cm/cmmd.h>

#ifdef FUTURES
#include "future-cell.h"
#endif
#include "mem-ref.h"
#endif

typedef enum {black, white, grey} Color;
typedef enum {northwest, northeast, southwest, southeast} ChildType;
typedef enum {north, east, south, west} Direction;

typedef struct quad_struct {
  Color color;
  ChildType childtype;
  struct quad_struct *nw ; // {50};
  struct quad_struct *ne ; //{50};
  struct quad_struct *sw ; // {50};
  struct quad_struct *se ; //{50};
  struct quad_struct *parent; // {50};
} *QuadTree;

QuadTree MakeTree(int size, int center_x, int center_y, int lo_proc,
                  int hi_proc, QuadTree parent, ChildType ct, int level);


#include <stdlib.h> //malloc
#include <stdio.h> // printf

extern void exit(int);

extern int __NumNodes;

#ifdef PLAIN
#include <time.h>
#define local
#define mymalloc malloc
#define CMMD_node_timer_clear(x)  (void)0
#define TIMESTART(clk) {clk=(double)clock();}
#define TIMESTOP(clk) {clk=1000000.0 * ((double)clock()-(clk))/CLOCKS_PER_SEC;}
extern double wallclock;
#define timer_start(x) TIMESTART(wallclock)
#define timer_stop(x) TIMESTOP(wallclock)
#define timer_elapsed(x) (wallclock / 1000.0)
#define chatting printf
#define NOTEST() (void)0
#define RETEST() (void)0
#define mymalloc malloc
#endif


