typedef struct tree {
  int sz;
  double x,y;
  struct tree *left, *right;
  /*struct tree *next, *prev;*/
  struct tree *next /*{95}*/, *prev /*{95}*/;
} *Tree;

/* Builds a 2D tree of n nodes in specified range with dir as primary 
   axis (0 for x, 1 for y) */
Tree build_tree(int n,int dir,int lo,int num_proc,double min_x,
                double max_x,double min_y,double max_y);
/* Compute TSP for the tree t -- use conquer for problems <= sz */
Tree tsp(Tree t, int sz, int nproc);

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
#define LOCAL(x) x
#define mymalloc malloc
#endif
