/* For copyright information, see olden_v1.0/COPYRIGHT */

/*
 * power.h
 *
 * By:  Martin C. Carlisle
 * 6/15/94
 *
 * Header file for the Power Pricing problem
 * adapted from code by Steve Lumetta, Sherry Li, and Ismail Khalil
 * University of California at Berkeley
 *
 */

typedef struct demand {
  double P;
  double Q;
} Demand;

#ifndef PLAIN
#include "future-cell.h"
#include "mem-ref.h"
typedef struct fc_demand {
    future_cell_impl impl;
    Demand value; /* cell's value */
  } future_cell_demand;
#endif

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
#endif

#include "math.h"
#include <stdlib.h> // malloc
#include <stdio.h> // printf

#ifndef NULL
#define NULL 0
#endif

#define NUM_FEEDERS 10
#define LATERALS_PER_FEEDER 20
#define BRANCHES_PER_LATERAL 5
#define LEAVES_PER_BRANCH 10

#define F_EPSILON 0.000001
#define G_EPSILON 0.000001
#define H_EPSILON 0.000001
#define ROOT_EPSILON 0.00001

typedef struct root {
  Demand D;
  double theta_R; 
  double theta_I; 
  Demand last;
  double last_theta_R; 
  double last_theta_I;
  struct lateral *feeders[NUM_FEEDERS];
} *Root;

typedef struct lateral {
  Demand D;
  double alpha;
  double beta;
  double R;
  double X;
  struct lateral *next_lateral;
  struct branch *branch;
} *Lateral;

typedef struct branch {
  Demand D;
  double alpha;
  double beta;
  double R;
  double X;
  struct branch *next_branch;
  struct leaf *leaves[LEAVES_PER_BRANCH];
} *Branch;

typedef struct leaf {
  Demand D;
  double pi_R;
  double pi_I;
} *Leaf;

#ifdef PLAIN
#define ALLOC(pn,sz) malloc(sz)
#define chatting printf
#define __NumNodes 1
#define __MyNodeId 0
#endif

/* Prototypes */
Root build_tree();
Lateral build_lateral(int i, int num);
Branch build_branch(int i, int j, int num);
Leaf build_leaf();

void Compute_Tree(Root r);
Demand Compute_Lateral(Lateral l, double theta_R, double theta_I,
                       double pi_R, double pi_I);
Demand Compute_Branch(Branch b, double theta_R, double theta_I,
                       double pi_R, double pi_I);
Demand Compute_Leaf(Leaf l, double pi_R, double pi_I);
