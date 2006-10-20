#ifndef SS_PLAIN_H
#define SS_PLAIN_H

void * ssplain_malloc(int size);
void * ssplain_calloc(int nelems, int size);
void ssplain_alloc_stats();
 
/* Convert MP shutdown to exit */
#define __ShutDown(ID)     { ssplain_alloc_stats(); exit(ID); } 

/* All these CM-5 things are nops */
#define CMMD_node_timer_clear(ID)
#define CMMD_node_timer_start(ID)
#define CMMD_node_timer_stop(ID)
#define CMMD_node_timer_elapsed(ID)   ((double)0)

#define CMMD_self_address()   0

#define ClearAllStats()

/* define away the CM-5 allocator */
#include <stdlib.h>

#ifndef ALLOC
#define ALLOC(NUM,ESIZE)  ssplain_calloc (NUM+1,ESIZE)
#endif ALLOC

#ifndef mymalloc
#define mymalloc ssplain_malloc
#endif mymalloc

/* Get all of these multiprocessing things out of here. */
/* My id will stay that way */
#define IDMASK 0xffffffff

/* Nothing is getting tested */
#ifndef RETEST
#define RETEST()
#endif RETEST

#ifndef NOTEST
#define NOTEST()
#endif NOTEST

/* Everything is local */
#ifndef local
#define local            
#endif local

#ifndef LOCAL
#define LOCAL(VAL)      (VAL)
#endif LOCAL

#ifndef ISLOCPTR
#define ISLOCPTR(VAL)   (1)
#endif ISLOCPTR

#ifndef MLOCAL
#define MLOCAL(VAL)
#endif MLOCAL

/* An atomic increment is a normal increment */
#ifndef ATOMICINC
#define ATOMICINC(PVAL) (*(PVAL) = *(PVAL) + 1)
#endif ATOMICINC

/* Nothing is migrating anywhere */
#ifndef MIGRATE
#define MIGRATE(ID)     
#endif MIGRATE

#ifndef MIGRPH
#define MIGRPH()
#endif MIGRPH

#ifndef UNPHASE
#define UNPHASE()
#endif UNPHASE

#ifndef PID
#define PID(VAL)  (0)
#endif PID

/* All these functions */
void chatting(char *s, ...);
void __Olden_panic(char *s, ...);

/* just define these guys, they are not going to change */
#define __NumNodes 1
#define __MyNodeId 0
#define __NDim     0

typedef struct ss_future_cell_int {
  int value;
} future_cell_int;

/* Where are these things for real? */
#ifdef SS_RAND
long lrand48();
double drand48();
void srand48(long seed);
#endif SS_RAND

#define MOD(V,M) ((V) & ((M) - 1))
#define INC_MOD(V,M) (V) = MOD((V) + 1, (M))

/* Prefetch instructions */

/* Use these for 1 lookahead prefetching */

#ifdef OVERHEAD_ONLY
#define ASSEMBLE_PREFETCH(ARG)
#define ASSEMBLE_PREFETCH_HEAD(ARG)
#else !OVERHEAD_ONLY

#define ASSEMBLE_PREFETCH(ARG) \
     asm ("lw $0, %0" : /* no outputs */ : "g" (ARG))
 
/* Use these for infinite lookahead prefetching */
#define ASSEMBLE_PREFETCH_HEAD(ARG) \
     asm ("lh $0, %0" : /* no outputs */ : "g" (ARG))

#endif OVERHEAD_ONLY

#endif SS_PLAIN_H



