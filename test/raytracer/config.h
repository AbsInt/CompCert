#include <math.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#ifdef SINGLE_PRECISION
typedef float flt;
#else
typedef double flt;
#endif

#if 0
extern void abord(void);

#define assert(cond) \
  if (!(cond)) { fprintf(stderr, "%s:%u: failed assertion\n", __FILE__, __LINE__); abort(); }

#endif

#define ASSIGN(lv,rv) memcpy(&(lv), &(rv), sizeof(rv))

void arena_init(void);
void arena_clear(void);
void * arena_alloc(int size);

