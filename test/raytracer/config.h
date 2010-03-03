#include <math.h>
#include <assert.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef SINGLE_PRECISION
typedef float flt;
#else
typedef double flt;
#endif

void arena_init(void);
void arena_clear(void);
void * arena_alloc(int size);
