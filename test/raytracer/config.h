#include <math.h>
#include <assert.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifndef M_PI
# define M_PI 3.14159265358979323846
#endif

#ifdef SINGLE_PRECISION
typedef float flt;
#else
typedef double flt;
#endif

void arena_init(void);
void arena_clear(void);
void * arena_alloc(int size);
