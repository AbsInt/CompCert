#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <limits.h>
#include <stddef.h>
#include "ssplain.h"

void chatting(char *s, ...)
{
  //printf("Here is a character: %c", *s);
  va_list ap;
  va_start(ap,s);
  vfprintf(stderr, s, ap);
  va_end(ap);
}



#ifdef SS_RAND
double drand48()
{
  double d;
  d = (double) random() / LONG_MAX;
  return d;
}


long lrand48()
{
  long l = random();
  return l;
}

void srand48(long seed)
{
  srand(seed);
}
#endif SS_RAND

#ifndef BEFOREBOX
static unsigned long bytes_allocated = 0;
static unsigned long allocations = 0;

void*
ssplain_malloc(int size)
{
  allocations++;
  bytes_allocated+=size;
  return malloc(size);
}

void*
ssplain_calloc(int nelems, int size)
{
  void *p;
  allocations++;
  bytes_allocated+= nelems * size;
  p =  calloc(nelems, size);
  if(!p) { printf("Cannot allocate\n"); exit(3); }
  return p;
}

void
ssplain_alloc_stats()
{
  chatting("Allocation stats: %d bytes allocated in %d allocations\n",
	   bytes_allocated, allocations);
}
#endif
