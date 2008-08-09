#include "config.h"
#include "arrays.h"

struct array * alloc_array(int eltsize, int initialsize)
{
  struct array * a = arena_alloc(sizeof(struct array));
  a->size = 0;
  a->capacity = initialsize;
  a->data = arena_alloc(eltsize * initialsize);
  return a;
}

void grow_array(int eltsize, struct array * arr)
{
  void * newdata = arena_alloc(arr->capacity * 2 * eltsize);
  memcpy(newdata, arr->data, arr->size * eltsize);
  arr->data = newdata;
  arr->capacity *= 2;
}

struct array * copy_array(int eltsize, struct array * arr, int extrasize)
{
  struct array * a = arena_alloc(sizeof(struct array));
  a->size = arr->size;
  a->capacity = arr->size + extrasize;
  a->data = arena_alloc(eltsize * a->capacity);
  memcpy(a->data, arr->data, eltsize * a->size);
  return a;
}

