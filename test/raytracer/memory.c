/* Arena-based memory management */

#include "config.h"

#define SIZE_AREA 1024000

struct area {
  struct area * next;
  char data[SIZE_AREA];
};

struct area * arena_head;
struct area * arena_cur;
int arena_cur_ofs;

void arena_init(void)
{
  arena_head = malloc(sizeof(struct area));
  if (arena_head == NULL) {
    fprintf(stderr, "Out of memory\n");
    exit(2);
  }
  arena_head->next = NULL;
  arena_cur = arena_head;
  arena_cur_ofs = 0;
}

void arena_clear(void)
{
  arena_cur = arena_head;
  arena_cur_ofs = 0;
}

void * arena_alloc(int size)
{
  char * res;
  struct area * n;

  if (size >= SIZE_AREA) {
    fprintf(stderr, "Memory request too large (%d)\n", size);
    exit(2);
  }
  if (arena_cur_ofs + size <= SIZE_AREA) {
    res = arena_cur->data + arena_cur_ofs;
    arena_cur_ofs += size;
    return res;
  }
  if (arena_cur->next == NULL) {
    n = malloc(sizeof(struct area));
    if (n == NULL) {
      fprintf(stderr, "Out of memory\n");
      exit(2);
    }
    n->next = NULL;
    arena_cur->next = n;
  }
  arena_cur = arena_cur->next;
  arena_cur_ofs = size;
  return arena_cur->data;
}
