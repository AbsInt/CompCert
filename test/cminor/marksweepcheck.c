/* Heap checking for the mark-sweep collector */

#include <stdio.h>
#include <stddef.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>

#ifdef DEBUG

enum block_kind { RAWDATA = 0, PTRDATA = 1, CLOSURE = 2 };
enum block_color { WHITE = 0, GRAY = 4, BLACK = 0xC };

#define At(p,ty) (*((ty *)(p)))
#define Kind_header(h) ((h) & 3)
#define Color_header(h) ((h) & 0xC)
#define Size_header(h) (((h) >> 2) & 0xFFFFFFFC)

extern char * heap_start, * heap_end, * freelist_head;

char * heap_bitmap = NULL;

static inline void bitmap_set(char * bm, unsigned i)
{
  bm[i >> 3] |= 1 << (i & 7);
}

static inline int bitmap_get(char * bm, unsigned i)
{
  return bm[i >> 3] & (1 << (i & 7));
}

static void check_block(char * p, unsigned s)
{
  char * d;
  for (/**/; s > 0; p += 4, s -= 4) {
    d = At(p, char *);
    if (d != NULL) {
      assert(d >= heap_start + 4);
      assert(d <= heap_end - 4);
      assert(((unsigned) d & 3) == 0);
      assert(bitmap_get(heap_bitmap, (d - heap_start) >> 2));
    }
  }
}

void check_heap(void)
{
  char * p, * f, * nextf;
  unsigned h, s, bitmap_size;

  bitmap_size = ((heap_end - heap_start) + 31) / 32;
  /* one bit per word -> one byte per 32 bytes in the heap */
  if (heap_bitmap == NULL) {
    heap_bitmap = malloc(bitmap_size);
    assert (heap_bitmap != NULL);
  }
  memset(heap_bitmap, 0, bitmap_size);

  /* Superficial check and construction of the bitmap */

  f = freelist_head;
  assert(f >= heap_start + 4);
  assert(f <= heap_end - 4);

  for (p = heap_start; p < heap_end; /**/) {
    h = At(p, unsigned);
    s = Size_header(h);
    assert(s >= 4);
    assert((s & 3) == 0);
    p = p + 4;
    assert (p + s <= heap_end);
    if (p == f) {
      /* this is a free list block */
      assert((h & 0xF) == 0);
      nextf = At(p, char *);
      if (nextf != NULL) {
        assert(nextf > f);
        assert(nextf <= heap_end - 4);
      }
      f = nextf;
    } else {
      /* this is an allocated block */
      assert(Color_header(h) == WHITE);
      bitmap_set(heap_bitmap, (p - heap_start) >> 2);
    }
    p = p + s;
  }
  assert (p == heap_end);
  assert (f == NULL);

  /* Check block contents */
  f = freelist_head;
  for (p = heap_start; p < heap_end; /**/) {
    h = At(p, unsigned);
    s = Size_header(h);
    p = p + 4;
    if (p == f) {
      /* Fill free block with garbage */
      memset(p + 4, 0xEE, s - 4);
      f = At(p, char *);
    } else {
      /* Check block contents */
      switch (Kind_header(h)) {
      case RAWDATA:
        break;
      case PTRDATA:
        check_block(p, s); break;
      case CLOSURE:
        check_block(p + 4, s - 4); break;
      default:
        assert(0);
      }
    }
    p = p + s;
  }
}

#endif
