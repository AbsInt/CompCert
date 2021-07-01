#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include "../endian.h"

static inline int bit(void * p, unsigned bitno)
{
  unsigned byteno = bitno / 8;
#ifdef ARCH_BIG_ENDIAN
  unsigned bit_in_byte = 7 - (bitno & 7);
#else
  unsigned bit_in_byte = bitno & 7;
#endif
  return (((unsigned char *) p)[byteno] >> bit_in_byte) & 1;
}

void print_prologue(char * name, size_t al, size_t sz)
{
  printf("%s: align %d, sizeof %d, layout", name, (int)al, (int)sz);
}

void print_next_field(_Bool first, size_t sz, void * p)
{
  static unsigned pos;

  if (first) pos = 0;
  /* Find first bit set, starting with [pos] */
  while (1) {
    assert (pos < 8 * sz);
    if (bit(p, pos)) break;
    pos += 1;
  }
  /* Print this position */
  printf(" %u", pos);
  /* Skip over one bits */
  while (pos < 8 * sz && bit(p, pos)) pos++;
}

void print_epilogue(void)
{
  printf("\n");
}

#define TEST4(s)                                                            \
  struct s x;                                                               \
  memset(&x, 0, sizeof(x));                                                 \
  print_prologue(#s, _Alignof(struct s), sizeof(x));                        \
  x.a = -1; print_next_field(1, sizeof(x), &x);                             \
  x.b = -1; print_next_field(0, sizeof(x), &x);                             \
  x.c = -1; print_next_field(0, sizeof(x), &x);                             \
  x.d = -1; print_next_field(0, sizeof(x), &x);                             \
  print_epilogue();

int main()
{
#include "layout.h"
  return 0;
}
