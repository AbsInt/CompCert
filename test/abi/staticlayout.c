#include <stdio.h>
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

#if 0
void print_contents(size_t sz, void * p)
{
  int last, lastpos;
  printf(" - ");
  last = 0; lastpos = 0;
  for (int i = 0; i < sz; i++) {
    for (int b = 0; b < 8; b++) {
      int curr = bit((char *) p + i, b);
      int currpos = i * 8 + b;
      if (curr != last) {
        if (currpos > lastpos) {
          printf("%d(%d)", last, currpos - lastpos);
        }
        last = curr; lastpos = currpos;
      }
    }
  }
  { int currpos = sz * 8;
    if (currpos > lastpos) {
      printf("%d(%d)", last, currpos - lastpos);
    }
  }
}
#else
void print_contents(size_t sz, void * p)
{
  printf(" - ");
  for (int i = 0; i < sz; i++) {
    printf("%02x", ((unsigned char *)p)[i]);
  }
}
#endif

void print_epilogue (void)
{
  printf("\n");
}


#define TEST4(s)                                                            \
  static struct s x1 = {-1, 0, 0, 0};                                       \
  static struct s x2 = {-1, -1, 0, 0};                                      \
  static struct s x3 = {-1, 0, -1, 0};                                      \
  static struct s x4 = {-1, -1, -1, -1};                                    \
  print_prologue(#s, _Alignof(struct s), sizeof(x1));                       \
  print_contents(sizeof(x1), &x1);                                          \
  print_contents(sizeof(x2), &x2);                                          \
  print_contents(sizeof(x3), &x3);                                          \
  print_contents(sizeof(x4), &x4);                                          \
  print_epilogue();

int main()
{
#include "layout.h"
  return 0;
}
