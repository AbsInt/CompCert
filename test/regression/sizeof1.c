#include <stdio.h>

struct s {
  char c;
  union { int i[3]; double d; } n;
  struct { struct s * hd; struct s * tl; } l;
};

char tbl[sizeof(struct s)];
/* Should be 32:
      char c  at 0
      union n at 8 because alignment = 8; sizeof = 12
      struct l at 8+12=20 with alignment = 4; sizeof = 8
      end of struct at 20+8=28
      alignment of whole struct is 8 because of d
      28 aligned to 8 -> 32
*/

struct bits1 {
  unsigned a: 1;
  unsigned b: 6;
};

char b1[sizeof(struct bits1)];  /* should be 1 */

struct bits2 {
  unsigned a: 1;
  unsigned b: 6;
  unsigned c: 28;
};

char b2[sizeof(struct bits2)];  /* should be 8 */

int main()
{
  printf("sizeof(struct s) = %d, sizeof(tbl) = %d\n",
         sizeof(struct s), sizeof(tbl));
  printf("sizeof(struct bits1) = %d, sizeof(b1) = %d\n",
         sizeof(struct bits1), sizeof(b1));
  printf("sizeof(struct bits2) = %d, sizeof(b2) = %d\n",
         sizeof(struct bits2), sizeof(b2));
  return 0;
}
