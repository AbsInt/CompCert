#include <stdio.h>

struct s {
  char c;
  union { short i[3]; int d; } n;
  struct { struct s * hd; struct s * tl; } l;
};

char tbl[sizeof(struct s)];
/* Should be 32:
      char c  at 0
      union n at 4 because alignment = 4; sizeof = 8
      struct l at 4+8=12 with alignment = 4; sizeof = 8
      end of struct at 12+8=20
      alignment of whole struct is 4
      20 aligned to 4 -> 20
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
         (int) sizeof(struct s), (int) sizeof(tbl));
  printf("sizeof(struct bits1) = %d, sizeof(b1) = %d\n",
         (int) sizeof(struct bits1), (int) sizeof(b1));
  printf("sizeof(struct bits2) = %d, sizeof(b2) = %d\n",
         (int) sizeof(struct bits2), (int) sizeof(b2));
  return 0;
}
