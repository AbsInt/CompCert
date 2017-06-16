/* Code generation for comparisons */

#include <stdio.h>

unsigned int f(int x, unsigned int y, char * z)
{
  unsigned int r = 0;

  /* Without explicit comparison */
  if (x) r |= 1;
  if (y) r |= 2;
  if (z) r |= 4;

  /* Negated comparisons */
  if (!x) r |= 8;
  if (!y) r |= 0x10;
  if (!z) r |= 0x20;

  /* Explicit comparisons against 0 */
  if (x == 0) r |= 0x40;
  if (y == 0) r |= 0x80;
  if (z == 0) r |= 0x100;

  if (x != 0) r |= 0x200;
  if (y != 0) r |= 0x400;
  if (z != 0) r |= 0x800;

  /* With masks */
  if (x & 1) r |= 0x1000;
  if (!(x & 2)) r |= 0x2000;
  if ((x & 4) == 0) r |= 0x4000;
  if ((x & 8) != 0) r |= 0x8000;

  return r;
}

/* Same, but we compute the boolean value of the tests */

unsigned int g(int x, unsigned int y, char * z)
{
  unsigned int r = 0;

#define MERGE(tst) r = (r << 1) | (tst)

  /* Without explicit comparison */
  MERGE((_Bool) x);
  MERGE((_Bool) y);
  MERGE((_Bool) z);

  /* Negated comparisons */
  MERGE((_Bool) !x);
  MERGE((_Bool) !y);
  MERGE((_Bool) !z);

  /* Explicit comparisons against 0 */
  MERGE(x == 0);
  MERGE(y == 0);
  MERGE(z == 0);

  MERGE(x != 0);
  MERGE(y != 0);
  MERGE(z != 0);

  /* With masks */
  MERGE((_Bool) (x & 1));
  MERGE(! (x & 2));
  MERGE((x & 4) == 0);
  MERGE((x & 8) != 0);

  return r;
}

int main(void)
{
  printf("f(0, 0, 0) = 0x%x\n", f(0, 0, 0));
  printf("g(0, 0, 0) = 0x%x\n", g(0, 0, 0));
  printf("f(12, 1, \"x\") = 0x%x\n", f(12, 1, "x"));
  printf("g(12, 1, \"x\") = 0x%x\n", g(12, 1, "x"));
  return 0;
}
