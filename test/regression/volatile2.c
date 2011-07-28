/* Checking that __builtin_volatile_xxx functions are correctly compiled */

#include <stdio.h>

#define TEST(msg,ty,x,v1,v2) \
  *((volatile ty *) &x) = v1;                                      \
  printf("%s 1: %s\n", msg, *((ty *) &x) == v1 ? "OK" : "FAILED"); \
  *((ty *) &x) = v2;                                               \
  printf("%s 2: %s\n", msg, *((volatile ty *) &x) == v2 ? "OK" : "FAILED");

int main()
{
  signed char sc;
  unsigned char uc;
  signed short ss;
  unsigned short us;
  int i;
  float f;
  double d;

  TEST("signed char", signed char, sc, 12, 34);
  TEST("unsigned char", unsigned char, uc, 56, 78);
  TEST("signed short", signed short, ss, 1234, 5678);
  TEST("unsigned short", unsigned short, us, 1357, 2468);
  TEST("int", int, i, 0x123456, 0x7890AB);
  TEST("float", float, f, 0.5, 256.0);
  TEST("double", double, d, 3.1415, 2.718);
  return 0;
}

