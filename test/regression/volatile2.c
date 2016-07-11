/* Checking that __builtin_volatile_xxx functions are correctly compiled */

#include <stdio.h>

#define TEST(msg,ty,x,v1,v2) \
  *((volatile ty *) &x) = v1;                                      \
  printf("%s 1: %s\n", msg, *((ty *) &x) == v1 ? "OK" : "FAILED"); \
  *((ty *) &x) = v2;                                               \
  printf("%s 2: %s\n", msg, *((volatile ty *) &x) == v2 ? "OK" : "FAILED");

signed char gsc;
unsigned char guc;
signed short gss;
unsigned short gus;
int gi;
unsigned gu;
float gf;
double gd;
long long gll;

int main()
{
  signed char sc;
  unsigned char uc;
  signed short ss;
  unsigned short us;
  int i;
  float f;
  double d;
  long long ll;

  TEST("signed char", signed char, sc, 12, 34);
  TEST("unsigned char", unsigned char, uc, 56, 78);
  TEST("signed short", signed short, ss, 1234, 5678);
  TEST("unsigned short", unsigned short, us, 1357, 2468);
  TEST("int", int, i, 0x123456, 0x7890AB);
  TEST("float", float, f, 0.5, 256.0);
  TEST("double", double, d, 3.1415, 2.718);
  TEST("long long", long long, ll, 0x123456789ABCDEFLL, 0x789ABCDEF1234567LL);
  TEST("global signed char", signed char, gsc, 12, 34);
  TEST("global unsigned char", unsigned char, guc, 56, 78);
  TEST("global signed short", signed short, gss, 1234, 5678);
  TEST("global unsigned short", unsigned short, gus, 1357, 2468);
  TEST("global int", int, gi, 0x123456, 0x7890AB);
  TEST("global float", float, gf, 0.5, 256.0);
  TEST("global double", double, gd, 3.1415, 2.718);
  TEST("global long long", long long, gll, 0x123456789ABCDEFLL, 0x789ABCDEF1234567LL);
  /* Test for unwanted partial constant propagation */
  *((volatile long long *) &gll) = gu;
  return 0;
}

