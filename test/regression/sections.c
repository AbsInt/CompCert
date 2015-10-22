#include <stdio.h>

/* Testing accesses to small data area and relative addressing sections */

struct s {
  signed char sc;
  unsigned char uc;
  signed short ss;
  unsigned short us;
  int i;
  float f;
  double d;
  long long ll;
};

struct s x = {0, };                     /* normal absolute addressing */

#pragma use_section SDATA y
struct s y = {0, };                     /* small data area */

#pragma section MYDATA ".mydata" ".mydata" far-data RW
#pragma use_section MYDATA z
struct s z = {0, };                    /* far data area, relative addressing */

#define TEST(msg,ty,x,v1,v2,v3)                                    \
  x = v1;                                                          \
  __builtin_membar();                                              \
  printf("%s 1: %s\n", msg, x == v1 ? "OK" : "FAILED");            \
  *((volatile ty *) &x) = v2;                                      \
  printf("%s 2: %s\n", msg, x == v2 ? "OK" : "FAILED");            \
  x = v3;                                                          \
  printf("%s 3: %s\n", msg, *((volatile ty *) &x) == v3 ? "OK" : "FAILED");

/* This function must be inlined so that global addressing modes are 
   generated */

static inline void test(struct s * p)
{
  TEST("signed char", signed char, p->sc, 12, 34, 56);
  TEST("unsigned char", unsigned char, p->uc, 56, 78, 123);
  TEST("signed short", signed short, p->ss, 1234, 5678, 9999);
  TEST("unsigned short", unsigned short, p->us, 1357, 2468, 3939);
  TEST("int", int, p->i, 0x123456, 0x7890AB, 0xDEADBEEF);
  TEST("float", float, p->f, 0.5f, 256.0f, 16.0f);
  TEST("double", double, p->d, 3.1415, 2.718, 0.747);
  TEST("long long", long long, p->ll, 
       0x123456789ABCDEFLL, 0x789ABCDEF1234567LL,
       0x128934AB56CD70EFLL);
}

void absolute(void)
{
  printf("---- Absolute addressing\n");
  test(&x);
}

void sda(void)
{
  printf("---- Small data area\n");
  test(&y);
}

void relative(void)
{
  printf("---- Relative addressing\n");
  test(&z);
}

int main(void)
{
  absolute();
  sda();
  relative();
  return 0;
}
