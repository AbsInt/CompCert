#include <stdio.h>
#include <math.h>

extern void intoffloat(int * r, double * x);
extern void intuoffloat(unsigned int * r, double * x);
extern void floatofint(double * r, int * x);
extern void floatofintu(double * r, unsigned int * x);

/* Linear congruential PRNG */

static unsigned int random_seed = 0;

unsigned int random_uint(void)
{
  random_seed = random_seed * 69069 + 25173;
  return random_seed;
}

double random_double(void)
{
  /* In range 0 .. 2^32+1 */
  unsigned int h = random_uint();
  unsigned int l = random_uint();
  return (double) h + ldexp((double) l, -32);
}

/* Individual test runs */

void test_intoffloat(double x)
{
  int r;
  intoffloat(&r, &x);
  if (r != (int) x) 
    printf("intoffloat(%g): expected %d, got %d\n", x, r, (int) x);
}

void test_intuoffloat(double x)
{
  unsigned int r;
  intuoffloat(&r, &x);
  if (r != (unsigned int) x) 
    printf("intuoffloat(%g): expected %d, got %d\n", x, r, (unsigned int) x);
}

void test_floatofint(int x)
{
  double r;
  floatofint(&r, &x);
  if (r != (double) x) 
    printf("floatofint(%d): expected %g, got %g\n", x, r, (double) x);
}

void test_floatofintu(unsigned int x)
{
  double r;
  floatofintu(&r, &x);
  if (r != (double) x) 
    printf("floatofint(%u): expected %g, got %g\n", x, r, (double) x);
}

/* Limit cases */

double cases_intoffloat[] = {
  0.0, 0.1, 0.5, 0.9, 1.0, 1.1, 1.6,
  -0.1, -0.5, -0.9, -1.0, -1.1, -1.6,
  2147483647.0, 2147483647.6, 2147483648.0, 2147483647.5, 
  2147483648.0, 2147483648.5, 2147483649.0, 10000000000.0,
  -2147483647.0, -2147483647.6, -2147483648.0, -2147483647.5, 
  -2147483648.0, -2147483648.5, -2147483649.0, -10000000000.0
};

double cases_intuoffloat[] = {
  0.0, 0.1, 0.5, 0.9, 1.0, 1.1, 1.6,
  -0.1, -0.5, -0.9, -1.0, -1.1, -1.6,
  2147483647.0, 2147483647.6, 2147483648.0, 2147483647.5, 
  2147483648.0, 2147483648.5, 2147483649.0,
  4294967295.0, 4294967295.6, 4294967296.0, 4294967296.5,
  10000000000.0
};

int cases_floatofint[] = {
  0, 1, 2, -1, -2, 2147483647, -2147483648
};

unsigned int cases_floatofintu[] = {
  0U, 1U, 2U, 2147483647U, 2147483648U, 4294967295U
};

#define TEST(testfun, cases, tyarg, gen) \
  for (i = 0; i < sizeof(cases) / sizeof(tyarg); i++) \
    testfun(cases[i]); \
  for (i = 0; i < numtests; i++) \
    testfun(gen);

int main(int argc, char ** argv)
{
  int i;
  int numtests = 1000000;

  TEST(test_intoffloat, cases_intoffloat, double,
       (random_double() - 2147483648.0));
  TEST(test_intuoffloat, cases_intuoffloat, double,
       random_double());
  TEST(test_floatofint, cases_floatofint, int,
       (int) random_uint());
  TEST(test_floatofintu, cases_floatofintu, unsigned int,
       random_uint());
  return 0;
}



  


