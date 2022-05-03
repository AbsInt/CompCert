#include <stdio.h>
#include <stdlib.h>

/* Some tests from GCC, c11-generic-1.c */

void check (int n)
{
  if (n) abort ();
}

void test1(void)
{
  int n = 0;

  check (_Generic (n++, int: 0));
  /* _Generic should not evaluate its argument.  */
  check (n);

  check (_Generic (n, double: n++, default: 0));
  check (n);

  /* Qualifiers are removed for the purpose of type matching.  */
  const int cn = 0;
  check (_Generic (cn, int: 0, default: n++));
  check (n);
  check (_Generic ((const int) n, int: 0, default: n++));
  check (n);

  /* Arrays decay to pointers.  */
  int a[1];
  const int ca[1];
  check (_Generic (a, int *: 0, const int *: n++));
  check (n);
  check (_Generic (ca, const int *: 0, int *: n++));
  check (n);

  /* Functions decay to pointers.  */
  extern void f (void);
  check (_Generic (f, void (*) (void): 0, default: n++));
  check (n);

  /* _Noreturn is not part of the function type.  */
  check (_Generic (&abort, void (*) (void): 0, default: n++));
  check (n);

  /* Integer promotions do not occur.  */
  short s;
  check (_Generic (s, short: 0, int: n++));
  check (n);
}


/* Some tests from Clang, Sema/generic-selection.c */

void test2(int n)
{
  int a1[_Generic(0, int: 1, short: 2, float: 3, default: 4) == 1 ? 1 : -1];
  int a2[_Generic(0, default: 1, short: 2, float: 3, int: 4) == 4 ? 1 : -1];
  int a3[_Generic(0L, int: 1, short: 2, float: 3, default: 4) == 4 ? 1 : -1];
  int a4[_Generic(0L, default: 1, short: 2, float: 3, int: 4) == 1 ? 1 : -1];
  int a5[_Generic(0, int: 1, short: 2, float: 3) == 1 ? 1 : -1];
  int a6[_Generic(0, short: 1, float: 2, int: 3) == 3 ? 1 : -1];
  int a7[_Generic("test", char *: 1, default: 2) == 1 ? 1 : -1];
  int a8[_Generic(test1, void (*)(void): 1, default: 2) == 1 ? 1 : -1];
  int b8[_Generic(test2, void (*)(void): 1, default: 2) == 2 ? 1 : -1];
  int c8[_Generic(test2, void (*)(int): 1, default: 2) == 1 ? 1 : -1];
  const int i = 12;
  int a9[_Generic(i, int: 1, default: 2) == 1 ? 1 : -1];
  (void)_Generic(*(int *)0, int: 1);
}

/* Misc tests */

void print_int(long long x)
{
  printf("%lld\n", x);
}

void print_fp(double x)
{
  printf("%.2f\n", x);
}

void print_other(void * x)
{
  printf("other\n");
}

#define PRINT(x) \
  _Generic((x), \
    int: print_int, long: print_int, long long: print_int, \
    float: print_fp, double: print_fp, \
    default: print_other) (x)

int main()
{
  test1();
  test2(5);
  PRINT(1);
  PRINT(-2L);
  PRINT(42LL);
  PRINT(1.23f);
  PRINT(4.56789);
  PRINT("hello!");
  PRINT(NULL);
}

