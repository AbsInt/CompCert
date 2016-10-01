/* Testing the alias analysis on ill-defined codes 
   where it should remain conservative. */

#include <stddef.h>
#include <stdint.h>

/* For testing with GCC */
#define NOINLINE __attribute__((noinline))

/* Passing a pointer through a long long */

void NOINLINE set1(long long x)
{
  int * p = (int *) (uintptr_t) x;
  *p = 1;
}

int get1(void)
{
  int x = 0;
  set1((uintptr_t) &x);
  return x;
}

/* Passing a pointer through a double */

void NOINLINE set2(double x)
{
  int * p = (int *) (uintptr_t) x;
  *p = 1;
}

int get2(void)
{
  int x = 0;
  set2((uintptr_t) &x);
  return x;
}

/* Tagging a pointer */

void NOINLINE set3(uintptr_t x)
{
  int * p = (int *) (x & ~1);
  *p = 1;
}

int get3(void)
{
  int x = 0;
  set3((uintptr_t) &x | 1);
  return x;
}

/* XOR-ing a pointer */

static uintptr_t key = 0xDEADBEEF;

void NOINLINE set4(uintptr_t x)
{
  int * p = (int *) (x ^ key);
  *p = 1;
}

int get4(void)
{
  int x = 0;
  set4((uintptr_t) &x ^ key);
  return x;
}

/* Byte-swapping a pointer.  For 32/64 bit compatibility, we just swap
   the two low bytes, but that's in the spirit. */

inline uintptr_t bswap(uintptr_t x)
{
  return (x & ~((uintptr_t) 0xFFFF))
    | ((x >> 8) & 0xFF)
    | ((x << 8) & 0xFF00);
}

void NOINLINE set5(uintptr_t x)
{
  int * p = (int *) bswap(x);
  *p = 1;
}

int get5(void)
{
  int x = 0;
  set5(bswap((uintptr_t) &x));
  return x;
}

/* Even more fun with xor.  This one manufactures a pointer to one object
   from a pointer to another, distinct object.  Neither GCC nor CompCert
   promise to implement the expected behavior, but both happen to do it.
*/

int g;

void NOINLINE set6(int * p, uintptr_t z)
{
  int * q = (int *) ((uintptr_t) p ^ z);
  *q = 1;
}

int get6(void)
{
  int y = 0;
  uintptr_t z = (uintptr_t) &g ^ (uintptr_t) &y;
  set6(&g, z);
  int res1 = y;
  g = 0;
  set6(&y, z);
  int res2 = g;
  return res1 & res2;
}

/* Aligning pointers the hard way */

int offset = 3;                 /* but not const */

int get7(void)
{
  union { int i; char c[4]; } u; /* force alignment to 4 */
  u.c[0] = 0;
  uintptr_t x = (uintptr_t) &(u.c[offset]);
  x = x & ~3;
  *((char *) x) = 1;
  return u.c[0];
}

/* This is an example where wild pointer arithmetic is used to jump
   from one object to another.  Like GCC and Clang, we don't preserve the
   expected behavior. */

ptrdiff_t NOINLINE delta8(int * p)
{
  return p - &g;
}

int get8(void)
{
  int x;
  ptrdiff_t d = delta8(&x);
  x = 0;
  *(&g + d) = 1;
  return x;
}

/* Test harness */

#include <stdio.h>

int main()
{
  printf("Test 1: %d\n", get1());
  printf("Test 2: %d\n", get2());
  printf("Test 3: %d\n", get3());
  printf("Test 4: %d\n", get4());
  printf("Test 5: %d\n", get5());
  printf("Test 6: %d\n", get6());
  printf("Test 7: %d\n", get7());
  printf("Test 8: %d\n", get8());
  return 0;
}

