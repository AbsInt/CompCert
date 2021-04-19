#include <stdio.h>
#include <stdint.h>

/* Test that uint32 type synonym works.
   This previously failed for standard headers where uint32 is defined
   as a (32-bit) unsigned long. */

struct s {
  uint32_t a: 1;
  uint32_t b: 2;
  uint32_t c: 9;
  uint32_t d: 20;
};

struct s x = { 1, 2, 3, 4 };

int main()
{
  printf("x = { a = %d, b = %d, c = %d, d = %d }\n", x.a, x.b, x.c, x.d);
}


