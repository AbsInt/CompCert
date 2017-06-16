#include <stdio.h>

struct s {
  signed char a: 6;
  unsigned int b: 2;
};

struct t {
  unsigned int c: 16;
  unsigned int d: 1;
  short e: 8;
};

struct u {
  unsigned int f: 18;
  unsigned int g: 24;
  char h;
};

struct s x = { 1, 2 };

struct t y = { 3, 4, 5 };

struct u z = { 6, 7, 8 };

int main()
{
  printf("x = { a = %d, b = %d }\n", x.a, x.b);
  printf("y = { c = %d, d = %d; e = %d }\n", y.c, y.d, y.e);
  printf("z = { f = %d, g = %d; h = %d }\n", z.f, z.g, z.h);
}

