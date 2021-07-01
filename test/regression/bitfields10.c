#include <stdio.h>

/* Dynamic initialization of bit-fields */
/* Known not to work with the reference interpreter */

struct s {
  signed char a: 6;
  unsigned int b: 2;
};

struct t {
  unsigned int c: 16;
  _Bool d: 1;
  short e: 8;
  int : 10;
};

union u {
  int u: 4;
  unsigned int v: 3;
};

void print_s(char * msg, struct s p)
{
  printf("%s = { a = %d, b = %d }\n", msg, p.a, p.b);
}

void print_t(char * msg, struct t p)
{
  printf("%s = { c = %d, d = %d, e = %d }\n", msg, p.c, p.d, p.e);
}

void print_u_u(char * msg, union u p)
{
  printf("%s = { u = %d }\n", msg, p.u);
}

void print_u_v(char * msg, union u p)
{
  printf("%s = { v = %u }\n", msg, p.v);
}

/* Local, non-static initialization */
void f(int x, int y, int z)
{
  struct s loc_s = { x, y };
  struct t loc_t = { x, z, y };
  union u loc_u_u = { .u = x };
  union u loc_u_v = { .v = z };
  print_s("loc_s", loc_s);
  print_t("loc_t", loc_t);
  print_u_u("loc_u_u", loc_u_u);
  print_u_v("loc_u_v", loc_u_v);
  print_s("compound_s", (struct s) { y, x });
  print_t("compound_t", (struct t) { y, ~z, -x });
  print_u_u("compound_u", (union u) { y });
}

int main()
{
  f(11, 2, 3);
  f(7, 50, 2);
  return 0;
}


