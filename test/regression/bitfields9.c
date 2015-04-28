#include <stdio.h>

/* Initialization of bit-fields */

struct s {
  signed char a: 6;
  unsigned int b: 2;
};

struct t {
  unsigned int c: 16;
  unsigned int d: 1;
  short e: 8;
};

void print_s(char * msg, struct s p)
{
  printf("%s = { a = %d, b = %d }\n", msg, p.a, p.b);
}

void print_t(char * msg, struct t p)
{
  printf("%s = { c = %d, d = %d, e = %d }\n", msg, p.c, p.d, p.e);
}

/* Global initialization */
struct s glob_s = { -12, 1 };
struct t glob_t = { 123, 0, -45 };

/* Local initialization */
void f(int x, int y)
{
  struct s loc_s = { x, y };
  struct t loc_t = { x, 1, y };
  print_s("loc_s", loc_s);
  print_t("loc_t", loc_t);
  print_s("compound_s", (struct s) { y, x });
  print_t("compound_t", (struct t) { y, 0, -x });
}

int main()
{
  print_s("glob_s", glob_s);
  print_t("glob_t", glob_t);
  f(11, 2);
  f(7, 50);
  return 0;
}

