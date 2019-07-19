/* Initialization of local variables */

#include <stdio.h>

static void print_chars(char * s, int sz)
{
  int i;
  for (i = 0; i < sz; i++) {
    if (s[i] >= 32 && s[i] < 127)
      printf("'%c', ", s[i]);
    else
      printf("%d, ", s[i]);
  }
}

/* Initialization of local const array */

int f(int x, int y)
{
  const int dfl = 2;
  const int tbl[3] = { y, y + 1, y + 2 };
  return tbl[x >= 0 && x < 3 ? x : dfl];
}

struct P { int x, y; };

struct S {
  int tag;
  struct P a;
  union {
    struct P b;
    char c[8];
  } u;
};
  
static void print_S(char * name, struct S * s)
{
  printf("%s = { tag = %d, a = {%d,%d}, u = ", name, s->tag, s->a.x, s->a.y);
  switch(s->tag) {
  case 0:
    printf("{%d,%d} }\n", s->u.b.x, s->u.b.y);
    break;
  case 1:
    printf("{"); print_chars(s->u.c, 8); printf("} }\n");
    break;
  default:
    printf("BAD }\n");
    break;
  }
}


int main()
{
  /* Initialization of arrays */
  const int x5[10] = { 1, 2, 3 };
  char x17[] = "Hello!";
  char * x18 = "Hello!";
  char * x19[2] = { "Hello", "world!" };
  char x20[3] = "Hello!";
  char x21[10] = "Hello!";
  printf("x5 = { ");
  for (int i = 0; i < 10; i++) printf("%d, ", x5[i]);
  printf("}\n");
  printf("x17[%d] = { ", (int) sizeof(x17));
  print_chars(x17, sizeof(x17));
  printf("}\n");
  printf("x18 = \"%s\"\n", x18);
  printf("x19 = { \"%s\", \"%s\" }\n", x19[0], x19[1]);
  printf("x20 = { ");
  print_chars(x20, sizeof(x20));
  printf("}\n");
  printf("x21 = { ");
  print_chars(x21, sizeof(x21));
  printf("}\n");
  /* Local const arrays */
  printf("f(0,42) = %d, f(1,42) = %d, f(2,42) = %d, f(3,42) = %d, f(4,42) = %d\n",
         f(0,42), f(1, 42), f(2, 42), f(3, 42), f(4, 42));
  /* Structs/unions */
  struct P p1 = { 66, 77 };
  struct S s1 = { 0, p1 };
  print_S("s1", &s1);
  struct S s2 = { .a.y = 1, .u.c[4] = 'x', .u.b = p1 };
  print_S("s2", &s2);
  /* ISO C99 and recent Clang say s3.a.y = 77
     GCC and earlier CompCert versions say s3.a.y = 0
     Now CompCert fails on an error "unsupported reinitialization". */
#if 0
  struct S s3 = { .tag = 1, .a = p1, .a.x = 1, .u.c = "Hello!", .u.c[7] = 'X' };
  print_S("s3", &s3);
#endif
  /* This other reinitialization is correctly supported, though. */
  struct S s4 = { .tag = 0, .a.x = 1, .a = p1, .u.b = 88, 99 };
  print_S("s4", &s4);
  return 0;
}
