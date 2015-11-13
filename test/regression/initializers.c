#include <stddef.h>
#include <stdio.h>

int x0;

char x1 = 'x';

int x2 = 12345;

double x3 = 3.14159;

char x4[4] = { 'a', 'b', 'c', 'd' };

int x5[10] = { 1, 2, 3 };

struct { int y; int z; } x6 = { 4, 5 };

struct { int y; char z; } x7 = { 6, 'u' };

struct { char y; int z; } x8 = { 'v', 7 };

struct { char y[9]; double z; } x9 = { { 'a', 'b' }, 2.718 };

struct {
  struct { char y; int z; } u;
  double v;
} x10 = { { 'v', 7 }, 2.718 };

float x11 = 1 + 1 / 3.14159;

double x12 = 1 / 3.14159 + 1;

typedef enum { AAA , BBB } MyEnum;

const MyEnum x13[2] = { AAA, BBB };

int * x14 = &x2;

struct { char * y; int * z; float * u; double * v; } x15 = { x4, x5, &x11, &x12 };

unsigned char * x16[3] = {
  (unsigned char *) (x4 + 1),
  (unsigned char *) &x4[2],
  ((unsigned char *) x4) + 3 };

char x17[] = "Hello!";

char * x18 = "Hello!";

char * x19[2] = { "Hello", "world!" };

char x20[3] = "Hello!";

char x21[10] = "Hello!";

char * x22 = &(x10.u.y);

/* Initializer can refer to ident just declared */
struct list { int hd; struct list * tl; } x23 = { sizeof(x23), &x23 };

/* Watch out for aliases of char types */
typedef unsigned char byte;
byte x24[] = "/*B*/";

/* Another tricky case with string literals */
char * x25[] = { "/tmp" };

/* One more */
char x26[] = { "world" };

/* Wide strings (issue #71) */
wchar_t x27[] = L"abc";
wchar_t x28[2] = L"abc";
wchar_t x29[10] = L"abc";

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

static void print_wchars(wchar_t * s, int sz)
{
  int i;
  for (i = 0; i < sz; i++) {
    if (s[i] >= 32 && s[i] < 127)
      printf("'%c', ", (char) s[i]);
    else
      printf("%d, ", (int) s[i]);
  }
}

int main()
{
  int i;

  printf("x0 = %d\n", x0);
  printf("x1 = '%c'\n", x1);
  printf("x2 = %d\n", x2);
  printf("x3 = %.5f\n", x3);
  printf("x4 = { '%c', '%c', '%c', '%c' }\n",
         x4[0], x4[1], x4[2], x4[3]);
  printf("x5 = { ");
  for (i = 0; i < 10; i++) printf("%d, ", x5[i]);
  printf("}\n");
  printf("x6 = { %d, %d }\n", x6.y, x6.z);
  printf("x7 = { %d, '%c' }\n", x7.y, x7.z);
  printf("x8 = { '%c', %d }\n", x8.y, x8.z);
  printf("x9 = { { ");
  print_chars(x9.y, 9);
  printf("}, %.3f }\n", x9.z);
  printf("x10 = { { '%c', %d }, %.3f }\n",
         x10.u.y, x10.u.z, x10.v);
  printf("x11 = %.10f\n", x11);
  printf("x12 = %.10f\n", x12);
  printf("x13 = { %d, %d }\n", x13[0], x13[1]);
  if (x14 == &x2) printf("x14 ok\n"); else printf("x14 error\n");
  if (x15.y == x4 && x15.z == x5 && x15.u == &x11 && x15.v == &x12)
    printf("x15 ok\n");
  else
    printf("x15 error\n");
  if (x16[0] == (unsigned char *) x4 + 1
      && x16[1] == (unsigned char *) x4 + 2
      && x16[2] == (unsigned char *) x4 + 3)
    printf("x16 ok\n");
  else
    printf("x16 error\n");
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
  if (x22 == &(x10.u.y))
    printf("x22 ok\n");
  else
    printf("x22 error\n");
  printf("x23 = { hd = %d, tl = %s }\n",
         x23.hd, x23.tl == &x23 ? "ok" : "ERROR");
  printf("x24[%d] = { ", (int) sizeof(x24));
  print_chars((char *) x24, sizeof(x24));
  printf("}\n");
  printf("x25[%d] = { \"%s\" }\n", (int) sizeof(x25), x25[0]);
  printf("x26[%d] = { ", (int) sizeof(x26));
  print_chars(x26, sizeof(x26));
  printf("}\n");
  printf("x27[%d] = { ", (int) (sizeof(x27) / sizeof(wchar_t)));
  print_wchars(x27, sizeof(x27) / sizeof(wchar_t));
  printf("}\n");
  printf("x28[%d] = { ", (int) (sizeof(x28) / sizeof(wchar_t)));
  print_wchars(x28, sizeof(x28) / sizeof(wchar_t));
  printf("}\n");
  printf("x29[%d] = { ", (int) (sizeof(x29) / sizeof(wchar_t)));
  print_wchars(x29, sizeof(x29) / sizeof(wchar_t));
  printf("}\n");
  return 0;
}

