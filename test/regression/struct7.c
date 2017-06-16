/* Assignment between structs and unions */

#include <stdio.h>

struct small {
  int x;
  double d;
  char c[5];
};

struct big {
  int x[100];
};

union u1 {
  char c;
  short s;
};

union u2 {
  struct small u;
  struct big v;
};

struct small A = { 1234, 3.14159, { 'H', 'e', 'l', 'l', 'o' }};
struct big B = { 1, 2, 3, 4, 5 };
union u1 C;
union u2 D;

int main()
{
  struct small A1, A2, AA[1];
  struct big B1, B2;
  union u1 C2;
  union u2 D2;
  int i;

  C.c = 'z';
  for (i = 0; i < 99; i++) D.v.x[i] = i;

  A2 = A;
  printf("A2 = { %d, %f, { '%c', ... , '%c' } }\n",
         A2.x, A2.d, A2.c[0], A2.c[4]);

  A2 = (A1 = A);
  printf("A2 = { %d, %f, { '%c', ... , '%c' } }\n",
         A2.x, A2.d, A2.c[0], A2.c[4]);

  B2 = B;
  printf("B2 = { %d, ..., %d, ..., %d }\n",
         B2.x[0], B2.x[4], B2.x[99]);

  B2 = (B1 = B);
  printf("B2 = { %d, ..., %d, ..., %d }\n",
         B2.x[0], B2.x[4], B2.x[99]);

  C2 = C;
  printf("C2.c = '%c'\n", C2.c);

  D2 = D;
  printf("D2.v = { %d, ..., %d, ..., %d }\n",
         D2.v.x[0], D2.v.x[4], D2.v.x[99]);

  AA[0] = A;
  A1.x = 0;
  A2.x = 0;
  AA[A1.x] = AA[A2.x];

  printf("AA[0] = { %d, %f, { '%c', ... , '%c' } }\n",
         AA[0].x, AA[0].d, AA[0].c[0], AA[0].c[4]);

  return 0;
}


