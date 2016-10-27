#include <stdio.h>

/* Examples of designated initializers from Harbison & Steele */

int a1[5] = { [2] = 100, [1] = 3 };
int a2[5] = { [0] = 10, [2] = -2, -1, -3 };
int a3[] = { 1, 2, 3, [2] = 5, 6, 7 };

struct S { int a; float b; char c[4]; };
struct S s1 = { .c = "abc" };
struct S s2 = { 13, 3.3, "xxx", .b = 4.5 };
struct S s3 = { .c = { 'a', 'b', 'c', '\0' } };

union U { int a; float b; char c[4]; };
union U u1 = { .c = "abc" };
union U u2 = { .a = 15 };
union U u3 = { .b = 3.14 };
union U u4 = { .a = 42, .c[2] = 1 };

struct Point { int x; int y; int z; };
typedef struct Point PointVector[4];
PointVector pv1 = {
  [0].x = 1, [0].y = 2, [0].z = 3,
  [1] = { .x = 11, .y = 12, .z = 13 },
  [3] = { .y = 3 }
};

typedef int Vector[3];
typedef int Matrix[3][3];
struct Trio { Vector v; Matrix m; };
struct Trio t = {
  .m = { [0][0] = 1, [1][1] = 1, [2][2] = 1 },
  .v = { [1] = 42, 43 }
};

int main()
{
  int i;

  printf("a1 = { %d, %d, %d, %d, %d }\n", 
         a1[0], a1[1], a1[2], a1[3], a1[4]);
  printf("a2 = { %d, %d, %d, %d, %d }\n", 
         a2[0], a2[1], a2[2], a2[3], a2[4]);
  printf("a3 = { %d, %d, %d, %d, %d } (size = %d)\n", 
         a3[0], a3[1], a3[2], a3[3], a3[4],
         (int)(sizeof(a3) / sizeof(int)));

  printf("s1 = { %d, %.2f, %s }\n",
         s1.a, s1.b, s1.c);
  printf("s2 = { %d, %.2f, %s }\n",
         s2.a, s2.b, s2.c);
  printf("s3 = { %d, %.2f, %s }\n",
         s3.a, s3.b, s3.c);

  printf("u1.c = %s\n", u1.c);
  printf("u2.a = %d\n", u2.a);
  printf("u3.b = %.2f\n", u3.b);
  printf("u4.c = {%d,%d,%d,%d}\n", u4.c[0], u4.c[1], u4.c[2], u4.c[3]);

  printf("pv1 = { ");
  for (i = 0; i < 4; i++)
    printf("{%d,%d,%d}, ", pv1[i].x, pv1[i].y, pv1[i].z);
  printf("}\n");

  printf("t = { {%d,%d,%d}, ", t.v[0], t.v[1], t.v[2]);
  printf("{");
  for (i = 0; i < 3; i++)
    printf("{%d,%d,%d}, ", t.m[i][0], t.m[i][1], t.m[i][2]);
  printf("} }\n");

  return 0;
}

  
