/* Testing compound literals */

#include <stdio.h>

struct point { int x, y; };
struct line { struct point from, to; };

void printpoint (struct point p)
{
  printf("{x = %d, y = %d}\n", p.x, p.y);
}

void printpointref (struct point * p)
{
  printf("{x = %d, y = %d}\n", p->x, p->y);
}

void printline (struct line l)
{
  printf("{from = {x = %d, y = %d}, to = {x = %d, y = %d}\n",
         l.from.x, l.from.y, l.to.x, l.to.y);
}

static inline struct point diff(struct point a, struct point b)
{
  return (struct point){ b.x - a.x, b.y - a.y };
}

/* H&S section 7.4.5 */

char * temp1 = (char []) {"/temp/XXXXXX"};
char * temp2 = "/temp/XXXXXX";

int pow2(int n)
{
  if (n >= 0 && n <= 7)
    return (const int []) {1,2,4,8,16,32,64,128} [n];
  else
    return -1;
}

void test1(int n)
{
  printf("temp1 = \"%s\"\n", temp1);
  printf("temp2 = \"%s\"\n", temp2);
  temp1[6] = '!';
  printf("mutated temp1 = \"%s\"\n", temp1);

  printpoint((struct point){.x=12, .y=n+3});
  printpointref(&(struct point){n,-n});
  printline((struct line){n,n+1,n+2,n+3});
  printline((struct line){.from = (struct point){n-3,n-2},
                          .to   = (struct point){n-1,n}});
  printpoint(diff((struct point){n,n}, (struct point){1,1}));
  int * ptrs[5];
  int i = 0;
 again:
  ptrs[i] = (int [1]){i};
  if (++i < 5) goto again;
  printf("ptrs contains %d %d %d %d %d\n",
         *(ptrs[0]), *(ptrs[1]), *(ptrs[2]), *(ptrs[3]),*(ptrs[4]));
  i = 0;
  ptrs[0] = (int [1]){i++};
  ptrs[1] = (int [1]){i++};
  ptrs[2] = (int [1]){i++};
  ptrs[3] = (int [1]){i++};
  ptrs[4] = (int [1]){i++};
  printf("ptrs contains %d %d %d %d %d\n",
         *(ptrs[0]), *(ptrs[1]), *(ptrs[2]), *(ptrs[3]),*(ptrs[4]));
}

/* Examples from GCC's manual */

struct foo { int a; char b[2]; } structure;

char **foo = (char *[]) { "x", "y", "z" };

static struct foo x = (struct foo) {1, 'a', 'b'};
// Dubious examples: GCC refuses them, Clang warns.
// static int y[] = (int []) {1, 2, 3};
// static int z[] = (int [3]) {1};

void test2(int n)
{
  structure = (struct foo) {n, 'a', 0};
  printf("structure = {a = %d, b = \"%s\"}\n", structure.a, structure.b);
  printf("foo = { \"%s\", \"%s\", \"%s\" }\n", foo[0], foo[1], foo[2]);
  printf("x = {a = %d, b[0] = '%c', b[1] = '%c'}\n", x.a, x.b[0], x.b[1]);
}

/* Example gathered from various places */

union U { float f; int i; };

void printU(int kind, const union U u)
{
  switch (kind) {
  case 0:  printf("{f = %f}\n", u.f); break;
  case 1:  printf("{i = %d}\n", u.i); break;
  }
}

struct list { char * value; struct list * next; };

void printlist(struct list * l)
{
  for (; l != NULL; l = l->next) printf("\"%s\", ", l->value);
  printf("NULL\n");
}

void printintref(int * p)
{
  printf("%d\n", *p);
}

struct S { int n; int *p; };

void printS(struct S s)
{
  printf("{ n = %d, p -> {%d,%d,%d,%d} }\n",
         s.n, s.p[0], s.p[1], s.p[2], s.p[3]);
}

void test3(void)
{
  printU(0, (const union U){0.25});
  printU(1, (const union U){.i = 11});
  printf("1 + 3 = %d\n", (int){1} + (int){3});
  for (int i = 0; i < 3; i++) printpoint((struct point){i,i});
  printpoint((struct point){1});
  printpoint((struct point){.y=2});
  printlist(&((struct list){"first", &((struct list){"second", NULL})}));
  printintref(&((int){77}));
  struct S s = (struct S) {3, (int[4]){0,1,2}};
  printS(s);
  printS((struct S) {4, (int[]){0,1,2,3}});
}

int main(void)
{
  test1(42);
  test2(12);
  test3();
  return 0;
}

