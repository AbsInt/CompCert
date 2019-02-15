/* The "aligned" attribute */

#include <stdio.h>

#define ALIGNED __attribute((aligned(16)))
#define ALIGNED1 __attribute((aligned(1)))

typedef ALIGNED char c16;

struct s {
  char y;
  char ALIGNED x;
};

typedef struct { char y; } ALIGNED u;

struct {
  char filler1;

  /* Base type */
  char ALIGNED a;
  /* Array */
  /* Expected: array of 3 naturally-aligned chars -> size = 3 */
  ALIGNED char b[3];
  /* Pointer */
  /* Expected: 16-aligned pointer to naturally-aligned char */
  ALIGNED char * c;

/* Typedef */

  c16 d;
  /* Expected: like char ALIGNED d */
  // c16 e[3] = {2, 3, 4};
  /* Expected: unclear.  This one is rejected by gcc.
     clang says size = 16, alignment = 16, but initializes first 3 bytes only.
     compcert says size = 3, alignment = 16. */
  char filler2;
  c16 * f;
  /* Expected: naturally-aligned pointer to 16-aligned char */

/* Struct */

  struct s g;
  /* Expected: alignment 16, size 17
     (1 byte, padding to mod 16, 1 bytes) */

  char filler3;

  struct t {
    char y;
  } ALIGNED h;
  /* Expected: type struct t and variable h have alignment 16 and size 1 */

  char filler4;

  struct t i;
  /* Expected: alignment 16 and size 1.  This checks that the ALIGNED
     attribute is attached to "struct t". */

  char filler5;

  u j;
  /* Expected: type u and variable j have alignment 16 and size 1. */
} x;

typedef char T1[100];

typedef struct { T1 mess[1]; } ALIGNED T2;
/* Expected: alignment 16, size 112 = 100 aligned to 16 */

typedef T2 T3[];

typedef struct { T3 *area; } T4;
/* Expected: size of a pointer, alignment of a pointer */

struct t1 { double d; };
struct t2 { char c; ALIGNED1 struct t1 d; };
/* Expected: size = 1 + 8, alignment 1 */

void check(const char * msg, void * addr, size_t sz)
{
  printf("%s: size %zu, offset mod 16 = %lu\n",
         msg, sz, (unsigned long) ((char *) addr - (char *) &x) % 16);
}

void checkptr(const char * msg, void * addr, size_t sz, size_t al)
{
  printf("%s: size %s that of a pointer, offset mod 16 %s\n",
         msg,
         sz == sizeof(void *) ? "is" : "IS NOT",
         (((char *) addr - (char *) &x) % 16) == al ?
            "is good" : "IS BAD");
}

int main()
{
  check("a", &(x.a), sizeof(x.a));
  check("b", &(x.b), sizeof(x.b));
  checkptr("c", &(x.c), sizeof(x.c), 0);
  check("d", &(x.d), sizeof(x.d));
  checkptr("f", &(x.f), sizeof(x.f), _Alignof(void *));
  check("g", &(x.g), sizeof(x.g));
  check("h", &(x.h), sizeof(x.h));
  check("i", &(x.i), sizeof(x.i));
  check("j", &(x.j), sizeof(x.j));

  printf("T2: size %zu, alignment %zu\n", sizeof(T2), _Alignof(T2));
  printf("T4: size %s that of a pointer, alignment %s that of a pointer\n",
         sizeof(T4) == sizeof(void *) ? "is" : "IS NOT",
         _Alignof(T4) == _Alignof(void *) ? "is" : "IS NOT");

  printf("t2: size %zu, alignment %zu\n",
         sizeof(struct t2), _Alignof(struct t2));
  return 0;
}
