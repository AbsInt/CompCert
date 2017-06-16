/* _Alignas and its interactions with sizeof */

#include <stdio.h>

#if  __STDC_VERSION__ < 201100 && defined(__GNUC__)
#define _Alignas(x) __attribute__((aligned(x)))
#define _Alignof(x) __alignof__(x)
#endif

/* Base type */
int _Alignas(16) a;
char filler1;

/* Array */
_Alignas(16) int b[3];

typedef int int3[3];
_Alignas(16) int3 bb;

#if 0
typedef _Alignas(16) int int16;
int16 bbb[3];
#endif

char filler2;

/* Struct */
struct s {
  char y;
  int _Alignas(16) x;
};

struct s c;
char filler3;

struct s _Alignas(64) d;
char filler4;

/* Union */
union u {
  int _Alignas(16) x;
  char y;
};

union u e;
char filler5;

union u _Alignas(32) f;
char filler6;

/* Arrays of structs */

struct s g[3];
char filler7;

struct _Alignas(64) ss {
  char y;
  int _Alignas(16) x;
};

struct ss h[3];
char filler8;

/* Test harness */

int main()
{
  printf("a: size = %u, alignment = %u, address mod 16 = %u\n",
         (unsigned) sizeof(a), (unsigned) _Alignof(a), ((unsigned) &a) & 0xF);
  printf("b: size = %u, alignment = %u, address mod 16 = %u\n",
         (unsigned) sizeof(b), (unsigned) _Alignof(b), ((unsigned) &b) & 0xF);
  printf("bb: size = %u, alignment = %u, address mod 16 = %u\n",
         (unsigned) sizeof(bb), (unsigned) _Alignof(bb), ((unsigned) &bb) & 0xF);
#if 0
  printf("bbb: size = %u, alignment = %u, address mod 16 = %u\n",
         (unsigned) sizeof(bbb), (unsigned) _Alignof(bbb), ((unsigned) &bbb) & 0xF);
#endif
  printf("c: size = %u, alignment = %u, address mod 16 = %u\n",
         (unsigned) sizeof(c), (unsigned) _Alignof(c), ((unsigned) &c) & 0xF);
  printf("d: size = %u, alignment = %u, address mod 64 = %u\n",
         (unsigned) sizeof(d), (unsigned) _Alignof(d), ((unsigned) &d) & 0x3F);
  printf("e: size = %u, alignment = %u, address mod 16 = %u\n",
         (unsigned) sizeof(e), (unsigned) _Alignof(e), ((unsigned) &e) & 0xF);
  printf("f: size = %u, alignment = %u, address mod 32 = %u\n",
         (unsigned) sizeof(f), (unsigned) _Alignof(f), ((unsigned) &f) & 0x1F);
  printf("g: size = %u, alignment = %u, address mod 16 = %u\n",
         (unsigned) sizeof(g), (unsigned) _Alignof(g), ((unsigned) &g) & 0xF);
  printf("h: size = %u, alignment = %u, address mod 64 = %u\n",
         (unsigned) sizeof(h), (unsigned) _Alignof(h), ((unsigned) &h) & 0x3F);
  return 0;
}




