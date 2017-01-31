/* gcc-style "aligned" and "section" attributes */

/* Caveat: some C standard libraries, when preprocessed with -U__GNUC__,
   #define away __attribute__, so we use __attribute in the following. */

#include <stdio.h>

/* Alignment */

char filler1 = 1;
__attribute((__aligned__(1<<4))) int a = 1234;
char filler2 = 1;
__attribute((__aligned__(8))) char b = 'b';
char filler7 = 1;
char g __attribute((__aligned__(8))) = 'g';

/* Sections */

__attribute((__section__("mydata"))) int c = 78;
char filler3 = 1;
__attribute((__section__("mydata"))) int d = 90;

__attribute((__section__("myconst"))) const int e = 12;
const char filler4 = 1;
__attribute((__section__("myconst"))) const int f = 34;

__attribute((__section__("mycode"))) int * myfunc(int * x) { return x + 1; }

/* Alignment with typedefs and structs */

struct __attribute((__aligned__(8))) mystruct { char c1, c2; };
char filler5 = 1;
struct mystruct u;

typedef __attribute((__aligned__(8))) int myint;
char filler6 = 1;
myint v;

/* Test harness */

int main()
{
  printf("Address of a = %u mod 16\n", ((unsigned int) &a) & 0xF);
  printf("Address of b = %u mod 8\n", ((unsigned int) &b) & 0x7);
  printf("Address of g = %u mod 8\n", ((unsigned int) &g) & 0x7);
  printf("Delta d - c = %u\n", ((unsigned int) &d) - ((unsigned int) &c));
  printf("Delta f - e = %u\n", ((unsigned int) &f) - ((unsigned int) &e));
  printf("Address of u = %u mod 8\n", ((unsigned int) &u) & 0x7);
  printf("Address of v = %u mod 8\n", ((unsigned int) &v) & 0x7);

  return 0;
}
