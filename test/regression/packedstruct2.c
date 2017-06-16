/* Initialization of packed structs */

#include <stdio.h>

/* Simple packing */

struct __packed__(1) s1 { unsigned short x; int y; char z; };

struct s1 s1 = { 2345, -12345678, 'x' };

void test1(void)
{
  printf("s1 = {x = %d, y = %d, z = '%c'}\n\n", s1.x, s1.y, s1.z);
}

/* Now with byte-swapped fields */

struct __packed__(1,1,1) s3 {
  unsigned char x; 
  unsigned short y;
  unsigned int z;
  signed short v;
  signed int w;
  char * p;
  unsigned int t[3];
  unsigned char s[2];
};

struct s3 s3 = {
  42, 123, 456789, -333, -314159, 0, 
  { 111, 222, 333 },
  { 'o', 'k' }
};

void test3(void)
{
  printf("s3 = {x = %u, y = %u, z = %u, v = %d, w = %d, p is %s, t = {%d,%d,%d}, s = {'%c','%c'}}\n\n",
         s3.x, s3.y, s3.z, s3.v, s3.w,
         (s3.p == 0 ? "ok" : "BAD"),
         s3.t[0], s3.t[1], s3.t[2],
         s3.s[0], s3.s[1]);
}

/* Back to normal */

struct s4 { unsigned short x; int y; double z; };

struct s4 s4 = { 123, -456789, 3.14159 };

void test4(void)
{
  printf("s4 = {x = %d, y = %d, z = %.5f}\n\n", s4.x, s4.y, s4.z);
}

/* Test harness */

int main(int argc, char ** argv)
{
  test1();
  test3();
  test4();
  return 0;
}
