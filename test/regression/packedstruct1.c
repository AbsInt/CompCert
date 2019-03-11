/* Packed structs */

#include <stdio.h>

/* offsetof is the offset computed by the verified front-end (cfrontend/) */
#define offsetof(s,f) (int)&(((struct s *)0)->f)

/* boffsetof is the offset computed by the elaborator (cparser/) */
#define boffsetof(s,f) (int)__builtin_offsetof(struct s, f)

/* szof is the size computed by the verified front-end (cfrontend/) */
#define szof(s) (int) sizeof(struct s)

/* bszof is the size computed by the elaborator (cparser/) */
#define bszof(s) (int) sizeof(char [sizeof(struct s)])

/* Simple packing */

struct __packed__(1) s1 { unsigned short x; int y; double z; };

void test1(void)
{
  struct s1 s1;
  printf("sizeof(struct s1) = %d\n", szof(s1));
  printf("precomputed sizeof(struct s1) = %d\n", bszof(s1));
  printf("offsetof(x) = %d, offsetof(y) = %d, offsetof(z) = %d\n",
         offsetof(s1,x), offsetof(s1,y), offsetof(s1,z));
  printf("precomputed offsetof(x) = %d, offsetof(y) = %d, offsetof(z) = %d\n",
         boffsetof(s1,x), boffsetof(s1,y), boffsetof(s1,z));
  s1.x = 123; s1.y = -456; s1.z = 3.14159;
  printf("s1 = {x = %d, y = %d, z = %.5f}\n\n", s1.x, s1.y, s1.z);
}

/* Packing plus alignment */

struct __packed__(2,16) s2 { unsigned char x; int y; double z; };

char filler1;

struct s2 s2;

void test2(void)
{
  printf("sizeof(struct s2) = %d\n", szof(s2));
  printf("precomputed sizeof(struct s2) = %d\n", bszof(s2));
  printf("&s2 mod 16 = %d\n", ((int) &s2) & 0xF);
  printf("offsetof(x) = %d, offsetof(y) = %d, offsetof(z) = %d\n",
         offsetof(s2,x), offsetof(s2,y), offsetof(s2,z));
  printf("precomputed offsetof(x) = %d, offsetof(y) = %d, offsetof(z) = %d\n",
         boffsetof(s2,x), boffsetof(s2,y), boffsetof(s2,z));
  s2.x = 12345; s2.y = -456; s2.z = 3.14159;
  printf("s2 = {x = %d, y = %d, z = %.5f}\n\n", s2.x, s2.y, s2.z);
}

/* Now with byte-swapped fields */

struct s3 {
  unsigned char x; 
  unsigned short y;
  unsigned int z;
  signed short v;
  signed int w;
  char * p;
  unsigned int t[3];
  unsigned char s[2];
} __packed__(1,1,1);

struct s3 s3;

void test3(void)
{
  char xx;

  printf("sizeof(struct s3) = %d\n", szof(s3));
  printf("precomputed sizeof(struct s3) = %d\n", bszof(s3));
  printf("offsetof(s) = %d\n", offsetof(s3,s));
  printf("precomputed offsetof(s) = %d\n", boffsetof(s3,s));
  s3.x = 123;
  s3.y = 45678;
  s3.z = 0x80000001U;
  s3.v = -456;
  s3.w = -1234567;
  s3.p = &xx;
  s3.t[0] = 111;
  s3.t[1] = 222;
  s3.t[2] = 333;
  s3.s[0] = 'o';
  s3.s[1] = 'k';
  printf("s3 = {x = %u, y = %u, z = %u, v = %d, w = %d, p is %s, t = {%d,%d,%d}, s = {'%c','%c'}}\n\n",
         s3.x, s3.y, s3.z, s3.v, s3.w,
         (s3.p == &xx ? "ok" : "BAD"),
         s3.t[0], s3.t[1], s3.t[2],
         s3.s[0], s3.s[1]);
}

/* Back to normal */

struct s4 { unsigned short x; int y; double z; };

void test4(void)
{
  struct s4 s4;

  printf("sizeof(struct s4) = %d\n", szof(s4));
  printf("precomputed sizeof(struct s4) = %d\n", bszof(s4));
  printf("offsetof(x) = %d, offsetof(y) = %d, offsetof(z) = %d\n",
         offsetof(s4,x), offsetof(s4,y), offsetof(s4,z));
  printf("precomputed offsetof(x) = %d, offsetof(y) = %d, offsetof(z) = %d\n",
         boffsetof(s4,x), boffsetof(s4,y), boffsetof(s4,z));
  s4.x = 123; s4.y = -456; s4.z = 3.14159;
  printf("s4 = {x = %d, y = %d, z = %.5f}\n\n", s4.x, s4.y, s4.z);
}

/* One more, with packed attribute */

struct __attribute((packed)) s5 { unsigned short x; int y; double z; };

void test5(void)
{
  struct s5 s5;

  printf("sizeof(struct s5) = %d\n", szof(s5));
  printf("precomputed sizeof(struct s5) = %d\n", bszof(s5));
  printf("offsetof(x) = %d, offsetof(y) = %d, offsetof(z) = %d\n",
         offsetof(s5,x), offsetof(s5,y), offsetof(s5,z));
  printf("precomputed offsetof(x) = %d, offsetof(y) = %d, offsetof(z) = %d\n",
         boffsetof(s5,x), boffsetof(s5,y), boffsetof(s5,z));
  s5.x = 123; s5.y = -456; s5.z = 3.14159;
  printf("s5 = {x = %d, y = %d, z = %.5f}\n\n", s5.x, s5.y, s5.z);
}

/* Yet another, with packed attribute after the struct decl */

struct s6 { unsigned short x; int y; double z; }  __attribute((packed)) const s61;

void test6(void)
{
  struct s6 s62;

  printf("sizeof(struct s6) = %d\n", szof(s6));
  printf("precomputed sizeof(struct s6) = %d\n", bszof(s6));
  printf("offsetof(x) = %d, offsetof(y) = %d, offsetof(z) = %d\n",
         offsetof(s6,x), offsetof(s6,y), offsetof(s6,z));
  printf("precomputed offsetof(x) = %d, offsetof(y) = %d, offsetof(z) = %d\n",
         boffsetof(s6,x), boffsetof(s6,y), boffsetof(s6,z));
  s62.x = 123; s62.y = -456; s62.z = 3.14159;
  printf("s62 = {x = %d, y = %d, z = %.5f}\n\n", s62.x, s62.y, s62.z);
}


/* Test harness */

int main(int argc, char ** argv)
{
  test1();
  test2();
  test3();
  test4();
  test5();
  test6();
  return 0;
}
