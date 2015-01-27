#if defined(COMPCERT_SIDE)
#define US(x) compcert_##x
#define THEM(x) native_##x
#elif defined(CC_SIDE)
#define US(x) native_##x
#define THEM(x) compcert_##x
#else
#define US(x) x
#define THEM(x) x
#endif

#include <stdio.h>

/* Alignment 1 */
struct S1 { char a; };
struct S2 { char a, b; };
struct S3 { char a, b, c; };
struct S4 { char a, b, c, d; };
struct S5 { char a, b, c, d, e; };
struct S6 { char a, b, c, d, e, f; };
struct S7 { char a, b, c, d, e, f, g; };
struct S8 { char a[32]; };

/* Alignment 2 */
struct T1 { short a; };
struct T2 { short a, b; };
struct T3 { short a, b, c; };
struct T4 { short a, b, c, d; };
struct T5 { short a, b, c, d; char e; };

/* Alignment >= 4 */
struct U1 { int a; };
struct U2 { int a, b; };
struct U3 { int a, b, c; };
struct U4 { int a, b, c, d; };
struct U5 { int a; char b; };
struct U6 { int a; short b; };
struct U7 { int a; short b; char c; };
struct U8 { char a; int b; };
struct U9 { double a, b; };

/* Struct passing */

extern void THEM(s1) (struct S1 x);
void US(s1) (struct S1 x)
{
  printf("s1 = { a = '%c' }\n", x.a);
}

extern void THEM(s2) (struct S2 x);
void US(s2) (struct S2 x)
{
  printf("s2 = { a = '%c', b = '%c' }\n", x.a, x.b);
}

extern void THEM(s3) (struct S3 x);
void US(s3) (struct S3 x)
{
  printf("s3 = { a = '%c', b = '%c', c = ' %c' }\n", x.a, x.b, x.c);
}

extern void THEM(s4) (struct S4 x);
void US(s4) (struct S4 x)
{
  printf("s4 = { a = '%c', b = '%c', c = ' %c', d = '%c' }\n",
         x.a, x.b, x.c, x.d);
}

extern void THEM(s5) (struct S5 x);
void US(s5) (struct S5 x)
{
  printf("s5 = { a = '%c', b = '%c', c = ' %c', d = '%c', e = '%c' }\n",
         x.a, x.b, x.c, x.d, x.e);
}

extern void THEM(s6) (struct S6 x);
void US(s6) (struct S6 x)
{
  printf("s6 = { a = '%c', b = '%c', c = ' %c', d = '%c', e = '%c', f = '%c' }\n",
         x.a, x.b, x.c, x.d, x.e, x.f);
}

extern void THEM(s7) (struct S7 x);
void US(s7) (struct S7 x)
{
  printf("s7 = { a = '%c', b = '%c', c = ' %c', d = '%c', e = '%c', f = '%c', g = '%c' }\n",
         x.a, x.b, x.c, x.d, x.e, x.f, x.g);
}

extern void THEM(s8) (struct S8 x);
void US(s8) (struct S8 x)
{
  printf("s8 = \"%s\"\n", x.a);
}

extern void THEM(t1) (struct T1 x);
void US(t1) (struct T1 x)
{
  printf("t1 = { a = %d }\n", x.a);
}

extern void THEM(t2) (struct T2 x);
void US(t2) (struct T2 x)
{
  printf("t2 = { a = %d, b = %d }\n", x.a, x.b);
}

extern void THEM(t3) (struct T3 x);
void US(t3) (struct T3 x)
{
  printf("t3 = { a = %d, b = %d, c = %d }\n", x.a, x.b, x.c);
}

extern void THEM(t4) (struct T4 x);
void US(t4) (struct T4 x)
{
  printf("t4 = { a = %d, b = %d, c = %d, d = %d }\n", x.a, x.b, x.c, x.d);
}

extern void THEM(t5) (struct T5 x);
void US(t5) (struct T5 x)
{
  printf("t4 = { a = %d, b = %d, c = %d, d = %d, e = '%c' }\n",
         x.a, x.b, x.c, x.d, x.e);
}

extern void THEM(u1) (struct U1 x);
void US(u1) (struct U1 x)
{
  printf("u1 = { a = %d }\n", x.a);
}

extern void THEM(u2) (struct U2 x);
void US(u2) (struct U2 x)
{
  printf("u2 = { a = %d, b = %d }\n", x.a, x.b);
}

extern void THEM(u3) (struct U3 x);
void US(u3) (struct U3 x)
{
  printf("u3 = { a = %d, b = %d, c = %d }\n", x.a, x.b, x.c);
}

extern void THEM(u4) (struct U4 x);
void US(u4) (struct U4 x)
{
  printf("u4 = { a = %d, b = %d, c = %d, d = %d }\n", x.a, x.b, x.c, x.d);
}

extern void THEM(u5) (struct U5 x);
void US(u5) (struct U5 x)
{
  printf("u5 = { a = %d, b = '%c' }\n", x.a, x.b);
}

extern void THEM(u6) (struct U6 x);
void US(u6) (struct U6 x)
{
  printf("u6 = { a = %d, b = %d }\n", x.a, x.b);
}

extern void THEM(u7) (struct U7 x);
void US(u7) (struct U7 x)
{
  printf("u7 = { a = %d, b = %d, c = '%c' }\n", x.a, x.b, x.c);
}

extern void THEM(u8) (struct U8 x);
void US(u8) (struct U8 x)
{
  printf("u8 = { a = '%c', b = %d }\n", x.a, x.b);
}

extern void THEM(u9) (struct U9 x);
void US(u9) (struct U9 x)
{
  printf("u9 = { a = %g, b = %g }\n", x.a, x.b);
}

/* Struct return */

extern struct S1 THEM(rs1) (void);
struct S1 US(rs1) (void)
{ return (struct S1){ 'a' }; }

extern struct S2 THEM(rs2) (void);
struct S2 US(rs2) (void)
{ return (struct S2){ 'a', 'b' }; }

extern struct S3 THEM(rs3) (void);
struct S3 US(rs3) (void)
{ return (struct S3){ 'a', 'b', 'c' }; }

extern struct S4 THEM(rs4) (void);
struct S4 US(rs4) (void)
{ return (struct S4){ 'a', 'b', 'c', 'd' }; }

extern struct S8 THEM(rs8) (void);
struct S8 US(rs8) (void)
{ return (struct S8){ "Lorem ipsum" }; }

extern struct U2 THEM(ru2) (void);
struct U2 US(ru2) (void)
{ return (struct U2){ 12, -34 }; }

extern struct U6 THEM(ru6) (void);
struct U6 US(ru6) (void)
{ return (struct U6){ 12345678, -9999 }; }

extern struct U9 THEM(ru9) (void);
struct U9 US(ru9) (void)
{ return (struct U9){ 0.1234, -5678.9 }; }

/* Test function, calling the functions compiled by the other compiler */

extern void THEM(test) (void);
void US(test) (void)
{
  THEM(s1)((struct S1) {'a'});
  THEM(s2)((struct S2) {'x', 'y'});
  THEM(s3)((struct S3) {'a', 'b', 'c'});
  THEM(s4)((struct S4) {'p', 'q', 'r', 's'});
  THEM(s5)((struct S5) {'a', 'b', 'c', 'd', 'e'});
  THEM(s6)((struct S6) {'a', 'b', 'c', 'd', 'e', 'f'});
  THEM(s7)((struct S7) {'a', 'b', 'c', 'd', 'e', 'f', 'g'});
  THEM(s8)((struct S8) { "Hello, world!" });
  THEM(t1)((struct T1) { 12 });
  THEM(t2)((struct T2) { 34, 56 });
  THEM(t3)((struct T3) { -1, -2, -3});
  THEM(t4)((struct T4) { 11, 22, 33, 44} );
  THEM(t5)((struct T5) { 1, 2, 3, 4, 'x'});
  THEM(u1)((struct U1) { 12345678 } );
  THEM(u2)((struct U2) { 1, -1});
  THEM(u3)((struct U3) { -1, -2, -3 });
  THEM(u4)((struct U4) { 4, 3, 2, 1 });
  THEM(u5)((struct U5) { 123, 'z' });
  THEM(u6)((struct U6) { -12345678, 555 });
  THEM(u7)((struct U7) { 111111111, 2222, 'a' });
  THEM(u8)((struct U8) { 'u', 8 });
  THEM(u9)((struct U9) { 3.14159, -2.718 });
  { struct S1 x = THEM(rs1)();
    printf("rs1 = { a = '%c' }\n", x.a); }
  { struct S2 x = THEM(rs2)();
    printf("rs2 = { a = '%c', b = '%c' }\n", x.a, x.b); }
  { struct S3 x = THEM(rs3)();
    printf("rs3 = { a = '%c', b = '%c', c = '%c' }\n", x.a, x.b, x.c); }
  { struct S4 x = THEM(rs4)();
    printf("rs4 = { a = '%c', b = '%c', c = '%c', d = '%c' }\n",
           x.a, x.b, x.c, x.d); }
  { struct S8 x = THEM(rs8)();
    printf("rs8 = { \"%s\" }\n", x.a); }
  { struct U2 x = THEM(ru2)();
    printf("ru2 = { a = %d, b = %d }\n", x.a, x.b); }
  { struct U6 x = THEM(ru6)();
    printf("ru6 = { a = %d, b = %d }\n", x.a, x.b); }
  { struct U9 x = THEM(ru9)();
    printf("ru9 = { a = %f, b = %f }\n", x.a, x.b); }
}

#if defined(COMPCERT_SIDE)

int main()
{
  printf("--- CompCert calling native:\n");
  compcert_test();
  printf("--- native calling CompCert:\n");
  native_test();
  return 0;
}

#elif !defined(CC_SIDE)

int main()
{
  printf("--- CompCert calling native:\n");
  test();
  printf("--- native calling CompCert:\n");
  test();
  return 0;
}

#endif


