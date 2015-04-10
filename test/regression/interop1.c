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
static struct S1 init_S1 = { 'a' };
#define print_S1(x) printf("{ a = '%c' }\n", x.a)

struct S2 { char a, b; };
static struct S2 init_S2 = { 'a', 'b' };
#define print_S2(x) printf("{ a = '%c', b = '%c' }\n", x.a, x.b)

struct S3 { char a, b, c; };
static struct S3 init_S3 = { 'a', 'b', 'c' };
#define print_S3(x) \
   printf("{ a = '%c', b = '%c', c = ' %c' }\n", x.a, x.b, x.c)

struct S4 { char a, b, c, d; };
static struct S4 init_S4 = { 'a', 'b', 'c', 'd' };
#define print_S4(x) \
   printf("{ a = '%c', b = '%c', c = ' %c', d = '%c' }\n", \
          x.a, x.b, x.c, x.d);

struct S5 { char a, b, c, d, e; };
static struct S5 init_S5 = { 'a', 'b', 'c', 'd', 'e' };
#define print_S5(x) \
  printf("{ a = '%c', b = '%c', c = ' %c', d = '%c', e = '%c' }\n", \
         x.a, x.b, x.c, x.d, x.e)

struct S6 { char a, b, c, d, e, f; };
static struct S6 init_S6 = { 'a', 'b', 'c', 'd', 'e', 'f' };
#define print_S6(x) \
  printf("{ a = '%c', b = '%c', c = ' %c', d = '%c', e = '%c', f = '%c' }\n", \
         x.a, x.b, x.c, x.d, x.e, x.f)

struct S7 { char a, b, c, d, e, f, g; };
static struct S7 init_S7 = { 'a', 'b', 'c', 'd', 'e', 'f', 'g' };
#define print_S7(x) \
  printf("{ a = '%c', b = '%c', c = ' %c', d = '%c', e = '%c', f = '%c', g = '%c' }\n", \
         x.a, x.b, x.c, x.d, x.e, x.f, x.g)

struct S8 { char a[32]; };
static struct S8 init_S8 = { "Hello world!" };
/* Do not use printf("%s") to avoid undefined behavior in the
   reference interpreter */
#define print_S8(x) \
  { char * p;       \
    printf("\"");   \
    for (p = x.a; *p != 0; p++) printf("%c", *p); \
    printf("\"\n");   \
  }

/* Alignment 2 */

struct T1 { short a; };
static struct T1 init_T1 = { 123 };
#define print_T1(x) printf("{ a = %d }\n", x.a)

struct T2 { short a, b; };
static struct T2 init_T2 = { 123, 456 };
#define print_T2(x) printf("{ a = %d, b = %d }\n", x.a, x.b)

struct T3 { short a, b, c; };
static struct T3 init_T3 = { 123, 456, 789 };
#define print_T3(x) printf("{ a = %d, b = %d, c = %d }\n", x.a, x.b, x.c)

struct T4 { short a, b, c, d; };
static struct T4 init_T4 = { 123, 456, 789, -111 };
#define print_T4(x) \
  printf("{ a = %d, b = %d, c = %d, d = %d }\n", x.a, x.b, x.c, x.d)

struct T5 { short a, b, c, d; char e; };
static struct T5 init_T5 = { 123, 456, 789, -999, 'x' };
#define print_T5(x) \
  printf("{ a = %d, b = %d, c = %d, d = %d, e = '%c' }\n", \
         x.a, x.b, x.c, x.d, x.e)

/* Alignment >= 4 */

struct U1 { int a; };
static struct U1 init_U1 = { 12 };
#define print_U1(x) printf("{ a = %d }\n", x.a)

struct U2 { int a, b; };
static struct U2 init_U2 = { 12, -34 };
#define print_U2(x) printf("{ a = %d, b = %d }\n", x.a, x.b)

struct U3 { int a, b, c; };
static struct U3 init_U3 = { 12, 34, -56};
#define print_U3(x) printf("{ a = %d, b = %d, c = %d }\n", x.a, x.b, x.c)

struct U4 { int a, b, c, d; };
static struct U4 init_U4 = { 12, 34, 56, -78 };
#define print_U4(x) \
  printf("{ a = %d, b = %d, c = %d, d = %d }\n", x.a, x.b, x.c, x.d)

struct U5 { int a; char b; };
static struct U5 init_U5 = { 1234, 'u' };
#define print_U5(x) \
  printf("{ a = %d, b = '%c' }\n", x.a, x.b)

struct U6 { int a; short b; };
static struct U6 init_U6 = { 55555, 666 };
#define print_U6(x) \
  printf("{ a = %d, b = %d }\n", x.a, x.b)

struct U7 { int a; short b; char c; };
static struct U7 init_U7 = { -10001, -789, 'z' };
#define print_U7(x) \
  printf("{ a = %d, b = %d, c = '%c' }\n", x.a, x.b, x.c)

struct U8 { char a; int b; };
static struct U8 init_U8 = { 'x', 12345 };
#define print_U8(x) \
  printf("{ a = '%c', b = %d }\n", x.a, x.b)

/* Struct passing */

#define PRINT(name,ty,print) \
extern void THEM(name) (struct ty x); \
void US(name) (struct ty x) { print(x); }

PRINT(s1,S1,print_S1)
PRINT(s2,S2,print_S2)
PRINT(s3,S3,print_S3)
PRINT(s4,S4,print_S4)
PRINT(s5,S5,print_S5)
PRINT(s6,S6,print_S6)
PRINT(s7,S7,print_S7)
PRINT(s8,S8,print_S8)
PRINT(t1,T1,print_T1)
PRINT(t2,T2,print_T2)
PRINT(t3,T3,print_T3)
PRINT(t4,T4,print_T4)
PRINT(t5,T5,print_T5)
PRINT(u1,U1,print_U1)
PRINT(u2,U2,print_U2)
PRINT(u3,U3,print_U3)
PRINT(u4,U4,print_U4)
PRINT(u5,U5,print_U5)
PRINT(u6,U6,print_U6)
PRINT(u7,U7,print_U7)
PRINT(u8,U8,print_U8)

/* Struct passing with modification in the callee */

extern void THEM (ms4) (struct S4 x);
void US (ms4) (struct S4 x)
{
  x.a += 1; x.d -= 1;
}

extern void THEM (mu4) (struct U4 x);
void US (mu4) (struct U4 x)
{
  x.a = 1; x.b = 2;
}

/* Struct return */

#define RETURN(name,ty,init) \
extern struct ty THEM(name)(void); \
struct ty US(name)(void) { return init; }

RETURN(rs1,S1,init_S1)
RETURN(rs2,S2,init_S2)
RETURN(rs3,S3,init_S3)
RETURN(rs4,S4,init_S4)
RETURN(rs5,S5,init_S5)
RETURN(rs6,S6,init_S6)
RETURN(rs7,S7,init_S7)
RETURN(rs8,S8,init_S8)
RETURN(rt1,T1,init_T1)
RETURN(rt2,T2,init_T2)
RETURN(rt3,T3,init_T3)
RETURN(rt4,T4,init_T4)
RETURN(rt5,T5,init_T5)
RETURN(ru1,U1,init_U1)
RETURN(ru2,U2,init_U2)
RETURN(ru3,U3,init_U3)
RETURN(ru4,U4,init_U4)
RETURN(ru5,U5,init_U5)
RETURN(ru6,U6,init_U6)
RETURN(ru7,U7,init_U7)
RETURN(ru8,U8,init_U8)

/* Test function, calling the functions compiled by the other compiler */

#define CALLPRINT(name,ty,init) \
  printf(#name": "); THEM(name)(init);

#define CALLRETURN(name,ty,print) \
  { struct ty x = THEM(name)(); \
    printf(#name": "); print(x); }

extern void THEM(test) (void);
void US(test) (void)
{
  CALLPRINT(s1,S1,init_S1)
  CALLPRINT(s2,S2,init_S2)
  CALLPRINT(s3,S3,init_S3)
  CALLPRINT(s4,S4,init_S4)
  CALLPRINT(s5,S5,init_S5)
  CALLPRINT(s6,S6,init_S6)
  CALLPRINT(s7,S7,init_S7)
  CALLPRINT(s8,S8,init_S8)
  CALLPRINT(t1,T1,init_T1)
  CALLPRINT(t2,T2,init_T2)
  CALLPRINT(t3,T3,init_T3)
  CALLPRINT(t4,T4,init_T4)
  CALLPRINT(t5,T5,init_T5)
  CALLPRINT(u1,U1,init_U1)
  CALLPRINT(u2,U2,init_U2)
  CALLPRINT(u3,U3,init_U3)
  CALLPRINT(u4,U4,init_U4)
  CALLPRINT(u5,U5,init_U5)
  CALLPRINT(u6,U6,init_U6)
  CALLPRINT(u7,U7,init_U7)
  CALLPRINT(u8,U8,init_U8)

  { struct S4 x = { 's', 'a', 'm', 'e' };
    THEM(ms4)(x);
    printf("after ms4, x = { '%c', '%c', '%c', '%c' }\n", x.a, x.b, x.c, x.d); }
  { struct U4 x = { 11, 22, 33, 44 };
    THEM(mu4)(x);
    printf("after mu4, x = { a = { %d, %d, %d, %d } }\n", x.a, x.b, x.c, x.d); }

  CALLRETURN(rs1,S1,print_S1)
  CALLRETURN(rs2,S2,print_S2)
  CALLRETURN(rs3,S3,print_S3)
  CALLRETURN(rs4,S4,print_S4)
  CALLRETURN(rs5,S5,print_S5)
  CALLRETURN(rs6,S6,print_S6)
  CALLRETURN(rs7,S7,print_S7)
  CALLRETURN(rs8,S8,print_S8)
  CALLRETURN(rt1,T1,print_T1)
  CALLRETURN(rt2,T2,print_T2)
  CALLRETURN(rt3,T3,print_T3)
  CALLRETURN(rt4,T4,print_T4)
  CALLRETURN(rt5,T5,print_T5)
  CALLRETURN(ru1,U1,print_U1)
  CALLRETURN(ru2,U2,print_U2)
  CALLRETURN(ru3,U3,print_U3)
  CALLRETURN(ru4,U4,print_U4)
  CALLRETURN(ru5,U5,print_U5)
  CALLRETURN(ru6,U6,print_U6)
  CALLRETURN(ru7,U7,print_U7)
  CALLRETURN(ru8,U8,print_U8)
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


