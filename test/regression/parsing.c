#include<stdio.h>

typedef signed int T;

T f(T(T));
T f(T a(T)) {
  T b;
  return 1;
}

T f1(T(x));
T f1(T x) {
  return x;
}

int g(int x) {
 T:;
  T y;
  T T;
  T=1;

  return 1;
}

void h() {
  for(int T; ;)
    if(1)
      ;
  T *x;
  x = 0;
}

void h2() {
  for(int T; ;)
    if(1)
      ;
    else T;
}

struct S {
  const T:3;
  unsigned T:3;
  const T:3;
};
struct S stru;
void i() {
  struct S s = stru;
  s.T = -1;
  if(s.T < 0) printf("ERROR i\n");
}

/* These ones are parsed correctly, but rejected by the elaborator. */
/* void j() { */
/*   typedef int I; */
/*   {sizeof(enum{I=2}); return I;} */
/*   {do sizeof(enum{I=2}); while((I)1);} */
/*   {if(1) return sizeof(enum{I=2}); */
/*    else  return (I)1;} */
/*   {if(sizeof(enum{I=2})) return I; */
/*    else return I;} */
/*   {sizeof(enum{I=2})+I;} */
/*   {for(int i = sizeof(enum{I=2}); I; I) I; (I)1;} */
/* } */
/* int f2(enum{I=2} x) { */
/*   return I; */
/* } */
/* void k(A, B) */
/*      int B; */
/*      int A[B]; */
/* { } */
/* int l(A) */
/*      enum {T=1} A; */
/* { return T * A; } */

void m() {
  if(0)
    if(1);
    else printf("ERROR m\n");
  if(0)
    for(int i; ; )
      if(1);
      else printf("ERROR m\n");
  if(0)
    for(1; ; )
      if(1);
      else printf("ERROR m\n");
  if(0)
    while(1)
      if(1);
      else printf("ERROR m\n");
  if(0)
  L: if(1);
     else printf("ERROR m\n");

  if(0)
  LL:for(1;;)
      for(int i;;)
        while(1)
          switch(1)
          case 1:
            if(1);
            else printf("ERROR m\n");
}

int j() {
  T T;
}

T k() {
  { T T; }
  T t;
  for(T T; ; );
  T u;
}

void krf(a)
     int a;
{
  printf("%d\n", a);
}

void krg();
void krg(int a)
{
  printf("%d\n", a);
}

void krh(int);
void krh(b)
  T b;
{
  printf("%d\n", b);
}

void kri();
void kri(b, c)
  int b;
  double c;
{
  printf("%d %f %f\n", b, c, 2*c);
}

void krj();
void krj(a, aa)
     int a[];
     void aa(int);
{
  printf("%d\n", *a);
  aa(3);
}

void aa(int x) {
  printf("%d\n", x);
}

void (*krk(a, b, c))(int)
  int b, a, c;
{
  printf("%d %d %d\n", a, b, c);
  return aa;
}

int hhh(int());

int (testparen)(int T) {
  return T;
}

int (testparen2(int T)) {
  return T;
}

int ((testparen3)(int T)) {
  return T;
}

int ((((((((((testparen10))))))))))(int T) {
  return T;
}


int main () {
  f(g);
  i();
  m();

  krf(2);
  krg(3);
  krh(4);
  kri(5.5, 4.5);
  int x = 23;
  krj(&x, aa);
  krk(12, 13, 14)(4);
  (*krk(12, 13, 14))(4);

  printf("aaa" "bbb\n");
  return 0;
}
