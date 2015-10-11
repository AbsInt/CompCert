#include<stdio.h>

typedef signed int T;

T f(T(T));
T f(T a(T)) {
  T b;
  return 1;
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

void i() {
  struct S s;
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

int main () {
  f(g);
  i();
  m();
  return 0;
}
