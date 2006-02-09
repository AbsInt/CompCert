#include <stdio.h>

void print_int(int n) { printf("%d\n", n); }
void print_float(double n) { printf("%g\n", n); }

extern void g(int,int,int,int,int,
              double,double,double,double,double);

int main()
{
  g(1,2,3,4,5, 0.1,0.2,0.3,0.4,0.5);
  return 0;
}
