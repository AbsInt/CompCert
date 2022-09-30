/* Nested `||`, `&&` and ` ? : ` expressions. */

#include <stdio.h>

int orand(int x, int y, int z) { return x || (y && z); }

int andor(int x, int y, int z) { return (x || y) && z; }

int choose(int x, int y, int z) { return x ? y : z; }

int choose2(int a, int x1, int y1, int z1, int x2, int y2, int z2)
{ return a ? (x1 ? y1 : z1) : (x2 ? y2 : z2); }

double choosed(int x, double y, double z) { return x ? y : z; }

double choose2d(int a, int x1, long long y1, int z1, int x2, double y2, long long z2)
{ return a ? (x1 ? y1 : z1) : (x2 ? y2 : z2); }

long long chooseandl(int a, long long x, int y, int z)
{ return a ? x : y && z; }

int main()
{
  printf("orand: %d %d %d %d\n",
         orand(1,0,0), orand(0,1,0), orand(0,0,1), orand(0,1,1));
  printf("andor: %d %d %d %d\n",
         andor(0,0,1), andor(1,0,1), andor(0,1,1), andor(1,1,0));
  printf("choose: %d %d\n",
         choose(1, 23, 45), choose(0, 23, 45));
  printf("choose2: %d %d %d %d\n",
         choose2(1, 1, 23, 45, 0, 67, 89),
         choose2(1, 0, 23, 45, 0, 67, 89),
         choose2(0, 0, 23, 45, 0, 67, 89),
         choose2(0, 0, 23, 45, 1, 67, 89));
  printf("choosed: %g %g\n",
         choosed(1, 23.32, 45.54), choosed(0, 23.32, 45.54));
  printf("choose2d: %g %g %g %g\n",
         choose2d(1, 1, 23, 45, 0, 67.76, 89),
         choose2d(1, 0, 23, 45, 0, 67.76, 89),
         choose2d(0, 0, 23, 45, 0, 67.76, 89),
         choose2d(0, 0, 23, 45, 1, 67.76, 89));
  printf("chooseandl: %lld %lld %lld %lld\n",
         chooseandl(1, 23, 0, 0),
         chooseandl(0, 23, 0, 1),
         chooseandl(0, 23, 1, 0),
         chooseandl(0, 23, 1, 1));
}
