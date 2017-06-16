#include <stdio.h>

/* Annotations */

int f(int x)
{
  return __builtin_annot_intval("f(%1)", x + 1);
}

double g(double x, double y, double u, double v)
{
  __builtin_annot("g(%1, %2, %3, %4)", x, y, u, v);
  return x + y;
}

int h(int a)
{
  /* Force spilling */
  int b = a+1;
  int c = b+1;
  int d = c+1;
  int e = d+1;
  int f = e+1;
  int g = f+1;
  int h = g+1;
  int i = h+1;
  int j = i+1;
  int k = j+1;
  int l = k+1;
  int m = l+1;
  int n = m+1;
  int o = n+1;
  int p = o+1;
  int q = p+1;
  int r = q+1;
  int s = r+1;
  int t = s+1;
  int u = t+1;
  int v = u+1;
  int w = v+1;
  int x = w+1;
  int y = x+1;
  int z = y+1;
  int aa = z+1;
  int bb = aa+1;
  int cc = bb+1;
  int dd = cc+1;
  __builtin_annot("h %1 %2 %3 %4 %5 %6 %7 %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20 %21 %22 %23 %24 %25 %26 %27 %28 %29 %30", a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, aa, bb, cc, dd);
  return dd;
}

const int C1 = 42;
const double C2 = 3.14;

void k(int arg)
{
  __builtin_annot("C1 + 1 is %1 and arg is %2 and C2 * 2 is %3",
                  C1 + 1, arg, C2 * 2);
}

int j(int a)
{
  /* Local variables that are stack-allocated early */
  short b = 0, c = 0;
  char d[4];
  *(a ? &b : &c) = 42;
  __builtin_annot("j %1 %2 %3 %4", b, c, d[0], d[3]);
  return b;
}

long long ll(long long a)
{
  /* Force spilling */
  long long b = a+1;
  long long c = b+1;
  long long d = c+1;
  long long e = d+1;
  long long f = e+1;
  long long g = f+1;
  long long h = g+1;
  long long i = h+1;
  long long j = i+1;
  long long k = j+1;
  long long l = k+1;
  long long m = l+1;
  long long n = m+1;
  long long o = n+1;
  long long p = o+1;
  long long q = p+1;
  long long r = q+1;
  long long s = r+1;
  long long t = s+1;
  __builtin_annot("ll %1 %2 %3 %4 %5 %6 %7 %8 %9 %10 %11 %12 %13 %14 %15 %16 %17 %18 %19 %20", a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t);
  return t;
}

int main()
{
  __builtin_annot("calling f");
  printf("f returns %d\n", f(12));
  __builtin_annot("calling g");
  printf("g returns %.2f\n", g(3.14, 2.718, 0, 1));
  return 0;
}

