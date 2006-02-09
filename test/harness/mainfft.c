#undef DEBUG
#include <math.h>
#include <stdlib.h>
#include <stdio.h>

#define PI  3.14159265358979323846

extern void dfft(double * xr, double * xi, int np);

double * xr, * xi;

#ifdef DEBUG
void trace()
{
  int i;
  for (i=0; i<=15; i++) printf("%d  %g  %g\n",i,xr[i],xi[i]);
  printf("-----------\n");
}
void print_int(int n) { printf("%d\n", n); }
void print_float(double x) { printf("%g\n", x); }
#endif

int main(int argc, char ** argv)
{
  int n, np, npm, n2, i, j;
  double enp, t, y, z, zr, zi, zm, a;
  double * pxr, * pxi;

  if (argc >= 2) n = atoi(argv[1]); else n = 12;
  np = 1 << n;
  enp = np; 
  npm = np / 2  - 1;  
  t = PI / enp;
  xr = calloc(np, sizeof(double));
  xi = calloc(np, sizeof(double));
  pxr = xr;
  pxi = xi;
  *pxr = (enp - 1.0) * 0.5;
  *pxi = 0.0;
  n2 = np / 2;  
  *(pxr+n2) = -0.5;
  *(pxi+n2) =  0.0;
  for (i = 1; i <= npm; i++) {
    j = np - i;
    *(pxr+i) = -0.5;
    *(pxr+j) = -0.5;
    z = t * (double)i;  
    y = -0.5*(cos(z)/sin(z));
    *(pxi+i) =  y;
    *(pxi+j) = -y;
  }
#ifdef DEBUG
  trace();
#endif
  dfft(xr,xi,np);
#ifdef DEBUG
  trace();
#endif
  zr = 0.0; 
  zi = 0.0; 
  npm = np-1;
  for (i = 0; i <= npm; i++ ) {
    a = fabs(pxr[i] - i);
    if (zr < a) zr = a;
    a = fabs(pxi[i]);
    if (zi < a) zi = a;
  }
  zm = zr;
  if (zr < zi) zm = zi;
  printf("%d points, error %g\n", np, zm);
  return 0;
}
