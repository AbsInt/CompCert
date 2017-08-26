/* -*- mode: c -*-
 *
 * The Great Computer Language Shootout
 * http://shootout.alioth.debian.org/
 *
 * Contributed by Sebastien Loisel
 */

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

static inline double eval_A(int i, int j) { return 1.0/((i+j)*(i+j+1)/2+i+1); }

void eval_A_times_u(int N, const double u[], double Au[])
{
  int i,j;
  for(i=0;i<N;i++)
    {
      Au[i]=0;
      for(j=0;j<N;j++) Au[i]+=eval_A(i,j)*u[j];
    }
}

void eval_At_times_u(int N, const double u[], double Au[])
{
  int i,j;
  for(i=0;i<N;i++)
    {
      Au[i]=0;
      for(j=0;j<N;j++) Au[i]+=eval_A(j,i)*u[j];
    }
}

void eval_AtA_times_u(int N, const double u[], double AtAu[])
{
  double *v = malloc(N * sizeof(double));
  eval_A_times_u(N,u,v);
  eval_At_times_u(N,v,AtAu);
  free(v);
}

int main(int argc, char *argv[])
{
  int i;
  int N = ((argc == 2) ? atoi(argv[1]) : 1000);
  double * u, * v, vBv, vv;
  u = malloc(N * sizeof(double));
  v = malloc(N * sizeof(double));
  for(i=0;i<N;i++) u[i]=1;
  for(i=0;i<10;i++)
    {
      eval_AtA_times_u(N,u,v);
      eval_AtA_times_u(N,v,u);
    }
  vBv=vv=0;
  for(i=0;i<N;i++) { vBv+=u[i]*v[i]; vv+=v[i]*v[i]; }
  printf("%0.9f\n",sqrt(vBv/vv));
  return 0;
}

/********
 build & benchmark results

BUILD COMMANDS FOR: spectralnorm.gcc

Fri Sep 15 20:48:08 PDT 2006

/usr/bin/gcc -pipe -Wall -O3 -fomit-frame-pointer -funroll-loops -march=pentium4 -lm spectralnorm.c -o spectralnorm.gcc_run

=================================================================
COMMAND LINE (%A is single numeric argument):

spectralnorm.gcc_run %A

N=2500

PROGRAM OUTPUT
==============
1.274224153
********/
