/****
    Copyright (C) 1996 McGill University.
    Copyright (C) 1996 McCAT System Group.
    Copyright (C) 1996 ACAPS Benchmark Administrator
                       benadmin@acaps.cs.mcgill.ca

    This program is free software; you can redistribute it and/or modify
    it provided this copyright notice is maintained.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  
****/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define DBL_EPSILON 0x1p-52

void  *allocvector(size_t size) 
{
  void *V;

  if ( (V = (void *) malloc((size_t) size)) == NULL ) {
    fprintf(stderr, "Error: couldn't allocate V in allocvector.\n");
    exit(2);
  }
  memset(V,0,size);
  return V;
}

void dallocvector(int n, double **V)
{
  *V = (double *) allocvector((size_t) n*sizeof(double));
}


#define FUDGE  (double) 1.01



int sturm(int n, double c[], double b[], double beta[], double x)

/**************************************************************************

Purpose:
------------
  Calculates the sturm sequence given by

    q_1(x)  =  c[1] - x

    q_i(x)  =  (c[i] - x) - b[i]*b[i] / q_{i-1}(x)

  and returns a(x) = the number of negative q_i. a(x) gives the number
  of eigenvalues smaller than x of the symmetric tridiagonal matrix
  with diagonal c[0],c[1],...,c[n-1] and off-diagonal elements
  b[1],b[2],...,b[n-1].


Input parameters:
------------------------
  n :
         The order of the matrix.

  c[0]..c[n-1] : 
        An n x 1 array giving the diagonal elements of the tridiagonal matrix.

  b[1]..b[n-1] :   
        An n x 1 array giving the sub-diagonal elements. b[0] may be 
        arbitrary but is replaced by zero in the procedure.

  beta[1]..beta[n-1] :
         An n x 1 array giving the square of the  sub-diagonal elements, 
         i.e. beta[i] = b[i]*b[i]. beta[0] may be arbitrary but is replaced by
         zero in the procedure.

  x :
         Argument for the Sturm sequence.


Returns:
------------------------
  integer a = Number of eigenvalues of the matrix smaller than x.


Notes:
------------------------
On SGI PowerChallenge this function should be compiled with option
"-O3 -OPT:IEEE_arithmetic=3" in order to activate the optimization 
mentioned in the code below.


**********************************************************************/

{
  int i;
  int a;
  double q;
  
  a = 0;
  q = 1.0;

  for(i=0; i<n; i++) {

#ifndef TESTFIRST

    if (q != 0.0) {

#ifndef RECIPROCAL
      q =  (c[i] - x) - beta[i]/q; 
#else 
  /* A potentially NUMERICALLY DANGEROUS optimizations is used here.
   * The previous statement should read:
   *         q = (c[i] - x) - beta[i]/q 
   * But computing the reciprocal might help on some architectures
   * that have multiply-add and/or reciprocal instuctions.
   */
     iq = 1.0/q;  
      q =  (c[i] - x) - beta[i]*iq; 
#endif

    }
    else {
      q = (c[i] - x) - fabs(b[i])/DBL_EPSILON;  
    }

    if (q < 0)
      a = a + 1;    
  }

#else
    
    if (q < 0) {
      a = a + 1;    
      
#ifndef RECIPROCAL
      q =  (c[i] - x) - beta[i]/q; 
#else 
      /* A potentially NUMERICALLY DANGEROUS optimizations is used here.
       * The previous statement should read:
       *         q = (c[i] - x) - beta[i]/q 
       * But computing the reciprocal might help on some architectures
       * that have multiply-add and/or reciprocal instuctions.
       */
      iq = 1.0/q;  
      q =  (c[i] - x) - beta[i]*iq; 
#endif
      
    }
    else if (q > 0.0) {
#ifndef RECIPROCAL
      q =  (c[i] - x) - beta[i]/q; 
#else 
      /* A potentially NUMERICALLY DANGEROUS optimizations is used here.
       * The previous statement should read:
       *         q = (c[i] - x) - beta[i]/q 
       * But computing the reciprocal might help on some architectures
       * that have multiply-add and/or reciprocal instuctions.
       */
      iq = 1.0/q;  
      q =  (c[i] - x) - beta[i]*iq; 
#endif
    }
    else {
      q = (c[i] - x) - fabs(b[i])/DBL_EPSILON;  
    }
    
  }
  if (q < 0)
    a = a + 1;    
#endif

  return a;
}
  



void dbisect(double c[], double b[], double beta[], 
	     int n, int m1, int m2, double eps1, double *eps2, int *z,  
	     double x[])


/**************************************************************************

Purpose:
------------
 
  Calculates eigenvalues lambda_{m1}, lambda_{m1+1},...,lambda_{m2} of
  a symmetric tridiagonal matrix with diagonal c[0],c[1],...,c[n-1]
  and off-diagonal elements b[1],b[2],...,b[n-1] by the method of
  bisection, using Sturm sequences.


  Input parameters:
------------------------

  c[0]..c[n-1] : 
        An n x 1 array giving the diagonal elements of the tridiagonal matrix.

  b[1]..b[n-1] :   
        An n x 1 array giving the sub-diagonal elements. b[0] may be 
        arbitrary but is replaced by zero in the procedure.

  beta[1]..beta[n-1] :
         An n x 1 array giving the square of the  sub-diagonal elements, 
         i.e. beta[i] = b[i]*b[i]. beta[0] may be arbitrary but is replaced by
         zero in the procedure.

  n :
         The order of the matrix.

  m1, m2 : 
         The eigenvalues lambda_{m1}, lambda_{m1+1},...,lambda_{m2} are 
         calculated (NB! lambda_1 is the smallest eigenvalue).
         m1 <= m2must hold otherwise no eigenvalues are computed.
         returned in x[m1-1],x[m1],...,x[m2-1]
 
  eps1 :
         a quantity that affects the precision to which eigenvalues are 
         computed. The bisection is continued as long as 
         x_high - x_low >  2*DBL_EPSILON(|x_low|  + |x_high|) + eps1       (1)
         When (1) is no longer satisfied, (x_high + x_low)/2  gives the
         current eigenvalue lambda_k. Here DBL_EPSILON (constant) is
         the machine accuracy, i.e. the smallest number such that
         (1 + DBL_EPSILON) > 1.

  Output parameters:
------------------------

  eps2 :
        The overall bound  for the error in any eigenvalue.
  z :
        The total number of iterations to find all eigenvalues.
  x : 
        The array  x[m1],x[m1+1],...,x[m2] contains the computed eigenvalues.

**********************************************************************/
{
  int i;
  double h,xmin,xmax;
  beta[0]  = b[0] = 0.0; 


  /* calculate Gerschgorin interval */
  xmin = c[n-1] - FUDGE*fabs(b[n-1]);
  xmax = c[n-1] + FUDGE*fabs(b[n-1]);
  for(i=n-2; i>=0; i--) { 
    h = FUDGE*(fabs(b[i]) + fabs(b[i+1]));
    if (c[i] + h > xmax)  xmax = c[i] + h;
    if (c[i] - h < xmin)  xmin = c[i] - h;
  }

  /*  printf("xmax = %lf  xmin = %lf\n",xmax,xmin); */

  /* estimate precision of calculated eigenvalues */  
  *eps2 = DBL_EPSILON * (xmin + xmax > 0 ? xmax : -xmin);
  if (eps1 <= 0)
    eps1 = *eps2;
  *eps2 = 0.5 * eps1 + 7 * *eps2;
  { int a,k;
    double x1,xu,x0;
    double *wu; 

    if( (wu = (double *) calloc(n+1,sizeof(double))) == NULL) {
      fputs("bisect: Couldn't allocate memory for wu",stderr);
      exit(1);
    }

    /* Start bisection process  */
    x0 = xmax;
    for(i=m2; i >= m1; i--) {
      x[i] = xmax;
      wu[i] = xmin;
    }
    *z = 0;
    /* loop for the k-th eigenvalue */
    for(k=m2; k>=m1; k--) {
      xu = xmin;
      for(i=k; i>=m1; i--) {
	if(xu < wu[i]) {
	  xu = wu[i];
	  break;
	}
      }
      if (x0 > x[k])
	x0 = x[k];

      x1 = (xu + x0)/2;
      while ( x0-xu > 2*DBL_EPSILON*(fabs(xu)+fabs(x0))+eps1 ) {	
	*z = *z + 1;
	
	/* Sturms Sequence  */

       	a = sturm(n,c,b,beta,x1); 

	/* Bisection step */
	if (a < k) {
	  if (a < m1) 
	    xu = wu[m1] = x1;
	  else {
	    xu = wu[a+1] = x1;
	    if (x[a] > x1) x[a] = x1;
	  }
	}
	else {
	  x0 = x1;
	}	
	x1 = (xu + x0)/2;	
      }
      x[k] = (xu + x0)/2;
    }
    free(wu);
  }
}     

void test_matrix(int n, double *C, double *B)
/* Symmetric tridiagonal matrix with diagonal

     c_i = i^4,  i = (1,2,...,n)

     and off-diagonal elements

     b_i = i-1,    i = (2,3,...n).
     It is possible to determine small eigenvalues of this matrix, with the
     same relative error as for the large ones. 
*/
{
  int i;
    
  for(i=0; i<n; i++) {
    B[i] = (double) i;
    C[i] = (double ) (i+1)*(i+1);
    C[i] = C[i] * C[i];
  }
}


int main(int argc,char *argv[])
{
  int rep,n,k,i,j;
  double eps,eps2;
  double *D,*E,*beta,*S;

  rep = 1;
  n = 500;
  eps = 2.2204460492503131E-16;

  dallocvector(n,&D);
  dallocvector(n,&E);
  dallocvector(n,&beta);
  dallocvector(n,&S);  
  
  for (j=0; j<rep; j++) {
    test_matrix(n,D,E);
    
    for (i=0; i<n; i++) {
      beta[i] = E[i] * E[i];
      S[i] = 0.0;
    }
    
    E[0] = beta[0] = 0;  
    dbisect(D,E,beta,n,1,n,eps,&eps2,&k,&S[-1]);    
    
  }
  
  for(i=1; i<20; i++)
    printf("%5d %.5e\n",i+1,S[i]); 

  printf("eps2 = %.5e,  k = %d\n",eps2,k);

  return 0;
}


