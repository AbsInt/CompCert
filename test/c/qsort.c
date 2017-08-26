#include <stdlib.h>
#include <stdio.h>
#include <string.h>

void quicksort(int lo, int hi, int base[])
{ 
  int i,j;
  int pivot,temp;
    
  if (lo<hi) {
    for (i=lo,j=hi,pivot=base[hi];i<j;) {
      while (i<hi && base[i]<=pivot) i++;
      while (j>lo && base[j]>=pivot) j--;
      if (i<j) { temp=base[i]; base[i]=base[j]; base[j]=temp; }
    }
    temp=base[i]; base[i]=base[hi]; base[hi]=temp;
    quicksort(lo,i-1,base);  quicksort(i+1,hi,base);
  }
}

int cmpint(const void * i, const void * j)
{
  int vi = *((int *) i);
  int vj = *((int *) j);
  if (vi == vj) return 0;
  if (vi < vj) return -1;
  return 1;
}

#define NITER 10

int main(int argc, char ** argv)
{
  int n, i, j;
  int * a, * b;

  if (argc >= 2) n = atoi(argv[1]); else n = 100000;
  a = malloc(n * sizeof(int));
  b = malloc(n * sizeof(int));
  for (j = 0; j < NITER; j++) {
    for (i = 0; i < n; i++) b[i] = a[i] = rand() & 0xFFFF;
    quicksort(0, n - 1, a);
  }
  qsort(b, n, sizeof(int), cmpint);
  for (i = 0; i < n; i++) {
    if (a[i] != b[i]) { printf("Bug!\n"); return 2; }
  }
  printf("OK\n");
  return 0;
}
