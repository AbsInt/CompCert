#include <stdio.h>

int main() { 
  int a[10];
  int *p = &a[0];
  int *q = &a[9];
  printf("p - q = %d\n", (int)(p - q));
  printf("q - p = %d\n", (int)(q - p));
  return 0;
}
