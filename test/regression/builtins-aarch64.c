/* AArch64-specific builtin functions */

#include <stdio.h>

int main(int argc, char ** argv)
{
  double a = 3.14159;
  double b = 2.718;
  double c = 1.414;
  signed int u = 1234567;
  signed int v = -9999;

  printf("cls(%d) = %d\n", u, __builtin_cls(u));
  printf("cls(%d) = %d\n", v, __builtin_cls(v));
  printf("clsll(%lld) = %d\n", (signed long long) u, __builtin_clsll(u));
  printf("clsll(%lld) = %d\n", (signed long long) v, __builtin_clsll(v));

  printf("fmadd(%f, %f, %f) = %f\n", a, b, c, __builtin_fmadd(a, b, c));
  printf("fmsub(%f, %f, %f) = %f\n", a, b, c, __builtin_fmsub(a, b, c));
  printf("fnmadd(%f, %f, %f) = %f\n", a, b, c, __builtin_fnmadd(a, b, c));
  printf("fnmsub(%f, %f, %f) = %f\n", a, b, c, __builtin_fnmsub(a, b, c));

  return 0;
}


  


