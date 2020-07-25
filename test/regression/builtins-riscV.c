/* RISC-V specific builtin functions */

#include <stdio.h>

unsigned int x = 0x12345678;
unsigned short s = 0x1234;
unsigned long long zz = 0x123456789ABCDEF0ULL;
double a = 3.14159;
double b = 2.718;
double c = 1.414;

int main(int argc, char ** argv)
{
  printf("fmadd(%f, %f, %f) = %f\n", a, b, c, __builtin_fmadd(a, b, c));
  printf("fmsub(%f, %f, %f) = %f\n", a, b, c, __builtin_fmsub(a, b, c));
  printf("fnmadd(%f, %f, %f) = %f\n", a, b, c, __builtin_fnmadd(a, b, c));
  printf("fnmsub(%f, %f, %f) = %f\n", a, b, c, __builtin_fnmsub(a, b, c));
  printf("fmax(%f, %f) = %f\n", a, b, __builtin_fmax(a, b));
  printf("fmin(%f, %f) = %f\n", a, b, __builtin_fmin(a, b));
  return 0;
}
