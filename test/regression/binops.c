/* Testing overloading resolution for binary arithmetic */

#include <stdio.h>

signed short ss = -12;
unsigned short us = 0x8001;
signed int si = -43;
unsigned int ui = 0xDEADBEEF;
signed long long sl = -123456789012LL;
unsigned long long ul = 0xDEADBEEF01234567ULL;
double d = 3.141592654;
double d2 = 2.718;

void print_ii(char * op, long long a1, long long a2, long long res)
{
  printf("%lld %s %lld = %lld\n", a1, op, a2, res);
}

void print_di(char * op, double a1, long long a2, double res)
{
  printf("%a %s %lld = %a\n", a1, op, a2, res);
}

void print_id(char * op, long long a1, double a2, double res)
{
  printf("%lld %s %a = %a\n", a1, op, a2, res);
}

void print_dd(char * op, double a1, double a2, double res)
{
  printf("%a %s %a = %a\n", a1, op, a2, res);
}

#define TEST1(op,a1) \
  print_ii(#op, a1, ss, a1 op ss); \
  print_ii(#op, a1, us, a1 op us); \
  print_ii(#op, a1, si, a1 op si); \
  print_ii(#op, a1, ui, a1 op ui); \
  print_ii(#op, a1, sl, a1 op sl); \
  print_ii(#op, a1, ul, a1 op ul); \
  print_id(#op, a1, d, a1 op d)

#define TEST2(op) \
  TEST1(op,ss); \
  TEST1(op,us); \
  TEST1(op,si); \
  TEST1(op,ui); \
  TEST1(op,sl); \
  TEST1(op,ul); \
  print_di(#op, d, ss, d op ss); \
  print_di(#op, d, us, d op us); \
  print_di(#op, d, si, d op si); \
  print_di(#op, d, ui, d op ui); \
  print_di(#op, d, sl, d op sl); \
  print_di(#op, d, ul, d op ul); \
  print_dd(#op, d, d2, d op d2)

int main()
{
  TEST2( + );
  TEST2( / );
  return 0;
}


