#include <stdarg.h>
#include <stdio.h>

int sum_v(int n, va_list ap)
{
  int i, s;
  for (i = 0, s = 0; i < n; i++) s += va_arg(ap, int);
  return s;
}

int sum_l(int n, ...)
{
  va_list ap;
  int s;
  va_start(ap, n);
  s = sum_v(n, ap);
  va_end(ap);
  return s;
}

int main()
{
  printf("Sum is %d\n", sum_l(10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10));
  return 0;
}
