#include <stdio.h>

struct s {
  unsigned int a: 32;
};

struct s x = { 0x12345678 };

int main()
{
  printf("x = {a = %x}\n", x.a);
  x.a = 0xDEADBEEF;
  printf("x = {a = %x}\n", x.a);
  return 0;
}
