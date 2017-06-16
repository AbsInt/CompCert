#include <stdio.h>

struct S1 {
  unsigned f0 : 13;
  unsigned : 6;
  unsigned f1 : 5;
  unsigned : 0;
  unsigned f2 : 8;
};

struct S1 g_207 = {1,2,3};

void print_S1(struct S1 * p)
{
  printf("f0 = %u, f1 = %u, f2 = %u, second = %u\n",
         p->f0, p->f1, p->f2, 
         *((unsigned char *)p + 4));
}

int main()
{
  struct S1 x;

  print_S1(&g_207);
  x.f0 = 123; x.f1 = 4; x.f2 = 56;
  print_S1(&x);
  return 0;
}
