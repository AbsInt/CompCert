#include <stdio.h>

struct S0 {
  signed f0 : 12;
  unsigned f1 : 28;
};

struct S5 {
  struct S0  f1;
  unsigned : 0;
  signed f2 : 26;
};

struct S5 g_22 = {{0,0},1};

int main(int argc, char* argv[])
{
   printf("g_22.f2 = %d\n", g_22.f2);
   return 0;
}
