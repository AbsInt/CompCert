#include <stdio.h>

int foo(void)
{
   return 2;
}

int main(void)
{
   int g_46 = 0 || foo();
   printf ("%d\n", g_46);
   return 0;
}
