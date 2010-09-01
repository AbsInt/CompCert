#include <stdio.h>

struct S0 {
   unsigned f : 10;
};

struct S1 {
   unsigned f : 32;
};

int main(void)
{
    struct S0 l = {1};
    struct S1 m = {1};
    printf("g = %d\n", (-1 >= l.f));
    printf("h = %d\n", (-1 >= m.f));
    return 0;
}
