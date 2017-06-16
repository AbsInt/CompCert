#include <stdio.h>

/* Local function declarations */

int f (int p)
{
    p = p + 1;
     return p;
}

int main (int argc, char **argv)
{
    int (*p)(int);
    int f();
    int i;

    p = f;
    i = (*p)(1);
    printf("Result is %d\n", i);
    return 0;
}
