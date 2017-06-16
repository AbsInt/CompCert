/* C99 'for' loops with declarations */

#include <stdio.h>

int main()
{
  int i;
  for (i = 0; i < 3; i++) printf("loop1: %d\n", i);
  for (int i = 0; i < 3; i++) printf("loop2: %d\n", i);
  printf("old i = %d\n", i);
  for (int i = 0, j; i < 3; i++) {
    j = i * 2 + 1; printf("loop3: %d %d\n", i, j);
  }
  printf("old i = %d\n", i);
  for (int i = 0, j = i + 4; i < 3; i++, j--) {
    printf("loop4: %d %d\n", i, j);
  }
  printf("old i = %d\n", i);
  return 0;
}
