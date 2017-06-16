#include <stdio.h>

/* Best-choice for signedness of bit-fields of enum type */

enum E1 { A = 0, B, C, D };
enum E2 { E = -2, F, G, H };

struct S { enum E1 x : 2; enum E2 y : 2; };

struct S s;

void printS(void)
{
  printf("s.x = %d, s.y = %d\n", s.x, s.y);
}

int main(void)
{
  s.x = A; s.y = E; printS();
  s.x = B; s.y = F; printS();
  s.x = C; s.y = G; printS();
  s.x = D; s.y = H; printS();
  return 0;
}
