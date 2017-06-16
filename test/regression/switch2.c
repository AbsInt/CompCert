/* switch over long long */

#include <stdio.h>

/* Jumptable */

int f(long long x)
{
  switch (x) {
  case 1: return 34;
  case 2: return 56;
  case 3: return 78;
  case 4: return 123;
  case 5: return 456;
  case 6: return 789;
  case 7: return 11;
  case 8: return 22;
  case 9: return 33;
  case 10: return 44;
  case 11: return 55;
  case 12: return 66;
  case 13: return 77;
  case 14: return 88;
  case 15: return 99;
  case 16: return 321;
  case 17: return 654;
  case 18: return 987;
  case 19: return 1001;
  default: return -1;
  }
}

/* Decision tree */

int g(long long x)
{
  switch(x) {
  case 0x7FFFFFFFFFFFFFFFLL: return 1;
  case -0x8000000000000000LL: return 2;
  case 0: return 3;
  case 4: return 4;
  case 13: return 5;
  default: return -1;
  }
}

int main(void)
{
  int i;
  for (i = -1; i <= 20; i++) {
    printf("f(%d) = %d\n", i, f(i));
  }
  long long j;
  j = 0x7FFFFFFFFFFFFFFFLL; printf("g(%lld) = %d\n", j, g(j));
  j = -0x8000000000000000LL; printf("g(%lld) = %d\n", j, g(j));
  j = 0x12300000000LL; printf("g(%lld) = %d\n", j, g(j));
  for (i = -1; i <= 20; i++) {
    printf("g(%d) = %d\n", i, g(i));
  }
  return 0;
}
