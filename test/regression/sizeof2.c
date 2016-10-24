#include <stdlib.h>
#include <stdio.h>

int main()
{
  printf("%d\n", (int) sizeof("abcd"));
  printf("%d\n", (int) (sizeof(L"abcd") / sizeof(wchar_t)));
  return 0;
}
