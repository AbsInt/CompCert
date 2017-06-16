#include <stdlib.h>
#include <stdio.h>

int main()
{
  printf("%d\n", sizeof("abcd"));
  printf("%d\n", sizeof(L"abcd") / sizeof(wchar_t));
  return 0;
}
