#include "testharness.h"
#include <stddef.h>

int main() {
  wchar_t *wbase = L"Hello" L", world";
  char * w = (char *)wbase;
  char * s =  "Hello" ", world";
  int i;

  // See if this is little or big endian
  short foo = 0x0011;
  char little_endian = (int) * (char*)&foo;

  for (i=0; i < 10; i++) {
    if (w[i * sizeof(wchar_t)] != (little_endian ? s[i] : 0)) {
      E(1); 
    } 
    if (w[i * sizeof(wchar_t) + (sizeof(wchar_t)-1)]
        != (little_endian ? 0 : s[i])) {
      E(2);
    } 
  }
  SUCCESS;
}
