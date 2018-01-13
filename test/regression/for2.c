/* Issue #211 */

#include <stdio.h>

int press = 100;
int valve = 0;

int main (void) {
  for (int press = 0; press < 3; press++) {
    valve++;
  }
  printf ("Value of 'press' should be 100, is: %d\n", press);
  return valve - 3;
}
