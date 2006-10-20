#include <stdio.h>
#include "little.h"

main() {
  term *t;
  t = variable("a");

  if(NULL == t) {
    printf("call to a term constructor returns a NULL pointer");
  } else {
    printf("a variable whose name is %s\n", t->term_body.string_val);
  }
}
