#include <stddef.h>

struct list {unsigned head; struct list *tail;};
struct list three[] = { {1, three+1}, {2, three+2}, {3, NULL} };
int f(int x) { return x;}
