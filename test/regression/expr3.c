/* Array decay in && */

struct s {
  int a[1];
};

int f(struct s * x) { return x && x->a; }
