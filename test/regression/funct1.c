int f() { return 0; }

int g(void) { return f(1); }

int h(x, y) int x, y; { return x + y; }

int k(void) { return h(1); }

