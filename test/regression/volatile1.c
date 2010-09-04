volatile int v;

int f1(void) { return v; }

void f2(void) { v = 42; }

int f3(void) { return v / v + 1 + v; }

void f4(void) { v; }
