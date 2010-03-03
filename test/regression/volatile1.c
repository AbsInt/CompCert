volatile int v;

int f1(void) { return v; }

int f2(void) { return v++; }

int f3(void) {return v / v + 1 + v; }

void f4(void) { v; }
