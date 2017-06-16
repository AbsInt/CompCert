struct B;
int f(struct B);
struct B { double d; };
int g() { struct B b; return f(b); }
