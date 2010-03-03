struct s;

struct s { int x; double y; };

struct s my_s;

double f(struct s * a) { return a->y; }

