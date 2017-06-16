/* Evaluator for GML */

struct closure {
  struct array * code;
  struct array * env;
};

struct surface_characteristics {
  flt x, y, z;
  flt kd;
  flt ks;
  flt phong;
};

void execute_program(struct array * toklist);

void surface_function(struct closure clos, int face, flt u, flt v,
                      /*out*/ struct surface_characteristics * sc);
