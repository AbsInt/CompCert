/* Evaluator for GML */

#include "config.h"
#include "arrays.h"
#include "gml.h"
#include "point.h"
#include "vector.h"
#include "eval.h"
#include "object.h"
#include "light.h"
#include "render.h"

struct value {
  enum { B, I, R, S, Arr, Clos, Point, Obj, Light } tag;
  union {
    int i;                      /* B, I */
    flt r;                   /* R */
    char * s;                   /* S */
    struct array * arr;         /* Arr */
    struct closure clos;        /* Clos */
    struct point * point;       /* Point */
    struct object * obj;        /* Obj */
    struct light * light;       /* Light */
  } u;
};

struct binding {
  char * name;
  int mutable;
  struct value val;
};

/* Lookup an identifier in an environment */

static int lookup(struct array * env, char * name, /*out*/ struct value * res)
{
  int i;
  for (i = env->size - 1; i >= 0; i--) {
    struct binding * b = &get_array(struct binding, env, i);
    if (name == b->name) {
      *res = b->val;
      return 1;
    }
  }
  return 0;
}

/* Assign an identifier in an environment */

static void assign(struct array * env, char * name, struct value * newval)
{
  int i;
  struct binding * b;
  for (i = env->size - 1; i >= 0; i--) {
    b = &get_array(struct binding, env, i);
    if (! b->mutable) break;
    if (name == b->name) {
      b->val = *newval;
      return;
    }
  }
  extend_array(struct binding, env);
  b = &get_array(struct binding, env, env->size - 1);
  b->name = name;
  b->mutable = 1;
  b->val = *newval;
}

/* Take an immutable copy of an environment */

static struct array * snapshot_env(struct array * env)
{
  int i;
  struct array * nenv = copy_array(sizeof(struct binding), env, 10);
  for (i = 0; i < nenv->size; i++)
    get_array(struct binding, nenv, i).mutable = 0;
  return nenv;
}

/* Utility math functions */

static inline flt degrees_to_radians(flt d)
{ return d * (M_PI / 180.0); }

static inline flt radians_to_degrees(flt d)
{ return d * (180.0 / M_PI); }

static inline flt deg_cos(flt a)
{ return cos(degrees_to_radians(a)); }

static inline flt deg_sin(flt a)
{ return sin(degrees_to_radians(a)); }

static inline flt deg_acos(flt a)
{ return radians_to_degrees(acos(a)); }

static inline flt deg_asin(flt a)
{ return radians_to_degrees(asin(a)); }

static inline flt clampf(flt r)
{
  if (r < 0.0) return 0.0;
  if (r > 1.0) return 1.0;
  return r;
}

/* For error printing */

static char * operator_names [] = {
  "<Identifier>", "<Binder>", "<Boolean>", "<Integer>", "<Real>",
  "<String>", "<Array>", "<Function>", "acos", "addi", "addf", "apply",
  "asin", "clampf", "cone", "cos", "cube", "cylinder", "difference",
  "divi", "divf", "eqi", "eqf", "floor", "frac", "get", "getx", "gety",
  "getz", "if", "intersect", "length", "lessi", "lessf", "light",
  "modi", "muli", "mulf", "negi", "negf", "plane", "point",
  "pointlight", "real", "render", "rotatex", "rotatey", "rotatez",
  "scale", "sin", "sphere", "spotlight", "sqrt", "subi", "subf",
  "translate", "union", "uscale", "print",
};

/* Convert a GML array of lights into a C array of lights */

static struct light ** light_array(struct array * arr)
{
  int sz = arr->size;
  struct light ** l = arena_alloc((sz + 1) * sizeof(struct light *));
  int i;
  for (i = 0; i < sz; i++) {
    struct value * v = &get_array(struct value, arr, i);
    if (v->tag != Light) {
      fprintf(stderr, "Light expected in array argument to `render'\n");
      exit(2);
    }
    l[i] = v->u.light;
  }
  l[sz] = NULL;
  return l;
}

/* Pretty-print a value */

static void print_value(struct value * s)
{
  switch (s->tag) {
  case B:
    printf("%s\n", s->u.i ? "true" : "false"); break;
  case I:
    printf("%d\n", s->u.i); break;
  case R:
    printf("%e\n", s->u.r); break;
  case S:
    printf("\"%s\"\n", s->u.s); break;
  case Arr:
    printf("array\n"); break;
  case Clos:
    printf("closure\n"); break;
  case Point:
    printf("point %e %e %e\n", 
           s->u.point->x, s->u.point->y, s->u.point->z);
    break;
  case Obj:
    printf("object\n"); break;
  case Light:
    printf("light\n"); break;
  }
}

/* The evaluation stack */

#define MAIN_STACK_SIZE 10000
#define SURFACE_STACK_SIZE 1000

static struct value main_stack[MAIN_STACK_SIZE];
static struct value surface_stack[SURFACE_STACK_SIZE];

/* Macros for stack checking and type checking */

#define push() if (--sp < bos) goto stack_overflow
#define can_pop(n) if (sp + (n) > tos) goto stack_underflow
#define check(n,ty) if (sp[n].tag != ty) goto type_error

/* Execute the given token list in the given environment */

static struct value * execute_list(struct array * code,
                                   struct array * env,
                                   struct value * bos,
                                   struct value * tos,
                                   struct value * sp)
{
  int i;
  struct tok * t;

  for (i = 0; i < code->size; i++) {
    t = &get_array(struct tok, code, i);
    switch (t->tag) {
    case Identifier:
      push();
      if (! lookup(env, t->u.s, sp)) {
        fprintf(stderr, "Unbound identifier %s\n", t->u.s);
        exit(2);
      }
      break;
    case Binder:
      can_pop(1);
      assign(env, t->u.s, sp);
      sp++;
      break;
    case Boolean:
      push();
      sp[0].tag = B; sp[0].u.i = t->u.i;
      break;
    case Integer:
      push();
      sp[0].tag = I; sp[0].u.i = t->u.i;
      break;
    case Real:
      push();
      sp[0].tag = R; sp[0].u.r = t->u.d;
      break;
    case String:
      push();
      sp[0].tag = S; sp[0].u.s = t->u.s;
      break;
    case Array: {
      struct value * esp = execute_list(t->u.a, env, bos, sp, sp);
      int sz = sp - esp;
      struct array * a = new_array(struct value, sz);
      int j;
      a->size = sz;
      for (j = 0; j < sz; j++) set_array(struct value, a, j, sp[-1-j]);
      push();
      sp[0].tag = Arr; sp[0].u.arr = a;
      break;
    }
    case Function:
      push();
      sp[0].tag = Clos;
      sp[0].u.clos.code = t->u.a;
      sp[0].u.clos.env = snapshot_env(env);
      break;
    case Op_acos:
      can_pop(1);
      check(0, R);
      sp[0].u.r = deg_acos(sp[0].u.r);
      break;
    case Op_addi:
      can_pop(2);
      check(1, I);
      check(0, I);
      sp[1].u.i = sp[1].u.i + sp[0].u.i;
      sp += 1;
      break;
    case Op_addf:
      can_pop(2);
      check(1, R);
      check(0, R);
      sp[1].u.r = sp[1].u.r + sp[0].u.r;
      sp += 1;
      break;
    case Op_apply:
      can_pop(1);
      check(0, Clos);
      sp = execute_list(sp[0].u.clos.code, sp[0].u.clos.env, bos, tos, sp + 1);
      break;
    case Op_asin:
      can_pop(1);
      check(0, R);
      sp[0].u.r = deg_asin(sp[0].u.r);
      break;
    case Op_clampf:
      can_pop(1);
      check(0, R);
      sp[0].u.r = clampf(sp[0].u.r);
      break;
    case Op_cone:
      can_pop(1);
      check(0, Clos);
      sp[0].tag = Obj;
      sp[0].u.obj = cone(sp[0].u.clos);
      break;
    case Op_cos:
      can_pop(1);
      check(0, R);
      sp[0].u.r = deg_cos(sp[0].u.r);
      break;
    case Op_cube:
      can_pop(1);
      check(0, Clos);
      sp[0].tag = Obj;
      sp[0].u.obj = cube(sp[0].u.clos);
      break;
    case Op_cylinder:
      can_pop(1);
      check(0, Clos);
      sp[0].tag = Obj;
      sp[0].u.obj = cylinder(sp[0].u.clos);
      break;
    case Op_difference:
      can_pop(2);
      check(1, Obj);
      check(0, Obj);
      sp[1].u.obj = odifference(sp[1].u.obj, sp[0].u.obj);
      sp += 1;
      break;
    case Op_divi:
      can_pop(2);
      check(1, I);
      check(0, I);
      if (sp[0].u.i == 0) goto division_by_zero;
      sp[1].u.i = sp[1].u.i / sp[0].u.i;
      sp += 1;
      break;
    case Op_divf:
      can_pop(2);
      check(1, R);
      check(0, R);
      sp[1].u.r = sp[1].u.r / sp[0].u.r;
      sp += 1;
      break;
    case Op_eqi:
      can_pop(2);
      check(1, I);
      check(0, I);
      sp[1].tag = B;
      sp[1].u.i = (sp[1].u.i == sp[0].u.i);
      sp += 1;
      break;
    case Op_eqf:
      can_pop(2);
      check(1, R);
      check(0, R);
      sp[1].tag = B;
      sp[1].u.i = (sp[1].u.r == sp[0].u.r);
      sp += 1;
      break;
    case Op_floor:
      can_pop(1);
      check(0, R);
      sp[0].tag = I;
      sp[0].u.i = (int) floor(sp[0].u.r);
      break;
    case Op_frac: {
      double rem;
      can_pop(1);
      check(0, R);
      sp[0].u.r = modf(sp[0].u.r, &rem);
      break;
    }
    case Op_get: {
      struct array * a;
      int idx;
      can_pop(2);
      check(1, Arr);
      check(0, I);
      a = sp[1].u.arr;
      idx = sp[0].u.i;
      if (idx < 0 || idx >= a->size) goto bound_error;
      sp[1] = get_array(struct value, a, idx);
      sp++;
      break;
    }
    case Op_getx:
      can_pop(1);
      check(0, Point);
      sp[0].tag = R;
      sp[0].u.r = sp[0].u.point->x;
      break;
    case Op_gety:
      can_pop(1);
      check(0, Point);
      sp[0].tag = R;
      sp[0].u.r = sp[0].u.point->y;
      break;
    case Op_getz:
      can_pop(1);
      check(0, Point);
      sp[0].tag = R;
      sp[0].u.r = sp[0].u.point->z;
      break;
    case Op_if:
      can_pop(3);
      check(2, B);
      check(1, Clos);
      check(0, Clos);
      if (sp[2].u.i)
        sp = execute_list(sp[1].u.clos.code, sp[1].u.clos.env, bos, tos, sp + 3);
      else
        sp = execute_list(sp[0].u.clos.code, sp[0].u.clos.env, bos, tos, sp + 3);
      break;
    case Op_intersect:
      can_pop(2);
      check(1, Obj);
      check(0, Obj);
      sp[1].u.obj = ointersect(sp[1].u.obj, sp[0].u.obj);
      sp += 1;
      break;
    case Op_length:
      can_pop(1);
      check(0, Arr);
      sp[0].tag = I;
      sp[0].u.i = sp[0].u.arr->size;
      break;
    case Op_lessi:
      can_pop(2);
      check(1, I);
      check(0, I);
      sp[1].tag = B;
      sp[1].u.i = (sp[1].u.i < sp[0].u.i);
      sp += 1;
      break;
    case Op_lessf:
      can_pop(2);
      check(1, R);
      check(0, R);
      sp[1].tag = B;
      sp[1].u.i = (sp[1].u.r < sp[0].u.r);
      sp += 1;
      break;
    case Op_light:
      can_pop(2);
      check(1, Point);
      check(0, Point);
      sp[1].tag = Light;
      sp[1].u.light = dirlight(sp[1].u.point, sp[0].u.point);
      sp += 1;
      break;
    case Op_modi:
      can_pop(2);
      check(1, I);
      check(0, I);
      if (sp[0].u.i == 0) goto division_by_zero;
      sp[1].u.i = sp[1].u.i % sp[0].u.i;
      sp += 1;
      break;
    case Op_muli:
      can_pop(2);
      check(1, I);
      check(0, I);
      sp[1].u.i = sp[1].u.i * sp[0].u.i;
      sp += 1;
      break;
    case Op_mulf:
      can_pop(2);
      check(1, R);
      check(0, R);
      sp[1].u.r = sp[1].u.r * sp[0].u.r;
      sp += 1;
      break;
    case Op_negi:
      can_pop(1);
      check(0, I);
      sp[0].u.i = - sp[0].u.i;
      break;
    case Op_negf:
      can_pop(1);
      check(0, R);
      sp[0].u.r = - sp[0].u.r;
      break;
    case Op_plane:
      can_pop(1);
      check(0, Clos);
      sp[0].tag = Obj;
      sp[0].u.obj = plane(sp[0].u.clos);
      break;
    case Op_point: {
      struct point * p;
      can_pop(3);
      check(2, R);
      check(1, R);
      check(0, R);
      p = arena_alloc(sizeof(struct point));
      p->x = sp[2].u.r;
      p->y = sp[1].u.r;
      p->z = sp[0].u.r;
      sp += 2;
      sp[0].tag = Point;
      sp[0].u.point = p;
      break;
    }
    case Op_pointlight:
      can_pop(2);
      check(1, Point);
      check(0, Point);
      sp[1].tag = Light;
      sp[1].u.light = pointlight(sp[1].u.point, sp[0].u.point);
      sp += 1;
      break;
    case Op_real:
      can_pop(1);
      check(0, I);
      sp[0].tag = R;
      sp[0].u.r = (flt) sp[0].u.i;
      break;
    case Op_render:
      can_pop(8);
      check(0, S);
      check(1, I);
      check(2, I);
      check(3, R);
      check(4, I);
      check(5, Obj);
      check(6, Arr);
      check(7, Point);
      render(sp[7].u.point,
             sp[6].u.arr->size,
             light_array(sp[6].u.arr),
             sp[5].u.obj,
             sp[4].u.i,
             degrees_to_radians(sp[3].u.r),
             sp[2].u.i,
             sp[1].u.i,
             sp[0].u.s);
      sp += 8;
      break;
    case Op_rotatex:
      can_pop(2);
      check(1, Obj);
      check(0, R);
      sp[1].u.obj = orotatex(sp[1].u.obj, degrees_to_radians(sp[0].u.r));
      sp += 1;
      break;
    case Op_rotatey:
      can_pop(2);
      check(1, Obj);
      check(0, R);
      sp[1].u.obj = orotatey(sp[1].u.obj, degrees_to_radians(sp[0].u.r));
      sp += 1;
      break;
    case Op_rotatez:
      can_pop(2);
      check(1, Obj);
      check(0, R);
      sp[1].u.obj = orotatez(sp[1].u.obj, degrees_to_radians(sp[0].u.r));
      sp += 1;
      break;
    case Op_scale:
      can_pop(4);
      check(3, Obj);
      check(2, R);
      check(1, R);
      check(0, R);
      sp[3].u.obj = oscale(sp[3].u.obj, sp[2].u.r, sp[1].u.r, sp[0].u.r);
      sp += 3;
      break;
    case Op_sin:
      can_pop(1);
      check(0, R);
      sp[0].u.r = deg_sin(sp[0].u.r);
      break;
    case Op_sphere:
      can_pop(1);
      check(0, Clos);
      sp[0].tag = Obj;
      sp[0].u.obj = sphere(sp[0].u.clos);
      break;
    case Op_spotlight:
      can_pop(5);
      check(4, Point);
      check(3, Point);
      check(2, Point);
      check(1, R);
      check(0, R);
      sp[4].tag = Light;
      sp[4].u.light = spotlight(sp[4].u.point, sp[3].u.point, sp[2].u.point, 
                                degrees_to_radians(sp[1].u.r), sp[0].u.r);
      sp += 4;
      break;
    case Op_sqrt:
      can_pop(1);
      check(0, R);
      if (sp[0].u.r < 0) goto negative_sqrt;
      sp[0].u.r = sqrt(sp[0].u.r);
      break;
    case Op_subi:
      can_pop(2);
      check(1, I);
      check(0, I);
      sp[1].u.i = sp[1].u.i - sp[0].u.i;
      sp += 1;
      break;
    case Op_subf:
      can_pop(2);
      check(1, R);
      check(0, R);
      sp[1].u.r = sp[1].u.r - sp[0].u.r;
      sp += 1;
      break;
    case Op_translate:
      can_pop(4);
      check(3, Obj);
      check(2, R);
      check(1, R);
      check(0, R);
      sp[3].u.obj = otranslate(sp[3].u.obj, sp[2].u.r, sp[1].u.r, sp[0].u.r);
      sp += 3;
      break;
    case Op_union:
      can_pop(2);
      check(1, Obj);
      check(0, Obj);
      sp[1].u.obj = ounion(sp[1].u.obj, sp[0].u.obj);
      sp += 1;
      break;
    case Op_uscale:
      can_pop(2);
      check(1, Obj);
      check(0, R);
      sp[1].u.obj = ouscale(sp[1].u.obj, sp[0].u.r);
      sp += 1;
      break;
    case Op_print:
      can_pop(1);
      print_value(sp);
      sp += 1;
      break;
    }
  }
  return sp;
  /* Error handling */
 stack_overflow:
  fprintf(stderr, "Stack overflow\n");
  goto print_context;
 stack_underflow:
  fprintf(stderr, "Stack underflow\n");
  goto print_context;
 type_error:
  fprintf(stderr, "Type error\n");
  goto print_context;
 division_by_zero:
  fprintf(stderr, "Division by zero\n");
  goto print_context;
 bound_error:
  fprintf(stderr, "Out-of-bound array access\n");
  goto print_context;
 negative_sqrt:
  fprintf(stderr, "Square root of negative number\n");
 print_context:
  fprintf(stderr, "(operation: %s, PC: %d)\n", operator_names[t->tag], i);
  exit(2);
}

/* Evaluate a surface function */

void surface_function(struct closure clos, int face, flt u, flt v,
                      /*out*/ struct surface_characteristics * sc)
{
  struct value * sp;
  sp = surface_stack + SURFACE_STACK_SIZE - 3;
  sp[2].tag = I;
  sp[2].u.i = face;
  sp[1].tag = R;
  sp[1].u.i = u;
  sp[0].tag = R;
  sp[0].u.i = v;
  sp =
    execute_list(clos.code, clos.env, surface_stack,
                 surface_stack + SURFACE_STACK_SIZE, sp);
  if (sp != surface_stack + SURFACE_STACK_SIZE - 4 ||
      sp[0].tag != R ||
      sp[1].tag != R ||
      sp[2].tag != R ||
      sp[3].tag != Point) {
    fprintf(stderr, "Wrong result for surface function\n");
    exit(2);
  }
  sc->x = sp[3].u.point->x;
  sc->y = sp[3].u.point->y;
  sc->z = sp[3].u.point->z;
  sc->kd = sp[2].u.r;
  sc->ks = sp[1].u.r;
  sc->phong = sp[0].u.r;
}

/* Execute the main program */

void execute_program(struct array * toklist)
{
  execute_list(toklist, new_array(struct binding, 50),
               main_stack,
               main_stack + MAIN_STACK_SIZE,
               main_stack + MAIN_STACK_SIZE);
}
