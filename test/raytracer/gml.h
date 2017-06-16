/* The GML abstract syntax tree */

enum operation {
    Identifier,
    Binder,
    Boolean,
    Integer,
    Real,
    String,
    Array,
    Function,
    Op_acos,
    Op_addi,
    Op_addf,
    Op_apply,
    Op_asin,
    Op_clampf,
    Op_cone,
    Op_cos,
    Op_cube,
    Op_cylinder,
    Op_difference,
    Op_divi,
    Op_divf,
    Op_eqi,
    Op_eqf,
    Op_floor,
    Op_frac,
    Op_get,
    Op_getx,
    Op_gety,
    Op_getz,
    Op_if,
    Op_intersect,
    Op_length,
    Op_lessi,
    Op_lessf,
    Op_light,
    Op_modi,
    Op_muli,
    Op_mulf,
    Op_negi,
    Op_negf,
    Op_plane,
    Op_point,
    Op_pointlight,
    Op_real,
    Op_render,
    Op_rotatex,
    Op_rotatey,
    Op_rotatez,
    Op_scale,
    Op_sin,
    Op_sphere,
    Op_spotlight,
    Op_sqrt,
    Op_subi,
    Op_subf,
    Op_translate,
    Op_union,
    Op_uscale,
    Op_print
};

struct tok {
  enum operation tag;
  union {
    char * s;                   /* Identifier, Binder, String */
    int i;                      /* Boolean, Integer */
    flt d;                      /* Real */
    struct array * a;           /* Array, Function */
  } u;
};
