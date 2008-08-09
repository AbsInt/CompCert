struct light {
  enum { Directional, Pointlight, Spot } kind;
  union {
    struct {
      struct point dir;
      struct point col;
    } directional;
    struct {
      struct point orig;
      struct point col;
    } point;
    struct {
      struct point orig;
      struct point at;
      struct point col;
      flt cutoff, exponent;
      struct vector unit;
    } spot;
  } u;
};

struct light * dirlight(struct point * dir, struct point * c);
struct light * pointlight(struct point * orig, struct point * c);
struct light * spotlight(struct point * pos, struct point * at,
                         struct point * c, flt a, flt cutoff);

void color_from_lights(struct object * obj,
                       struct point * p,
                       struct vector * v,
                       struct vector * n,
                       flt kd, flt ks, flt phong,
                       struct light ** lights,
                       /*out*/ struct point * il);
