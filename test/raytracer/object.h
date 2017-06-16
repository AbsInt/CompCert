struct object {
  enum { Cone, Cube, Cylinder, Plane, Sphere,
         Union, Intersection, Difference } kind;
  /* For base objects: Cone, Cube, Cylinder, Plane, Sphere */
  struct closure surf;          /* surface function */
  struct matrix * world2obj, * obj2world;
  flt max_scale_applied;
  /* For compound objects: Union, Intersection, Difference */
  struct object * o1, * o2;
  /* For all objects: bounding sphere (center and radius) */
  struct point center;
  flt radius;
};

struct object * cone(struct closure c);
struct object * cube(struct closure c);
struct object * cylinder(struct closure c);
struct object * plane(struct closure c);
struct object * sphere(struct closure c);

struct object * orotatex(struct object * o1, flt a);
struct object * orotatey(struct object * o1, flt a);
struct object * orotatez(struct object * o1, flt a);
struct object * oscale(struct object * o1, flt sx, flt sy, flt sz);
struct object * otranslate(struct object * o1,
                           flt tx, flt ty, flt tz);
struct object * ouscale(struct object * o1, flt s);

struct object * odifference(struct object * o1, struct object * o2);
struct object * ointersect(struct object * o1, struct object * o2);
struct object * ounion(struct object * o1, struct object * o2);

void normal_vector(struct object * obj, struct point * p, int face,
                   /*out*/ struct vector * n);

#define BS_NOT_COMPUTED (-1.0)
