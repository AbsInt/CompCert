/* Return the closest base object intersecting the given ray, and
   the curvilinear abscissa t of the intersection point.
   Return NULL if no intersection.
   Return t = 0.0 if the viewpoint (origin of the ray) is inside an
   object. */

struct object * intersect_ray(struct point * p,
                              struct vector * v,
                              struct object * obj,
                              int initial,
                              /*out*/ flt * t);
