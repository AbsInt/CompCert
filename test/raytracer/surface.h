/* Return the texture coordinates for the given point on the given
   object.  Point in object coords. */

void surface_coords(struct object * obj, struct point * p,
                    /*out*/ int * face,
                    /*out*/ flt * u,
                    /*out*/ flt * v);
