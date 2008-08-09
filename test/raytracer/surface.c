#include "config.h"
#include "point.h"
#include "vector.h"
#include "eval.h"
#include "object.h"
#include "surface.h"

/* Sphere:
      x = sqrt(1 - y^2) sin(360u)
      y = 2v - 1
      z = sqrt(1 - y^2) cos(360u)
   hence v = (y+1)/2
     and u = atan2_turns(x, z) (atan2 in "number of turns")
*/

#define INV2PI (1.0 / (2.0 * M_PI))

static inline flt atan2_turns(flt x, flt z)
{
  flt r = atan2(x, z) * INV2PI;
  if (r < 0.0) r += 1.0;
  return r;
}

static inline void sphere_coords(flt x, flt y, flt z,
                                 int * face, flt * u, flt * v)
{
  *face = 0;
  *u = atan2_turns(x, z);
  *v = (y + 1.0) * 0.5;
}

/* Cube:
     (x, y, 0)  ->  (0, x, y)
     (x, y, 1)  ->  (1, x, y)
     (0, y, z)  ->  (2, z, y)
     (1, y, z)  ->  (3, z, y)
     (x, 1, z)  ->  (4, x, z)
     (x, 0, z)  ->  (5, x, z)
   Watch out for rounding errors when determining which coordinate is 0 or 1;
   see which one is closest to 0 or 1 */

static inline void cube_coords(flt x, flt y, flt z,
                               int * face, flt * u, flt * v)
{
  flt dists[6] =
  { fabs(z), fabs(1 - z), fabs(x), fabs(1 - x), fabs(y), fabs(1 - y) };
  flt min;
  int f, i;

  f = 0; min = dists[0];
  for (i = 1; i < 6; i++)
    if (dists[i] < min) { min = dists[i]; f = i; }
  *face = f;
  switch (f) {
  case 0: case 1:
    *u = x; *v = y; break;
  case 2: case 3:
    *u = z; *v = y; break;
  case 4: case 5:
    *u = x; *v = z; break;
  }
}

/* Cylinder:
     (x, 0, z)  ->  (2, u, v) where x = 2u-1 and z = 2v-1 hence
     (x, 1, z)  ->  (1, x, z)   u = (x+1)/2 and v = (z+1)/2
     (x, y, z)  ->  (0, u, v) where x = sin(360u)  v = y  z = cos(360u)
                              hence u = atan2_turns(x, z)  and v = y
*/

static inline void cylinder_coords(flt x, flt y, flt z,
                                   int * face, flt * u, flt * v)
{
  flt min, d;
  int f;

  min = y * y; f = 0;
  d = (1 - y) * (1 - y);
  if (d < min) { min = d; f = 1; }
  d = fabs(x * x + z * z - 1);
  if (d < min) { min = d; f = 2; }
  *face = 2 - f;
  if (f < 2) {
    *u = (x + 1) * 0.5;
    *v = (z + 1) * 0.5;
  } else {
    *u = atan2_turns(x, z);
    *v = y;
  }
}

/* Cone:
     (x, y, z)  ->  (0, u, v)  where x = v sin 360u
                                     y = v
                                     z = v cos 360u
                               hence u = atan2_turns(x, z) and v = y
     (x, 1, z)  ->  (1, u, v)  where x = 2u-1 and z = 2v-1
                               hence u = (x+1)/2 and v = (z+1)/2
*/

static inline void cone_coords(flt x, flt y, flt z,
                               int * face, flt * u, flt * v)
{
  if ((1 - y) * (1 - y) < fabs(x * x + z * z - y * y)) {
    *face = 1;
    *u = (x + 1) * 0.5;
    *v = (z + 1) * 0.5;
  } else {
    *face = 0;
    *u = atan2_turns(x, z);
    *v = y;
  }
}

/* Plane */

static inline void plane_coords(flt x, flt y, flt z,
                                int * face, flt * u, flt * v)
{
  *face = 0;
  *u = x;
  *v = z;
}

/* All together */

void surface_coords(struct object * obj, struct point * p,
                    /*out*/ int * face,
                    /*out*/ flt * u,
                    /*out*/ flt * v)
{
  switch (obj->kind) {
  case Cone:
    cone_coords(p->x, p->y, p->z, face, u, v); break;
  case Cube:
    cube_coords(p->x, p->y, p->z, face, u, v); break;
  case Cylinder:
    cylinder_coords(p->x, p->y, p->z, face, u, v); break;
  case Plane:
    plane_coords(p->x, p->y, p->z, face, u, v); break;
  case Sphere:
    sphere_coords(p->x, p->y, p->z, face, u, v); break;
  default:
    assert(0);
  }
}

