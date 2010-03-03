#include "config.h"
#include "point.h"
#include "vector.h"
#include "arrays.h"
#include "matrix.h"
#include "eval.h"
#include "object.h"
#include "simplify.h"

#define INFINITE_RADIUS HUGE_VAL

static flt cone_radius = 1.0;
static flt cube_radius = 0.86602540378443859659; /* sqrt(3)/2 */
static flt cylinder_radius = 1.11803398874989490253; /* sqrt(5)/2 */
static flt sphere_radius = 1.0;

static struct point cone_center = { 0.0, 1.0, 0.0 };
static struct point cube_center = { 0.5, 0.5, 0.5 };
static struct point cylinder_center = { 0.0, 0.5, 0.0 };
static struct point sphere_center = { 0, 0, 0 };
static struct point plane_center = { 0, 0, 0 };

static struct point origin = { 0, 0, 0 };

static inline void set_infinite(struct object * t)
{
  t->radius = INFINITE_RADIUS;
}

static inline void union_bs(struct object * t1, struct object * t2,
                            struct object * obj)
{
  struct vector c1c2;
  flt dd2, rr, rr2, d, alpha;

  if (t1->radius >= INFINITE_RADIUS || t2->radius >= INFINITE_RADIUS) {
    obj->radius = INFINITE_RADIUS;
    return;
  }
  between(&t1->center, &t2->center, &c1c2);
  dd2 = vlength2(&c1c2);
  rr = t2->radius - t1->radius;
  rr2 = rr * rr;
  if (dd2 <= rr2) {
    /* take the biggest sphere */
    if (t1->radius <= t2->radius) {
      obj->center = t2->center;
      obj->radius = t2->radius;
      set_infinite(t2);
    } else {
      obj->center = t1->center;
      obj->radius = t1->radius;
      set_infinite(t1);
    }
    return;
  }
  d = sqrt(dd2);
  alpha = rr / (2 * d) + 0.5;
  point_along(&t1->center, &c1c2, alpha, &obj->center);
  obj->radius = (d + t1->radius + t2->radius) / 2;
}

static inline void intersection_bs(struct object * t1, struct object * t2,
                                   struct object * obj)
{
  struct vector c1c2;
  flt dd2, rr, rr2, rpr, rpr2, diff, d, te1, te2, te3, te4, te, alpha;

  if (t1->radius >= INFINITE_RADIUS) {
    obj->center = t2->center;
    obj->radius = t2->radius;
    return;
  }
  if (t2->radius >= INFINITE_RADIUS) {
    obj->center = t1->center;
    obj->radius = t1->radius;
    return;
  }
  between(&t1->center, &t2->center, &c1c2);
  dd2 = vlength2(&c1c2);
  rr = t1->radius - t2->radius;
  rr2 = rr * rr;
  if (dd2 <= rr2) {
    /* take the smallest sphere */
    if (t2->radius <= t1->radius) {
      obj->center = t2->center;
      obj->radius = t2->radius;
      set_infinite(t2);
    } else {
      obj->center = t1->center;
      obj->radius = t1->radius;
      set_infinite(t1);
    }
    return;
  }
  rpr = t1->radius + t2->radius;
  rpr2 = rpr * rpr;
  if (dd2 > rpr2) {
    obj->center = origin;
    obj->radius = 0.0;
    return;
  }
  diff = t1->radius * t1->radius - t2->radius * t2->radius;
  if (dd2 <= diff) {
    obj->center = t2->center;
    obj->radius = t2->radius;
    set_infinite(t2);
    return;
  }
  if (dd2 <= -diff) {
    obj->center = t1->center;
    obj->radius = t1->radius;
    set_infinite(t1);
    return;
  }
  d = sqrt(dd2);
  te1 = t1->radius + d + t2->radius;
  te2 = t1->radius + d - t2->radius;
  te3 = t2->radius + d - t1->radius;
  te4 = t1->radius + t2->radius - d;
  te = (sqrt (te1 * te2 * te3 * te4)) / (2 * d);
  alpha =
    (t1->radius * t1->radius - t2->radius * t2->radius) / (2 * dd2) + 0.5;
  point_along(&t1->center, &c1c2, alpha, &obj->center);
  obj->radius = te;
}

static inline void difference_bs(struct object * t1, struct object * t2,
                                   struct object * obj)
{
  obj->center = t1->center;
  obj->radius = t1->radius;
  set_infinite(t1);
}

void compute_bounding_spheres(struct object * obj)
{
  if (obj->radius >= 0.0) return; /* already computed */
  switch (obj->kind) {
  case Cone:
    apply_to_point(obj->obj2world, &cone_center, &obj->center);
    obj->radius = obj->max_scale_applied * cone_radius;
    break;
  case Cube:
    apply_to_point(obj->obj2world, &cube_center, &obj->center);
    obj->radius = obj->max_scale_applied * cube_radius;
    break;
  case Cylinder:
    apply_to_point(obj->obj2world, &cylinder_center, &obj->center);
    obj->radius = obj->max_scale_applied * cylinder_radius;
    break;
  case Plane:
    obj->center = plane_center;
    obj->radius = INFINITE_RADIUS;
    break;
  case Sphere:
    apply_to_point(obj->obj2world, &sphere_center, &obj->center);
    obj->radius = obj->max_scale_applied * sphere_radius;
    break;
  case Union:
    compute_bounding_spheres(obj->o1);
    compute_bounding_spheres(obj->o2);
    union_bs(obj->o1, obj->o2, obj);
    break;
  case Intersection:
    compute_bounding_spheres(obj->o1);
    compute_bounding_spheres(obj->o2);
    intersection_bs(obj->o1, obj->o2, obj);
    break;
  case Difference:
    compute_bounding_spheres(obj->o1);
    compute_bounding_spheres(obj->o2);
    difference_bs(obj->o1, obj->o2, obj);
    break;
  }
}

