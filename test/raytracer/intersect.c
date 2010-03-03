#include "config.h"
#include "arrays.h"
#include "point.h"
#include "vector.h"
#include "eval.h"
#include "object.h"
#include "matrix.h"
#include "intersect.h"

/* Operations on interval lists */

#define POS_INFTY HUGE_VAL

struct intervlist {
  flt beg;
  struct object * obeg;
  flt end;
  struct object * oend;
  struct intervlist * next;
};

typedef struct intervlist * intervlist;

static intervlist cons(flt b, struct object * ob,
                       flt e, struct object * oe,
                       intervlist next)
{
  intervlist l = arena_alloc(sizeof(struct intervlist));
  l->beg = b;
  l->obeg = ob;
  l->end = e;
  l->oend = oe;
  l->next = next;
  return l;
}

static intervlist conshead(intervlist i, intervlist next)
{
  intervlist l = arena_alloc(sizeof(struct intervlist));
  l->beg = i->beg;
  l->obeg = i->obeg;
  l->end = i->end;
  l->oend = i->oend;
  l->next = next;
  return l;
}

static intervlist union_intervals(intervlist l1, intervlist l2)
{
  flt beg;
  struct object * obeg;

  if (l1 == NULL) return l2;
  if (l2 == NULL) return l1;
  if (l1->end < l2->beg)
    /* int1 strictly before int2 */
    return conshead(l1, union_intervals(l1->next, l2));
  if (l2->end < l1->beg)
    /* int2 strictly before int1 */
    return conshead(l2, union_intervals(l1, l2->next));
  /* int1 and int2 overlap, merge */
  if (l1->beg < l2->beg) {
    beg = l1->beg;
    obeg = l1->obeg;
  } else {
    beg = l2->beg;
    obeg = l2->obeg;
  }
  if (l1->end < l2->end)
    return union_intervals(l1->next,
                           cons(beg, obeg, l2->end, l2->oend, l2->next));
  else
    return union_intervals(cons(beg, obeg, l1->end, l1->oend, l1->next),
                           l2->next);
}

static intervlist intersect_intervals(intervlist l1, intervlist l2)
{
  flt beg;
  struct object * obeg;

  if (l1 == NULL) return NULL;
  if (l2 == NULL) return NULL;
  if (l1->end < l2->beg)
    /* int1 strictly before int2 */
    return intersect_intervals(l1->next, l2);
  if (l2->end < l1->beg)
    /* int2 strictly before int1 */
    return intersect_intervals(l1, l2->next);
  /* int1 and int2 overlap, add intersection */
  if (l1->beg > l2->beg) {
    beg = l1->beg;
    obeg = l1->obeg;
  } else {
    beg = l2->beg;
    obeg = l2->obeg;
  }
  if (l1->end < l2->end)
    return cons(beg, obeg, l1->end, l1->oend, intersect_intervals(l1->next, l2));
  else
    return cons(beg, obeg, l2->end, l2->oend, intersect_intervals(l1, l2->next));
}

static intervlist difference_intervals(intervlist l1, intervlist l2)
{
  intervlist l;

  if (l1 == NULL) return NULL;
  if (l2 == NULL) return l1;
  if (l1->end < l2->beg)
    /* int1 strictly before int2, keep int1 */
    return conshead(l1, difference_intervals(l1->next, l2));
  if (l2->end < l1->beg)
    /* int2 strictly before int1, throw int2 away */
    return difference_intervals(l1, l2->next);
  /* int and int2 overlap */
  if (l1->end > l2->end)
    /* int1 extends beyond int2, add segment [l2->end,l1->end] */
    l = difference_intervals(cons(l2->end, l2->oend, l1->end, l1->oend, l1->next), l2->next);
  else
    /* int2 doesn't extend beyond int2, nothing to add */
    l = difference_intervals(l1->next, l2);
  if (l1->beg < l2->beg)
    /* int1 starts before l2, add segment [l1->beg,l2->beg] */
    l = cons(l1->beg, l1->obeg, l2->beg, l2->obeg, l);
  return l;
}

/* Intersections between rays (p + tv) and basic objects (bobj) */

static intervlist intersect_ray_plane(struct object * bobj,
                                      struct point * p,
                                      struct vector * v)
{
  if (p->y >= 0)
    if (v->dy >= 0)
      return NULL;
    else
      return cons(- p->y / v->dy, bobj, POS_INFTY, bobj, NULL);
  else
    if (v->dy >= 0)
      return cons(0, bobj, - p->y / v->dy, bobj, NULL);
    else
      return cons(0, bobj, POS_INFTY, bobj, NULL);
}

static intervlist intersect_ray_sphere(struct object * bobj,
                                       struct point * p,
                                       struct vector * v)
{
  flt a, b, c, d, sq, t0, t1, tswap;

  a = v->dx * v->dx + v->dy * v->dy + v->dz * v->dz;
  b = p->x * v->dx + p->y * v->dy + p->z * v->dz;
  c = p->x * p->x + p->y * p->y + p->z * p->z - 1.0;
  d = b * b - a * c;
  if (d <= 0) return NULL;
  sq = sqrt(d);
  /* Numerically stable solution of quadratic */
  if (b >= 0) {
    t0 = c / (- b - sq);
    t1 = (- b - sq) / a;
  } else {
    t0 = c / (- b + sq);
    t1 = (- b + sq) / a;
  }
  if (t0 >= t1) {
    tswap = t0; t0 = t1; t1 = tswap;
  }
  if (t1 <= 0) {
    assert (t0 <= 0);
    return NULL;
  }
  if (t0 >= 0) {
    assert (t1 >= 0);
    return cons(t0, bobj, t1, bobj, NULL);
  }
  return cons(0, bobj, t1, bobj, NULL);
}

static intervlist intersect_ray_slice(struct object * bobj,
                                      flt pc, flt vc)
{
  if (pc > 1.0) {
    if (vc >= 0.0)
      return NULL;
    else
      return cons((1.0 - pc) / vc, bobj, - pc / vc, bobj, NULL);
  }
  if (pc < 0.0) {
    if (vc <= 0.0)
      return NULL;
    else
      return cons(- pc / vc, bobj, (1.0 - pc) / vc, bobj, NULL);
  }
  if (vc == 0.0)
    return cons(0.0, bobj, POS_INFTY, bobj, NULL);
  if (vc > 0.0)
    return cons(0.0, bobj, (1.0 - pc) / vc, bobj, NULL);
  else
    return cons(0.0, bobj, - pc / vc, bobj, NULL);
}

static intervlist intersect_ray_cube(struct object * bobj,
                                     struct point * p,
                                     struct vector * v)
{
  return intersect_intervals(intersect_ray_slice(bobj, p->x, v->dx),
           intersect_intervals(intersect_ray_slice(bobj, p->y, v->dy),
                               intersect_ray_slice(bobj, p->z, v->dz)));
}

static intervlist intersect_ray_infinite_cylinder(struct object * bobj,
                                                  struct point * p,
                                                  struct vector * v)
{
  flt a, b, c, d, sq, t0, t1, tswap;

  a = v->dx * v->dx + v->dz * v->dz;
  b = p->x * v->dx + p->z * v->dz;
  c = p->x * p->x + p->z * p->z - 1.0;
  d = b * b - a * c;
  if (d <= 0.0) return NULL;
  sq = sqrt(d);
  if (b >= 0.0) {
    t0 = c / (- b - sq);
    t1 = (- b - sq) / a;
  } else {
    t0 = c / (- b + sq);
    t1 = (- b + sq) / a;
  }
  if (t0 >= t1) { tswap = t0; t0 = t1; t1 = tswap; }
  if (t1 <= 0.0) {
    assert (t0 <= 0.0);
    return NULL;
  }
  if (t0 >= 0.0) {
    assert (t1 >= 0.0);
    return cons(t0, bobj, t1, bobj, NULL);
  }
  return cons(0.0, bobj, t1, bobj, NULL);
}

static intervlist intersect_ray_cylinder(struct object * bobj,
                                         struct point * p,
                                         struct vector * v)
{
  return intersect_intervals(intersect_ray_infinite_cylinder(bobj, p, v),
                             intersect_ray_slice(bobj, p->y, v->dy));
}

static intervlist intersect_ray_infinite_cone(struct object * bobj,
                                              struct point * p,
                                              struct vector * v)
{
  flt a, b, c, d, sq, t, t0, t1, tswap;

  a = v->dx * v->dx - v->dy * v->dy + v->dz * v->dz;
  b = p->x * v->dx - p->y * v->dy + p->z * v->dz;
  c = p->x * p->x - p->y * p->y + p->z * p->z;
  if (a == 0.0) {
    if (b == 0.0) return NULL;
    t = - 0.5 * c / b;
    if (c < 0.0) {
      if (t <= 0.0)
        return cons(0.0, bobj, POS_INFTY, bobj, NULL);
      else
        return cons(0.0, bobj, t, bobj, NULL);
    }
    if (t <= 0.0)
      return NULL;
    else
      return cons(t, bobj, POS_INFTY, bobj, NULL);
  }
  d = b * b - a * c;
  if (d <= 0.0) return NULL;
  sq = sqrt(d);
  if (b >= 0.0) {
    t0 = c / (- b - sq);
    t1 = (- b - sq) / a;
  } else {
    t0 = c / (- b + sq);
    t1 = (- b + sq) / a;
  }
  if (t0 >= t1) { tswap = t0; t0 = t1; t1 = tswap; }
  if (t1 <= 0.0) {
      assert (t0 <= 0.0);
      if (c < 0.0)
        return cons(0.0, bobj, POS_INFTY, bobj, NULL);
      else
        return NULL;
  }
  if (t0 >= 0.0) {
    assert (t1 >= 0.0);
    if (c < 0.0)
      return cons(0.0, bobj, t0, bobj,
                  cons (t1, bobj, POS_INFTY, bobj, NULL));
    else
      return cons(t0, bobj, t1, bobj, NULL);
  }
  if (c < 0.0)
    return cons(0.0, bobj, t1, bobj, NULL);
  else
    return cons(t1, bobj, POS_INFTY, bobj, NULL);
}

static intervlist intersect_ray_cone(struct object * bobj,
                                     struct point * p,
                                     struct vector * v)
{
  return intersect_intervals(intersect_ray_infinite_cone(bobj, p, v),
                             intersect_ray_slice(bobj, p->y, v->dy));
}

/* Approximate test based on bounding sphere */

static inline int inside_bs(struct point * p,
                            struct vector * v,
                            struct object * obj)
{
  flt x, y, z, a, b, c;

  assert(obj->radius >= 0.0);

  if (obj->radius >= POS_INFTY) return 1;
  /* Shift origin to obj.center */
  x = p->x - obj->center.x;
  y = p->y - obj->center.y;
  z = p->z - obj->center.z;
  /* Check whether quadratic has positive discriminant */
  a = v->dx * v->dx + v->dy * v->dy + v->dz * v->dz;
  b = x * v->dx + y * v->dy + z * v->dz;
  c = x * x + y * y + z * z - obj->radius * obj->radius;
  return (b * b > a * c);
}

/* Interval list representing the intersection of the given ray
   and the given composite object */

static intervlist intersect_ray_object(struct point * p,
                                       struct vector * v,
                                       struct object * obj)
{
#define CONVERT_V_P \
    apply_to_point(obj->world2obj, p, &p2); \
    apply_to_vect(obj->world2obj, v, &v2)
  struct point p2;
  struct vector v2;
  intervlist res;

  /* Fast, approximate test based on bounding sphere */
  if (! inside_bs(p, v, obj)) return NULL;
  /* Slow, exact test */
  switch (obj->kind) {
  case Cone:
    CONVERT_V_P;
    res = intersect_ray_cone(obj, &p2, &v2);
    break;
  case Cube:
    CONVERT_V_P;
    res = intersect_ray_cube(obj, &p2, &v2);
    break;
  case Cylinder:
    CONVERT_V_P;
    res = intersect_ray_cylinder(obj, &p2, &v2);
    break;
  case Plane:
    CONVERT_V_P;
    res = intersect_ray_plane(obj, &p2, &v2);
    break;
  case Sphere:
    CONVERT_V_P;
    res = intersect_ray_sphere(obj, &p2, &v2);
    break;
  case Union:
    res = union_intervals(intersect_ray_object(p, v, obj->o1),
                           intersect_ray_object(p, v, obj->o2));
    break;
  case Intersection:
    res = intersect_intervals(intersect_ray_object(p, v, obj->o1),
                               intersect_ray_object(p, v, obj->o2));
    break;
  case Difference:
    res = difference_intervals(intersect_ray_object(p, v, obj->o1),
                                intersect_ray_object(p, v, obj->o2));
    break;
  default:
    assert(0);
  }
#undef CONVERT_V_P
  return res;
}

/* Return the closest base object intersecting the given ray, and
   the curvilinear abscissa t of the intersection point.
   Return NULL if no intersection.
   Return t = 0.0 if the viewpoint (origin of the ray) is inside an
   object. */

struct object * intersect_ray(struct point * p,
                              struct vector * v,
                              struct object * obj,
                              int initial,
                              /*out*/ flt * t)
{
  intervlist l = intersect_ray_object(p, v, obj);
  if (l == NULL) return NULL;
  assert(l->beg >= 0.0);
  if (l->beg <= 0.0 && !initial) {
    /* skip first intersection */
    l = l->next;
    if (l == NULL) return NULL;
  }
  *t = l->beg;
  return l->obeg;
}
