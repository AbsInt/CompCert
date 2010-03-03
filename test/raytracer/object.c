#include "config.h"
#include "arrays.h"
#include "point.h"
#include "vector.h"
#include "eval.h"
#include "object.h"
#include "matrix.h"

static struct object * new_object(int kind, struct closure c)
{
  struct object * o = arena_alloc(sizeof(struct object));
  o->kind = kind;
  o->surf = c;
  o->world2obj = o->obj2world = mid;
  o->max_scale_applied = 1.0;
  o->radius = BS_NOT_COMPUTED;
  return o;
}

struct object * cone(struct closure c)
{ return new_object(Cone, c); }

struct object * cube(struct closure c)
{ return new_object(Cube, c); }

struct object * cylinder(struct closure c)
{ return new_object(Cylinder, c); }

struct object * plane(struct closure c)
{ return new_object(Plane, c); }

struct object * sphere(struct closure c)
{ return new_object(Sphere, c); }

static struct object * transform(struct object * o,
                                 struct matrix * t,
                                 struct matrix * tinv,
                                 flt scale)
{
  struct object * no = arena_alloc(sizeof(struct object));
  no->kind = o->kind;
  switch (o->kind) {
  case Union:
  case Intersection:
  case Difference:
    no->o1 = transform(o->o1, t, tinv, scale);
    no->o2 = transform(o->o2, t, tinv, scale);
    break;
  default:
    no->surf = o->surf;
    no->world2obj = mcompose(o->world2obj, tinv);
    no->obj2world = mcompose(t, o->obj2world);
    no->max_scale_applied = o->max_scale_applied * scale;
  }
  no->radius = BS_NOT_COMPUTED;
  return no;
}

struct object * orotatex(struct object * o1, flt a)
{
  return transform(o1, mrotatex(a), mrotatex(-a), 1.0);
}

struct object * orotatey(struct object * o1, flt a)
{
  return transform(o1, mrotatey(a), mrotatey(-a), 1.0);
}

struct object * orotatez(struct object * o1, flt a)
{
  return transform(o1, mrotatez(a), mrotatez(-a), 1.0);
}

struct object * oscale(struct object * o1, flt sx, flt sy, flt sz)
{
  flt scale = sx;
  if (sy > scale) scale = sy;
  if (sz > scale) scale = sz;
  return transform(o1, mscale(sx, sy, sz), mscale(1 / sx, 1 / sy, 1 / sz),
                   scale);
}

struct object * otranslate(struct object * o1,
                           flt tx, flt ty, flt tz)
{
  return transform(o1, mtranslate(tx, ty, tz), mtranslate(- tx, - ty, - tz), 
                   1.0);
}

struct object * ouscale(struct object * o1, flt s)
{
  flt sinv = 1 / s;
  return transform(o1, mscale(s, s, s), mscale(sinv, sinv, sinv), s);
}

struct object * odifference(struct object * o1, struct object * o2)
{
  struct object * o = arena_alloc(sizeof(struct object));
  o->kind = Difference;
  o->o1 = o1;
  o->o2 = o2;
  o->radius = BS_NOT_COMPUTED;
  return o;
}

struct object * ointersect(struct object * o1, struct object * o2)
{
  struct object * o = arena_alloc(sizeof(struct object));
  o->kind = Intersection;
  o->o1 = o1;
  o->o2 = o2;
  o->radius = BS_NOT_COMPUTED;
  return o;
}

struct object * ounion(struct object * o1, struct object * o2)
{
  struct object * o = arena_alloc(sizeof(struct object));
  o->kind = Union;
  o->o1 = o1;
  o->o2 = o2;
  o->radius = BS_NOT_COMPUTED;
  return o;
}

static void normal_vector_object(struct object * obj, 
                                 struct point * p,
                                 int face,
                                 /*out*/ struct vector * v)
{
  switch (obj->kind) {
  case Cone:
    if (face == 0) {
      v->dx = p->x; v->dy = - p->y; v->dz = p->z;
    } else {
      v->dx = 0; v->dy = 1; v->dz = 0;
    }
    break;
  case Cube:
    switch (face) {
    case 0:
      v->dx = 0; v->dy = 0; v->dz = -1; break;
    case 1:
      v->dx = 0; v->dy = 0; v->dz = 1; break;
    case 2:
      v->dx = -1; v->dy = 0; v->dz = 0; break;
    case 3:
      v->dx = 1; v->dy = 0; v->dz = 0; break;
    case 4:
      v->dx = 0; v->dy = 1; v->dz = 0; break;
    case 5:
      v->dx = 0; v->dy = -1; v->dz = 0; break;
    }
    break;
  case Cylinder:
    switch (face) {
    case 0:
      v->dx = p->x; v->dy = 0; v->dz = p->z; break;
    case 1:
      v->dx = 0; v->dy = 1; v->dz = 0; break;
    case 2:
      v->dx = 0; v->dy = -1; v->dz = 0; break;
    }
    break;
  case Plane:
    v->dx = 0; v->dy = 1; v->dz = 0; break;
  case Sphere:
    v->dx = p->x; v->dy = p->y; v->dz = p->z; break;
  default:
    assert(0);
  }
}

static void tangent_vectors(struct vector * n,
                            /*out*/ struct vector * t1,
                            /*out*/ struct vector * t2)
{
  if (n->dy > 0) {
    t1->dx = n->dy; t1->dy = - n->dx; t1->dz = 0;
    t2->dx = 0; t2->dy = n->dz; t2->dz = - n->dy;
  }
  /*   y   0      xy      x
      -x ^ z   =  yy  = y y
       0  -y      yz      z */
  else if (n->dy == 0) {
    t1->dx = n->dz; t1->dy = 0; t1->dz = - n->dx;
    t2->dx = n->dz; t2->dy = 1; t2->dz = - n->dx;
  }
  /*   z   z       x      x
       0 ^ 1   =   0  = 1 y
      -x  -x       z      z */
  else {
    t1->dx = n->dy; t1->dy = - n->dx; t1->dz = 0;
    t2->dx = 0; t2->dy = - n->dz; t2->dz = n->dy;
  }
  /*   y    0      -xy        x
      -x ^ -z  =   -yy = (-y) y
       0    y      -zy        z */
}

void normal_vector(struct object * obj, struct point * p, int face,
                   /*out*/ struct vector * n)
{
  struct point pobj;
  struct vector nobj, tang_obj1, tang_obj2, tang_world1, tang_world2;

  apply_to_point(obj->world2obj, p, &pobj);
  normal_vector_object(obj, &pobj, face, &nobj);
  tangent_vectors(&nobj, &tang_obj1, &tang_obj2);
  apply_to_vect(obj->obj2world, &tang_obj1, &tang_world1);
  apply_to_vect(obj->obj2world, &tang_obj2, &tang_world2);
  product(&tang_world1, &tang_world2, n);
  vnormalize(n, n);
}

