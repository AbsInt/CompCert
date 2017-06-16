#include "config.h"
#include "point.h"
#include "vector.h"

flt dotproduct(struct vector * a, struct vector * b)
{
  return a->dx * b->dx + a->dy * b->dy + a->dz * b->dz;
}

void between(struct point * p, struct point * q,
                           /*out*/ struct vector * v)
{
  v->dx = q->x - p->x;
  v->dy = q->y - p->y;
  v->dz = q->z - p->z;
}

void opposite(struct vector * v,
              /*out*/ struct vector * w)
{
  w->dx = - v->dx;
  w->dy = - v->dy;
  w->dz = - v->dz;
}

void point_along(struct point * p, struct vector * v,
                 flt ac,
                 /*out*/ struct point * q)
{
  q->x = p->x + v->dx * ac;
  q->y = p->y + v->dy * ac;
  q->z = p->z + v->dz * ac;
}

void product(struct vector * a, struct vector * b,
                           /*out*/ struct vector * v)
{
  v->dx = a->dy * b->dz - a->dz * b->dy;
  v->dy = a->dz * b->dx - a->dx * b->dz;
  v->dz = a->dx * b->dy - a->dy * b->dx;
}

flt vlength2(struct vector * a)
{
  return a->dx * a->dx + a->dy * a->dy + a->dz * a->dz;
}

flt vlength(struct vector * a)
{
  return sqrt(vlength2(a));
}

void vscale(struct vector * a, flt s,
                          /*out*/ struct vector * v)
{
  v->dx = a->dx * s;
  v->dy = a->dy * s;
  v->dz = a->dz * s;
}

void vnormalize(struct vector * a, /*out*/ struct vector * v)
{
  vscale(a, 1 / vlength(a), v);
}

void vsub(struct vector * a, struct vector * b,
                        /*out*/ struct vector * v)
{
  v->dx = a->dx - b->dx;
  v->dy = a->dy - b->dy;
  v->dz = a->dz - b->dz;
}

  
