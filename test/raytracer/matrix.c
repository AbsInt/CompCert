#include "config.h"
#include "point.h"
#include "vector.h"
#include "matrix.h"

void apply_to_point(struct matrix * m, struct point * p,
                                  /*out*/ struct point * r)
{
  r->x = m->xx * p->x + m->xy * p->y + m->xz * p->z + m->xt;
  r->y = m->yx * p->x + m->yy * p->y + m->yz * p->z + m->yt;
  r->z = m->zx * p->x + m->zy * p->y + m->zz * p->z + m->zt;
}

void apply_to_vect(struct matrix * m, struct vector * v,
                                  /*out*/ struct vector * r)
{
  r->dx = m->xx * v->dx + m->xy * v->dy + m->xz * v->dz;
  r->dy = m->yx * v->dx + m->yy * v->dy + m->yz * v->dz;
  r->dz = m->zx * v->dx + m->zy * v->dy + m->zz * v->dz;
}

static struct matrix matrix_identity = {
  1.0,  0.0,  0.0,  0.0,
  0.0,  1.0,  0.0,  0.0,
  0.0,  0.0,  1.0,  0.0,
};

struct matrix * mid = &matrix_identity;

struct matrix * mtranslate(flt sx, flt sy, flt sz)
{
  struct matrix * m = arena_alloc(sizeof(struct matrix));
  m->xx = 1.0;  m->xy = 0.0;  m->xz = 0.0;  m->xt = sx;
  m->yx = 0.0;  m->yy = 1.0;  m->yz = 0.0;  m->yt = sy;
  m->zx = 0.0;  m->zy = 0.0;  m->zz = 1.0;  m->zt = sz;
  return m;
}

struct matrix * mscale(flt sx, flt sy, flt sz)
{
  struct matrix * m = arena_alloc(sizeof(struct matrix));
  m->xx = sx;   m->xy = 0.0;  m->xz = 0.0;  m->xt = 0.0;
  m->yx = 0.0;  m->yy = sy ;  m->yz = 0.0;  m->yt = 0.0;
  m->zx = 0.0;  m->zy = 0.0;  m->zz = sz ;  m->zt = 0.0;
  return m;
}

struct matrix * mrotatex(flt a)
{
  struct matrix * m = arena_alloc(sizeof(struct matrix));
  flt c = cos(a);
  flt s = sin(a);
  m->xx = 1.0;  m->xy = 0.0;  m->xz = 0.0;  m->xt = 0.0;
  m->yx = 0.0;  m->yy = c;    m->yz = - s;  m->yt = 0.0;
  m->zx = 0.0;  m->zy = s;    m->zz = c;    m->zt = 0.0;
  return m;
}

struct matrix * mrotatey(flt a)
{
  struct matrix * m = arena_alloc(sizeof(struct matrix));
  flt c = cos(a);
  flt s = sin(a);
  m->xx = c;    m->xy = 0.0;  m->xz = s;    m->xt = 0.0;
  m->yx = 0.0;  m->yy = 1.0;  m->yz = 0.0;  m->yt = 0.0;
  m->zx = - s;  m->zy = 0.0;  m->zz = c;    m->zt = 0.0;
  return m;
}

struct matrix * mrotatez(flt a)
{
  struct matrix * m = arena_alloc(sizeof(struct matrix));
  flt c = cos(a);
  flt s = sin(a);
  m->xx = c;    m->xy = - s;  m->xz = 0.0;  m->xt = 0.0;
  m->yx = s;    m->yy = c;    m->yz = 0.0;  m->yt = 0.0;
  m->zx = 0.0;  m->zy = 0.0;  m->zz = 1.0;  m->zt = 0.0;
  return m;
}

struct matrix * mcompose(struct matrix * m, struct matrix * n)
{
  struct matrix * r = arena_alloc(sizeof(struct matrix));

  r->xx = m->xx * n->xx + m->xy * n->yx + m->xz * n->zx;
  r->xy = m->xx * n->xy + m->xy * n->yy + m->xz * n->zy;
  r->xz = m->xx * n->xz + m->xy * n->yz + m->xz * n->zz;
  r->xt = m->xx * n->xt + m->xy * n->yt + m->xz * n->zt + m->xt;

  r->yx = m->yx * n->xx + m->yy * n->yx + m->yz * n->zx;
  r->yy = m->yx * n->xy + m->yy * n->yy + m->yz * n->zy;
  r->yz = m->yx * n->xz + m->yy * n->yz + m->yz * n->zz;
  r->yt = m->yx * n->xt + m->yy * n->yt + m->yz * n->zt + m->yt;

  r->zx = m->zx * n->xx + m->zy * n->yx + m->zz * n->zx;
  r->zy = m->zx * n->xy + m->zy * n->yy + m->zz * n->zy;
  r->zz = m->zx * n->xz + m->zy * n->yz + m->zz * n->zz;
  r->zt = m->zx * n->xt + m->zy * n->yt + m->zz * n->zt + m->zt;

  return r;
}

