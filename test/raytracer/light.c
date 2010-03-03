#include "config.h"
#include "point.h"
#include "vector.h"
#include "eval.h"
#include "object.h"
#include "intersect.h"
#include "light.h"

struct light * dirlight(struct point * dir, struct point * c)
{
  struct light * l = arena_alloc(sizeof(struct light));
  l->kind = Directional;
  l->u.directional.dir = *dir;
  l->u.directional.col = *c;
  return l;
}

struct light * pointlight(struct point * orig, struct point * c)
{
  struct light * l = arena_alloc(sizeof(struct light));
  l->kind = Pointlight;
  l->u.point.orig = *orig;
  l->u.point.col = *c;
  return l;
}

struct light * spotlight(struct point * pos, struct point * at,
                         struct point * c, flt cutoff, flt exp)
{
  struct light * l = arena_alloc(sizeof(struct light));
  struct vector uv;
  l->kind = Spot;
  l->u.spot.orig = *pos;
  l->u.spot.at = *at;
  l->u.spot.col = *c;
  l->u.spot.cutoff = cutoff;
  l->u.spot.exponent = exp;
  between(at, pos, &uv);
  vnormalize(&uv, &(l->u.spot.unit));
  return l;
}

static void color_from_light(struct object * scene,
                             struct point * pt,
                             struct vector * v,
                             struct vector * n,
                             flt kd, flt ks, flt phong,
                             struct light * light,
                             /*out*/ struct point * il)
{
  struct vector dir;
  struct object * obj;
  struct vector L, H, vnorm;
  struct point i;
  flt t, att, dp, m;

  /* Compute direction towards light source */
  switch (light->kind) {
  case Directional:
    dir.dx = - light->u.directional.dir.x;
    dir.dy = - light->u.directional.dir.y;
    dir.dz = - light->u.directional.dir.z;
    break;
  case Pointlight:
    between(pt, &light->u.point.orig, &dir);
    break;
  case Spot:
    between(pt, &light->u.spot.orig, &dir);
    break;
  }
  /* Check that light source is not behind us */
  if (dotproduct(&dir, n) <= 0.0) return; /*no contribution*/
  /* Check that no object blocks the light */
  obj = intersect_ray(pt, &dir, scene, 0 /*??*/, &t);
  if (obj != NULL && (light->kind == Directional || t <= 1.0)) return;
  /* Compute the L and H vectors */
  vnormalize(&dir, &L);
  vnormalize(v, &vnorm);
  vsub(&L, &vnorm, &H);
  vnormalize(&H, &H);
  /* Intensity of light source at object */
  switch (light->kind) {
  case Directional:
    i = light->u.directional.col;
    break;
  case Pointlight:
    att = 100.0 / (99.0 + dist2(pt, &light->u.point.orig));
    i.x = light->u.point.col.x * att;
    i.y = light->u.point.col.y * att;
    i.z = light->u.point.col.z * att;
    break;
  case Spot:
    dp = dotproduct(&L, &light->u.spot.unit);
    if (acos(dp) >= light->u.spot.cutoff) return;
    att =
      pow(dp, light->u.spot.exponent)
      * (100.0 / (99.0 + dist2(pt, &light->u.spot.orig)));
    i.x = light->u.spot.col.x * att;
    i.y = light->u.spot.col.y * att;
    i.z = light->u.spot.col.z * att;
    break;
  }
  /* Add final contribution */
  m = kd * dotproduct(n, &L) + ks * pow(dotproduct(n, &H), phong);
  il->x += m * i.x;
  il->y += m * i.y;
  il->z += m * i.z;
}

void color_from_lights(struct object * scene,
                       struct point * p,
                       struct vector * v,
                       struct vector * n,
                       flt kd, flt ks, flt phong,
                       struct light ** lights,
                       /*out*/ struct point * il)
{
  int i;

  il->x = il->y = il->z = 0.0;
  for (i = 0; lights[i] != NULL; i++)
    color_from_light(scene, p, v, n, kd, ks, phong, lights[i], il);
}

