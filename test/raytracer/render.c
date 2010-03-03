#include "config.h"
#include "point.h"
#include "vector.h"
#include "matrix.h"
#include "eval.h"
#include "object.h"
#include "light.h"
#include "intersect.h"
#include "surface.h"
#include "simplify.h"
#include "render.h"

static void render_ray(struct point * amb,
                       int depth,
                       int initial,
                       struct object * obj,
                       struct light ** lights,
                       struct point * p,
                       struct vector * v,
                       flt multx,
                       flt multy,
                       flt multz,
                       /*out*/ struct point * color)
{
  struct object * bobj;
  flt t;
  struct point inter_w, inter_o;
  int face;
  flt surf_u, surf_v;
  struct surface_characteristics sc;
  flt dotprod;
  struct vector n, n2, s;
  struct point il, is;

  if (depth < 0) {
    color->x = color->y = color->z = 0.0;
    return;
  }
  bobj = intersect_ray(p, v, obj, initial, &t);
  if (bobj == NULL || t == 0.0) {
    color->x = color->y = color->z = 0.0;
    return;
  }
  /* Compute surface characteristics */
  point_along(p, v, t, &inter_w);
  apply_to_point(bobj->world2obj, &inter_w, &inter_o);
  surface_coords(bobj, &inter_o, &face, &surf_u, &surf_v);
  surface_function(bobj->surf, face, surf_u, surf_v, &sc);
  /* Construct the vectors on figure 4 */
  normal_vector(bobj, &inter_w, face, &n);
  dotprod = dotproduct(v, &n);
  vscale(&n, 2.0 * dotprod, &n2);
  vsub(v, &n2, &s);
  if (dotprod > 0.0) opposite(&n, &n);
  /* Light sources */
  color_from_lights(obj, &inter_w, v, &n,
                    sc.kd, sc.ks, sc.phong,
                    lights, &il);
  /* Recursive call for ray along s */
  multx = multx * sc.ks * sc.x;
  multy = multy * sc.ks * sc.y;
  multz = multz * sc.ks * sc.z;
  if (multx < 0.1 && multy < 0.1 && multz < 0.1)
    is.x = is.y = is.z = 0.0;
  else
    render_ray(amb, depth - 1, 0, obj, lights, &inter_w, &s,
               multx, multy, multz, &is);
  /* Compute final color */
  color->x = (sc.kd * amb->x + il.x + sc.ks * is.x) * sc.x;
  color->y = (sc.kd * amb->y + il.y + sc.ks * is.y) * sc.y;
  color->z = (sc.kd * amb->z + il.z + sc.ks * is.z) * sc.z;
}

static int convert_color(flt c)
{
  int n = (int) (c * 255.0);
  if (n < 0) n = 0;
  if (n > 255) n = 255;
  return n;
}

void render(struct point * amb,
            int numlights,
            struct light ** lights,
            struct object * scene,
            int depth,
            flt fov,
            int wid,
            int ht,
            char * filename)
{
  FILE * oc;
  flt wid2, ht2, scale, x, y;
  int i, j;
  struct point p;
  struct vector v;
  struct point color;
  char * command;

  compute_bounding_spheres(scene);
  wid2 = (flt) wid / 2.0;
  ht2 = (flt) ht / 2.0;
  scale = tan(fov / 2.0) / wid2;
  oc = fopen(filename, "w");
  fprintf(oc, "P6\n# Camls 'R Us\n%d %d\n255\n", wid, ht);
  arena_init();
  for (j = ht - 1; j >= 0; j--) {
    y = ((flt) j - ht2 + 0.5) * scale;
    for (i = 0; i < wid; i++) {
      x = ((flt) i - wid2 + 0.5) * scale;
      p.x = p.y = 0.0; p.z = -1.0;
      v.dx = x; v.dy = y; v.dz = 1.0;
      render_ray(amb, depth, 1, scene, lights, &p, &v, 255.0, 255.0, 255.0,
                 &color);
      fputc(convert_color(color.x), oc);
      fputc(convert_color(color.y), oc);
      fputc(convert_color(color.z), oc);
      arena_clear();
    }
  }
  fclose(oc);
#ifdef XV
  command = malloc(strlen(filename) + 20);
  sprintf(command, "xv %s &", filename);
  system(command);
  free(command);
#endif
}
