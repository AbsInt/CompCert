/* Initializer can refer to ident just declared */

struct list { int hd; struct list * tl; } circular = { sizeof(circular), &circular };
