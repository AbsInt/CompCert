/* Parser for GML */

#include "config.h"

#include "arrays.h"
#include "gml.h"
#include "gmllexer.h"
#include "gmlparser.h"

static struct array * parse_tokenlist(void);

static int parse_token(struct tok * t)
{
  get_lexeme();
  switch (current_lexeme.kind) {
  case OPERATOR:
    discard_lexeme();
    t->tag = current_lexeme.u.op;
    break;
  case IDENTIFIER:
    discard_lexeme();
    t->tag = Identifier;
    t->u.s = current_lexeme.u.s;
    break;
  case BINDER:
    discard_lexeme();
    t->tag = Binder;
    t->u.s = current_lexeme.u.s;
    break;
  case BOOLEAN:
    discard_lexeme();
    t->tag = Boolean;
    t->u.i = current_lexeme.u.i;
    break;
  case INTEGER:
    discard_lexeme();
    t->tag = Integer;
    t->u.i = current_lexeme.u.i;
    break;
  case REAL:
    discard_lexeme();
    t->tag = Real;
    t->u.d = current_lexeme.u.d;
    break;
  case STRING:
    discard_lexeme();
    t->tag = String;
    t->u.s = current_lexeme.u.s;
    break;
  case LBRACE:
    discard_lexeme();
    t->tag = Function;
    t->u.a = parse_tokenlist();
    get_lexeme();
    if (current_lexeme.kind != RBRACE) {
      fprintf(stderr, "} expected\n");
      exit(2);
    }
    discard_lexeme();
    break;
  case LBRACKET:
    discard_lexeme();
    t->tag = Array;
    t->u.a = parse_tokenlist();
    get_lexeme();
    if (current_lexeme.kind != RBRACKET) {
      fprintf(stderr, "] expected\n");
      exit(2);
    }
    discard_lexeme();
    break;
  default:
    return 0;
  }
  return 1;
}

static struct array * parse_tokenlist(void)
{
  struct array * a = alloc_array(sizeof(struct tok), 10);
  struct tok t;
  int i = 0;
  while (parse_token(&t)) {
    extend_array(struct tok, a);
    set_array(struct tok, a, i, t);
    i++;
  }
  return a;
}

struct array * parse_program(void)
{
  struct array * a = parse_tokenlist();
  get_lexeme();
  if (current_lexeme.kind != END_OF_FILE) {
    fprintf(stderr, "syntax error at end of program\n");
    exit(2);
  }
  return a;
}

  
