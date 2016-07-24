/* Lexer for GML */

#include "config.h"
#include <ctype.h>
#include "gmllexer.h"
#include "gml.h"

struct lexeme current_lexeme;

struct bucket {
  int kind;
  struct bucket * next;
  int op;
  char string[1];
};

#define HASHTABLE_SIZE 256

static struct bucket * hashtable[HASHTABLE_SIZE] = { NULL, /*all nulls*/};

#define BUFFER_SIZE 1024

static char buffer[BUFFER_SIZE];

#define STORE_BUFFER(pos,c) if (pos < sizeof(buffer) - 1) buffer[pos++] = c

static inline unsigned int hash_ident(char * s)
{
  unsigned int h;
  for (h = 0; *s != 0; s++) h = (h << 4) + h + *s;
  return h % HASHTABLE_SIZE;
}

static void get_ident(int firstchar)
{
  int c, pos;
  unsigned int h;
  struct bucket * b;

  /* Read characters of the ident */
  buffer[0] = firstchar;
  pos = 1;
  while (1) {
    c = getchar();
    if (! (isalnum(c) || c == '-' || c == '_')) break;
    STORE_BUFFER(pos, c);
  }
  if (c != EOF) ungetc(c, stdin);
  buffer[pos] = 0;
  /* Hash the ident */
  h = hash_ident(buffer);
  /* Look it up in the hash table */
  for (b = hashtable[h]; b != NULL; b = b->next) {
    if (strcmp(b->string, buffer) == 0) {
      /* Found: return hash table entry */
      current_lexeme.kind = b->kind;
      if (b->kind == IDENTIFIER)
        current_lexeme.u.s = b->string;
      else
        current_lexeme.u.op = b->op;
      return;
    }
  }
  /* Not found: enter it */
  b = malloc(sizeof(struct bucket) + pos);
  b->kind = IDENTIFIER;
  strcpy(b->string, buffer);
  b->next = hashtable[h];
  hashtable[h] = b;
  current_lexeme.kind = IDENTIFIER;
  current_lexeme.u.s = b->string;
}

static void get_binder(void)
{
  int c = getchar();
  if (! isalpha(c)) {
    fprintf(stderr, "Bad binder /%c...\n", c);
    exit(2);
  }
  get_ident(c);
  if (current_lexeme.kind != IDENTIFIER) {
    fprintf(stderr, "Binder /%s rebinds reserved identifier\n",
            current_lexeme.u.s);
    exit(2);
  }
  current_lexeme.kind = BINDER;
}

static void get_number(int firstchar)
{
  int c, pos, is_real;

  pos = 0;
  is_real = 0;
  c = firstchar;
  /* Initial sign */
  if (c == '-') {
    STORE_BUFFER(pos, c);
    c = getchar();
    if (! isdigit(c)) goto bad_number;
  }
  /* Decimal number */
  do {
    STORE_BUFFER(pos, c);
    c = getchar();
  } while (isdigit(c));
  /* Period and fractional part */
  if (c == '.') {
    is_real = 1;
    STORE_BUFFER(pos, c);
    c = getchar();
    if (! isdigit(c)) goto bad_number;
    do {
      STORE_BUFFER(pos, c);
      c = getchar();
    } while (isdigit(c));
  }
  /* Exponent */
  if (c == 'e' || c == 'E') {
    is_real = 1;
    STORE_BUFFER(pos, c);
    c = getchar();
    if (c == '-') {
      STORE_BUFFER(pos, c);
      c = getchar();
    }
    if (! isdigit(c)) goto bad_number;
    do {
      STORE_BUFFER(pos, c);
      c = getchar();
    } while (isdigit(c));
  }
  if (c != EOF) ungetc(c, stdin);
  /* Convert to token */
  buffer[pos] = 0;
  if (is_real) {
    current_lexeme.kind = REAL;
    current_lexeme.u.d = strtod(buffer, NULL);
  } else {
    current_lexeme.kind = INTEGER;
    current_lexeme.u.i = atoi(buffer);
  }
  return;
 bad_number:
  fprintf(stderr, "Illegal number\n");
  exit(2);
}

static char * my_strdup(char * s)
{
  size_t l = strlen(s);
  char * t = malloc(l + 1);
  if (t != NULL) memcpy(t, s, l + 1);
  return t;
}

static void get_string()
{
  int c, pos;
  pos = 0;
  while (1) {
    c = getchar();
    if (c == '"') break;
    if (! isprint(c)) goto bad_string;
    STORE_BUFFER(pos, c);
  }
  buffer[pos] = 0;
  current_lexeme.kind = STRING;
  current_lexeme.u.s = my_strdup(buffer);
  return;
 bad_string:
  fprintf(stderr, "Illegal string literal\n");
  exit(2);
}

void get_lexeme(void)
{
  int c;

  if (current_lexeme.kind != NONE) return;
 again:
  c = getchar();
  switch (c) {
  case EOF:
    current_lexeme.kind = END_OF_FILE; break;
  case ' ': case '\n': case '\t': case '\r': case 11:
    goto again;
  case '%':
    do { c = getchar(); } while (c != '\n' && c != EOF);
    goto again;
  case '/':
    get_binder(); break;
  case '-': case '0': case '1': case '2': case '3': case '4':
  case '5': case '6': case '7': case '8': case '9':
    get_number(c); break;
  case '"':
    get_string(); break;
  case '{':
    current_lexeme.kind = LBRACE; break;
  case '}':
    current_lexeme.kind = RBRACE; break;
  case '[':
    current_lexeme.kind = LBRACKET; break;
  case ']':
    current_lexeme.kind = RBRACKET; break;
  default:
    if (isalpha(c)) {
      get_ident(c);
    } else {
      fprintf(stderr, "Illegal character `%c'\n", c);
      exit(2);
    }
    break;
  }
}

void discard_lexeme(void)
{
  current_lexeme.kind = NONE;
}

/* Enter the operators in the hashtable */

struct op_init { char * name; int kind; int op; };

static struct op_init operators[] =
   { { "true", BOOLEAN, 1 },
     { "false", BOOLEAN, 0 },
     { "acos", OPERATOR, Op_acos },
     { "addi", OPERATOR, Op_addi },
     { "addf", OPERATOR, Op_addf },
     { "apply", OPERATOR, Op_apply },
     { "asin", OPERATOR, Op_asin },
     { "clampf", OPERATOR, Op_clampf },
     { "cone", OPERATOR, Op_cone },
     { "cos", OPERATOR, Op_cos },
     { "cube", OPERATOR, Op_cube },
     { "cylinder", OPERATOR, Op_cylinder },
     { "difference", OPERATOR, Op_difference },
     { "divi", OPERATOR, Op_divi },
     { "divf", OPERATOR, Op_divf },
     { "eqi", OPERATOR, Op_eqi },
     { "eqf", OPERATOR, Op_eqf },
     { "floor", OPERATOR, Op_floor },
     { "frac", OPERATOR, Op_frac },
     { "get", OPERATOR, Op_get },
     { "getx", OPERATOR, Op_getx },
     { "gety", OPERATOR, Op_gety },
     { "getz", OPERATOR, Op_getz },
     { "if", OPERATOR, Op_if },
     { "intersect", OPERATOR, Op_intersect },
     { "length", OPERATOR, Op_length },
     { "lessi", OPERATOR, Op_lessi },
     { "lessf", OPERATOR, Op_lessf },
     { "light", OPERATOR, Op_light },
     { "modi", OPERATOR, Op_modi },
     { "muli", OPERATOR, Op_muli },
     { "mulf", OPERATOR, Op_mulf },
     { "negi", OPERATOR, Op_negi },
     { "negf", OPERATOR, Op_negf },
     { "plane", OPERATOR, Op_plane },
     { "point", OPERATOR, Op_point },
     { "pointlight", OPERATOR, Op_pointlight },
     { "real", OPERATOR, Op_real },
     { "render", OPERATOR, Op_render },
     { "rotatex", OPERATOR, Op_rotatex },
     { "rotatey", OPERATOR, Op_rotatey },
     { "rotatez", OPERATOR, Op_rotatez },
     { "scale", OPERATOR, Op_scale },
     { "sin", OPERATOR, Op_sin },
     { "sphere", OPERATOR, Op_sphere },
     { "spotlight", OPERATOR, Op_spotlight },
     { "sqrt", OPERATOR, Op_sqrt },
     { "subi", OPERATOR, Op_subi },
     { "subf", OPERATOR, Op_subf },
     { "translate", OPERATOR, Op_translate },
     { "union", OPERATOR, Op_union },
     { "uscale", OPERATOR, Op_uscale },
     { "print", OPERATOR, Op_print },
   };

void init_lexer(void)
{
  int i;
  for (i = 0; i < sizeof(operators) / sizeof(struct op_init); i++) {
    struct op_init * opi = &(operators[i]);
    struct bucket * b = malloc(sizeof(struct bucket) + strlen(opi->name));
    unsigned int h = hash_ident(opi->name);
    b->kind = opi->kind;
    strcpy(b->string, opi->name);
    b->op = opi->op;
    b->next = hashtable[h];
    hashtable[h] = b;
  }
}

