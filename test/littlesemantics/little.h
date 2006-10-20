#include <stdio.h>
#include <string.h>

typedef struct term {
  short select;
  union {
    struct term **children;
    int int_val;
    char *string_val;
  } term_body;
} term;

term *true();
term *false();
term *numeral(int i);
term *variable(char *s);
char *variable_name(term *t);
int numeral_value(term *t);
term *variable_list(term *i1, term *i2);
term *greater(term *i1, term *i2);
term *addition(term *i1, term *i2);
term *skip();
term *assignment(term *i1, term *i2);
term *sequence(term *i1, term *i2);
term *term_while(term *i1, term *i2);
term *variable_value(term *i1, term *i2);

term *child(term *t, int rank);
term *lookup(term *env, char *var);
term *update(term *env, char *var_name, term *val);
term *evaluate(term *env, term *exp);
term *execute(term *env, term *inst);
