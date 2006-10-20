#include "string.h"
#include "stdio.h"

#define VARIABLE_LIST 1
#define VARIABLE_VALUE 2
#define VARIABLE 3
#define NUMERAL 4
#define ADDITION 5
#define GREATER 6
#define ASSIGNMENT 7
#define SEQUENCE 8
#define WHILE 9
#define SKIP 10

typedef struct term {
  short select;
  union {
    struct term **children;
    int int_val;
    char *string_val;
  } term_body;
} term;

void panic(char *s) {
  /*fprintf(stderr, "%s\n", s);*/
       printf( "%s\n", s);
  exit(-1);
}

term *make_term(int tag) {
  term *ptr;

  if(!(ptr = (term *)malloc(sizeof(term)))) {
    panic("allocation failed in make_term");
  }
  ptr->select = tag;
  return ptr;
}

term *make_binary_term(int tag, term *i1, term *i2) {
  term *ptr = make_term(tag);
  if(!(ptr->term_body.children
           = (term **)malloc(sizeof(term*)*2))) {
    panic("could not allocate memory in make_binary_term");
  }
  ptr->term_body.children[0] = i1;
  ptr->term_body.children[1] = i2;
  return ptr;
}

term *variable(char *s) {
  term *ptr = make_term(VARIABLE);
  ptr->term_body.string_val = s;
  return ptr;
}

term *numeral(int i) {
  term *ptr = make_term(NUMERAL);
  ptr->term_body.int_val = i;
  return ptr;
}

term *addition(term *i1, term *i2) {
  return make_binary_term(ADDITION, i1, i2);
}

term *variable_list(term *i1, term *i2) {
  return make_binary_term(VARIABLE_LIST, i1, i2);
}

term *variable_value(term *i1, term *i2) {
  return make_binary_term(VARIABLE_VALUE, i1, i2);
}

term *greater(term *i1, term *i2) {
  return make_binary_term(GREATER, i1, i2);
}

term *assignment(term *i1, term *i2) {
  return make_binary_term(ASSIGNMENT, i1, i2);
}

term *sequence(term *i1, term *i2) {
  return make_binary_term(SEQUENCE, i1, i2);
}

term *term_while(term *i1, term *i2) {
  return make_binary_term(WHILE, i1, i2);
}

term *skip() {
  return make_term(SKIP);
}

char *variable_name(term *v) {
  return (v->term_body.string_val);
}

int numeral_value(term *t) {
  return(t->term_body.int_val);
}

term *child(term *t, int rank) {
  return (t->term_body.children[rank-1]);
}

int lookup(term *env, char *var) {
  while(NULL != env) {
    term *pair = child(env, 1);
    if(strcmp(variable_name(child(pair, 1)), var)==0) {
      return numeral_value(child(pair, 2));
    } else {
      env = child(env, 2);
    }
  }
  /*  fprintf(stderr, "%s : ", var);*/
  printf( "%s : ", var);
  panic("no such variable in environment for lookup");
}

term *update(term *env, char *var_name, term *val) {
  if(NULL != env) {
    term *var = child(child(env, 1), 1);
    if(strcmp(variable_name(var), var_name) == 0) {
      return(variable_list(variable_value(var, val),
                           child(env, 2)));
    } else {
      return(variable_list(child(env, 1),
                           update(child(env, 2), var_name, val)));
    }
  } else {
    /*fprintf(stderr, "%s : ", var_name);*/
printf( "%s : ", var_name);
    panic("no such variable in environment for update");
  }
}

int evaluate(term *env, term *exp) {
  int n1, n2;
  switch(exp->select) {
  case VARIABLE: return lookup(env, variable_name(exp));
  case NUMERAL: return numeral_value(exp);
  case ADDITION:
    return (evaluate(env, child(exp, 1)) +
            evaluate(env, child(exp, 2)));
  }
}

int evaluate_bool(term *env, term *exp) {
  int n1 = evaluate(env, child(exp, 1));
  int n2 = evaluate(env, child(exp, 2));
  return (n1 > n2);
}

term *execute(term *env, term *inst) {
  switch(inst->select) {
  case ASSIGNMENT:
    return update(env,
                  variable_name(child(inst, 1)),
                  numeral(evaluate(env,child(inst, 2))));
  case SEQUENCE:
    return execute(execute(env,child(inst, 1)),child(inst, 2));
  case WHILE:
    if(evaluate_bool(env,child(inst, 1))) {
      return execute(execute(env,child(inst, 2)), inst);
    } else {
      return env;
    }
  }
}

void print_env(term *env) {

  while(env != NULL) {
    printf("%s : %d\n", variable_name(child(child(env,1),1)),
	   numeral_value(child(child(env,1),2)));
    env = child(env, 2);
    }
}


