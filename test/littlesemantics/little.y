%{
#include <stdio.h>
#include <string.h>
#include "little.h"
#define YYSTYPE term *

  char *lextext;
  int lexnum;

  term *revert_env(term *t) {
    term *r = NULL, *t1;
    while(NULL != t) {
      t1 = r;
      r = t;
      t = child(t,2);
      r->term_body.children[1] = t1;
    }
    return r;
  }

  void yyerror(char const *s) {
    fprintf(stderr, "%s\n", s);
  }
%}

%token T_VARIABLES T_IN T_END T_WHILE T_DO T_DONE T_GT
%token T_ASSIGN T_PLUS T_SCOLUMN T_OPEN T_CLOSE T_OPEN_B T_CLOSE_B
%token T_SKIP NUM ID 
%left T_PLUS
%right T_SCOLUMN
%%
program : T_VARIABLES environment T_IN inst T_END
{ print_env(execute(revert_env($2),$4)); exit(0) }
;
b_exp: exp T_GT exp {$$=greater($1, $3); }
;
num : NUM { $$=numeral(lexnum); }
;
identifier : ID { $$=variable(lextext); }
;
variable_value : identifier num { $$=variable_value($1,$2);}
;
environment : variable_value { $$ = variable_list($1, NULL); }
| environment T_SCOLUMN variable_value { $$ = variable_list($3, $1);
   printf ("foo\n"); }
;
inst: identifier T_ASSIGN exp {$$ = assignment($1,$3); }
|  inst T_SCOLUMN inst {$$ = sequence($1,$3); }
|  T_WHILE b_exp T_DO inst T_DONE {$$ = term_while($2,$4); } 
|  T_SKIP { $$ = skip(); }
|  T_OPEN_B exp T_CLOSE_B { $$ = $2; }
;
exp: num {$$= $1;}
|    identifier {$$=$1; }
|    exp T_PLUS exp {$$=addition($1, $3); }
|    T_OPEN exp T_CLOSE { $$= $2; }
;
%%

main(int argc, char **argv) {
  yyparse();
}
