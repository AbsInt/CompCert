%{
 open List;;
 open Little;;
%}
%token T_VARIABLES T_IN T_END T_WHILE T_DO T_DONE T_ASSIGN T_PLUS
%token T_SCOLUMN T_OPEN T_CLOSE T_OPEN_B T_CLOSE_B T_SKIP T_GT
%token <int> NUM
%token <string> ID
%left T_PLUS
%right T_SCOLUMN
%type <unit> main
%type <Little.inst> inst
%start main
%type <int> num
%type <string> identifier
%%
main : T_VARIABLES environment T_IN inst T_END
{ (print_env(execute(rev $2) $4); exit(0)) }
;
num : NUM { $1 }
;
identifier : ID { $1 }
;
variable_value : identifier num { ($1, $2) }
;
environment : { [] }
| environment variable_value { $2::$1 }
;
inst: identifier T_ASSIGN exp { Assignment($1,$3) }
|  inst T_SCOLUMN inst { Sequence($1,$3) }
|  T_WHILE b_exp T_DO inst T_DONE { While($2,$4) }
|  T_SKIP { Skip }
|  T_OPEN_B inst T_CLOSE_B { $2 }
;
exp: num { Numeral($1) }
|    identifier { Variable($1) }
|    exp T_PLUS exp { Addition($1, $3); }
|    T_OPEN exp T_CLOSE { $2 }
;
b_exp: exp T_GT exp { Greater($1, $3) }
;
%%
