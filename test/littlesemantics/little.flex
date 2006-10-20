%option noyywrap
%{
#include <string.h>
#include "little.tab.h"
extern char* lextext;
extern int lexnum;
%}


DIGIT [0-9]
ID    [A-Za-z_][A-Za-z_0-9]*

%%

-?{DIGIT}+ { lexnum = atoi(yytext); return NUM; }
"while" { return T_WHILE; }
"do"    { return T_DO; }
"done"  { return T_DONE; }
"end"   { return T_END; }
"in"    { return T_IN; }
"skip"  { return T_SKIP; }
"variables" {return T_VARIABLES; }
":="    {return T_ASSIGN; }
">"     {return T_GT; }
";"     {return T_SCOLUMN;}
"+"     {return T_PLUS;}
"("     {return T_OPEN;}
")"     {return T_CLOSE;}
"{"     {return T_OPEN_B;}
"}"     {return T_CLOSE_B;}
[ \t\n]
{ID} { if(!(lextext =(char*)malloc(yyleng*sizeof(char)))) {
    printf("failed memory allocation for variable %s", yytext);
    exit(-1);
  }
  memcpy(lextext, yytext, yyleng);
  return(ID);
}

%%

