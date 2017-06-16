/* Lexer for GML */

struct lexeme {
  enum {
    NONE,
    OPERATOR, IDENTIFIER, BINDER, BOOLEAN, INTEGER, REAL, STRING,
    LBRACE, RBRACE, LBRACKET, RBRACKET, END_OF_FILE
  } kind;
  union {
    int op;                     /* for operators */
    char * s;                   /* for identifiers, binders, strings */
    int i;                      /* for integer and boolean literals */
    flt d;                      /* for float literals */
  } u;
};

extern struct lexeme current_lexeme;

extern void get_lexeme(void);
extern void discard_lexeme(void);
extern void init_lexer(void);
