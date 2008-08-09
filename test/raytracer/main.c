#include "config.h"
#include "arrays.h"
#include "gmllexer.h"
#include "gmlparser.h"
#include "eval.h"

int main(int argc, char ** argv)
{
  arena_init();
  init_lexer();
  execute_program(parse_program());
  return 0;
}
