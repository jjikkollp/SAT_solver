#include <string.h>

#include "sat.hpp"
#include "sudoku.hpp"

char s[10010];
int main(int argc, char *argv[]) {
  sudoku *test = new sudoku(8);
  test->gen(30);
  test->show();
}
