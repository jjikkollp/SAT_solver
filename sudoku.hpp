#pragma once
#include "sat.hpp"
#include <cassert>
#include <random>
#include <vector>

struct sudoku {
  int n;
  int a[111][111], ok[111][111];
  Solver *sudoku_sat;
  sudoku(int n) : n(n) { assert(!(n & 1)); }
  inline int id(int x, int y) { return x * n + y + 1; }
  inline int getx(int id) { return (id - 1) / n; }
  inline int gety(int id) { return (id - 1) % n; }
  /*
      random fill n^2/6 blocks for sudoku
      @return void
  */
  void random_gener() {
    std::mt19937 generator(time(NULL));
    int cnt = 0;
    for (int i = 0; i < n; ++i) {
      for (int j = 0; j < n; ++j) {
        cnt += (ok[i][j] = ((generator() & 1) && (generator() & 1)));
        if (cnt > n * n / 6)
          ok[i][j] = 0;
      }
    }
    for (int i = 0; i < n; ++i) {
      for (int j = 0; j < n; ++j) {
        if (ok[i][j])
          a[i][j] = generator() & 1;
        else
          a[i][j] = -1;
      }
    }
  }
  /*
      convert sudoku to a SAT solver class
      @return void
  */
  void convert(Solver *cur) {
    // rule 0: unit literal
    for (int i = 0; i < n; ++i) {
      for (int j = 0; j < n; ++j) {
        if (a[i][j] == -1)
          continue;
        std::vector<int> tmp;
        if (a[i][j] == 1)
          tmp.emplace_back(id(i, j));
        else
          tmp.emplace_back(-id(i, j));
        cur->addClause(tmp);
      }
    }
    // rule 1: every 3
    for (int i = 0; i < n; ++i) {
      for (int j = 0; j < n; ++j) {
        std::vector<int> tmp, tmp2, tmp3, tmp4;
        // line 3
        if (j + 2 < n) {
          tmp.emplace_back(id(i, j));
          tmp.emplace_back(id(i, j + 1));
          tmp.emplace_back(id(i, j + 2));
          tmp2.emplace_back(-id(i, j));
          tmp2.emplace_back(-id(i, j + 1));
          tmp2.emplace_back(-id(i, j + 2));
        }
        // col 3
        if (i + 2 < n) {
          tmp3.emplace_back(id(i, j));
          tmp3.emplace_back(id(i + 1, j));
          tmp3.emplace_back(id(i + 2, j));
          tmp4.emplace_back(-id(i, j));
          tmp4.emplace_back(-id(i + 1, j));
          tmp4.emplace_back(-id(i + 2, j));
        }
        cur->addClause(tmp);
        cur->addClause(tmp2);
        cur->addClause(tmp3);
        cur->addClause(tmp4);
      }
    }
    // rule 2 : n/2 zero n/2 one
    // init bit-mask
    std::vector<int> bitMask;
    std::vector<int> bitMask2;
    for (int i = 0; i < (1 << n); ++i) {
      int fl = 1;
      for (int test = 7; test < (1 << n); test <<= 1) {
        if (i & test && ~i & test)
          continue;
        fl = 0;
      }
      if (!fl)
        continue;
      if (__builtin_popcount(i) == n / 2 + 1) {
        // fprintf(stderr,"%d\n",i);
        bitMask.emplace_back(i);
      } else if (__builtin_popcount(i) == n / 2) {
        bitMask2.emplace_back(i);
      }
    }
    for (int i = 0; i < n; ++i) {
      for (int x : bitMask) {
        std::vector<int> tmp, tmp2, tmp3, tmp4;
        for (int j = 0; j < n; ++j) {
          if (x & (1 << j)) {
            tmp.emplace_back(id(i, j));
            tmp2.emplace_back(-id(i, j));
            tmp3.emplace_back(id(j, i));
            tmp4.emplace_back(-id(j, i));
          }
        }
        cur->addClause(tmp);
        cur->addClause(tmp2);
        cur->addClause(tmp3);
        cur->addClause(tmp4);
      }
    }
    for (int i = 0; i < n; ++i) {
      for (int x : bitMask2) {
        for (int j = i + 1; j < n; ++j) {
          std::vector<int> tmp, tmp2;
          for (int k = 0; k < n; ++k) {
            int m = x >> k & 1;
            if (m) {
              tmp.emplace_back(id(i, k));
              tmp.emplace_back(id(j, k));
              tmp2.emplace_back(id(k, i));
              tmp2.emplace_back(id(k, j));
            } else {
              tmp.emplace_back(-id(i, k));
              tmp.emplace_back(-id(j, k));
              tmp2.emplace_back(-id(k, i));
              tmp2.emplace_back(-id(k, j));
            }
          }
          cur->addClause(tmp);
          cur->addClause(tmp2);
        }
      }
    }
    // cur->showClauses();
  }
  /*
      check if sudoku is solvable
      @return true if sudoku is solvable
  */
  bool validate(int isSave = 0) {
    Solver *cur = new Solver;

    convert(cur);
    // cur->showClauses();
    int flag = cur->solve();
    if (isSave)
      sudoku_sat = cur;
    else
      delete cur;
    return flag == 0;
  }
  /*
      gen a full sudoku
      @return void
  */
  void gen_full() {
    int ok = 0;
    while (!ok) {
      random_gener();
      ok = validate();
    }
    // show();
    validate(1);
    std::vector<int> ans = sudoku_sat->printAnswerToSudoku();
    for (auto x : ans) {
      // std::cerr<<"x="<<x<<std::endl;
      int id = abs(x);
      a[getx(id)][gety(id)] = (x > 0);
    }
    show();
  }
  /*
      gen a playable soduku by max_cnt = cnt of holes
      @return void
  */
  void gen(int max_cnt) {
    std::mt19937 generator(clock());
    gen_full();
    // delete
    int cntHole = 0, cntRandom = 0;
    while (cntHole <= max_cnt && cntRandom < 100) {
      int x = generator() % n, y = generator() % n;
      if (a[x][y] == -1) {
      } else {
        a[x][y] = !a[x][y];
        if (validate()) {
          a[x][y] = !a[x][y];
        } else {
          a[x][y] = -1;
          ++cntHole;
        }
      }
      ++cntRandom;
    }
  }
  /*
      output sudoku
      @return void
  */
  void show() {
    for (int i = 0; i < n; ++i) {
      for (int j = 0; j < n; ++j) {
        printf("%d ", a[i][j]);
      }
      printf("\n");
    }
  }
};