#pragma once
#include <math.h>
#include <stdio.h>

#include <ctime>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <vector>

struct Solver {
  /*Data structures & typedefs*/

  // Literal bool true,false & undef
  const int l_True = 0;
  const int l_False = 1;
  const int l_Undef = 2;

  // Varible
  const int var_Undef = -1;

  /*Data Structures*/

  /*LITERAL BEGIN*/
  /*
     x=2*t represents  [t]
     x=2*t+1 represents  [!t]
     ~l-> (t to !t)
  */
  struct Lit {
    int x;
    Lit() { x = 0; }
    Lit(int x) : x(x) {}
    inline bool operator==(Lit p) const { return x == p.x; }
    inline bool operator!=(Lit p) const { return x != p.x; }
  };

  // make a literal using VARIBLE & ITS int vaule
  //  var + l_True or l_False
  inline Lit mkLit(int var, bool sign) {
    Lit p(var + var + sign);
    return p;
  };

  // default literal value
  const Lit lit_Undef = {-2};
  /*LITERAL END*/

  /*WATCHER BEGIN*/
  /*
      using 2-literal watching algorithm
  */
  struct Watcher {
    int cref; // Clause id
    Lit blocker;
    Watcher() {}
    Watcher(int cr, Lit p) : cref(cr), blocker(p) {}
    bool operator==(const Watcher &w) const { return cref == w.cref; }
    bool operator!=(const Watcher &w) const { return cref != w.cref; }
  };
  /*WATCHER END*/

  /*CLAUSE BEGIN*/
  struct Clause {
    int size;
    std::vector<Lit> data;
    Clause() {}
    Clause(const std::vector<Lit> &ps, bool learnt) {
      size = ps.size();
      data.resize(size);
      for (int i = 0; i < ps.size(); i++) {
        data[i] = ps[i];
      }
    }
    Lit &operator[](int i) { return data[i]; }
    Lit operator[](int i) const { return data[i]; }
  };

  // Add clause
  int allocClause(std::vector<Lit> &ps, bool learnt = false) {
    ca.emplace_back(Clause(ps, learnt));
    return ca.size() - 1;
  }

  // Add new VARIBLE and alloc memory
  int newVar(bool sign = true, bool dvar = true) {
    int v = varNumbers();

    assigns.emplace_back(l_Undef);
    vardata.emplace_back(std::make_pair(-1, 0));
    activity.emplace_back(0.0);
    vis.push_back(false);
    polarity.push_back(sign);
    order_set.emplace(std::make_pair(0.0, v));
    return v;
  }

  bool addClause_(std::vector<Lit> &ps) {
    // empty clause
    if (ps.size() == 0) {
      return false;
    } else if (ps.size() == 1) {
      unitEnque(ps[0]);
    } else {
      int cr = allocClause(ps, false);
      attachClause(cr);
    }

    return true;
  }

  // Add watches
  void attachClause(int cr) {
    const Clause &c = ca[cr];
    watches[c[0].x ^ 1].emplace_back(Watcher(cr, c[1]));
    watches[c[1].x ^ 1].emplace_back(Watcher(cr, c[0]));
  }

  // Input
  void readClause(const std::string &line, std::vector<Lit> &lits) {
    lits.clear();
    int parsed_lit, var;
    parsed_lit = var = 0;
    bool neg = false;
    std::stringstream ss(line);
    while (ss) {
      int val;
      ss >> val;
      if (val == 0)
        break;
      var = abs(val) - 1;
      while (var >= varNumbers()) {
        newVar();
      }
      lits.emplace_back(val > 0 ? mkLit(var, l_True) : mkLit(var, l_False));
    }
  }

  std::vector<Clause> ca;
  // store clauses

  std::vector<std::vector<Watcher>> watches;
  // watches[i] storage  : when literal i stands , clauses which will be affects

  /*VARDATA BEGIN*/
  // In CDCL algorithm
  // how we get this varible : reason
  // data level in inplication graph
  /*VARDATA END*/
  std::vector<std::pair<int, int>>
      vardata;                // store reason and level for each variable
  std::vector<bool> polarity; // The preferred polarity of each variable
  std::vector<bool> vis;

  // storage decision levels
  int qhead; // current implicationGraph position
  std::vector<Lit> implicationGraph;
  std::vector<int> iGEveryLevel;
  // return current level
  int decisionLevel() const { return iGEveryLevel.size(); }
  // build a new level
  void newDecisionLevel() {
    iGEveryLevel.emplace_back(implicationGraph.size());
  }

  // an ordered set to storage every varible and its value
  // bigger value means more possibility to cause conflict
  // so we choose it first
  std::set<std::pair<double, int>> order_set;
  // varible's activitity
  std::vector<double> activity;
  // varible value by level
  double var_inc;
  int varNumbers() const { return vardata.size(); }

  inline int level(int x) const { return vardata[x].second; }

  inline void increaseVarActivity(int v) {
    std::pair<double, int> p = std::make_pair(activity[v], v);
    activity[v] += var_inc;
    if (order_set.erase(p) == 1) {
      order_set.emplace(std::make_pair(activity[v], v));
    }

    if (activity[v] > 1e50) {
      // Rescale
      std::set<std::pair<double, int>> tmp_order;
      tmp_order = std::move(order_set);
      order_set.clear();
      for (int i = 0; i < varNumbers(); i++) {
        activity[i] *= 1e-50;
      }
      for (auto &val : tmp_order) {
        order_set.emplace(std::make_pair(activity[val.second], val.second));
      }
      var_inc *= 1e-50;
    }
  }
  inline int value(int p) const { return assigns[p]; }
  int value(Lit p) const {
    if (assigns[(p.x >> 1)] == l_Undef) {
      return l_Undef;
    }
    return assigns[(p.x >> 1)] ^ (p.x & 1);
  }
  // add unit var to queue
  void unitEnque(Lit p, int from = -1) {
    assigns[(p.x >> 1)] = (p.x & 1);
    vardata[(p.x >> 1)] = std::move(std::make_pair(from, decisionLevel()));
    implicationGraph.emplace_back(p);
  }
  // decision
  Lit pickBranchLit() {
    int next = var_Undef;
    while (next == var_Undef || value(next) != l_Undef) {
      if (order_set.empty()) {
        next = var_Undef;
        break;
      } else {
        auto p = *order_set.rbegin();
        next = p.second;
        order_set.erase(p);
      }
    }
    return next == var_Undef ? lit_Undef : mkLit(next, polarity[next]);
  }
  // using cdcl algorithm, studying a new clause
  void cdclAnalyze(int confl, std::vector<Lit> &out_learnt, int &out_btlevel) {
    int pathC = 0;
    Lit p = lit_Undef;
    int index = implicationGraph.size() - 1;
    out_learnt.emplace_back(mkLit(0, l_True));
    do {
      Clause &c = ca[confl];
      for (int j = (p == lit_Undef) ? 0 : 1; j < c.size; j++) {
        Lit q = c[j];
        if (!vis[(q.x >> 1)] && level((q.x >> 1)) > 0) {
          increaseVarActivity((q.x >> 1));
          vis[(q.x >> 1)] = 1;
          if (level((q.x >> 1)) >= decisionLevel()) {
            pathC++;
          } else {
            out_learnt.emplace_back(q);
          }
        }
      }
      while (!vis[(implicationGraph[index--].x >> 1)])
        ;
      p = implicationGraph[index + 1];
      confl = vardata[(p.x >> 1)].first; // backtrack to father
      vis[(p.x >> 1)] = 0;
      pathC--;
    } while (pathC > 0);

    out_learnt[0] = Lit(p.x ^ 1);

    // unit clause
    if (out_learnt.size() == 1) {
      out_btlevel = 0;
    } else {
      // get deepest level to bktrack
      int max_i = 1;
      for (int i = 2; i < out_learnt.size(); i++) {
        if (level((out_learnt[i].x >> 1)) > level((out_learnt[max_i].x >> 1))) {
          max_i = i;
        }
      }

      Lit p = out_learnt[max_i];
      out_learnt[max_i] = out_learnt[1];
      out_learnt[1] = p;
      out_btlevel = level((p.x >> 1));
    }

    for (int i = 0; i < out_learnt.size(); i++) {
      vis[(out_learnt[i].x >> 1)] = false;
    }
  }

  // backtrack
  void backTo(int level, int flag = 0) {
    if (decisionLevel() > level) {
      for (int c = implicationGraph.size() - 1; c >= iGEveryLevel[level]; c--) {
        int x = (implicationGraph[c].x >> 1);
        assigns[x] = l_Undef;
        // phase saving algorithm
        polarity[x] = (implicationGraph[c].x & 1) ^ flag;
        order_set.emplace(std::make_pair(activity[x], x));
      }
      qhead = iGEveryLevel[level];
      implicationGraph.erase(implicationGraph.end() - (implicationGraph.size() -
                                                       iGEveryLevel[level]),
                             implicationGraph.end());
      iGEveryLevel.erase(iGEveryLevel.end() - (iGEveryLevel.size() - level),
                         iGEveryLevel.end());
    }
  }

  // retrun clauses that causes conflict
  // no conflicts -> -1
  int BCP() {
    int confl = -1;
    while (qhead < implicationGraph.size()) {
      Lit p = implicationGraph[qhead++]; // p is enqueued fact to BCP.
      std::vector<Watcher> &ws = watches[p.x];
      // watched clauses will be affects by p
      std::vector<Watcher>::iterator i, j, end;
      // 2-literal watching
      for (i = j = ws.begin(), end = i + ws.size(); i != end;) {
        Lit blocker = i->blocker;
        if (value(blocker) == l_True) {
          *j++ = *i++;
          continue;
        }

        int cr = i->cref;
        Clause &c = ca[cr];
        Lit false_lit = Lit(p.x ^ 1);
        if (c[0] == false_lit)
          c[0] = c[1], c[1] = false_lit;
        i++;

        Lit first = c[0];
        Watcher w = Watcher(cr, first);
        if (first != blocker && value(first) == l_True) {
          *j++ = w;
          continue;
        }

        // Look for new watch:
        for (int k = 2; k < c.size; k++)
          if (value(c[k]) != l_False) {
            c[1] = c[k];
            c[k] = false_lit;
            watches[c[1].x ^ 1].emplace_back(w);
            goto NextClause;
          }
        *j++ = w;
        if (value(first) == l_False) { // conflict
          confl = cr;
          qhead = implicationGraph.size();
          while (i < end)
            *j++ = *i++;
        } else {
          unitEnque(first, cr);
        }
      NextClause:;
      }
      int size = i - j;
      ws.erase(ws.end() - size, ws.end());
    }
    return confl;
  }

  // luby sequence
  static double luby(double y, int x) {
    // Find the finite subsequence that contains index 'x', and the size of that
    // subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x + 1; seq++, size = 2 * size + 1)
      ;

    while (size - 1 != x) {
      size = (size - 1) >> 1;
      seq--;
      x = x % size;
    }
    return pow(y, seq);
  }

  // DPLL main solver
  // flag = CDCL
  int search(int conflictsLimit, int flag = true) {
    int backtrack_level;
    std::vector<Lit> learnt_clause;
    int conflictC = 0;
    while (true) {
      int confl = BCP();

      if (confl != -1) {
        // CONFLICT
        conflictC++;
        if (decisionLevel() == 0)
          return l_False;
        if (flag == true) { // using CDCL
          learnt_clause.clear();
          cdclAnalyze(confl, learnt_clause, backtrack_level);
          backTo(backtrack_level);
          if (learnt_clause.size() == 1) {
            unitEnque(learnt_clause[0]);
          } else {
            int cr = allocClause(learnt_clause, true);
            attachClause(cr);
            unitEnque(learnt_clause[0], cr);
          }
        } else {
          Clause &c = ca[confl];
          for (int j = 0; j < c.size; j++) {
            Lit q = c[j];
            if (level((q.x >> 1)) > 0) {
              increaseVarActivity((q.x >> 1));
            }
          }
          backTo(decisionLevel() - 1, 1);
        }
        // varDecay
        var_inc *= 1.05;
      } else {
        // NO CONFLICT
        if ((conflictsLimit >= 0 && conflictC >= conflictsLimit)) {
          backTo(0);
          return l_Undef;
        }
        Lit next = pickBranchLit();
        if (next == lit_Undef) {
          return l_True;
        }
        newDecisionLevel();
        unitEnque(next);
      }
    }
  };

  std::vector<int> assigns; // The current assignments
                            // 0 represents literal is true
                            // 1 represents literal is false

  int answer; // final answer SATISFIABLE 0 UNSATISFIABLE 1 UNKNOWN 2
  int resolveCNF(std::string problem_name) {
    std::vector<Lit> lits;
    int vars = 0;
    int clauses = 0;
    std::string line;
    std::ifstream ifs(problem_name, std::ios_base::in);
    if (!ifs.good()) {
      ifs.close();
      return false;
    }
    while (ifs.good()) {
      getline(ifs, line);
      if (line.size() > 0) {
        if (line[0] == 'p') {
          sscanf(line.c_str(), "p cnf %d %d", &vars, &clauses);
        } else if (line[0] == 'c' || line[0] == 'p') {
          continue;
        } else {
          readClause(line, lits);
          if (lits.size() > 0)
            addClause_(lits);
        }
      }
    }
    ifs.close();
    return true;
  }

  clock_t st;
  void start() { st = clock(); }

  // main Solver
  int solve(int para = 1) {
    start();
    int status;
    if (para == 0) { // CDCL
      qhead = 0;
      status = l_Undef;
      answer = l_Undef;
      var_inc = 1.01;
      status = search(-1);
    } else { // CDCL && luby restart
      qhead = 0;
      status = l_Undef;
      answer = l_Undef;
      var_inc = 1.01;
      int curr_restarts = 0;
      double restart_inc = 2;
      double restart_first = 100;
      while (status == l_Undef) {
        double rest_base = luby(restart_inc, curr_restarts);
        // using luby restart
        status = search(rest_base * restart_first);
        curr_restarts++;
      }
    }
    answer = status;
    if (answer != 100) {
      printf("Time: %.6fs\n", ((double)(clock() - st)) / CLOCKS_PER_SEC);
    } else {
      printf("Time Out\n");
    }
    return status;
  };
  // add one clause
  void addClause(std::vector<int> &clause) {
    std::vector<Lit> lits;
    lits.resize(clause.size());
    for (int i = 0; i < clause.size(); i++) {
      int var = abs(clause[i]) - 1;
      while (var >= varNumbers())
        newVar();
      lits[i] =
          std::move((clause[i] > 0 ? mkLit(var, l_True) : mkLit(var, l_False)));
    }
    addClause_(lits);
  }
  // Output
  void printAnswer() {
    if (answer == 100) {
      puts("Time Out");
    } else if (answer == 0) {
      puts("SAT");
      for (int i = 0; i < assigns.size(); i++) {
        if (assigns[i] == 0) {
          printf("%d ", i + 1);
        } else {
          printf("%d ", -(i + 1));
        }
      }
      puts("0");
    } else {
      puts("UNSAT");
    }
  }
  // Return Answer to sudoku
  std::vector<int> printAnswerToSudoku() {
    std::vector<int> vec;
    if (answer == 100) {
      puts("Time Out");
    } else if (answer == 0) {
      for (int i = 0; i < assigns.size(); i++) {
        if (assigns[i] == 0) {
          vec.emplace_back(i + 1);
        } else {
          vec.emplace_back(-(i + 1));
        }
      }
      puts("0");
    } else {
      puts("UNSAT");
    }
    return vec;
  }
  // Output to file
  void printAnswerToFile(char *filename) {
    FILE *fp = fopen(filename, "w+");
    if (answer == 0) {
      fprintf(fp, "SAT\n");
      for (int i = 0; i < assigns.size(); i++) {
        if (assigns[i] == 0) {
          fprintf(fp, "%d ", i + 1);
        } else {
          fprintf(fp, "%d ", -(i + 1));
        }
      }
      fprintf(fp, "0\n");
    } else {
      fprintf(fp, "UNSAT\n");
    }
    fclose(fp);
  }
  void showClauses() {
    for (auto ww : ca) {
      for (auto y : ww.data) {
        printf("%d ", (y.x >> 1) * (y.x & 1 ? -1 : 1));
      }
      puts("");
    }
  }
  Solver() {
    qhead = 0;
    watches.resize(1000010);
  }
};
