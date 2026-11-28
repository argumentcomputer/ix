// Intrusive-RC recycling C++ sibling of `nqueens` (Perceus/IxCC RC control).
// Uses single-threaded non-atomic intrusive reference counting with in-place
// unique-cell reuse and deterministic deallocation of all dead sub-solutions.
// `upstream/nqueens.cpp` (which intentionally leaks memory) is kept unmodified.
#include <cstdint>
#include <cstdlib>
#include <iostream>

struct IntNode {
  uint32_t rc;
  int head;
  IntNode* tail;
};

struct SolNode {
  uint32_t rc;
  IntNode* head;
  SolNode* tail;
};

#ifdef RC_DEBUG_CHECK
static int64_t g_live_int = 0;
static int64_t g_live_sol = 0;
#endif

static inline IntNode* alloc_int(int hd, IntNode* tl) {
#ifdef RC_DEBUG_CHECK
  ++g_live_int;
#endif
  return new IntNode{1, hd, tl};
}

static inline void free_int(IntNode* p) {
#ifdef RC_DEBUG_CHECK
  --g_live_int;
#endif
  delete p;
}

static inline SolNode* alloc_sol(IntNode* hd, SolNode* tl, SolNode* reuse = nullptr) {
  if (reuse != nullptr) {
    reuse->rc = 1;
    reuse->head = hd;
    reuse->tail = tl;
    return reuse;
  }
#ifdef RC_DEBUG_CHECK
  ++g_live_sol;
#endif
  return new SolNode{1, hd, tl};
}

static inline void free_sol(SolNode* p) {
#ifdef RC_DEBUG_CHECK
  --g_live_sol;
#endif
  delete p;
}

static inline IntNode* inc_int(IntNode* p) {
  if (p != nullptr) ++p->rc;
  return p;
}

static inline void dec_int(IntNode* p) {
  while (p != nullptr) {
    if (p->rc > 1) {
      --p->rc;
      return;
    }
    IntNode* next = p->tail;
    free_int(p);
    p = next;
  }
}

static inline void dec_sol(SolNode* p) {
  while (p != nullptr) {
    if (p->rc > 1) {
      --p->rc;
      return;
    }
    IntNode* hd = p->head;
    SolNode* next = p->tail;
    free_sol(p);
    dec_int(hd);
    p = next;
  }
}

static int len(const SolNode* xs) {
  int n = 0;
  while (xs != nullptr) {
    ++n;
    xs = xs->tail;
  }
  return n;
}

static bool safe(int queen, const IntNode* xs) {
  const IntNode* cur = xs;
  int diag = 1;
  while (cur != nullptr) {
    int q = cur->head;
    if (queen == q || queen == (q + diag) || queen == (q - diag)) {
      return false;
    }
    ++diag;
    cur = cur->tail;
  }
  return true;
}

static SolNode* append_safe(int k, IntNode* soln, SolNode* solns, SolNode* reuse) {
  SolNode* acc = solns;
  int n = k;
  while (n > 0) {
    if (safe(n, soln)) {
      acc = alloc_sol(alloc_int(n, inc_int(soln)), acc, reuse);
      reuse = nullptr;
    }
    --n;
  }
  if (reuse != nullptr) free_sol(reuse);
  return acc;
}

static SolNode* extend(int n, SolNode* solns) {
  SolNode* acc = nullptr;
  SolNode* cur = solns;
  while (cur != nullptr) {
    IntNode* soln = cur->head;
    SolNode* next = cur->tail;
    SolNode* reuse = nullptr;
    if (cur->rc == 1) {
      reuse = cur;
    } else {
      inc_int(soln);
      if (next != nullptr) ++next->rc;
      --cur->rc;
    }
    acc = append_safe(n, soln, acc, reuse);
    dec_int(soln);
    cur = next;
  }
  return acc;
}

static SolNode* find_solutions(int n) {
  int k = 0;
  SolNode* acc = alloc_sol(nullptr, nullptr);
  while (k < n) {
    acc = extend(n, acc);
    ++k;
  }
  return acc;
}

static int nqueens(int n) {
  SolNode* solns = find_solutions(n);
  int count = len(solns);
  dec_sol(solns);
  return count;
}

int main(int argc, char** argv) {
  int n = 13;
  if (argc == 2) {
    n = std::atoi(argv[1]);
  }
  std::cout << nqueens(n) << "\n";
#ifdef RC_DEBUG_CHECK
  if (g_live_int != 0 || g_live_sol != 0) {
    std::cerr << "LEAK DETECTED: live_int=" << g_live_int
              << " live_sol=" << g_live_sol << "\n";
    return 99;
  }
#endif
  return 0;
}
