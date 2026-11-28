// Intrusive-RC recycling C++ sibling of `const_fold` (Perceus/IxCC RC control).
// Uses single-threaded non-atomic intrusive reference counting with Perceus-style
// in-place unique-cell reuse across all Expr constructors and iterative release.
// `cfold.cpp` (which intentionally leaks memory, as upstream) is kept unmodified.
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

enum Kind : uint32_t {
  Val = 0,
  Var = 1,
  Add = 2,
  Mul = 3,
};

struct Expr {
  uint32_t rc;
  Kind kind;
  union {
    long value;
    struct {
      Expr* left;
      Expr* right;
    } bin;
  };
};

#ifdef RC_DEBUG_CHECK
static int64_t g_live_expr = 0;
#endif

static inline Expr* alloc_expr(Expr* reuse = nullptr) {
  if (reuse != nullptr) return reuse;
#ifdef RC_DEBUG_CHECK
  ++g_live_expr;
#endif
  return new Expr;
}

static inline void free_expr(Expr* e) {
#ifdef RC_DEBUG_CHECK
  --g_live_expr;
#endif
  delete e;
}

static inline Expr* mk_val(long v, Expr* reuse = nullptr) {
  Expr* e = alloc_expr(reuse);
  e->rc = 1;
  e->kind = Val;
  e->value = v;
  return e;
}

static inline Expr* mk_var(long name, Expr* reuse = nullptr) {
  Expr* e = alloc_expr(reuse);
  e->rc = 1;
  e->kind = Var;
  e->value = name;
  return e;
}

static inline Expr* mk_bin(Kind k, Expr* l, Expr* r, Expr* reuse = nullptr) {
  Expr* e = alloc_expr(reuse);
  e->rc = 1;
  e->kind = k;
  e->bin.left = l;
  e->bin.right = r;
  return e;
}

static inline Expr* inc(Expr* e) {
  ++e->rc;
  return e;
}

static void dec(Expr* e) {
  std::vector<Expr*> work;
  while (e != nullptr) {
    if (e->rc > 1) {
      --e->rc;
      if (work.empty()) return;
      e = work.back();
      work.pop_back();
      continue;
    }
    if (e->kind == Add || e->kind == Mul) {
      Expr* l = e->bin.left;
      Expr* r = e->bin.right;
      free_expr(e);
      if (l->kind == Add || l->kind == Mul) {
        work.push_back(l);
      } else if (l->rc > 1) {
        --l->rc;
      } else {
        free_expr(l);
      }
      e = r;
    } else {
      free_expr(e);
      if (work.empty()) return;
      e = work.back();
      work.pop_back();
    }
  }
}

static Expr* mk_expr(long n, long v) {
  if (n == 0) {
    if (v == 0) return mk_var(1);
    else return mk_val(v);
  } else {
    return mk_bin(Add, mk_expr(n - 1, v + 1), mk_expr(n - 1, v == 0 ? 0 : v - 1));
  }
}

static Expr* append_add(Expr* e1, Expr* e2, Expr* reuse) {
  if (e1->kind == Add) {
    if (e1->rc == 1) {
      e1->bin.right = append_add(e1->bin.right, e2, reuse);
      return e1;
    } else {
      Expr* l = inc(e1->bin.left);
      Expr* r = inc(e1->bin.right);
      dec(e1);
      return mk_bin(Add, l, append_add(r, e2, nullptr), reuse);
    }
  } else {
    return mk_bin(Add, e1, e2, reuse);
  }
}

static Expr* append_mul(Expr* e1, Expr* e2, Expr* reuse) {
  if (e1->kind == Mul) {
    if (e1->rc == 1) {
      e1->bin.right = append_mul(e1->bin.right, e2, reuse);
      return e1;
    } else {
      Expr* l = inc(e1->bin.left);
      Expr* r = inc(e1->bin.right);
      dec(e1);
      return mk_bin(Mul, l, append_mul(r, e2, nullptr), reuse);
    }
  } else {
    return mk_bin(Mul, e1, e2, reuse);
  }
}

static Expr* reassoc(Expr* e) {
  if (e->kind == Add) {
    Expr* l;
    Expr* r;
    Expr* reuse = nullptr;
    if (e->rc == 1) {
      l = e->bin.left;
      r = e->bin.right;
      reuse = e;
    } else {
      l = inc(e->bin.left);
      r = inc(e->bin.right);
      dec(e);
    }
    return append_add(reassoc(l), reassoc(r), reuse);
  } else if (e->kind == Mul) {
    Expr* l;
    Expr* r;
    Expr* reuse = nullptr;
    if (e->rc == 1) {
      l = e->bin.left;
      r = e->bin.right;
      reuse = e;
    } else {
      l = inc(e->bin.left);
      r = inc(e->bin.right);
      dec(e);
    }
    return append_mul(reassoc(l), reassoc(r), reuse);
  } else {
    return e;
  }
}

static Expr* const_folding(Expr* e) {
  if (e->kind == Add || e->kind == Mul) {
    Kind k = e->kind;
    Expr* l;
    Expr* r;
    Expr* reuse = nullptr;
    if (e->rc == 1) {
      l = e->bin.left;
      r = e->bin.right;
      reuse = e;
    } else {
      l = inc(e->bin.left);
      r = inc(e->bin.right);
      dec(e);
    }
    Expr* e1 = const_folding(l);
    Expr* e2 = const_folding(r);
    if (e1->kind == Val && e2->kind == Val) {
      long res = (k == Add) ? (e1->value + e2->value) : (e1->value * e2->value);
      if (reuse != nullptr) {
        dec(e1);
        dec(e2);
        return mk_val(res, reuse);
      } else if (e1->rc == 1) {
        dec(e2);
        return mk_val(res, e1);
      } else if (e2->rc == 1) {
        dec(e1);
        return mk_val(res, e2);
      } else {
        dec(e1);
        dec(e2);
        return mk_val(res);
      }
    } else if (e1->kind == Val && e2->kind == k && e2->bin.right->kind == Val) {
      long res = (k == Add) ? (e1->value + e2->bin.right->value)
                            : (e1->value * e2->bin.right->value);
      Expr* b_left;
      Expr* val_reuse = nullptr;
      if (e2->rc == 1) {
        b_left = e2->bin.left;
        Expr* b_right = e2->bin.right;
        if (b_right->rc == 1) {
          val_reuse = b_right;
        } else {
          dec(b_right);
        }
        if (reuse != nullptr) {
          free_expr(e2);
        } else {
          reuse = e2;
        }
      } else {
        b_left = inc(e2->bin.left);
        dec(e2);
      }
      if (val_reuse != nullptr) {
        dec(e1);
      } else if (e1->rc == 1) {
        val_reuse = e1;
      } else {
        dec(e1);
      }
      return mk_bin(k, mk_val(res, val_reuse), b_left, reuse);
    } else if (e1->kind == Val && e2->kind == k && e2->bin.left->kind == Val) {
      long res = (k == Add) ? (e1->value + e2->bin.left->value)
                            : (e1->value * e2->bin.left->value);
      Expr* b_right;
      Expr* val_reuse = nullptr;
      if (e2->rc == 1) {
        b_right = e2->bin.right;
        Expr* b_left = e2->bin.left;
        if (b_left->rc == 1) {
          val_reuse = b_left;
        } else {
          dec(b_left);
        }
        if (reuse != nullptr) {
          free_expr(e2);
        } else {
          reuse = e2;
        }
      } else {
        b_right = inc(e2->bin.right);
        dec(e2);
      }
      if (val_reuse != nullptr) {
        dec(e1);
      } else if (e1->rc == 1) {
        val_reuse = e1;
      } else {
        dec(e1);
      }
      return mk_bin(k, mk_val(res, val_reuse), b_right, reuse);
    } else {
      return mk_bin(k, e1, e2, reuse);
    }
  } else {
    return e;
  }
}

static long eval(const Expr* e) {
  if (e->kind == Var) {
    return 0;
  } else if (e->kind == Val) {
    return e->value;
  } else if (e->kind == Add) {
    return eval(e->bin.left) + eval(e->bin.right);
  } else if (e->kind == Mul) {
    return eval(e->bin.left) * eval(e->bin.right);
  } else {
    return 0;
  }
}

int main(int argc, char** argv) {
  Expr* e = mk_expr(argc == 2 ? std::atol(argv[1]) : 20, 1);
  long v1 = eval(e);
  Expr* folded = const_folding(reassoc(e));
  long v2 = eval(folded);
  dec(folded);
  std::cout << v1 << " " << v2 << "\n";
#ifdef RC_DEBUG_CHECK
  if (g_live_expr != 0) {
    std::cerr << "LEAK DETECTED: live_expr=" << g_live_expr << "\n";
    return 99;
  }
#endif
  return 0;
}
