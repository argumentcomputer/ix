// Compilatr.ix twin of Lean `rbmap_checkpoint`: a persistent (path-copying)
// red-black tree with shared ownership, so that every checkpoint stays valid
// while later insertions proceed. The driver follows Koka
// `test/bench/cpp/rbtree-ck.cpp` and Lean `tests/bench/rbmap_checkpoint_cpp_std.cpp`
// (both Apache-2.0; see benchmarks/fixtures/LICENSES/), which checkpoint by
// copying a whole std::map and so need memory quadratic in n / freq; the
// insertion and balancing cases follow Lean's `ins`, `balance1` and `balance2`.
// The output is "length count", as in Lean.
#include <cstdint>
#include <cstdlib>
#include <forward_list>
#include <iostream>
#include <memory>

enum class Color : unsigned char { red, black };

struct Node;
using Tree = std::shared_ptr<const Node>;

struct Node {
  Color color;
  Tree left;
  uint64_t key;
  bool val;
  Tree right;
  Node(Color c, Tree l, uint64_t k, bool v, Tree r)
      : color(c), left(std::move(l)), key(k), val(v), right(std::move(r)) {}
};

static Tree node(Color c, Tree l, uint64_t k, bool v, Tree r) {
  return std::make_shared<const Node>(c, std::move(l), k, v, std::move(r));
}

static bool is_red(const Tree &t) { return t && t->color == Color::red; }

// n is the rebuilt left subtree of a black node (kv, vv) with right subtree t.
static Tree balance1(uint64_t kv, bool vv, const Tree &t, const Tree &n) {
  if (!n) return nullptr;
  if (is_red(n->left)) {
    const Node &l = *n->left;
    return node(Color::red, node(Color::black, l.left, l.key, l.val, l.right), n->key, n->val,
                node(Color::black, n->right, kv, vv, t));
  }
  if (is_red(n->right)) {
    const Node &r = *n->right;
    return node(Color::red, node(Color::black, n->left, n->key, n->val, r.left), r.key, r.val,
                node(Color::black, r.right, kv, vv, t));
  }
  return node(Color::black, node(Color::red, n->left, n->key, n->val, n->right), kv, vv, t);
}

// n is the rebuilt right subtree of a black node (kv, vv) with left subtree t.
static Tree balance2(const Tree &t, uint64_t kv, bool vv, const Tree &n) {
  if (!n) return nullptr;
  if (is_red(n->left)) {
    const Node &l = *n->left;
    return node(Color::red, node(Color::black, t, kv, vv, l.left), l.key, l.val,
                node(Color::black, l.right, n->key, n->val, n->right));
  }
  if (is_red(n->right)) {
    const Node &r = *n->right;
    return node(Color::red, node(Color::black, t, kv, vv, n->left), n->key, n->val,
                node(Color::black, r.left, r.key, r.val, r.right));
  }
  return node(Color::black, t, kv, vv, node(Color::red, n->left, n->key, n->val, n->right));
}

static Tree ins(uint64_t kx, bool vx, const Tree &t) {
  if (!t) return node(Color::red, nullptr, kx, vx, nullptr);
  const Node &n = *t;
  if (n.color == Color::red) {
    if (kx < n.key) return node(Color::red, ins(kx, vx, n.left), n.key, n.val, n.right);
    if (kx == n.key) return node(Color::red, n.left, kx, vx, n.right);
    return node(Color::red, n.left, n.key, n.val, ins(kx, vx, n.right));
  }
  if (kx < n.key) {
    if (is_red(n.left)) return balance1(n.key, n.val, n.right, ins(kx, vx, n.left));
    return node(Color::black, ins(kx, vx, n.left), n.key, n.val, n.right);
  }
  if (kx == n.key) return node(Color::black, n.left, kx, vx, n.right);
  if (is_red(n.right)) return balance2(n.left, n.key, n.val, ins(kx, vx, n.right));
  return node(Color::black, n.left, n.key, n.val, ins(kx, vx, n.right));
}

static Tree set_black(const Tree &t) {
  if (!t) return t;
  return node(Color::black, t->left, t->key, t->val, t->right);
}

static Tree insert(uint64_t k, bool v, const Tree &t) {
  if (is_red(t)) return set_black(ins(k, v, t));
  return ins(k, v, t);
}

static std::forward_list<Tree> mk_map(uint64_t n, uint64_t freq) {
  std::forward_list<Tree> stack;
  Tree m;
  while (n > 0) {
    --n;
    m = insert(n, n % 10 == 0, m);
    if (n % freq == 0) stack.push_front(m);
  }
  stack.push_front(m);
  return stack;
}

static uint64_t fold(const Tree &t, uint64_t r) {
  if (!t) return r;
  r = fold(t->left, r);
  if (t->val) r = r + 1;
  return fold(t->right, r);
}

// Lean's myLen: the number of non-empty checkpoints.
static uint64_t my_len(const std::forward_list<Tree> &stack) {
  uint64_t r = 0;
  for (const Tree &t : stack)
    if (t) r++;
  return r;
}

int main(int argc, char **argv) {
  if (argc != 3) {
    std::cout << "invalid number of arguments\n";
    return 1;
  }
  uint64_t n = strtoull(argv[1], nullptr, 10);
  uint64_t freq = strtoull(argv[2], nullptr, 10);
  if (freq == 0) freq = 1;
  std::forward_list<Tree> stack = mk_map(n, freq);
  std::cout << my_len(stack) << " " << fold(stack.front(), 0) << "\n";
  return 0;
}
