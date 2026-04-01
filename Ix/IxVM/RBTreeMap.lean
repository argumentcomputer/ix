module
public import Ix.Aiur.Meta

public section

namespace IxVM

def rbTreeMap := ⟦
  enum RBTreeMap {
    -- Color {0: red, 1: black}, key, value, left, right
    Node(G, G, G, &RBTreeMap, &RBTreeMap),
    Nil
  }

  -- Okasaki-style balance: fixes red-red violations after insertion
  fn rbtree_map_balance(color: G, key: G, value: G, left: RBTreeMap, right: RBTreeMap) -> RBTreeMap {
    match (color, left, right) {
      -- Case 1: left child red, left-left grandchild red
      (1, RBTreeMap.Node(0, yk, yv, &RBTreeMap.Node(0, xk, xv, a, b), c), d) =>
        RBTreeMap.Node(0, yk, yv,
          store(RBTreeMap.Node(1, xk, xv, a, b)),
          store(RBTreeMap.Node(1, key, value, c, store(d)))),
      -- Case 2: left child red, left-right grandchild red
      (1, RBTreeMap.Node(0, xk, xv, a, &RBTreeMap.Node(0, yk, yv, b, c)), d) =>
        RBTreeMap.Node(0, yk, yv,
          store(RBTreeMap.Node(1, xk, xv, a, b)),
          store(RBTreeMap.Node(1, key, value, c, store(d)))),
      -- Case 3: right child red, right-left grandchild red
      (1, a, RBTreeMap.Node(0, zk, zv, &RBTreeMap.Node(0, yk, yv, b, c), d)) =>
        RBTreeMap.Node(0, yk, yv,
          store(RBTreeMap.Node(1, key, value, store(a), b)),
          store(RBTreeMap.Node(1, zk, zv, c, d))),
      -- Case 4: right child red, right-right grandchild red
      (1, a, RBTreeMap.Node(0, yk, yv, b, &RBTreeMap.Node(0, zk, zv, c, d))) =>
        RBTreeMap.Node(0, yk, yv,
          store(RBTreeMap.Node(1, key, value, store(a), b)),
          store(RBTreeMap.Node(1, zk, zv, c, d))),
      -- No violation
      _ => RBTreeMap.Node(color, key, value, store(left), store(right)),
    }
  }

  -- Internal insert (new nodes are red)
  fn rbtree_map_ins(key: G, value: G, tree: RBTreeMap) -> RBTreeMap {
    match tree {
      RBTreeMap.Nil =>
        RBTreeMap.Node(0, key, value, store(RBTreeMap.Nil), store(RBTreeMap.Nil)),
      RBTreeMap.Node(color, k, v, &left, &right) =>
        let lt = u32_less_than(key, k);
        match lt {
          1 => rbtree_map_balance(color, k, v, rbtree_map_ins(key, value, left), right),
          _ =>
            let gt = u32_less_than(k, key);
            match gt {
              1 => rbtree_map_balance(color, k, v, left, rbtree_map_ins(key, value, right)),
              _ => RBTreeMap.Node(color, key, value, store(left), store(right)),
            },
        },
    }
  }

  -- Public insert: inserts key-value pair, enforces black root
  fn rbtree_map_insert(key: G, value: G, tree: RBTreeMap) -> RBTreeMap {
    let result = rbtree_map_ins(key, value, tree);
    match result {
      RBTreeMap.Node(_, k, v, left, right) => RBTreeMap.Node(1, k, v, left, right),
    }
  }

  -- Lookup: returns the value associated with the key.
  -- Fails if the key is not found (no Nil case).
  fn rbtree_map_lookup(key: G, tree: RBTreeMap) -> G {
    match tree {
      RBTreeMap.Node(_, k, v, &left, &right) =>
        let lt = u32_less_than(key, k);
        match lt {
          1 => rbtree_map_lookup(key, left),
          _ =>
            let gt = u32_less_than(k, key);
            match gt {
              1 => rbtree_map_lookup(key, right),
              _ => v,
            },
        },
    }
  }

  /- # Test entrypoints -/

  pub fn rbtree_map_test() -> [G; 22] {
    -- Single insert and lookup
    let tree = rbtree_map_insert(5, 42, RBTreeMap.Nil);
    let r0 = rbtree_map_lookup(5, tree);

    -- Three inserts
    let tree = rbtree_map_insert(10, 100, RBTreeMap.Nil);
    let tree = rbtree_map_insert(20, 200, tree);
    let tree = rbtree_map_insert(5, 50, tree);
    let r1 = rbtree_map_lookup(5, tree);
    let r2 = rbtree_map_lookup(10, tree);
    let r3 = rbtree_map_lookup(20, tree);

    -- Overwrite
    let tree = rbtree_map_insert(10, 100, RBTreeMap.Nil);
    let tree = rbtree_map_insert(10, 999, tree);
    let r4 = rbtree_map_lookup(10, tree);

    -- Ascending insertion order
    let tree = rbtree_map_insert(1, 10, RBTreeMap.Nil);
    let tree = rbtree_map_insert(2, 20, tree);
    let tree = rbtree_map_insert(3, 30, tree);
    let tree = rbtree_map_insert(4, 40, tree);
    let tree = rbtree_map_insert(5, 50, tree);
    let r5 = rbtree_map_lookup(1, tree);
    let r6 = rbtree_map_lookup(2, tree);
    let r7 = rbtree_map_lookup(3, tree);
    let r8 = rbtree_map_lookup(4, tree);
    let r9 = rbtree_map_lookup(5, tree);

    -- Descending insertion order
    let tree = rbtree_map_insert(5, 50, RBTreeMap.Nil);
    let tree = rbtree_map_insert(4, 40, tree);
    let tree = rbtree_map_insert(3, 30, tree);
    let tree = rbtree_map_insert(2, 20, tree);
    let tree = rbtree_map_insert(1, 10, tree);
    let r10 = rbtree_map_lookup(1, tree);
    let r11 = rbtree_map_lookup(2, tree);
    let r12 = rbtree_map_lookup(3, tree);
    let r13 = rbtree_map_lookup(4, tree);
    let r14 = rbtree_map_lookup(5, tree);

    -- Mixed insertion order
    let tree = rbtree_map_insert(50, 500, RBTreeMap.Nil);
    let tree = rbtree_map_insert(30, 300, tree);
    let tree = rbtree_map_insert(70, 700, tree);
    let tree = rbtree_map_insert(20, 200, tree);
    let tree = rbtree_map_insert(40, 400, tree);
    let tree = rbtree_map_insert(60, 600, tree);
    let tree = rbtree_map_insert(80, 800, tree);
    let r15 = rbtree_map_lookup(20, tree);
    let r16 = rbtree_map_lookup(30, tree);
    let r17 = rbtree_map_lookup(40, tree);
    let r18 = rbtree_map_lookup(50, tree);
    let r19 = rbtree_map_lookup(60, tree);
    let r20 = rbtree_map_lookup(70, tree);
    let r21 = rbtree_map_lookup(80, tree);

    [r0,
     r1, r2, r3,
     r4,
     r5, r6, r7, r8, r9,
     r10, r11, r12, r13, r14,
     r15, r16, r17, r18, r19, r20, r21]
  }
⟧

end IxVM

end
