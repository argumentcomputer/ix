module
public import Ix.Aiur.Meta

public section

namespace IxVM

def rbTreeMap := ⟦
  enum RBTreeMap‹V› {
    -- Color {0: red, 1: black}, key, value, left, right
    Node(G, G, V, &RBTreeMap‹V›, &RBTreeMap‹V›),
    Nil
  }

  -- Okasaki-style balance: fixes red-red violations after insertion.
  --
  -- A violation can only occur under a BLACK parent (color 1); a red
  -- parent never rebalances. The 4 rebalance cases are WIDE (they deref a
  -- red grandchild and rebuild 3 nodes), so they're factored into the cold
  -- `rbtree_map_balance_fix`. Aiur lays a function's width as the max over
  -- match arms, so keeping the hot path (red parent / black parent with no
  -- violation) here as a narrow color-dispatch keeps `balance` itself
  -- narrow; the wide rebalance machinery only taxes the rows that actually
  -- reach `_fix` (black parents).
  fn rbtree_map_balance‹V›(color: G, key: G, value: V, left: RBTreeMap‹V›, right: RBTreeMap‹V›) -> RBTreeMap‹V› {
    match color {
      1 => rbtree_map_balance_fix(key, value, left, right),
      _ => RBTreeMap.Node(color, key, value, store(left), store(right)),
    }
  }

  -- Cold path: parent is black (color 1). Match the 4 red-red grandchild
  -- configurations; the fall-through is "black parent, no violation".
  fn rbtree_map_balance_fix‹V›(key: G, value: V, left: RBTreeMap‹V›, right: RBTreeMap‹V›) -> RBTreeMap‹V› {
    match (left, right) {
      -- Case 1: left child red, left-left grandchild red
      (RBTreeMap.Node(0, yk, yv, &RBTreeMap.Node(0, xk, xv, a, b), c), d) =>
        RBTreeMap.Node(0, yk, yv,
          store(RBTreeMap.Node(1, xk, xv, a, b)),
          store(RBTreeMap.Node(1, key, value, c, store(d)))),
      -- Case 2: left child red, left-right grandchild red
      (RBTreeMap.Node(0, xk, xv, a, &RBTreeMap.Node(0, yk, yv, b, c)), d) =>
        RBTreeMap.Node(0, yk, yv,
          store(RBTreeMap.Node(1, xk, xv, a, b)),
          store(RBTreeMap.Node(1, key, value, c, store(d)))),
      -- Case 3: right child red, right-left grandchild red
      (a, RBTreeMap.Node(0, zk, zv, &RBTreeMap.Node(0, yk, yv, b, c), d)) =>
        RBTreeMap.Node(0, yk, yv,
          store(RBTreeMap.Node(1, key, value, store(a), b)),
          store(RBTreeMap.Node(1, zk, zv, c, d))),
      -- Case 4: right child red, right-right grandchild red
      (a, RBTreeMap.Node(0, yk, yv, b, &RBTreeMap.Node(0, zk, zv, c, d))) =>
        RBTreeMap.Node(0, yk, yv,
          store(RBTreeMap.Node(1, key, value, store(a), b)),
          store(RBTreeMap.Node(1, zk, zv, c, d))),
      -- No violation (black parent)
      _ => RBTreeMap.Node(1, key, value, store(left), store(right)),
    }
  }

  -- Internal insert (new nodes are red)
  fn rbtree_map_ins‹V›(key: G, value: V, tree: RBTreeMap‹V›) -> RBTreeMap‹V› {
    match tree {
      RBTreeMap.Nil =>
        RBTreeMap.Node(0, key, value, store(RBTreeMap.Nil), store(RBTreeMap.Nil)),
      RBTreeMap.Node(color, k, v, &left, &right) =>
        let lt = u32_less_than(key, k);
        match lt {
          1 => rbtree_map_balance(color, k, v, rbtree_map_ins(key, value, left), right),
          _ =>
            -- key not < k. Distinguish equal (overwrite) from greater
            -- (recurse right) with a field subtraction instead of a second
            -- u32_less_than (which would cost +12 aux / +6 lookups). Keys
            -- are u32-range field elements, so `key - k == 0` iff equal.
            let eq = key - k;
            match eq {
              0 => RBTreeMap.Node(color, key, value, store(left), store(right)),
              _ => rbtree_map_balance(color, k, v, left, rbtree_map_ins(key, value, right)),
            },
        },
    }
  }

  -- Public insert: inserts key-value pair, enforces black root
  fn rbtree_map_insert‹V›(key: G, value: V, tree: RBTreeMap‹V›) -> RBTreeMap‹V› {
    let result = rbtree_map_ins(key, value, tree);
    match result {
      RBTreeMap.Node(_, k, v, left, right) => RBTreeMap.Node(1, k, v, left, right),
    }
  }

  -- Lookup: returns the value associated with the key.
  -- Panics if the key is not found (no Nil case) — tightest circuit
  -- when callers know the key is present by construction.
  fn rbtree_map_lookup‹V›(key: G, tree: RBTreeMap‹V›) -> V {
    match tree {
      RBTreeMap.Node(_, k, v, &left, &right) =>
        let lt = u32_less_than(key, k);
        match lt {
          1 => rbtree_map_lookup(key, left),
          _ =>
            let eq = key - k;
            match eq {
              0 => v,
              _ => rbtree_map_lookup(key, right),
            },
        },
    }
  }

  -- Lookup with default: returns the value if found, else `default`.
  -- Use when the caller can't statically guarantee key presence
  -- (e.g. `find_addr_idx_safe`).
  fn rbtree_map_lookup_or_default‹V›(key: G, tree: RBTreeMap‹V›, default: V) -> V {
    match tree {
      RBTreeMap.Nil => default,
      RBTreeMap.Node(_, k, v, &left, &right) =>
        let lt = u32_less_than(key, k);
        match lt {
          1 => rbtree_map_lookup_or_default(key, left, default),
          _ =>
            let eq = key - k;
            match eq {
              0 => v,
              _ => rbtree_map_lookup_or_default(key, right, default),
            },
        },
    }
  }
⟧

/-- RBTreeMap test entrypoint. Kept out of the `rbTreeMap` library
toplevel so it only adds circuits to systems that merge it explicitly. -/
def rbTreeMapTests := ⟦
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
