module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes

public section

namespace IxVM

/-! ## Level operations + literal equality + expr_inst_levels

Mirror: src/ix/kernel/level.rs + literal-equality helpers from
src/ix/kernel/expr.rs. Self-contained; new kernel modules
(Subst/Whnf/Infer/DefEq/Check) import from here.
-/

def levels := ⟦
  fn level_is_not_zero(l: KLevel) -> G {
    match load(l) {
      KLevelNode.Zero => 0,
      KLevelNode.Param(_) => 0,
      KLevelNode.Succ(_) => 1,
      KLevelNode.Max(a, b) => match (level_is_not_zero(a), level_is_not_zero(b)) {
        (0, 0) => 0,
        _ => 1,
      },
      KLevelNode.IMax(_, b) => level_is_not_zero(b),
    }
  }

  fn level_eq(a: KLevel, b: KLevel) -> G {
    match load(a) {
      KLevelNode.Zero =>
        match load(b) {
          KLevelNode.Zero => 1,
          _ => 0,
        },
      KLevelNode.Succ(a1) =>
        match load(b) {
          KLevelNode.Succ(b1) => level_eq(a1, b1),
          _ => 0,
        },
      KLevelNode.Max(a1, a2) =>
        match load(b) {
          KLevelNode.Max(b1, b2) => level_eq(a1, b1) * level_eq(a2, b2),
          _ => 0,
        },
      KLevelNode.IMax(a1, a2) =>
        match load(b) {
          KLevelNode.IMax(b1, b2) => level_eq(a1, b1) * level_eq(a2, b2),
          _ => 0,
        },
      KLevelNode.Param(i) =>
        match load(b) {
          KLevelNode.Param(j) => eq_zero(i - j),
          _ => 0,
        },
    }
  }

  -- ============================================================================
  -- Canonical level normalization (mirror: src/ix/kernel/level.rs
  -- normalize_level / norm_level_eq / norm_level_le, itself a port of
  -- Lean4Lean's Level.Normalize with the documented subsumption and
  -- covers-split fixes).
  --
  -- Semantic level comparison via the recursive `Level.leq` with its
  -- two-way param-substitution split per Max/IMax-with-param is
  -- exponential in the number of params, and every branch materializes
  -- freshly substituted levels (the Int16.instRxcHasSize_eq pathology:
  -- 93% of the record was level_subst_reduce/level_leq rows).
  -- Normalization is linear in the level size, `level_normalize` is
  -- keyed on the level ALONE so each distinct level normalizes once per
  -- run, and equality/leq on canonical forms is cheap.
  --
  -- Canonical form: a path-sorted list of entries `(path, const, vars)`
  -- where `path` is the sorted list of param indices conditioning an
  -- imax chain (all assumed >= 1 along that branch), `const` the max
  -- constant contribution, `vars` the idx-sorted `(param, offset)`
  -- contributions.
  -- ============================================================================
  enum NLVar {
    Mk(G, G)
  }

  enum NLEntry {
    Mk(List‹G›, G, List‹&NLVar›)
  }

  -- Lexicographic compare of sorted G-lists: 0 = eq, 1 = a < b, 2 = a > b.
  fn glist_cmp(a: List‹G›, b: List‹G›) -> G {
    match load(a) {
      ListNode.Nil =>
        match load(b) {
          ListNode.Nil => 0,
          ListNode.Cons(_, _) => 1,
        },
      ListNode.Cons(x, ar) =>
        match load(b) {
          ListNode.Nil => 2,
          ListNode.Cons(y, br) =>
            match u32_less_than(x, y) {
              1 => 1,
              0 =>
                match u32_less_than(y, x) {
                  1 => 2,
                  0 => glist_cmp(ar, br),
                },
            },
        },
    }
  }

  -- Sorted-list subset test.
  fn glist_subset(xs: List‹G›, ys: List‹G›) -> G {
    match load(xs) {
      ListNode.Nil => 1,
      ListNode.Cons(x, xr) =>
        match load(ys) {
          ListNode.Nil => 0,
          ListNode.Cons(y, yr) =>
            match u32_less_than(x, y) {
              1 => 0,
              0 =>
                match u32_less_than(y, x) {
                  1 => glist_subset(xs, yr),
                  0 => glist_subset(xr, yr),
                },
            },
        },
    }
  }

  fn glist_eq_len(a: List‹G›, b: List‹G›) -> G {
    match load(a) {
      ListNode.Nil =>
        match load(b) {
          ListNode.Nil => 1,
          ListNode.Cons(_, _) => 0,
        },
      ListNode.Cons(_, ar) =>
        match load(b) {
          ListNode.Nil => 0,
          ListNode.Cons(_, br) => glist_eq_len(ar, br),
        },
    }
  }

  -- Insert into a sorted G-list. Returns (1, new_list) on insert,
  -- (0, original) when already present. Mirrors level.rs ordered_insert.
  fn glist_ordered_insert(x: G, l: List‹G›) -> (G, List‹G›) {
    match load(l) {
      ListNode.Nil => (1, store(ListNode.Cons(x, store(ListNode.Nil)))),
      ListNode.Cons(h, r) =>
        match u32_less_than(x, h) {
          1 => (1, store(ListNode.Cons(x, l))),
          0 =>
            match u32_less_than(h, x) {
              0 => (0, l),
              1 =>
                match glist_ordered_insert(x, r) {
                  (f, r2) => (f, store(ListNode.Cons(h, r2))),
                },
            },
        },
    }
  }

  -- Insert (idx, k) into an idx-sorted var list; on duplicate idx keep
  -- the max offset. Mirrors Node::add_var.
  fn nlvars_add(vars: List‹&NLVar›, idx: G, k: G) -> List‹&NLVar› {
    match load(vars) {
      ListNode.Nil =>
        store(ListNode.Cons(store(NLVar.Mk(idx, k)), store(ListNode.Nil))),
      ListNode.Cons(v, rest) =>
        match load(v) {
          NLVar.Mk(vi, vo) =>
            match u32_less_than(idx, vi) {
              1 => store(ListNode.Cons(store(NLVar.Mk(idx, k)), vars)),
              0 =>
                match u32_less_than(vi, idx) {
                  1 => store(ListNode.Cons(v, nlvars_add(rest, idx, k))),
                  0 =>
                    match u32_less_than(vo, k) {
                      1 => store(ListNode.Cons(store(NLVar.Mk(vi, k)), rest)),
                      0 => vars,
                    },
                },
            },
        },
    }
  }

  fn nlvars_eq(a: List‹&NLVar›, b: List‹&NLVar›) -> G {
    match load(a) {
      ListNode.Nil =>
        match load(b) {
          ListNode.Nil => 1,
          ListNode.Cons(_, _) => 0,
        },
      ListNode.Cons(x, ar) =>
        match load(b) {
          ListNode.Nil => 0,
          ListNode.Cons(y, br) =>
            match load(x) {
              NLVar.Mk(xi, xo) =>
                match load(y) {
                  NLVar.Mk(yi, yo) =>
                    match xi - yi {
                      0 =>
                        match xo - yo {
                          0 => nlvars_eq(ar, br),
                          _ => 0,
                        },
                      _ => 0,
                    },
                },
            },
        },
    }
  }

  fn nlvars_max_offset(vars: List‹&NLVar›) -> G {
    match load(vars) {
      ListNode.Nil => 0,
      ListNode.Cons(v, rest) =>
        match load(v) {
          NLVar.Mk(_, vo) =>
            let m = nlvars_max_offset(rest);
            match u32_less_than(m, vo) {
              1 => vo,
              0 => m,
            },
        },
    }
  }

  -- Keep x in xs unless ys has the same idx with offset >= x's.
  -- Mirrors level.rs subsume_vars (sorted merge walk).
  fn nlvars_subsume(xs: List‹&NLVar›, ys: List‹&NLVar›) -> List‹&NLVar› {
    match load(xs) {
      ListNode.Nil => xs,
      ListNode.Cons(x, xr) =>
        match load(ys) {
          ListNode.Nil => xs,
          ListNode.Cons(y, yr) =>
            match load(x) {
              NLVar.Mk(xi, xo) =>
                match load(y) {
                  NLVar.Mk(yi, yo) =>
                    match u32_less_than(xi, yi) {
                      1 => store(ListNode.Cons(x, nlvars_subsume(xr, ys))),
                      0 =>
                        match u32_less_than(yi, xi) {
                          1 => nlvars_subsume(xs, yr),
                          0 =>
                            match u32_less_than(yo, xo) {
                              1 => store(ListNode.Cons(x, nlvars_subsume(xr, yr))),
                              0 => nlvars_subsume(xr, yr),
                            },
                        },
                    },
                },
            },
        },
    }
  }

  -- Max the constant contribution into the entry at `path` (path-sorted
  -- insert). Mirrors norm_add_const incl. its skip rule: k = 0 never
  -- contributes; k = 1 only at the empty path (along a non-empty path
  -- all conditioning params are >= 1 so the branch value is >= 1 anyway).
  fn nl_add_const(acc: List‹&NLEntry›, path: List‹G›, k: G) -> List‹&NLEntry› {
    match k {
      0 => acc,
      1 =>
        match load(path) {
          ListNode.Nil => nl_add_const_go(acc, path, k),
          ListNode.Cons(_, _) => acc,
        },
      _ => nl_add_const_go(acc, path, k),
    }
  }

  fn nl_add_const_go(acc: List‹&NLEntry›, path: List‹G›, k: G) -> List‹&NLEntry› {
    match load(acc) {
      ListNode.Nil =>
        store(ListNode.Cons(
          store(NLEntry.Mk(path, k, store(ListNode.Nil))),
          store(ListNode.Nil))),
      ListNode.Cons(e, rest) =>
        match load(e) {
          NLEntry.Mk(ep, ec, ev) =>
            match glist_cmp(path, ep) {
              0 =>
                match u32_less_than(ec, k) {
                  1 => store(ListNode.Cons(store(NLEntry.Mk(ep, k, ev)), rest)),
                  0 => acc,
                },
              1 =>
                store(ListNode.Cons(
                  store(NLEntry.Mk(path, k, store(ListNode.Nil))), acc)),
              _ => store(ListNode.Cons(e, nl_add_const_go(rest, path, k))),
            },
        },
    }
  }

  -- Add var (idx, k) to the entry at `path` (path-sorted insert).
  fn nl_add_var(acc: List‹&NLEntry›, path: List‹G›, idx: G, k: G) -> List‹&NLEntry› {
    match load(acc) {
      ListNode.Nil =>
        store(ListNode.Cons(
          store(NLEntry.Mk(path, 0,
            store(ListNode.Cons(store(NLVar.Mk(idx, k)), store(ListNode.Nil))))),
          store(ListNode.Nil))),
      ListNode.Cons(e, rest) =>
        match load(e) {
          NLEntry.Mk(ep, ec, ev) =>
            match glist_cmp(path, ep) {
              0 =>
                store(ListNode.Cons(
                  store(NLEntry.Mk(ep, ec, nlvars_add(ev, idx, k))), rest)),
              1 =>
                store(ListNode.Cons(
                  store(NLEntry.Mk(path, 0,
                    store(ListNode.Cons(store(NLVar.Mk(idx, k)), store(ListNode.Nil))))),
                  acc)),
              _ => store(ListNode.Cons(e, nl_add_var(rest, path, idx, k))),
            },
        },
    }
  }

  -- Flatten a level into canonical form. `path` = imax conditioning chain
  -- (sorted param idxs), `k` = accumulated Succ offset. Mirrors
  -- normalize_aux; the IMax arm delegates to the dispatch (whose cases
  -- replicate the aux IMax-shape cases verbatim, as in level.rs).
  fn normalize_aux(l: KLevel, path: List‹G›, k: G,
                   acc: List‹&NLEntry›) -> List‹&NLEntry› {
    match load(l) {
      KLevelNode.Zero => nl_add_const(acc, path, k),
      KLevelNode.Succ(inner) => normalize_aux(inner, path, k + 1, acc),
      KLevelNode.Max(a, b) =>
        normalize_aux(b, path, k, normalize_aux(a, path, k, acc)),
      KLevelNode.IMax(u, b) => normalize_imax_dispatch(u, b, path, k, acc),
      KLevelNode.Param(idx) =>
        match glist_ordered_insert(idx, path) {
          (1, new_path) =>
            nl_add_var(nl_add_const(acc, path, k), new_path, idx, k),
          (0, _) =>
            match k {
              0 => acc,
              _ => nl_add_var(acc, path, idx, k),
            },
        },
    }
  }

  -- imax(a, b) by b's shape: zero kills the branch; succ is never-zero so
  -- imax = max; max/imax distribute; param conditions the path.
  fn normalize_imax_dispatch(a: KLevel, b: KLevel, path: List‹G›, k: G,
                             acc: List‹&NLEntry›) -> List‹&NLEntry› {
    match load(b) {
      KLevelNode.Zero => nl_add_const(acc, path, k),
      KLevelNode.Succ(v) =>
        normalize_aux(v, path, k + 1, normalize_aux(a, path, k, acc)),
      KLevelNode.Max(v, w) =>
        -- imax(a, max(v, w)) = max(imax(a, v), imax(a, w))
        normalize_imax_dispatch(a, w, path, k,
          normalize_imax_dispatch(a, v, path, k, acc)),
      KLevelNode.IMax(v, w) =>
        -- imax(a, imax(v, w)) = max(imax(a, w), imax(v, w))
        normalize_imax_dispatch(v, w, path, k,
          normalize_imax_dispatch(a, w, path, k, acc)),
      KLevelNode.Param(idx) =>
        match glist_ordered_insert(idx, path) {
          (1, new_path) =>
            -- param(idx) = 0 branch: imax(a, 0) = 0, contributing k.
            normalize_aux(a, new_path, k,
              nl_add_var(nl_add_const(acc, path, k), new_path, idx, k)),
          (0, _) =>
            let acc2 = match k {
              0 => acc,
              _ => nl_add_var(acc, path, idx, k),
            };
            normalize_aux(a, path, k, acc2),
        },
    }
  }

  -- Phase 2 subsumption: drop contributions dominated by another entry
  -- whose path is a subset (active whenever the dominated one is).
  -- Each entry folds over the ORIGINAL (snapshot) list, mirroring the
  -- Rust snapshot semantics. Callers seed `snapshot` with the same list
  -- they pass as `rem`.
  fn nl_subsumption_walk(rem: List‹&NLEntry›,
                         snapshot: List‹&NLEntry›) -> List‹&NLEntry› {
    match load(rem) {
      ListNode.Nil => rem,
      ListNode.Cons(e, rest) =>
        store(ListNode.Cons(
          nl_subsume_entry(e, snapshot),
          nl_subsumption_walk(rest, snapshot))),
    }
  }

  fn nl_subsume_entry(e: &NLEntry, snap: List‹&NLEntry›) -> &NLEntry {
    match load(snap) {
      ListNode.Nil => e,
      ListNode.Cons(s, srest) =>
        match load(e) {
          NLEntry.Mk(p1, c1, v1) =>
            match load(s) {
              NLEntry.Mk(p2, c2, v2) =>
                match glist_subset(p2, p1) {
                  0 => nl_subsume_entry(e, srest),
                  _ =>
                    -- subset + equal length <=> p1 == p2 (self entry)
                    let same = glist_eq_len(p1, p2);
                    let c1n = match c1 {
                      0 => 0,
                      _ =>
                        let or1 = match same {
                          1 => 1,
                          0 => u32_less_than(c2, c1),
                        };
                        let or2 = match load(v2) {
                          ListNode.Nil => 1,
                          ListNode.Cons(_, _) =>
                            u32_less_than(nlvars_max_offset(v1) + 1, c1),
                        };
                        match or1 * or2 {
                          0 => 0,
                          _ => c1,
                        },
                    };
                    let v1n = match same {
                      1 => v1,
                      0 =>
                        match load(v2) {
                          ListNode.Nil => v1,
                          ListNode.Cons(_, _) => nlvars_subsume(v1, v2),
                        },
                    };
                    nl_subsume_entry(store(NLEntry.Mk(p1, c1n, v1n)), srest),
                },
            },
        },
    }
  }

  fn nl_eq(a: List‹&NLEntry›, b: List‹&NLEntry›) -> G {
    match load(a) {
      ListNode.Nil =>
        match load(b) {
          ListNode.Nil => 1,
          ListNode.Cons(_, _) => 0,
        },
      ListNode.Cons(x, ar) =>
        match load(b) {
          ListNode.Nil => 0,
          ListNode.Cons(y, br) =>
            match load(x) {
              NLEntry.Mk(xp, xc, xv) =>
                match load(y) {
                  NLEntry.Mk(yp, yc, yv) =>
                    match glist_cmp(xp, yp) {
                      0 =>
                        match xc - yc {
                          0 =>
                            match nlvars_eq(xv, yv) {
                              1 => nl_eq(ar, br),
                              0 => 0,
                            },
                          _ => 0,
                        },
                      _ => 0,
                    },
                },
            },
        },
    }
  }

  -- Does some entry (p2, n2) in l2 with p2 SUBSET-OF p1 dominate the
  -- constant c along every assignment activating p1? n2.const counts
  -- unconditionally in that branch; each var (idx, off) counts as
  -- >= off + 1 because idx IN p2 implies the param is >= 1 there.
  -- Mirrors level.rs covers_const (the fixed, split-search version).
  fn nl_covers_const(l2: List‹&NLEntry›, p1: List‹G›, c: G) -> G {
    match load(l2) {
      ListNode.Nil => 0,
      ListNode.Cons(e, rest) =>
        match load(e) {
          NLEntry.Mk(p2, c2, v2) =>
            match glist_subset(p2, p1) {
              0 => nl_covers_const(rest, p1, c),
              _ =>
                let hit = match u32_less_than(c2, c) {
                  0 => 1,
                  1 => nlvars_any_offset_geq(v2, c),
                };
                match hit {
                  1 => 1,
                  0 => nl_covers_const(rest, p1, c),
                },
            },
        },
    }
  }

  -- Any var with offset + 1 >= c?
  fn nlvars_any_offset_geq(vars: List‹&NLVar›, c: G) -> G {
    match load(vars) {
      ListNode.Nil => 0,
      ListNode.Cons(v, rest) =>
        match load(v) {
          NLVar.Mk(_, vo) =>
            match u32_less_than(vo + 1, c) {
              0 => 1,
              1 => nlvars_any_offset_geq(rest, c),
            },
        },
    }
  }

  -- Does some entry (p2, n2) in l2 with p2 SUBSET-OF p1 contain a var
  -- (w, off2) with off2 >= off? Mirrors level.rs covers_var.
  fn nl_covers_var(l2: List‹&NLEntry›, p1: List‹G›, w: G, off: G) -> G {
    match load(l2) {
      ListNode.Nil => 0,
      ListNode.Cons(e, rest) =>
        match load(e) {
          NLEntry.Mk(p2, _, v2) =>
            match glist_subset(p2, p1) {
              0 => nl_covers_var(rest, p1, w, off),
              _ =>
                match nlvars_dominates(v2, w, off) {
                  1 => 1,
                  0 => nl_covers_var(rest, p1, w, off),
                },
            },
        },
    }
  }

  fn nlvars_dominates(vars: List‹&NLVar›, w: G, off: G) -> G {
    match load(vars) {
      ListNode.Nil => 0,
      ListNode.Cons(v, rest) =>
        match load(v) {
          NLVar.Mk(vi, vo) =>
            match vi - w {
              0 =>
                match u32_less_than(vo, off) {
                  0 => 1,
                  1 => nlvars_dominates(rest, w, off),
                },
              _ => nlvars_dominates(rest, w, off),
            },
        },
    }
  }

  -- Semantic l1 <= l2 on canonical forms: every entry's contribution in
  -- its activation branch must be dominated by subset-path entries of l2.
  -- Mirrors level.rs norm_level_le (with its covers split, sound where
  -- Lean4Lean's single-entry search is incomplete).
  fn nl_le(l1: List‹&NLEntry›, l2: List‹&NLEntry›) -> G {
    match load(l1) {
      ListNode.Nil => 1,
      ListNode.Cons(e, rest) =>
        match load(e) {
          NLEntry.Mk(p1, c1, v1) =>
            let c_ok = match c1 {
              0 => 1,
              _ => nl_covers_const(l2, p1, c1),
            };
            match c_ok {
              0 => 0,
              1 =>
                match nl_le_vars(v1, l2, p1) {
                  0 => 0,
                  1 => nl_le(rest, l2),
                },
            },
        },
    }
  }

  fn nl_le_vars(vars: List‹&NLVar›, l2: List‹&NLEntry›, p1: List‹G›) -> G {
    match load(vars) {
      ListNode.Nil => 1,
      ListNode.Cons(v, rest) =>
        match load(v) {
          NLVar.Mk(vi, vo) =>
            match nl_covers_var(l2, p1, vi, vo) {
              0 => 0,
              1 => nl_le_vars(rest, l2, p1),
            },
        },
    }
  }

  -- Keyed on the level alone: each distinct level normalizes once per run.
  -- Seeded with the empty-path entry, mirroring normalize_level.
  fn level_normalize(l: KLevel) -> List‹&NLEntry› {
    let seed = store(ListNode.Cons(
      store(NLEntry.Mk(store(ListNode.Nil), 0, store(ListNode.Nil))),
      store(ListNode.Nil)));
    let raw = normalize_aux(l, store(ListNode.Nil), 0, seed);
    nl_subsumption_walk(raw, raw)
  }

  fn level_leq(a: KLevel, b: KLevel) -> G {
    match level_eq(a, b) {
      1 => 1,
      0 =>
        match load(a) {
          KLevelNode.Zero => 1,
          _ => nl_le(level_normalize(a), level_normalize(b)),
        },
    }
  }

  -- Semantic level equality via canonical forms (mirror: level.rs
  -- univ_eq). The previous leq(a,b)*leq(b,a) did a two-way
  -- param-substitution split per Max/IMax-with-param -- exponential in
  -- params and the dominant record cost on instance-heavy checks.
  fn level_equal(a: KLevel, b: KLevel) -> G {
    match level_eq(a, b) {
      1 => 1,
      0 => nl_eq(level_normalize(a), level_normalize(b)),
    }
  }

  -- Mirror level.rs KUniv::max exactly: explicit-numeral collapse,
  -- STRUCTURAL equality (store dedup makes structurally identical levels
  -- pointer-equal), zero absorption, max-subsumption, same-base offset
  -- collapse — and NO Succ-over-Max factoring. Lean stores type-former
  -- levels normalized with Succ distributed INTO Max (`max (u+1) (v+1)`);
  -- factoring Succ back out here rebuilt Succ-headed forms whose variant
  -- rank differs, diverging canonical-sort comparisons (aux view order)
  -- from the stored/compile shapes.
  fn level_max(a: KLevel, b: KLevel) -> KLevel {
    match level_explicit_val(a) {
      (1, na) =>
        match level_explicit_val(b) {
          (1, nb) =>
            match u32_less_than(na, nb) {
              1 => b,
              0 => a,
            },
          _ => level_max_go(a, b),
        },
      _ => level_max_go(a, b),
    }
  }

  fn level_max_go(a: KLevel, b: KLevel) -> KLevel {
    match level_struct_eq(a, b) {
      1 => a,
      0 =>
        match load(a) {
          KLevelNode.Zero => b,
          _ =>
            match load(b) {
              KLevelNode.Zero => a,
              _ =>
                match level_max_subsumes(b, a) {
                  1 => b,
                  0 =>
                    match level_max_subsumes(a, b) {
                      1 => a,
                      0 => level_max_offsets(a, b),
                    },
                },
            },
        },
    }
  }

  -- Structural (raw, non-normalizing) level equality — mirror of Rust's
  -- KUniv `==` (hash equality over the raw structure). Pointer equality
  -- is a sound fast path (same data), but pointer INEQUALITY does not
  -- imply different data, so the fallback compares values recursively.
  fn level_struct_eq(a: KLevel, b: KLevel) -> G {
    match ptr_val(a) - ptr_val(b) {
      0 => 1,
      _ =>
        match load(a) {
          KLevelNode.Zero =>
            match load(b) {
              KLevelNode.Zero => 1,
              _ => 0,
            },
          KLevelNode.Succ(x) =>
            match load(b) {
              KLevelNode.Succ(y) => level_struct_eq(x, y),
              _ => 0,
            },
          KLevelNode.Max(x1, x2) =>
            match load(b) {
              KLevelNode.Max(y1, y2) =>
                level_struct_eq(x1, y1) * level_struct_eq(x2, y2),
              _ => 0,
            },
          KLevelNode.IMax(x1, x2) =>
            match load(b) {
              KLevelNode.IMax(y1, y2) =>
                level_struct_eq(x1, y1) * level_struct_eq(x2, y2),
              _ => 0,
            },
          KLevelNode.Param(i) =>
            match load(b) {
              KLevelNode.Param(j) =>
                match i - j {
                  0 => 1,
                  _ => 0,
                },
              _ => 0,
            },
        },
    }
  }

  -- 1 iff `m` is `Max(l, r)` with `l` or `r` structurally equal to `x`:
  -- max(x, max(x, b)) = max(x, b) etc.
  fn level_max_subsumes(m: KLevel, x: KLevel) -> G {
    match load(m) {
      KLevelNode.Max(l, r) =>
        match level_struct_eq(l, x) {
          1 => 1,
          0 => level_struct_eq(r, x),
        },
      _ => 0,
    }
  }

  -- Same-base offset collapse: succ^n(x) vs succ^m(x) with structurally
  -- equal base → the larger; otherwise the raw Max node.
  fn level_max_offsets(a: KLevel, b: KLevel) -> KLevel {
    match level_offset_of(a, 0) {
      (base_a, off_a) =>
        match level_offset_of(b, 0) {
          (base_b, off_b) =>
            match level_struct_eq(base_a, base_b) {
              1 =>
                match u32_less_than(off_a, off_b) {
                  1 => b,
                  0 => a,
                },
              0 => store(KLevelNode.Max(a, b)),
            },
        },
    }
  }

  -- (1, n) iff the level is the explicit numeral succ^n(Zero).
  fn level_explicit_val(l: KLevel) -> (G, G) {
    match load(l) {
      KLevelNode.Zero => (1, 0),
      KLevelNode.Succ(inner) =>
        match level_explicit_val(inner) {
          (1, n) => (1, n + 1),
          _ => (0, 0),
        },
      _ => (0, 0),
    }
  }

  -- Peel Succs: level_offset_of(succ^n(x), 0) = (x, n).
  fn level_offset_of(l: KLevel, k: G) -> (KLevel, G) {
    match load(l) {
      KLevelNode.Succ(inner) => level_offset_of(inner, k + 1),
      _ => (l, k),
    }
  }

  fn level_imax(a: KLevel, b: KLevel) -> KLevel {
    match load(b) {
      KLevelNode.Zero => store(KLevelNode.Zero),
      KLevelNode.Succ(_) => level_max(a, b),
      _ =>
        let not_zero = level_is_not_zero(b);
        match not_zero {
          1 => level_max(a, b),
          0 =>
            match load(a) {
              KLevelNode.Zero => b,
              _ =>
                let eq = level_eq(a, b);
                match eq {
                  1 => a,
                  0 => store(KLevelNode.IMax(a, b)),
                },
            },
        },
    }
  }

  fn level_reduce(l: KLevel) -> KLevel {
    match load(l) {
      KLevelNode.Zero => store(KLevelNode.Zero),
      KLevelNode.Param(i) => store(KLevelNode.Param(i)),
      KLevelNode.Succ(u) => store(KLevelNode.Succ(level_reduce(u))),
      KLevelNode.Max(a, b) => level_max(level_reduce(a), level_reduce(b)),
      KLevelNode.IMax(a, b) => level_imax(level_reduce(a), level_reduce(b)),
    }
  }

  fn level_inst_params(l: KLevel, params: List‹KLevel›) -> KLevel {
    match load(l) {
      KLevelNode.Zero => store(KLevelNode.Zero),
      KLevelNode.Succ(u) => store(KLevelNode.Succ(level_inst_params(u, params))),
      KLevelNode.Max(a, b) =>
        level_max(level_inst_params(a, params), level_inst_params(b, params)),
      KLevelNode.IMax(a, b) =>
        level_imax(level_inst_params(a, params), level_inst_params(b, params)),
      KLevelNode.Param(i) => list_lookup(params, i),
    }
  }

  fn level_list_inst(lvls: List‹KLevel›, params: List‹KLevel›) -> List‹KLevel› {
    match load(lvls) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(l, rest) =>
        store(ListNode.Cons(
          level_inst_params(l, params),
          level_list_inst(rest, params))),
    }
  }

  fn expr_inst_levels(e: KExpr, params: List‹KLevel›) -> KExpr {
    -- Fast path: empty param list = identity. Common when caller's lvls
    -- list is Nil (constants with no universe params).
    match load(params) {
      ListNode.Nil => e,
      _ => expr_inst_levels_walk(e, params),
    }
  }

  fn expr_inst_levels_walk(e: KExpr, params: List‹KLevel›) -> KExpr {
    match load(e) {
      KExprNode.BVar(i) => store(KExprNode.BVar(i)),
      KExprNode.Srt(l) =>
        store(KExprNode.Srt(level_inst_params(l, params))),
      KExprNode.Const(idx, lvls) =>
        store(KExprNode.Const(idx, level_list_inst(lvls, params))),
      KExprNode.App(f, a) =>
        store(KExprNode.App(expr_inst_levels(f, params), expr_inst_levels(a, params))),
      KExprNode.Lam(ty, body) =>
        store(KExprNode.Lam(expr_inst_levels(ty, params), expr_inst_levels(body, params))),
      KExprNode.Forall(ty, body) =>
        store(KExprNode.Forall(expr_inst_levels(ty, params), expr_inst_levels(body, params))),
      KExprNode.Let(ty, val, body) =>
        store(KExprNode.Let(
          expr_inst_levels(ty, params),
          expr_inst_levels(val, params),
          expr_inst_levels(body, params))),
      KExprNode.Lit(lit) => store(KExprNode.Lit(lit)),
      KExprNode.Proj(tidx, fidx, e1) =>
        store(KExprNode.Proj(tidx, fidx, expr_inst_levels(e1, params))),
    }
  }

  -- ============================================================================
  -- Literal equality
  -- ============================================================================

  fn klimbs_eq(a: KLimbs, b: KLimbs) -> G {
    match load(a) {
      ListNode.Nil =>
        match load(b) {
          ListNode.Nil => 1,
          _ => 0,
        },
      ListNode.Cons(la, ra) =>
        match load(b) {
          ListNode.Nil => 0,
          ListNode.Cons(lb, rb) =>
            let eq = u64_eq(la, lb);
            match eq {
              1 => klimbs_eq(ra, rb),
              0 => 0,
            },
        },
    }
  }

  fn bytestream_eq(a: ByteStream, b: ByteStream) -> G {
    match load(a) {
      ListNode.Nil =>
        match load(b) {
          ListNode.Nil => 1,
          _ => 0,
        },
      ListNode.Cons(ba, ra) =>
        match load(b) {
          ListNode.Nil => 0,
          ListNode.Cons(bb, rb) =>
            match to_field(ba) - to_field(bb) {
              0 => bytestream_eq(ra, rb),
              _ => 0,
            },
        },
    }
  }

  fn literal_eq(a: KLiteral, b: KLiteral) -> G {
    match a {
      KLiteral.Nat(na) =>
        match b {
          KLiteral.Nat(nb) => klimbs_eq(na, nb),
          _ => 0,
        },
      KLiteral.Str(sa) =>
        match b {
          KLiteral.Str(sb) => bytestream_eq(sa, sb),
          _ => 0,
        },
    }
  }
⟧

end IxVM

end
