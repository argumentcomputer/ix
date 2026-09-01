module
public import Ix.Aiur.Meta

public section

namespace IxVM

def core := ⟦
  enum ListNode‹T› {
    Cons(T, List‹T›),
    Nil
  }

  type List‹T› = &ListNode‹T›

  enum Option‹T› {
    Some(T),
    None
  }

  -- Memoized u32 comparison for hot structural and frontier walks. Aiur
  -- memoizes function calls automatically, so keeping the decomposition in
  -- this shared helper avoids charging the wide intrinsic layout repeatedly;
  -- recurring `(a, b)` pairs share one constrained helper row. This belongs
  -- in Core because both the IxVM substitution circuits and the recursive
  -- multi-STARK verifier rely on the same optimization.
  fn memo_u32_less_than(a: G, b: G) -> G {
    u32_less_than(a, b)
  }

  -- Interned 32-element address (blake3 content hash).
  --
  -- DIFFERENT POINTER VALUES DO NOT IMPLY DIFFERENT DATA. The Aiur
  -- executor content-dedups `store`, so in an honest trace equal content
  -- yields one canonical pointer — but that is an executor convention,
  -- not a constraint. The memory AIR (`crates/aiur/src/memory.rs`)
  -- enforces only that `is_real` is boolean, that real rows form a
  -- prefix, and that `ptr + 1 = ptr_next`. Pointers are unique; VALUES
  -- ARE NOT. `Op::Store` witnesses its pointer as a free auxiliary column
  -- and merely requires `(channel, size, ptr, values)` to be present in
  -- the memory table, so a prover may commit two rows holding identical
  -- content and direct a store to either.
  --
  -- Consequently, comparing addresses is `address_eq` — NEVER a pointer
  -- subtraction. A raw `ptr_val` comparison is admissible in exactly two
  -- places, and both must say so at the site:
  --   1. as a fast path with a COMPLETE fallback that decides correctly
  --      when the pointers differ (`level_struct_eq`, `ind_is_solo`,
  --      `canon_cmp_kexpr_ctx`, the `k_is_def_eq` entry shortcut), or
  --   2. inside `assert_eq!`, where only the positive answer is acted on
  --      and a spurious mismatch costs completeness, never soundness.
  type Addr = &[U8; 32]

  -- Cold path of `address_eq`: byte 0 already matched, compare the other
  -- 31. A separate function on purpose — Aiur charges a function's full
  -- width on every one of its rows, so a nested match inside `address_eq`
  -- would save nothing; the split has to be a function boundary, and this
  -- circuit's height is only the rare byte-0-match rows.
  fn address_eq_tail(a: Addr, b: Addr) -> G {
    let [_, a1, a2, a3, a4, a5, a6, a7,
         a8, a9, a10, a11, a12, a13, a14, a15,
         a16, a17, a18, a19, a20, a21, a22, a23,
         a24, a25, a26, a27, a28, a29, a30, a31] = load(a);
    let [_, b1, b2, b3, b4, b5, b6, b7,
         b8, b9, b10, b11, b12, b13, b14, b15,
         b16, b17, b18, b19, b20, b21, b22, b23,
         b24, b25, b26, b27, b28, b29, b30, b31] = load(b);
    -- Pack 7 bytes per field element, base 256, then compare packed
    -- limbs: 31 matched variables become 5. A `U8` is `< 256` by type, so
    -- base-256 packing is INJECTIVE and the comparison decides byte
    -- equality exactly — unlike a weighted sum with smaller coefficients,
    -- where distinct byte strings collide and unequal addresses would
    -- compare equal. Seven is the largest safe group: `256^7 - 1 = 2^56-1`
    -- fits Goldilocks, while eight bytes would reach `2^64-1 > p` and wrap
    -- the packing back into collisions.
    -- Compared one limb at a time, each packed inside the branch that
    -- needs it: a mismatch in an early group returns without ever packing
    -- the later ones. Width is set by the widest path, so this costs the
    -- same as comparing all five at once and executes strictly less.
    let pa1 = ((((((to_field(a7) * 256) + to_field(a6)) * 256 +
                 to_field(a5)) * 256 + to_field(a4)) * 256 +
                 to_field(a3)) * 256 + to_field(a2)) * 256 + to_field(a1);
    let pb1 = ((((((to_field(b7) * 256) + to_field(b6)) * 256 +
                 to_field(b5)) * 256 + to_field(b4)) * 256 +
                 to_field(b3)) * 256 + to_field(b2)) * 256 + to_field(b1);
    match pa1 - pb1 {
      0 =>
        let pa2 = ((((((to_field(a14) * 256) + to_field(a13)) * 256 +
                     to_field(a12)) * 256 + to_field(a11)) * 256 +
                     to_field(a10)) * 256 + to_field(a9)) * 256 + to_field(a8);
        let pb2 = ((((((to_field(b14) * 256) + to_field(b13)) * 256 +
                     to_field(b12)) * 256 + to_field(b11)) * 256 +
                     to_field(b10)) * 256 + to_field(b9)) * 256 + to_field(b8);
        match pa2 - pb2 {
          0 =>
            let pa3 = ((((((to_field(a21) * 256) + to_field(a20)) * 256 +
                         to_field(a19)) * 256 + to_field(a18)) * 256 +
                         to_field(a17)) * 256 + to_field(a16)) * 256 +
                         to_field(a15);
            let pb3 = ((((((to_field(b21) * 256) + to_field(b20)) * 256 +
                         to_field(b19)) * 256 + to_field(b18)) * 256 +
                         to_field(b17)) * 256 + to_field(b16)) * 256 +
                         to_field(b15);
            match pa3 - pb3 {
              0 =>
                let pa4 = ((((((to_field(a28) * 256) + to_field(a27)) * 256 +
                             to_field(a26)) * 256 + to_field(a25)) * 256 +
                             to_field(a24)) * 256 + to_field(a23)) * 256 +
                             to_field(a22);
                let pb4 = ((((((to_field(b28) * 256) + to_field(b27)) * 256 +
                             to_field(b26)) * 256 + to_field(b25)) * 256 +
                             to_field(b24)) * 256 + to_field(b23)) * 256 +
                             to_field(b22);
                match pa4 - pb4 {
                  0 =>
                    let pa5 = ((to_field(a31) * 256) + to_field(a30)) * 256 +
                                to_field(a29);
                    let pb5 = ((to_field(b31) * 256) + to_field(b30)) * 256 +
                                to_field(b29);
                    match pa5 - pb5 {
                      0 => 1,
                      _ => 0,
                    },
                  _ => 0,
                },
              _ => 0,
            },
          _ => 0,
        },
      _ => 0,
    }
  }

  -- Content equality over all 32 bytes. Sound in BOTH directions, and
  -- therefore the only comparison that may decide anything about two
  -- addresses.
  --
  -- Byte-0 prefilter: one differing byte proves inequality, and nearly
  -- every comparison — the primitive-dispatch gauntlet in whnf above all
  -- — mismatches at byte 0, so hot rows reject at narrow width and only
  -- byte-0 matches pay the wide tail. Result is identical to a flat
  -- 32-byte compare.
  fn address_eq(a: Addr, b: Addr) -> G {
    let av = load(a);
    let bv = load(b);
    match to_field(av[0]) - to_field(bv[0]) {
      0 => address_eq_tail(a, b),
      _ => 0,
    }
  }

  fn list_length‹T›(list: List‹T›) -> G {
    match load(list) {
      ListNode.Nil => 0,
      ListNode.Cons(_, rest) => list_length(rest) + 1,
    }
  }

  fn list_length_u64‹T›(list: List‹T›) -> U64 {
    match load(list) {
      ListNode.Nil => [0u8; 8],
      ListNode.Cons(_, rest) => relaxed_u64_succ(list_length_u64(rest)),
    }
  }

  fn list_concat‹T›(a: List‹T›, b: List‹T›) -> List‹T› {
    match load(a) {
      ListNode.Nil => b,
      ListNode.Cons(v, rest) => store(ListNode.Cons(v, list_concat(rest, b))),
    }
  }

  fn list_is_empty‹T›(list: List‹T›) -> G {
    match load(list) {
      ListNode.Nil => 1,
      ListNode.Cons(_, _) => 0,
    }
  }

  fn list_lookup‹T›(list: List‹T›, idx: G) -> T {
    let ListNode.Cons(v, _) = load(list_drop(list, idx));
    v
  }

  fn list_lookup_or_default‹T›(list: List‹T›, idx: G, default: T) -> T {
    match load(list_drop(list, idx)) {
      ListNode.Nil => default,
      ListNode.Cons(v, _) => v,
    }
  }

  fn list_lookup_u64‹T›(list: List‹T›, idx: U64) -> T {
    let ListNode.Cons(v, rest) = load(list);
    let z = u64_is_zero(idx);
    match z {
      1 => v,
      0 => list_lookup_u64(rest, relaxed_u64_pred(idx)),
    }
  }

  fn list_drop‹T›(list: List‹T›, n: G) -> List‹T› {
    match n {
      0 => list,
      _ =>
        let ListNode.Cons(_, rest) = load(list_drop(list, n - 1));
        rest,
    }
  }

  fn list_take‹T›(list: List‹T›, n: G) -> List‹T› {
    match n {
      0 => store(ListNode.Nil),
      _ =>
        let ListNode.Cons(v, rest) = load(list);
        store(ListNode.Cons(v, list_take(rest, n - 1))),
    }
  }

  fn list_snoc‹T›(list: List‹T›, v: T) -> List‹T› {
    match load(list) {
      ListNode.Nil => store(ListNode.Cons(v, store(ListNode.Nil))),
      ListNode.Cons(head, rest) => store(ListNode.Cons(head, list_snoc(rest, v))),
    }
  }

  -- O(N) reverse via accumulator. Used by hot-path builders that
  -- accumulate via cons (O(1)) then reverse once instead of O(N²) snoc.
  fn list_reverse‹T›(list: List‹T›) -> List‹T› {
    list_reverse_acc(list, store(ListNode.Nil))
  }

  fn list_reverse_acc‹T›(list: List‹T›, acc: List‹T›) -> List‹T› {
    match load(list) {
      ListNode.Nil => acc,
      ListNode.Cons(head, rest) =>
        list_reverse_acc(rest, store(ListNode.Cons(head, acc))),
    }
  }
⟧

end IxVM

end
