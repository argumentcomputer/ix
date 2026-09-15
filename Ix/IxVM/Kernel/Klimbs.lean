module
public import Ix.Aiur.Meta

set_option maxRecDepth 8192

public section

namespace IxVM

/-! ## KLimbs bignum arithmetic

Bignum gadgets backing the Nat primitives (see crates/kernel/src/primitive.rs).

Kept in a module of its own, separate from the primitive dispatch that
consumes it, so the arithmetic can be read and tested without the
address-recognition machinery around it.

Ops covered:
- klimbs_succ / klimbs_dec / klimbs_add / klimbs_sub / klimbs_le /
  klimbs_is_zero / klimbs_normalize
- klimbs_mul (schoolbook) / klimbs_div / klimbs_mod / klimbs_div_mod
  (unconstrained big-uint witness)
- klimbs_gcd (Euclidean) / klimbs_pow (binary exponentiation)
- klimbs_land / klimbs_lor / klimbs_xor_op
- klimbs_shl / klimbs_shr (via mul/div by 2^n)
- u64_add / u64_mul (radix-2^16 schoolbook) / u64_sub_with_borrow /
  u64_and / u64_or / u64_xor_kbits (element-wise byte ops)
- divmod_256 (unconstrained witness generator for u32 byte decomposition)

Aiur builtin gadgets used (compiler-provided): u8_add, u8_sub,
u8_xor, u8_and, u8_or, u8_from_field_unsafe, u32_less_than,
u64_add, u64_is_zero, list_snoc, unconstrained_big_uint_div_mod,
unconstrained_g_to_bytes.
-/

set_option maxRecDepth 16384 in
def klimbs := ⟦

  -- Mirror: BigUint::succ. Increment a KLimbs by 1; ripple carry.
  fn klimbs_succ(n: KLimbs) -> KLimbs {
    match load(n) {
      ListNode.Nil =>
        store(ListNode.Cons([1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil))),
      ListNode.Cons(limb, rest) =>
        let pair = u64_add(limb, [1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
        match pair {
          (sum, carry) =>
            match carry {
              0 => store(ListNode.Cons(sum, rest)),
              _ => store(ListNode.Cons(sum, klimbs_succ(rest))),
            },
        },
    }
  }

  -- Mirror: BigUint::add. Limb-wise add with ripple carry.
  -- KLimbs are little-endian; head = least significant.
  -- Asymmetric lengths handled by terminating on shorter list and
  -- propagating carry into the longer.
  fn klimbs_add_carry(a: KLimbs, b: KLimbs, carry: G) -> KLimbs {
    match load(a) {
      ListNode.Nil =>
        match carry {
          0 => b,
          _ => klimbs_succ(b),
        },
      ListNode.Cons(la, ra) =>
        match load(b) {
          ListNode.Nil =>
            match carry {
              0 => a,
              _ => klimbs_succ(a),
            },
          ListNode.Cons(lb, rb) =>
            let pair1 = u64_add(la, lb);
            match pair1 {
              (sum1, carry1) =>
                let pair2 = u64_add(sum1, [u8_from_field_unsafe(carry), 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
                match pair2 {
                  (sum2, carry2) =>
                    -- carry1, carry2 mutually exclusive: carry1=1 ⇒ sum1 ≤
                    -- 2^64-2 ⇒ sum1 + carry_in ≤ 2^64-1 ⇒ carry2=0.
                    let total_carry = to_field(carry1) + to_field(carry2);
                    store(ListNode.Cons(sum2, klimbs_add_carry(ra, rb, total_carry))),
                },
            },
        },
    }
  }

  fn klimbs_add(a: KLimbs, b: KLimbs) -> KLimbs {
    klimbs_add_carry(a, b, 0)
  }

  -- Mirror: byte-wise u64_sub with explicit final borrow.
  -- Per-byte: u_t = borrow(a_i - b_i); u_r = borrow((a_i + 256 - b_i) - br_in).
  -- u_t = 1 ⇒ a_i + 256 - b_i ≥ 1 ⇒ subtracting br_in ∈ {0,1} cannot underflow
  -- ⇒ u_r = 0. So `u_t` and `u_r` are mutually-exclusive 0/1 values; field `+`
  -- substitutes for `g_or` (which charges +1 aux +1 lookup per call). See
  -- [[reference_aiur_carry_add]].
  fn u64_sub_with_borrow(a: U64, b: U64) -> (U64, G) {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    let (r0, br1) = u8_sub(a0, b0);
    let (t1, u_t1) = u8_sub(a1, b1);
    let (r1, u_r1) = u8_sub(t1, br1);
    let br2 = to_field(u_t1) + to_field(u_r1);
    let (t2, u_t2) = u8_sub(a2, b2);
    let (r2, u_r2) = u8_sub(t2, u8_from_field_unsafe(br2));
    let br3 = to_field(u_t2) + to_field(u_r2);
    let (t3, u_t3) = u8_sub(a3, b3);
    let (r3, u_r3) = u8_sub(t3, u8_from_field_unsafe(br3));
    let br4 = to_field(u_t3) + to_field(u_r3);
    let (t4, u_t4) = u8_sub(a4, b4);
    let (r4, u_r4) = u8_sub(t4, u8_from_field_unsafe(br4));
    let br5 = to_field(u_t4) + to_field(u_r4);
    let (t5, u_t5) = u8_sub(a5, b5);
    let (r5, u_r5) = u8_sub(t5, u8_from_field_unsafe(br5));
    let br6 = to_field(u_t5) + to_field(u_r5);
    let (t6, u_t6) = u8_sub(a6, b6);
    let (r6, u_r6) = u8_sub(t6, u8_from_field_unsafe(br6));
    let br7 = to_field(u_t6) + to_field(u_r6);
    let (t7, u_t7) = u8_sub(a7, b7);
    let (r7, u_r7) = u8_sub(t7, u8_from_field_unsafe(br7));
    let final_borrow = to_field(u_t7) + to_field(u_r7);
    ([r0, r1, r2, r3, r4, r5, r6, r7], final_borrow)
  }

  -- Mirror: BigUint::sub with saturating-at-zero (Lean Nat.sub semantics).
  -- a - b clamped to 0 when b > a.
  --
  -- Walk both lists in parallel limb-by-limb with borrow ripple. If the
  -- final borrow is 1 OR `b` has more limbs than `a`, return 0 (Nil).
  -- Otherwise normalize trailing zero limbs.
  fn klimbs_sub_borrow(a: KLimbs, b: KLimbs, borrow: G) -> (KLimbs, G) {
    match load(a) {
      ListNode.Nil =>
        match load(b) {
          ListNode.Nil =>
            -- 0 - 0 - borrow: borrow=1 → underflow.
            (store(ListNode.Nil), borrow),
          ListNode.Cons(_, _) =>
            -- 0 - non-empty. A non-empty limb list is not necessarily a
            -- non-zero number: trailing zero limbs are a valid encoding, and
            -- `klimbs_div`/`klimbs_mod` hand back the raw prover-supplied
            -- q/r, so denormalized operands do reach here. Treating every
            -- non-empty `b` as an underflow made `klimbs_le([3], [2,0])`
            -- certify "3 <= 2".
            match klimbs_is_zero(b) {
              1 => (store(ListNode.Nil), borrow),
              _ => (store(ListNode.Nil), 1),
            },
        },
      ListNode.Cons(la, ra) =>
        match load(b) {
          ListNode.Nil =>
            -- a - 0 - borrow: subtract borrow from la, propagate.
            match borrow {
              0 => (a, 0),
              _ =>
                let pair = u64_sub_with_borrow(la, [1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
                match pair {
                  (diff, br) =>
                    let pair2 = klimbs_sub_borrow(ra, store(ListNode.Nil), br);
                    match pair2 {
                      (rest_res, br2) =>
                        (store(ListNode.Cons(diff, rest_res)), br2),
                    },
                },
            },
          ListNode.Cons(lb, rb) =>
            let pair1 = u64_sub_with_borrow(la, lb);
            match pair1 {
              (sum1, br1) =>
                let pair2 = u64_sub_with_borrow(sum1, [u8_from_field_unsafe(borrow), 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
                match pair2 {
                  (sum2, br2) =>
                    -- br1, br2 mutually exclusive: br1=1 ⇒ sum1 ≥ 1 ⇒
                    -- sum1 - borrow ≥ 0 ⇒ br2=0.
                    let total = br1 + br2;
                    let rec_pair = klimbs_sub_borrow(ra, rb, total);
                    match rec_pair {
                      (rest_res, br_final) =>
                        (store(ListNode.Cons(sum2, rest_res)), br_final),
                    },
                },
            },
        },
    }
  }

  -- Convert a prover-supplied field-typed limb list into a checked
  -- `KLimbs`: every byte is forced into [0, 256) and the CHECKED outputs
  -- (typed `u8`) rebuild the limbs. This is the only door from
  -- `unconstrained_big_uint_div_mod` advice (typed `List‹[G; 8]›` by the
  -- checker precisely so it cannot pose as bytes) back into `KLimbs`.
  --
  -- `KLimbs` is canonical in two independent ways — no trailing zero
  -- limbs, and every byte in range — and `klimbs_normalize` only
  -- establishes the first. The second matters because `klimbs_eq` is a
  -- raw limb compare: a value-correct but digit-wrong `KLimbs` compares
  -- unequal to its canonical form, so `Nat.beq` answers `false` where
  -- Lean answers `true`. `u8_range_check` takes a pair per lookup row,
  -- so eight bytes cost four.
  fn glimbs_to_klimbs(n: List‹[G; 8]›) -> KLimbs {
    match load(n) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(limb, rest) =>
        let [b0, b1, b2, b3, b4, b5, b6, b7] = limb;
        let (c0, c1) = u8_range_check(b0, b1);
        let (c2, c3) = u8_range_check(b2, b3);
        let (c4, c5) = u8_range_check(b4, b5);
        let (c6, c7) = u8_range_check(b6, b7);
        store(ListNode.Cons([c0, c1, c2, c3, c4, c5, c6, c7],
          glimbs_to_klimbs(rest))),
    }
  }

  fn klimbs_normalize(n: KLimbs) -> KLimbs {
    match load(n) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(limb, rest) =>
        let normalized_rest = klimbs_normalize(rest);
        match load(normalized_rest) {
          ListNode.Nil =>
            match u64_is_zero(limb) {
              1 => store(ListNode.Nil),
              0 => store(ListNode.Cons(limb, store(ListNode.Nil))),
            },
          _ => store(ListNode.Cons(limb, normalized_rest)),
        },
    }
  }

  fn klimbs_sub(a: KLimbs, b: KLimbs) -> KLimbs {
    let pair = klimbs_sub_borrow(a, b, 0);
    match pair {
      (result, borrow) =>
        match borrow {
          1 => store(ListNode.Nil),
          0 => klimbs_normalize(result),
        },
    }
  }

  -- Mirror: Nat.le. Returns 1 if a ≤ b, 0 otherwise.
  -- Uses saturating sub: a ≤ b iff (a - b) saturates to 0.
  fn klimbs_le(a: KLimbs, b: KLimbs) -> G {
    let diff = klimbs_sub(a, b);
    match load(diff) {
      ListNode.Nil => 1,
      _ => 0,
    }
  }

  -- Mirror: Nat.pred. Saturating decrement; pred(0) = 0.
  fn klimbs_dec(a: KLimbs) -> KLimbs {
    let one = store(ListNode.Cons([1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil)));
    klimbs_sub(a, one)
  }

  -- Returns (remainder, quotient): remainder = x mod 256, quotient = x / 256.
  -- Repeated subtraction. Only invoked from the `#split_u32`
  -- unconstrained witness generator, so the O(x/256)
  -- iteration cost is off-circuit (untraced).
  fn divmod_256(x: G, q: G) -> (G, G) {
    match u32_less_than(x, 256) {
      1 => (x, q),
      0 => divmod_256(x - 256, q + 1),
    }
  }

  -- Radix-2^16 schoolbook multiplication: four digits per operand.
  -- Even with arbitrary checked carry advice, each column is < 2^35:
  -- at most four 16-bit products plus a 24-bit carry. Its reconstruction
  -- from five checked bytes is < 2^40. Both bounds are
  -- strictly below the field modulus, so field equality is integer equality.
  -- Input and output representations are unchanged (eight LE bytes per limb).
  fn u64_mul(a: U64, b: U64) -> (U64, U64) {
    let a0 = to_field(a[0]) + 256 * to_field(a[1]);
    let b0 = to_field(b[0]) + 256 * to_field(b[1]);
    let a1 = to_field(a[2]) + 256 * to_field(a[3]);
    let b1 = to_field(b[2]) + 256 * to_field(b[3]);
    let a2 = to_field(a[4]) + 256 * to_field(a[5]);
    let b2 = to_field(b[4]) + 256 * to_field(b[5]);
    let a3 = to_field(a[6]) + 256 * to_field(a[7]);
    let b3 = to_field(b[6]) + 256 * to_field(b[7]);
    let (r0, c0) = @u64_mul_column((a0 * b0));
    let (r1, c1) = @u64_mul_column((a0 * b1) + (a1 * b0) + to_field(c0[0]) + 256 * to_field(c0[1]) + 65536 * to_field(c0[2]));
    let (r2, c2) = @u64_mul_column((a0 * b2) + (a1 * b1) + (a2 * b0) + to_field(c1[0]) + 256 * to_field(c1[1]) + 65536 * to_field(c1[2]));
    let (r3, c3) = @u64_mul_column((a0 * b3) + (a1 * b2) + (a2 * b1) + (a3 * b0) + to_field(c2[0]) + 256 * to_field(c2[1]) + 65536 * to_field(c2[2]));
    let (r4, c4) = @u64_mul_column((a1 * b3) + (a2 * b2) + (a3 * b1) + to_field(c3[0]) + 256 * to_field(c3[1]) + 65536 * to_field(c3[2]));
    let (r5, c5) = @u64_mul_column((a2 * b3) + (a3 * b2) + to_field(c4[0]) + 256 * to_field(c4[1]) + 65536 * to_field(c4[2]));
    let (r6, c6) = @u64_mul_column((a3 * b3) + to_field(c5[0]) + 256 * to_field(c5[1]) + 65536 * to_field(c5[2]));
    assert_eq!(c6[2], 0u8, "u64_mul: final carry exceeds one radix digit");
    ([r0[0], r0[1], r1[0], r1[1], r2[0], r2[1], r3[0], r3[1]],
     [r4[0], r4[1], r5[0], r5[1], r6[0], r6[1], c6[0], c6[1]])
  }

  fn u64_mul_column(x: G) -> ([U8; 2], [U8; 3]) {
    let bytes = unconstrained_g_to_bytes(x);
    let (r0, r1) = u8_range_check(bytes[0], bytes[1]);
    let (c0, c1) = u8_range_check(bytes[2], bytes[3]);
    let (c2, _) = u8_range_check(bytes[4], 0);
    assert_eq!(x, to_field(r0) + 256 * to_field(r1)
      + 65536 * (to_field(c0) + 256 * to_field(c1) + 65536 * to_field(c2)),
      "u64_mul: column hint does not recompose");
    ([r0, r1], [c0, c1, c2])
  }

  -- Mirror: BigUint::mul. Limb-wise schoolbook multiply.
  fn klimbs_mul(a: KLimbs, b: KLimbs) -> KLimbs {
    klimbs_mul_outer(a, b, store(ListNode.Nil), 0)
  }

  fn klimbs_mul_outer(a: KLimbs, b: KLimbs, acc: KLimbs, shift: G) -> KLimbs {
    match load(a) {
      ListNode.Nil => acc,
      ListNode.Cons(a_limb, rest) =>
        let prod = klimbs_mul_single(a_limb, b, [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
        let shifted = klimbs_shl_limbs(prod, shift);
        let new_acc = klimbs_add(acc, shifted);
        klimbs_mul_outer(rest, b, new_acc, shift + 1),
    }
  }

  -- Build the low limb onto the recursively computed tail. Repeated snoc
  -- copied growing output prefixes; cons builds each result limb once and
  -- removes the irrelevant output prefix from the memo key. The arithmetic
  -- and the zero/trailing-limb representation are unchanged.
  fn klimbs_mul_single(a_limb: U64, b: KLimbs, carry: U64) -> KLimbs {
    match load(b) {
      ListNode.Nil =>
        match u64_is_zero(carry) {
          1 => store(ListNode.Nil),
          0 => store(ListNode.Cons(carry, store(ListNode.Nil))),
        },
      ListNode.Cons(b_limb, rest) =>
        match u64_mul(a_limb, b_limb) {
          (lo, hi) =>
            match u64_add(lo, carry) {
              (sum, carry_out) =>
                -- u64_mul range-checks ALL eight high bytes. The carry is
                -- a bit, and the old addition discarded overflow, so reuse
                -- hi or take its modular successor.
                match carry_out {
                  0 => store(ListNode.Cons(sum,
                    klimbs_mul_single(a_limb, rest, hi))),
                  _ => store(ListNode.Cons(sum,
                    klimbs_mul_single(a_limb, rest, relaxed_u64_succ(hi)))),
                },
            },
        },
    }
  }

  fn klimbs_shl_limbs(x: KLimbs, shift: G) -> KLimbs {
    match shift {
      0 => x,
      _ =>
        let prepended = store(ListNode.Cons([0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], x));
        klimbs_shl_limbs(prepended, shift - 1),
    }
  }

  fn klimbs_is_zero(x: KLimbs) -> G {
    match load(klimbs_normalize(x)) {
      ListNode.Nil => 1,
      _ => 0,
    }
  }

  -- Unconstrained Aiur op `unconstrained_big_uint_div_mod(a, b) -> (q, r)`
  -- pushes prover-supplied (q, r) into the trace map; no constraints emitted
  -- by the op itself. Caller verifies `q*b + r == a` (under normalize) and
  -- `r < b` when `b != 0`. For `b == 0` the op returns `(0, a)`; only the
  -- `q*b + r == a` equality is required (which holds: `0*0 + a == a`).
  --
  -- Soundness on the prover-supplied bytes: pinned by the range checks
  -- inside `glimbs_to_klimbs` below, NOT by the arithmetic — and the
  -- checker enforces the discipline by typing the hint `List‹[G; 8]›`,
  -- so the limbs cannot reach a `u8` consumer without that conversion.
  -- `u64_mul` uses raw field products with checked decomposition hints,
  -- whose u8 checks constrain the split OUTPUTS, not the input digits —
  -- and it re-canonicalizes while multiplying, so a digit-wrong `q`
  -- still yields a canonical `q*b` and sails through the equality below.
  -- That left the quotient's VALUE pinned but its representation free,
  -- which is enough: `klimbs_eq` compares limbs rather than values, so a
  -- digit-wrong quotient makes `Nat.beq (Nat.div 300 1) 300` answer
  -- `false`. Trailing junk limbs are caught by the post-normalize
  -- equality.
  fn klimbs_div_mod(a: KLimbs, b: KLimbs) -> (KLimbs, KLimbs) {
    let (q_hint, r_hint) = unconstrained_big_uint_div_mod(a, b);
    -- Convert (range-checking every byte), then normalize. The op is
    -- unconstrained, so nothing stops the prover returning limb lists
    -- with trailing zeros, and these values are returned to callers:
    -- `klimbs_gcd` feeds the remainder straight back as the next
    -- DIVISOR, where a trailing zero limb made the `r < b` test pass
    -- vacuously.
    let q = klimbs_normalize(glimbs_to_klimbs(q_hint));
    let r = klimbs_normalize(glimbs_to_klimbs(r_hint));
    let qb = klimbs_mul(q, b);
    let lhs = klimbs_normalize(klimbs_add(qb, r));
    let rhs = klimbs_normalize(a);
    -- Pins the unconstrained div/mod hint: q*b + r must equal a.
    assert_eq!(lhs, rhs, "div/mod hint: q*b + r != a");
    match klimbs_is_zero(b) {
      1 =>
        -- `q * 0 + r == a` pins r to a but leaves q entirely free, so
        -- without this the prover picks any quotient for `n / 0` — enough
        -- to fold `Nat.div 1 0` to 1 against Lean's `Nat.div_zero = 0`.
        assert_eq!(klimbs_is_zero(q), 1,
          "div/mod hint: division by zero must yield a zero quotient");
        (q, r),
      0 =>
        -- r < b iff (r + 1) ≤ b. One klimbs_le on klimbs_succ(r); cheapest
        -- of the sound variants empirically (vs `le(r,b)∧¬eq(r,b)` or
        -- `¬le(b,r)`).
        assert_eq!(klimbs_le(klimbs_succ(r), b), 1,
          "div/mod hint: remainder is not less than the divisor");
        (q, r),
    }
  }

  fn klimbs_div(a: KLimbs, b: KLimbs) -> KLimbs {
    match klimbs_div_mod(a, b) { (q, _) => q, }
  }

  fn klimbs_mod(a: KLimbs, b: KLimbs) -> KLimbs {
    match klimbs_div_mod(a, b) { (_, r) => r, }
  }

  fn klimbs_gcd(a: KLimbs, b: KLimbs) -> KLimbs {
    match klimbs_is_zero(b) {
      1 => a,
      0 => klimbs_gcd(b, klimbs_mod(a, b)),
    }
  }

  -- Binary exponentiation. Replaces the old O(exp) recursive
  -- `klimbs_mul(base, klimbs_pow(base, klimbs_dec(exp)))` body, which
  -- created one per-fn memo row per exponent step and OOM'd for
  -- non-trivial exponents. Recursion depth is `log2(exp)` — for
  -- `exp = 2^32` that's 32 memo entries instead of 4 billion.
  --
  -- Both `klimbs_div2` (= `klimbs_div(exp, 2)`) and `klimbs_is_odd`
  -- (= `klimbs_mod(exp, 2) != 0`) route through `klimbs_div_mod`, which
  -- is itself native (unconstrained_big_uint_div_mod) — so the
  -- division per step is O(1) work.
  fn klimbs_pow(base: KLimbs, exp: KLimbs) -> KLimbs {
    match klimbs_is_zero(exp) {
      1 => store(ListNode.Cons([1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil))),
      0 =>
        let two = store(ListNode.Cons([2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil)));
        let (half, r) = klimbs_div_mod(exp, two);
        let sq = klimbs_pow(klimbs_normalize(klimbs_mul(base, base)), klimbs_normalize(half));
        match klimbs_is_zero(r) {
          1 => sq,
          0 => klimbs_mul(base, sq),
        },
    }
  }

  -- Byte-wise AND on two U64 limbs.
  fn u64_and(a: U64, b: U64) -> U64 {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    [u8_and(a0, b0), u8_and(a1, b1), u8_and(a2, b2), u8_and(a3, b3),
     u8_and(a4, b4), u8_and(a5, b5), u8_and(a6, b6), u8_and(a7, b7)]
  }

  fn u64_or(a: U64, b: U64) -> U64 {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    [u8_or(a0, b0), u8_or(a1, b1), u8_or(a2, b2), u8_or(a3, b3),
     u8_or(a4, b4), u8_or(a5, b5), u8_or(a6, b6), u8_or(a7, b7)]
  }

  fn u64_xor_kbits(a: U64, b: U64) -> U64 {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    [u8_xor(a0, b0), u8_xor(a1, b1), u8_xor(a2, b2), u8_xor(a3, b3),
     u8_xor(a4, b4), u8_xor(a5, b5), u8_xor(a6, b6), u8_xor(a7, b7)]
  }

  -- Mirror: BigUint::bitand. Walks parallel limbs; result length = min(len(a), len(b)).
  fn klimbs_land(a: KLimbs, b: KLimbs) -> KLimbs {
    match load(a) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(la, ra) =>
        match load(b) {
          ListNode.Nil => store(ListNode.Nil),
          ListNode.Cons(lb, rb) =>
            store(ListNode.Cons(u64_and(la, lb), klimbs_land(ra, rb))),
        },
    }
  }

  -- Mirror: BigUint::bitor. Result length = max(len(a), len(b)); shorter is zero-padded.
  fn klimbs_lor(a: KLimbs, b: KLimbs) -> KLimbs {
    match load(a) {
      ListNode.Nil => b,
      ListNode.Cons(la, ra) =>
        match load(b) {
          ListNode.Nil => a,
          ListNode.Cons(lb, rb) =>
            store(ListNode.Cons(u64_or(la, lb), klimbs_lor(ra, rb))),
        },
    }
  }

  -- Mirror: BigUint::bitxor. Result length = max(len(a), len(b)); zero-padded shorter.
  fn klimbs_xor_op(a: KLimbs, b: KLimbs) -> KLimbs {
    match load(a) {
      ListNode.Nil => b,
      ListNode.Cons(la, ra) =>
        match load(b) {
          ListNode.Nil => a,
          ListNode.Cons(lb, rb) =>
            store(ListNode.Cons(u64_xor_kbits(la, lb), klimbs_xor_op(ra, rb))),
        },
    }
  }

  -- Shift left by n bits via repeated multiplication by 2.
  fn klimbs_shl(a: KLimbs, n: KLimbs) -> KLimbs {
    let two = store(ListNode.Cons([2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil)));
    klimbs_mul(a, klimbs_pow(two, n))
  }

  -- Shift right by n bits via integer division by 2^n.
  fn klimbs_shr(a: KLimbs, n: KLimbs) -> KLimbs {
    let two = store(ListNode.Cons([2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil)));
    klimbs_div(a, klimbs_pow(two, n))
  }
⟧

end IxVM

end
