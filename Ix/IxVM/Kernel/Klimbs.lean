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
- u64_add / u64_mul (byte schoolbook) / u64_sub_with_borrow /
  u64_and / u64_or / u64_xor_kbits (element-wise byte ops)
- split_carry (constant-time unconstrained byte hint for u64_mul columns)

Aiur builtin gadgets used (compiler-provided): u8_add, u8_sub,
u8_xor, u8_and, u8_or, u8_from_field_unsafe, u32_less_than,
u64_add, u64_is_zero, unconstrained_big_uint_div_mod,
#split_carry, unconstrained_g_to_bytes.
-/

set_option maxRecDepth 16384 in
def klimbs := ⟦

  -- Checked successor with carry-out. Unlike adding a whole zero-padded
  -- U64 one, this needs eight byte-add lookups instead of fifteen and its
  -- memo key holds just one limb. Every input/output byte is still checked
  -- by u8_add, including bytes above the point where carry stops.
  fn u64_succ_carry(a: U64) -> (U64, U8) {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let (s0, c1) = u8_add(a0, 1u8);
    let (s1, c2) = u8_add(a1, c1);
    let (s2, c3) = u8_add(a2, c2);
    let (s3, c4) = u8_add(a3, c3);
    let (s4, c5) = u8_add(a4, c4);
    let (s5, c6) = u8_add(a5, c5);
    let (s6, c7) = u8_add(a6, c6);
    let (s7, c8) = u8_add(a7, c7);
    ([s0, s1, s2, s3, s4, s5, s6, s7], c8)
  }

  -- Fused a + b + 1. Keep the carry-zero case on u64_add; specializing the
  -- carry-one case avoids a second full-width memo row and a second ripple
  -- over the limb. Sixteen checked byte adds versus thirty for two u64_adds.
  -- At each column the two overflow bits are mutually exclusive: if a+b
  -- overflowed, its low byte is <= 254, so adding a carry bit cannot overflow.
  fn u64_add_carry_one(a: U64, b: U64) -> (U64, U8) {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    let (t0, o0) = u8_add(a0, b0);
    let (s0, c0a) = u8_add(t0, 1u8);
    let c1 = u8_from_field_unsafe(to_field(o0) + to_field(c0a));
    let (t1, o1) = u8_add(a1, b1);
    let (s1, c1a) = u8_add(t1, c1);
    let c2 = u8_from_field_unsafe(to_field(o1) + to_field(c1a));
    let (t2, o2) = u8_add(a2, b2);
    let (s2, c2a) = u8_add(t2, c2);
    let c3 = u8_from_field_unsafe(to_field(o2) + to_field(c2a));
    let (t3, o3) = u8_add(a3, b3);
    let (s3, c3a) = u8_add(t3, c3);
    let c4 = u8_from_field_unsafe(to_field(o3) + to_field(c3a));
    let (t4, o4) = u8_add(a4, b4);
    let (s4, c4a) = u8_add(t4, c4);
    let c5 = u8_from_field_unsafe(to_field(o4) + to_field(c4a));
    let (t5, o5) = u8_add(a5, b5);
    let (s5, c5a) = u8_add(t5, c5);
    let c6 = u8_from_field_unsafe(to_field(o5) + to_field(c5a));
    let (t6, o6) = u8_add(a6, b6);
    let (s6, c6a) = u8_add(t6, c6);
    let c7 = u8_from_field_unsafe(to_field(o6) + to_field(c6a));
    let (t7, o7) = u8_add(a7, b7);
    let (s7, c7a) = u8_add(t7, c7);
    let c8 = u8_from_field_unsafe(to_field(o7) + to_field(c7a));
    ([s0, s1, s2, s3, s4, s5, s6, s7], c8)
  }

  -- Mirror: BigUint::succ. Increment a KLimbs by 1; ripple carry.
  fn klimbs_succ(n: KLimbs) -> KLimbs {
    match load(n) {
      ListNode.Nil =>
        store(ListNode.Cons([1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil))),
      ListNode.Cons(limb, rest) =>
        let pair = u64_succ_carry(limb);
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
          1 => klimbs_succ(b),
        },
      ListNode.Cons(la, ra) =>
        match load(b) {
          ListNode.Nil =>
            match carry {
              0 => a,
              1 => klimbs_succ(a),
            },
          ListNode.Cons(lb, rb) =>
            -- Dispatch before the helper call so zero carry leaves no
            -- add-zero row. The carry is a BIT, not an arbitrary byte.
            let (sum, next) = match carry {
              0 => u64_add(la, lb),
              1 => u64_add_carry_one(la, lb),
            };
            store(ListNode.Cons(sum, klimbs_add_carry(ra, rb, to_field(next)))),
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

  -- Unconstrained witness generator: split `x` into its low byte `limb`
  -- and the two bytes (clo, chi) of `x div 256`. Always invoked as
  -- `#split_carry(...)`; the result is prover-provided and MUST be pinned
  -- by the caller with u8 range checks + a reconstruction assert.
  --
  -- The native byte hint avoids repeated-subtraction division: even an
  -- unconstrained Aiur call retains memo rows, so the old O(x/256) loop
  -- consumed substantial execution time and RAM despite having no circuit.
  -- Valid u64_mul columns are < 2^19, hence the low three bytes suffice.
  -- The hint itself is NOT trusted; all existing caller checks remain.
  fn split_carry(x: G) -> (G, G, G) {
    let [limb, clo, chi, _, _, _, _, _] = unconstrained_g_to_bytes(x);
    (limb, clo, chi)
  }

  -- u64×u64 → (lo: U64, hi: U64) via byte schoolbook. Faithful port of the
  -- `MulWitness`/`Product` reference: column k is the raw field sum
  -- Σ_{i+j=k} a[i]*b[j]; each column accumulator `out` is decomposed by a
  -- prover-provided (unconstrained) split into result byte + 16-bit carry,
  -- then pinned by three u8 range checks (`u8_xor(_, 0)`) and the
  -- reconstruction assert `out == limb + 256·clo + 65536·chi`. No `u8_mul`
  -- gadget and no constrained division. Column accumulators are < 2^19, so
  -- the decomposition into (limb, clo, chi) ∈ [0,256)³ is unique → sound.
  fn u64_mul(a: U64, b: U64) -> (U64, U64) {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    let col0 = (to_field(a0) * to_field(b0));
    let col1 = (to_field(a0) * to_field(b1)) + (to_field(a1) * to_field(b0));
    let col2 = (to_field(a0) * to_field(b2)) + (to_field(a1) * to_field(b1)) + (to_field(a2) * to_field(b0));
    let col3 = (to_field(a0) * to_field(b3)) + (to_field(a1) * to_field(b2)) + (to_field(a2) * to_field(b1)) + (to_field(a3) * to_field(b0));
    let col4 = (to_field(a0) * to_field(b4)) + (to_field(a1) * to_field(b3)) + (to_field(a2) * to_field(b2)) + (to_field(a3) * to_field(b1)) + (to_field(a4) * to_field(b0));
    let col5 = (to_field(a0) * to_field(b5)) + (to_field(a1) * to_field(b4)) + (to_field(a2) * to_field(b3)) + (to_field(a3) * to_field(b2)) + (to_field(a4) * to_field(b1)) + (to_field(a5) * to_field(b0));
    let col6 = (to_field(a0) * to_field(b6)) + (to_field(a1) * to_field(b5)) + (to_field(a2) * to_field(b4)) + (to_field(a3) * to_field(b3)) + (to_field(a4) * to_field(b2)) + (to_field(a5) * to_field(b1)) + (to_field(a6) * to_field(b0));
    let col7 = (to_field(a0) * to_field(b7)) + (to_field(a1) * to_field(b6)) + (to_field(a2) * to_field(b5)) + (to_field(a3) * to_field(b4)) + (to_field(a4) * to_field(b3)) + (to_field(a5) * to_field(b2)) + (to_field(a6) * to_field(b1)) + (to_field(a7) * to_field(b0));
    let col8 = (to_field(a1) * to_field(b7)) + (to_field(a2) * to_field(b6)) + (to_field(a3) * to_field(b5)) + (to_field(a4) * to_field(b4)) + (to_field(a5) * to_field(b3)) + (to_field(a6) * to_field(b2)) + (to_field(a7) * to_field(b1));
    let col9 = (to_field(a2) * to_field(b7)) + (to_field(a3) * to_field(b6)) + (to_field(a4) * to_field(b5)) + (to_field(a5) * to_field(b4)) + (to_field(a6) * to_field(b3)) + (to_field(a7) * to_field(b2));
    let col10 = (to_field(a3) * to_field(b7)) + (to_field(a4) * to_field(b6)) + (to_field(a5) * to_field(b5)) + (to_field(a6) * to_field(b4)) + (to_field(a7) * to_field(b3));
    let col11 = (to_field(a4) * to_field(b7)) + (to_field(a5) * to_field(b6)) + (to_field(a6) * to_field(b5)) + (to_field(a7) * to_field(b4));
    let col12 = (to_field(a5) * to_field(b7)) + (to_field(a6) * to_field(b6)) + (to_field(a7) * to_field(b5));
    let col13 = (to_field(a6) * to_field(b7)) + (to_field(a7) * to_field(b6));
    let col14 = (to_field(a7) * to_field(b7));
    match #split_carry(col0) {
      (rl0, rc0, rh0) =>
        let r0 = u8_xor(u8_from_field_unsafe(rl0), 0u8);
        let lo0 = u8_xor(u8_from_field_unsafe(rc0), 0u8);
        let hi0 = u8_xor(u8_from_field_unsafe(rh0), 0u8);
        assert_eq!(col0, to_field(r0) + (256 * to_field(lo0)) + (65536 * to_field(hi0)),
          "u64_mul column 0: split_carry hint does not recompose to the column sum");
        let out1 = col1 + to_field(lo0) + (256 * to_field(hi0));
        match #split_carry(out1) {
          (rl1, rc1, rh1) =>
            let r1 = u8_xor(u8_from_field_unsafe(rl1), 0u8);
            let lo1 = u8_xor(u8_from_field_unsafe(rc1), 0u8);
            let hi1 = u8_xor(u8_from_field_unsafe(rh1), 0u8);
            assert_eq!(out1, to_field(r1) + (256 * to_field(lo1)) + (65536 * to_field(hi1)),
              "u64_mul column 1: split_carry hint does not recompose to the column sum");
            let out2 = col2 + to_field(lo1) + (256 * to_field(hi1));
            match #split_carry(out2) {
              (rl2, rc2, rh2) =>
                let r2 = u8_xor(u8_from_field_unsafe(rl2), 0u8);
                let lo2 = u8_xor(u8_from_field_unsafe(rc2), 0u8);
                let hi2 = u8_xor(u8_from_field_unsafe(rh2), 0u8);
                assert_eq!(out2, to_field(r2) + (256 * to_field(lo2)) + (65536 * to_field(hi2)),
                  "u64_mul column 2: split_carry hint does not recompose to the column sum");
                let out3 = col3 + to_field(lo2) + (256 * to_field(hi2));
                match #split_carry(out3) {
                  (rl3, rc3, rh3) =>
                    let r3 = u8_xor(u8_from_field_unsafe(rl3), 0u8);
                    let lo3 = u8_xor(u8_from_field_unsafe(rc3), 0u8);
                    let hi3 = u8_xor(u8_from_field_unsafe(rh3), 0u8);
                    assert_eq!(out3, to_field(r3) + (256 * to_field(lo3)) + (65536 * to_field(hi3)),
                      "u64_mul column 3: split_carry hint does not recompose to the column sum");
                    let out4 = col4 + to_field(lo3) + (256 * to_field(hi3));
                    match #split_carry(out4) {
                      (rl4, rc4, rh4) =>
                        let r4 = u8_xor(u8_from_field_unsafe(rl4), 0u8);
                        let lo4 = u8_xor(u8_from_field_unsafe(rc4), 0u8);
                        let hi4 = u8_xor(u8_from_field_unsafe(rh4), 0u8);
                        assert_eq!(out4, to_field(r4) + (256 * to_field(lo4)) + (65536 * to_field(hi4)),
                          "u64_mul column 4: split_carry hint does not recompose to the column sum");
                        let out5 = col5 + to_field(lo4) + (256 * to_field(hi4));
                        match #split_carry(out5) {
                          (rl5, rc5, rh5) =>
                            let r5 = u8_xor(u8_from_field_unsafe(rl5), 0u8);
                            let lo5 = u8_xor(u8_from_field_unsafe(rc5), 0u8);
                            let hi5 = u8_xor(u8_from_field_unsafe(rh5), 0u8);
                            assert_eq!(out5, to_field(r5) + (256 * to_field(lo5)) + (65536 * to_field(hi5)),
                              "u64_mul column 5: split_carry hint does not recompose to the column sum");
                            let out6 = col6 + to_field(lo5) + (256 * to_field(hi5));
                            match #split_carry(out6) {
                              (rl6, rc6, rh6) =>
                                let r6 = u8_xor(u8_from_field_unsafe(rl6), 0u8);
                                let lo6 = u8_xor(u8_from_field_unsafe(rc6), 0u8);
                                let hi6 = u8_xor(u8_from_field_unsafe(rh6), 0u8);
                                assert_eq!(out6, to_field(r6) + (256 * to_field(lo6)) + (65536 * to_field(hi6)),
                                  "u64_mul column 6: split_carry hint does not recompose to the column sum");
                                let out7 = col7 + to_field(lo6) + (256 * to_field(hi6));
                                match #split_carry(out7) {
                                  (rl7, rc7, rh7) =>
                                    let r7 = u8_xor(u8_from_field_unsafe(rl7), 0u8);
                                    let lo7 = u8_xor(u8_from_field_unsafe(rc7), 0u8);
                                    let hi7 = u8_xor(u8_from_field_unsafe(rh7), 0u8);
                                    assert_eq!(out7, to_field(r7) + (256 * to_field(lo7)) + (65536 * to_field(hi7)),
                                      "u64_mul column 7: split_carry hint does not recompose to the column sum");
                                    let out8 = col8 + to_field(lo7) + (256 * to_field(hi7));
                                    match #split_carry(out8) {
                                      (rl8, rc8, rh8) =>
                                        let r8 = u8_xor(u8_from_field_unsafe(rl8), 0u8);
                                        let lo8 = u8_xor(u8_from_field_unsafe(rc8), 0u8);
                                        let hi8 = u8_xor(u8_from_field_unsafe(rh8), 0u8);
                                        assert_eq!(out8, to_field(r8) + (256 * to_field(lo8)) + (65536 * to_field(hi8)),
                                          "u64_mul column 8: split_carry hint does not recompose to the column sum");
                                        let out9 = col9 + to_field(lo8) + (256 * to_field(hi8));
                                        match #split_carry(out9) {
                                          (rl9, rc9, rh9) =>
                                            let r9 = u8_xor(u8_from_field_unsafe(rl9), 0u8);
                                            let lo9 = u8_xor(u8_from_field_unsafe(rc9), 0u8);
                                            let hi9 = u8_xor(u8_from_field_unsafe(rh9), 0u8);
                                            assert_eq!(out9, to_field(r9) + (256 * to_field(lo9)) + (65536 * to_field(hi9)),
                                              "u64_mul column 9: split_carry hint does not recompose to the column sum");
                                            let out10 = col10 + to_field(lo9) + (256 * to_field(hi9));
                                            match #split_carry(out10) {
                                              (rl10, rc10, rh10) =>
                                                let r10 = u8_xor(u8_from_field_unsafe(rl10), 0u8);
                                                let lo10 = u8_xor(u8_from_field_unsafe(rc10), 0u8);
                                                let hi10 = u8_xor(u8_from_field_unsafe(rh10), 0u8);
                                                assert_eq!(out10, to_field(r10) + (256 * to_field(lo10)) + (65536 * to_field(hi10)),
                                                  "u64_mul column 10: split_carry hint does not recompose to the column sum");
                                                let out11 = col11 + to_field(lo10) + (256 * to_field(hi10));
                                                match #split_carry(out11) {
                                                  (rl11, rc11, rh11) =>
                                                    let r11 = u8_xor(u8_from_field_unsafe(rl11), 0u8);
                                                    let lo11 = u8_xor(u8_from_field_unsafe(rc11), 0u8);
                                                    let hi11 = u8_xor(u8_from_field_unsafe(rh11), 0u8);
                                                    assert_eq!(out11, to_field(r11) + (256 * to_field(lo11)) + (65536 * to_field(hi11)),
                                                      "u64_mul column 11: split_carry hint does not recompose to the column sum");
                                                    let out12 = col12 + to_field(lo11) + (256 * to_field(hi11));
                                                    match #split_carry(out12) {
                                                      (rl12, rc12, rh12) =>
                                                        let r12 = u8_xor(u8_from_field_unsafe(rl12), 0u8);
                                                        let lo12 = u8_xor(u8_from_field_unsafe(rc12), 0u8);
                                                        let hi12 = u8_xor(u8_from_field_unsafe(rh12), 0u8);
                                                        assert_eq!(out12, to_field(r12) + (256 * to_field(lo12)) + (65536 * to_field(hi12)),
                                                          "u64_mul column 12: split_carry hint does not recompose to the column sum");
                                                        let out13 = col13 + to_field(lo12) + (256 * to_field(hi12));
                                                        match #split_carry(out13) {
                                                          (rl13, rc13, rh13) =>
                                                            let r13 = u8_xor(u8_from_field_unsafe(rl13), 0u8);
                                                            let lo13 = u8_xor(u8_from_field_unsafe(rc13), 0u8);
                                                            let hi13 = u8_xor(u8_from_field_unsafe(rh13), 0u8);
                                                            assert_eq!(out13, to_field(r13) + (256 * to_field(lo13)) + (65536 * to_field(hi13)),
                                                              "u64_mul column 13: split_carry hint does not recompose to the column sum");
                                                            let out14 = col14 + to_field(lo13) + (256 * to_field(hi13));
                                                            match #split_carry(out14) {
                                                              (rl14, rc14, rh14) =>
                                                                let r14 = u8_xor(u8_from_field_unsafe(rl14), 0u8);
                                                                let lo14 = u8_xor(u8_from_field_unsafe(rc14), 0u8);
                                                                let hi14 = u8_xor(u8_from_field_unsafe(rh14), 0u8);
                                                                assert_eq!(out14, to_field(r14) + (256 * to_field(lo14)) + (65536 * to_field(hi14)),
                                                                  "u64_mul column 14: split_carry hint does not recompose to the column sum");
                                                                let r15 = u8_from_field_unsafe(to_field(lo14) + (256 * to_field(hi14)));
                                                                ([r0, r1, r2, r3, r4, r5, r6, r7],
                                                                 [r8, r9, r10, r11, r12, r13, r14, r15]),
                                                            },
                                                        },
                                                    },
                                                },
                                            },
                                        },
                                    },
                                },
                            },
                        },
                    },
                },
            },
        },
    }
  }

  -- Mirror: BigUint::mul. Schoolbook multiplication, streaming later product
  -- rows into the accumulator instead of retaining separate product/shifted
  -- lists. Tests/Ix/IxVM/FusedMul.lean retains the old composition and a
  -- producer/consumer fusion proof parameterized by the arithmetic steps.
  fn klimbs_mul(a: KLimbs, b: KLimbs) -> KLimbs {
    -- The first row has no accumulator and no shift. Use its already-linear
    -- builder directly: avoid recording fused-row, shift-zero and add-empty
    -- wrappers when there is no producer/consumer pair to fuse.
    match load(a) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(limb, rest) =>
        let first = klimbs_mul_single(limb, b, [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
        klimbs_mul_acc_outer(rest, b, first, 1),
    }
  }

  fn klimbs_mul_acc_outer(a: KLimbs, b: KLimbs, acc: KLimbs, shift: G) -> KLimbs {
    match load(a) {
      ListNode.Nil => acc,
      ListNode.Cons(a_limb, rest) =>
        let next = klimbs_mul_acc_shift(a_limb, b, acc, shift);
        klimbs_mul_acc_outer(rest, b, next, shift + 1),
    }
  }

  -- acc + (row << shift). Copy the unchanged low accumulator prefix but
  -- retain the old checked add-zero operation, not an assumption that loaded
  -- U64-typed fields have already been byte-range-checked. An empty product
  -- still contributes shift zero limbs, exactly like klimbs_shl_limbs.
  fn klimbs_mul_acc_shift(a: U64, b: KLimbs, acc: KLimbs, shift: G) -> KLimbs {
    match shift {
      0 => klimbs_mul_acc_row(a, b, acc, [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], 0),
      _ => match load(acc) {
        ListNode.Nil => store(ListNode.Cons([0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
          klimbs_mul_acc_shift(a, b, acc, shift - 1))),
        ListNode.Cons(limb, rest) =>
          let (sum, carry) = u64_add(limb, [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
          assert_eq!(carry, 0u8, "multiply-accumulate prefix overflow");
          store(ListNode.Cons(sum, klimbs_mul_acc_shift(a, b, rest, shift - 1))),
      },
    }
  }

  -- EXACTLY add_carry(acc, mul_single(a, b, mul_carry), add_carry).
  -- Keep the two original carries separate: no new arithmetic identity is
  -- trusted and a carry from adding the accumulator never changes the product
  -- recurrence. Only the intermediate product-list nodes disappear. Empty
  -- tails retain the existing helpers' zero/trailing-limb behavior.
  fn klimbs_mul_acc_row(a: U64, b: KLimbs, acc: KLimbs,
      mul_carry: U64, add_carry: G) -> KLimbs {
    match load(b) {
      ListNode.Nil => klimbs_add_carry(acc, klimbs_mul_single(a, b, mul_carry), add_carry),
      ListNode.Cons(b_limb, b_rest) => match load(acc) {
        ListNode.Nil => klimbs_add_carry(acc, klimbs_mul_single(a, b, mul_carry), add_carry),
        ListNode.Cons(acc_limb, acc_rest) =>
          let (lo, hi) = u64_mul(a, b_limb);
          let (digit, carry_out) = u64_add(lo, mul_carry);
          -- Branch-local continuation avoids joining a full eight-byte carry
          -- into the hot circuit. Match the already-validated row builder.
          match to_field(carry_out) {
            0 =>
              let (sum, next) = match add_carry {
                0 => u64_add(acc_limb, digit),
                1 => u64_add_carry_one(acc_limb, digit),
              };
              store(ListNode.Cons(sum,
                klimbs_mul_acc_row(a, b_rest, acc_rest, hi, to_field(next)))),
            1 =>
              let (high, overflow) = u64_succ_carry(hi);
              assert_eq!(overflow, 0u8, "multiplication row carry overflow");
              let (sum, next) = match add_carry {
                0 => u64_add(acc_limb, digit),
                1 => u64_add_carry_one(acc_limb, digit),
              };
              store(ListNode.Cons(sum,
                klimbs_mul_acc_row(a, b_rest, acc_rest, high, to_field(next)))),
          },
      },
    }
  }

  -- Build the little-endian result by consing each low limb onto the
  -- recursively computed higher limbs. The previous accumulator used
  -- list_snoc for every limb, copying prefixes quadratically and retaining
  -- their memo/memory rows. This visits each input limb once and also drops
  -- the irrelevant output prefix from the memo key.
  --
  -- For any old prefix acc: old_row(a, b, carry, acc) = acc ++ row(a, b, carry).
  -- The arithmetic relation is preserved. Keep zero limbs in the body and
  -- omit only a zero FINAL carry, exactly as before; normalization belongs
  -- to the existing callers, not this list-construction optimization.
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
                -- Keep the recursive call in each branch: joining an
                -- eight-byte carry first adds nine avoidable circuit
                -- columns. The branch-local form has the same memo rows.
                match to_field(carry_out) {
                  0 => store(ListNode.Cons(sum,
                    klimbs_mul_single(a_limb, rest, hi))),
                  1 =>
                    let (next, overflow) = u64_succ_carry(hi);
                    -- For byte-canonical operands, hi <= 2^64 - 2.
                    -- Keep that no-overflow obligation explicit.
                    assert_eq!(overflow, 0u8, "multiplication row carry overflow");
                    store(ListNode.Cons(sum,
                      klimbs_mul_single(a_limb, rest, next))),
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
  -- `u64_mul` was rewritten to raw field products plus `#split_carry`,
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
