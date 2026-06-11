module
public import Ix.Aiur.Meta

/-!
# Self-tests for the Multi-STARK recursive verifier

The `pub fn *_test` entrypoints validating the verifier's primitives against
Rust reference values (`multi-stark/src/types.rs` test outputs). They live in a
SEPARATE toplevel fragment, merged on top of the production verifier toplevel
(`MultiStark.multiStarkTests` in `Ix/MultiStark.lean`): every `pub fn` adds a
circuit to the compiled system, so keeping the tests out of
`MultiStark.multiStark` keeps the production verifier's width free of
test-only circuits.

Cross-fragment references (e.g. `gl_add`, `mmcs_hash_row`, `fri_fold2`,
`ch_sample_bits`) resolve after the merge — the merged toplevel has a flat
namespace.
-/

public section

namespace MultiStark

def tests := ⟦
  -- ==========================================================================
  -- Non-native Goldilocks byte arithmetic (vs `gl_ops_ref`).
  -- ==========================================================================
  fn assert_g8(x: Goldilocks, e: Goldilocks) -> G {
    assert_eq!(to_field(x[0]), to_field(e[0]));
    assert_eq!(to_field(x[1]), to_field(e[1]));
    assert_eq!(to_field(x[2]), to_field(e[2]));
    assert_eq!(to_field(x[3]), to_field(e[3]));
    assert_eq!(to_field(x[4]), to_field(e[4]));
    assert_eq!(to_field(x[5]), to_field(e[5]));
    assert_eq!(to_field(x[6]), to_field(e[6]));
    assert_eq!(to_field(x[7]), to_field(e[7]));
    1
  }
  pub fn gl_addsub_test() -> G {
    let a = [16u8, 50u8, 84u8, 118u8, 152u8, 186u8, 220u8, 254u8]; -- 0xFEDCBA9876543210
    let b = [240u8, 222u8, 188u8, 154u8, 120u8, 86u8, 52u8, 18u8]; -- 0x123456789ABCDEF0
    assert_eq!(assert_g8(gl_add(a, b), [255u8, 16u8, 17u8, 17u8, 18u8, 17u8, 17u8, 17u8]), 1);
    assert_eq!(assert_g8(gl_sub(a, b), [32u8, 83u8, 151u8, 219u8, 31u8, 100u8, 168u8, 236u8]), 1);
    assert_eq!(assert_g8(gl_sub(b, a), [225u8, 172u8, 104u8, 36u8, 223u8, 155u8, 87u8, 19u8]), 1);
    -- edge: (p-1) + 5 ≡ 4 ; 5 - (p-1) ≡ 6
    let pm1 = [0u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8]; -- 0xFFFFFFFF00000000
    let five = [5u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
    assert_eq!(assert_g8(gl_add(pm1, five), [4u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]), 1);
    assert_eq!(assert_g8(gl_sub(five, pm1), [6u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]), 1);
    1
  }

  fn assert_eg(x: ExtGoldilocks, e0: Goldilocks, e1: Goldilocks) -> G {
    assert_eq!(assert_g8(x[0], e0), 1);
    assert_eq!(assert_g8(x[1], e1), 1);
    1
  }
  pub fn gl_muldiv_test() -> G {
    let a = [16u8, 50u8, 84u8, 118u8, 152u8, 186u8, 220u8, 254u8]; -- 0xFEDCBA9876543210
    let b = [240u8, 222u8, 188u8, 154u8, 120u8, 86u8, 52u8, 18u8]; -- 0x123456789ABCDEF0
    assert_eq!(assert_g8(gl_mul(a, b), [212u8, 186u8, 123u8, 108u8, 31u8, 253u8, 234u8, 250u8]), 1);
    assert_eq!(assert_g8(gl_inverse(a), [97u8, 29u8, 109u8, 46u8, 183u8, 100u8, 8u8, 102u8]), 1);
    assert_eq!(assert_g8(gl_div(a, b), [63u8, 59u8, 61u8, 54u8, 46u8, 255u8, 29u8, 186u8]), 1);
    -- edge: (p-1)·5 ≡ p-5
    let pm1 = [0u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8];
    let five = [5u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
    assert_eq!(assert_g8(gl_mul(pm1, five), [252u8, 255u8, 255u8, 255u8, 254u8, 255u8, 255u8, 255u8]), 1);
    -- a·a⁻¹ = 1 and b·b⁻¹ = 1
    assert_eq!(assert_g8(gl_mul(a, gl_inverse(a)), gl_one()), 1);
    assert_eq!(assert_g8(gl_mul(b, gl_inverse(b)), gl_one()), 1);
    1
  }
  pub fn eg_ops_test() -> G {
    -- e0 = (0xFEDCBA9876543210, 0x0123456789ABCDEF), e1 = (0x1111111122222222, 0x3333333344444444)
    let e0 = [[16u8, 50u8, 84u8, 118u8, 152u8, 186u8, 220u8, 254u8],
              [239u8, 205u8, 171u8, 137u8, 103u8, 69u8, 35u8, 1u8]];
    let e1 = [[34u8, 34u8, 34u8, 34u8, 17u8, 17u8, 17u8, 17u8],
              [68u8, 68u8, 68u8, 68u8, 51u8, 51u8, 51u8, 51u8]];
    assert_eq!(assert_eg(eg_add(e0, e1),
      [49u8, 84u8, 118u8, 152u8, 170u8, 203u8, 237u8, 15u8],
      [51u8, 18u8, 240u8, 205u8, 154u8, 120u8, 86u8, 52u8]), 1);
    assert_eq!(assert_eg(eg_mul(e0, e1),
      [10u8, 238u8, 162u8, 36u8, 224u8, 127u8, 182u8, 134u8],
      [215u8, 234u8, 152u8, 224u8, 219u8, 254u8, 32u8, 67u8]), 1);
    assert_eq!(assert_eg(eg_inverse(e0),
      [221u8, 238u8, 29u8, 131u8, 179u8, 89u8, 214u8, 216u8],
      [114u8, 99u8, 206u8, 108u8, 15u8, 88u8, 161u8, 246u8]), 1);
    assert_eq!(assert_eg(eg_div(e0, e1),
      [42u8, 59u8, 64u8, 77u8, 226u8, 214u8, 95u8, 63u8],
      [200u8, 46u8, 148u8, 147u8, 124u8, 180u8, 248u8, 140u8]), 1);
    -- e0 · e0⁻¹ = 1
    assert_eq!(assert_eg(eg_mul(e0, eg_inverse(e0)), gl_one(), gl_zero()), 1);
    1
  }

  -- ==========================================================================
  -- Challenger (vs `pcs_challenger_ref` / `pcs_challenger4_ref`).
  -- ==========================================================================

  -- Self-test: `sample_bits(20)` after observing the single `Val`
  -- `0x0102030405060708` (8 LE bytes) must equal the reference `799146`
  -- (`pcs_challenger_ref` in `multi-stark/src/types.rs`).
  pub fn sample_bits_test() -> G {
    let input = store(ListNode.Cons(8u8, store(ListNode.Cons(7u8, store(ListNode.Cons(6u8,
      store(ListNode.Cons(5u8, store(ListNode.Cons(4u8, store(ListNode.Cons(3u8,
      store(ListNode.Cons(2u8, store(ListNode.Cons(1u8, store(ListNode.Nil)))))))))))))))));
    let (bits, _i, _o) = ch_sample_bits(input, store(ListNode.Nil), 20);
    assert_eq!(bits_to_num(bits), 799146);
    1
  }

  -- Self-test: replay the synthetic PCS challenger sequence from
  -- `pcs_challenger4_ref` (multi-stark/src/types.rs) and check every sampled
  -- challenge against the reference. Decisively exercises the two consecutive
  -- ext samples (α_pcs then α_fri) sharing one hash `output` stream.
  pub fn pcs_challenger4_test() -> G {
    -- post-ζ input buffer = observe V0 then V1 (forward / observation order).
    let v0 = [8u8, 7u8, 6u8, 5u8, 4u8, 3u8, 2u8, 1u8];     -- 0x0102030405060708
    let v1 = [136u8, 119u8, 102u8, 85u8, 68u8, 51u8, 34u8, 17u8]; -- 0x1122334455667788
    let input = snoc_b8(snoc_b8(store(ListNode.Nil), v0), v1);
    -- α_pcs (output empty ⇒ flush), then α_fri (CONSECUTIVE ⇒ thread output).
    let (apcs, input, o1) = pcs_sample_ext(input, store(ListNode.Nil));
    let (afri, input, o2) = pcs_sample_ext(input, o1);
    assert_eq!(limb_to_field(apcs[0]), 2882912772410685996);
    assert_eq!(limb_to_field(apcs[1]), 910933442133595775);
    assert_eq!(limb_to_field(afri[0]), 14440140149289897216);
    assert_eq!(limb_to_field(afri[1]), 8092267645441512944);
    -- observe commit (clears output), sample β.
    let v2 = [239u8, 190u8, 173u8, 222u8, 0u8, 0u8, 0u8, 0u8]; -- 0x00000000deadbeef
    let (input, _oc) = ch_observe_val(input, v2);
    let (beta, input, _ob) = pcs_sample_ext(input, store(ListNode.Nil));
    assert_eq!(limb_to_field(beta[0]), 10456048119516576995);
    assert_eq!(limb_to_field(beta[1]), 3173538015651228593);
    -- observe final_poly coeff + log_arity (each a Val), then sample the index.
    let v3 = [4u8, 3u8, 2u8, 1u8, 13u8, 12u8, 11u8, 10u8]; -- 0x0a0b0c0d01020304
    let v4 = [2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];     -- 0x0000000000000002
    let (input, _o3) = ch_observe_val(input, v3);
    let (input, _o4) = ch_observe_val(input, v4);
    let (bits, _bi, _bo) = ch_sample_bits(input, store(ListNode.Nil), 20);
    assert_eq!(bits_to_num(bits), 336138);
    1
  }

  -- ==========================================================================
  -- FRI fold + reduced openings (vs `fri_fold_ref` / `ro_fold_ref`).
  -- ==========================================================================

  -- Self-test: arity-2 fold at index 5, log_height 3 vs the `fri_fold_ref`
  -- reference (computed by the real `TwoAdicFriFolding::fold_row`).
  pub fn fri_fold_test() -> G {
    let index_bits = store(ListNode.Cons(1, store(ListNode.Cons(0,
                       store(ListNode.Cons(1, store(ListNode.Nil)))))));
    let e0 = [[17u8, 17u8, 17u8, 17u8, 17u8, 17u8, 17u8, 17u8],
              [34u8, 34u8, 34u8, 34u8, 34u8, 34u8, 34u8, 34u8]];
    let e1 = [[51u8, 51u8, 51u8, 51u8, 51u8, 51u8, 51u8, 51u8],
              [68u8, 68u8, 68u8, 68u8, 68u8, 68u8, 68u8, 68u8]];
    let beta = [[85u8, 85u8, 85u8, 85u8, 85u8, 85u8, 85u8, 85u8],
                [102u8, 102u8, 102u8, 102u8, 102u8, 102u8, 102u8, 102u8]];
    let folded = fri_fold2(index_bits, 3, beta, e0, e1);
    assert_eq!(limb_to_field(folded[0]), 9349172584842537206);
    assert_eq!(limb_to_field(folded[1]), 984486879173118962);
    1
  }

  -- Self-test vs `ro_fold_ref`: x at index 5 / log_height 3, then accumulate
  -- (p_z − p_x)/(z − x) over 3 columns with alpha powers.
  pub fn ro_fold_test() -> G {
    let index_bits = store(ListNode.Cons(1, store(ListNode.Cons(0,
                       store(ListNode.Cons(1, store(ListNode.Nil)))))));
    let x = ro_x(index_bits, 3);
    assert_eq!(limb_to_field(x), 117440512);
    let z = [[154u8, 120u8, 86u8, 52u8, 18u8, 0u8, 0u8, 0u8],
             [1u8, 239u8, 205u8, 171u8, 0u8, 0u8, 0u8, 0u8]];
    let alpha = [[17u8, 17u8, 17u8, 17u8, 17u8, 17u8, 17u8, 17u8],
                 [2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]];
    let px0 = [11u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
    let px1 = [22u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
    let px2 = [33u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
    let p_x = store(ListNode.Cons(px0, store(ListNode.Cons(px1,
                store(ListNode.Cons(px2, store(ListNode.Nil)))))));
    let pz0 = [[100u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], [1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]];
    let pz1 = [[200u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], [2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]];
    let pz2 = [[44u8, 1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], [3u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]];
    let p_z = store(ListNode.Cons(pz0, store(ListNode.Cons(pz1,
                store(ListNode.Cons(pz2, store(ListNode.Nil)))))));
    let q = eg_inverse(eg_sub(z, [x, gl_zero()]));
    let (ro, _ap) = ro_fold(p_x, p_z, q, alpha, [gl_zero(), gl_zero()], [gl_one(), gl_zero()]);
    assert_eq!(limb_to_field(ro[0]), 7130765474285082575);
    assert_eq!(limb_to_field(ro[1]), 12254464995725315436);
    1
  }

  -- ==========================================================================
  -- Keccak MMCS sponge/compression + Merkle verify_batch
  -- (vs `pcs_ref_values` / `pcs_merkle_ref`). Compares each output lane mod p
  -- via `limb_to_field` (all reference lanes are canonical, so this is exact).
  -- ==========================================================================

  -- A small single-byte value as a `U64` (8 LE bytes).
  fn u64_of(b: U8) -> U64 {
    [b, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]
  }
  -- `[i+1, i+2, …, n]` as a `List‹U64›`.
  fn build_range(i: G, n: G) -> List‹U64› {
    match n - i {
      0 => store(ListNode.Nil),
      _ => store(ListNode.Cons(u64_of(u8_from_field_unsafe(i + 1)), build_range(i + 1, n))),
    }
  }
  fn assert_digest(d: Digest, e0: G, e1: G, e2: G, e3: G) -> G {
    assert_eq!(limb_to_field(d[0]), e0);
    assert_eq!(limb_to_field(d[1]), e1);
    assert_eq!(limb_to_field(d[2]), e2);
    assert_eq!(limb_to_field(d[3]), e3);
    1
  }
  pub fn pcs_hash_test() -> G {
    -- LEAF3: hash([1,2,3])
    let d3 = mmcs_hash_row(build_range(0, 3));
    assert_eq!(assert_digest(d3, 0xc55a6a1beaea9fec, 0xc8f0dbc4c59ec440,
                                 0xacb1295de9bfe032, 0x445d569d3dfc9543), 1);
    -- LEAF17: exactly one full block, no extra permute.
    let d17 = mmcs_hash_row(build_range(0, 17));
    assert_eq!(assert_digest(d17, 0x388da73622e8fdd5, 0xec687be9c50d2218,
                                  0x528d145dfe6571af, 0xd2eb808dfba4703c), 1);
    -- LEAF22: full block + 5-element partial (two permutes), >20 lanes.
    let d22 = mmcs_hash_row(build_range(0, 22));
    assert_eq!(assert_digest(d22, 520358013996801752, 12301199992631688477,
      8732686820159480415, 10883226686987971725), 1);
    -- LEAF20: full block + 3-element partial (two permutes).
    let d20 = mmcs_hash_row(build_range(0, 20));
    assert_eq!(assert_digest(d20, 0xec696847be88d358, 0x202861c67ff4cec8,
                                  0x88e006a48aaa0661, 0xabaddb9d32ecd024), 1);
    -- COMPRESS([1,2,3,4],[5,6,7,8])
    let c = mmcs_compress([u64_of(1u8), u64_of(2u8), u64_of(3u8), u64_of(4u8)],
                          [u64_of(5u8), u64_of(6u8), u64_of(7u8), u64_of(8u8)]);
    assert_eq!(assert_digest(c, 0xda1ef0642722b22e, 0x4851efdbdb2a2fd8,
                                0x37e8ff900ea95d47, 0xa153eee7805376fb), 1);
    1
  }

  -- Merkle `verify_batch` self-test against the `pcs_merkle_ref` reference: a
  -- cap-height-0 tree over 3 matrices of heights 8/4/2 (log-heights 3/2/1),
  -- opened at index 5 (path bits 1,0,1). Checks the recomputed root matches the
  -- committed root and that the cap index is 0, then that a tampered opened row
  -- yields a different (rejected) root.
  pub fn pcs_merkle_test() -> G {
    -- opened rows (matrix order): m0 row5, m1 row2, m2 row1.
    let row0 = store(ListNode.Cons(u64_of(11u8), store(ListNode.Cons(u64_of(12u8), store(ListNode.Nil)))));
    let row1 = store(ListNode.Cons(u64_of(107u8), store(ListNode.Cons(u64_of(108u8),
                 store(ListNode.Cons(u64_of(109u8), store(ListNode.Nil)))))));
    let row2 = store(ListNode.Cons(u64_of(202u8), store(ListNode.Nil)));
    let rows = store(ListNode.Cons(row0, store(ListNode.Cons(row1,
                 store(ListNode.Cons(row2, store(ListNode.Nil)))))));
    -- log-heights and path bits (index 5 = 0b101, LSB first).
    let lhs = store(ListNode.Cons(3, store(ListNode.Cons(2, store(ListNode.Cons(1, store(ListNode.Nil)))))));
    let ibits = store(ListNode.Cons(1, store(ListNode.Cons(0, store(ListNode.Cons(1, store(ListNode.Nil)))))));
    -- authentication path SIB0, SIB1, SIB2 (each a Digest = [U64; 4]).
    let sib0 = [[9u8, 36u8, 179u8, 127u8, 205u8, 83u8, 105u8, 203u8],
                [95u8, 229u8, 105u8, 223u8, 113u8, 55u8, 97u8, 122u8],
                [135u8, 8u8, 65u8, 248u8, 163u8, 163u8, 68u8, 81u8],
                [9u8, 11u8, 20u8, 209u8, 10u8, 168u8, 151u8, 125u8]];
    let sib1 = [[227u8, 58u8, 255u8, 213u8, 77u8, 152u8, 42u8, 77u8],
                [113u8, 86u8, 2u8, 151u8, 97u8, 63u8, 58u8, 45u8],
                [228u8, 139u8, 228u8, 194u8, 182u8, 115u8, 107u8, 221u8],
                [248u8, 16u8, 30u8, 93u8, 176u8, 36u8, 205u8, 88u8]];
    let sib2 = [[236u8, 144u8, 115u8, 218u8, 140u8, 5u8, 86u8, 229u8],
                [95u8, 186u8, 252u8, 175u8, 21u8, 247u8, 153u8, 25u8],
                [113u8, 78u8, 92u8, 200u8, 212u8, 175u8, 247u8, 47u8],
                [78u8, 145u8, 206u8, 54u8, 175u8, 155u8, 165u8, 206u8]];
    let proof = store(ListNode.Cons(sib0, store(ListNode.Cons(sib1,
                  store(ListNode.Cons(sib2, store(ListNode.Nil)))))));
    let (root, capidx) = mmcs_root(rows, lhs, ibits, proof, 3);
    assert_eq!(capidx, 0);
    assert_eq!(assert_digest(root, 0x6211b9a1a116a006, 0x435ee98e1504880f,
                                   0x900c7274b9a215f, 0xf6e3aaac5dcd90bd), 1);
    -- tamper: perturb m0's first opened value → root must change.
    let bad0 = store(ListNode.Cons(u64_of(99u8), store(ListNode.Cons(u64_of(12u8), store(ListNode.Nil)))));
    let bad_rows = store(ListNode.Cons(bad0, store(ListNode.Cons(row1,
                     store(ListNode.Cons(row2, store(ListNode.Nil)))))));
    let cap = store(ListNode.Cons([[6u8, 160u8, 22u8, 161u8, 161u8, 185u8, 17u8, 98u8],
                                   [15u8, 136u8, 4u8, 21u8, 142u8, 233u8, 94u8, 67u8],
                                   [95u8, 33u8, 154u8, 75u8, 39u8, 199u8, 0u8, 9u8],
                                   [189u8, 144u8, 205u8, 93u8, 172u8, 170u8, 227u8, 246u8]],
                    store(ListNode.Nil)));
    assert_eq!(mmcs_verify(cap, rows, lhs, ibits, proof, 3), 1);
    assert_eq!(mmcs_verify(cap, bad_rows, lhs, ibits, proof, 3), 0);
    1
  }
⟧

end MultiStark

end
