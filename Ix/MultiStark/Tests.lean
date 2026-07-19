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
  -- Native Goldilocks arithmetic (vs `gl_ops_ref`; reference vectors kept as
  -- their canonical LE bytes and folded with `gl_val`, which is injective on
  -- canonical bytes).
  -- ==========================================================================
  fn assert_g8(x: Goldilocks, e: Goldilocks) -> G {
    assert_eq!(x, e);
    1
  }
  pub fn gl_addsub_test() -> G {
    let a = gl_val([16u8, 50u8, 84u8, 118u8, 152u8, 186u8, 220u8, 254u8]); -- 0xFEDCBA9876543210
    let b = gl_val([240u8, 222u8, 188u8, 154u8, 120u8, 86u8, 52u8, 18u8]); -- 0x123456789ABCDEF0
    assert_eq!(assert_g8(gl_add(a, b), gl_val([255u8, 16u8, 17u8, 17u8, 18u8, 17u8, 17u8, 17u8])), 1);
    assert_eq!(assert_g8(gl_sub(a, b), gl_val([32u8, 83u8, 151u8, 219u8, 31u8, 100u8, 168u8, 236u8])), 1);
    assert_eq!(assert_g8(gl_sub(b, a), gl_val([225u8, 172u8, 104u8, 36u8, 223u8, 155u8, 87u8, 19u8])), 1);
    -- edge: (p-1) + 5 ≡ 4 ; 5 - (p-1) ≡ 6
    let pm1 = gl_val([0u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8]); -- 0xFFFFFFFF00000000
    let five = gl_val([5u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
    assert_eq!(assert_g8(gl_add(pm1, five), gl_val([4u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8])), 1);
    assert_eq!(assert_g8(gl_sub(five, pm1), gl_val([6u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8])), 1);
    1
  }

  fn assert_eg(x: ExtGoldilocks, e0: Goldilocks, e1: Goldilocks) -> G {
    assert_eq!(assert_g8(x[0], e0), 1);
    assert_eq!(assert_g8(x[1], e1), 1);
    1
  }
  pub fn gl_muldiv_test() -> G {
    let a = gl_val([16u8, 50u8, 84u8, 118u8, 152u8, 186u8, 220u8, 254u8]); -- 0xFEDCBA9876543210
    let b = gl_val([240u8, 222u8, 188u8, 154u8, 120u8, 86u8, 52u8, 18u8]); -- 0x123456789ABCDEF0
    assert_eq!(assert_g8(gl_mul(a, b), gl_val([212u8, 186u8, 123u8, 108u8, 31u8, 253u8, 234u8, 250u8])), 1);
    assert_eq!(assert_g8(gl_inverse(a), gl_val([97u8, 29u8, 109u8, 46u8, 183u8, 100u8, 8u8, 102u8])), 1);
    assert_eq!(assert_g8(gl_div(a, b), gl_val([63u8, 59u8, 61u8, 54u8, 46u8, 255u8, 29u8, 186u8])), 1);
    -- edge: (p-1)·5 ≡ p-5
    let pm1 = gl_val([0u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8]);
    let five = gl_val([5u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
    assert_eq!(assert_g8(gl_mul(pm1, five), gl_val([252u8, 255u8, 255u8, 255u8, 254u8, 255u8, 255u8, 255u8])), 1);
    -- a·a⁻¹ = 1 and b·b⁻¹ = 1
    assert_eq!(assert_g8(gl_mul(a, gl_inverse(a)), gl_one()), 1);
    assert_eq!(assert_g8(gl_mul(b, gl_inverse(b)), gl_one()), 1);
    1
  }
  pub fn eg_ops_test() -> G {
    -- e0 = (0xFEDCBA9876543210, 0x0123456789ABCDEF), e1 = (0x1111111122222222, 0x3333333344444444)
    let e0 = [gl_val([16u8, 50u8, 84u8, 118u8, 152u8, 186u8, 220u8, 254u8]),
              gl_val([239u8, 205u8, 171u8, 137u8, 103u8, 69u8, 35u8, 1u8])];
    let e1 = [gl_val([34u8, 34u8, 34u8, 34u8, 17u8, 17u8, 17u8, 17u8]),
              gl_val([68u8, 68u8, 68u8, 68u8, 51u8, 51u8, 51u8, 51u8])];
    assert_eq!(assert_eg(eg_add(e0, e1),
      gl_val([49u8, 84u8, 118u8, 152u8, 170u8, 203u8, 237u8, 15u8]),
      gl_val([51u8, 18u8, 240u8, 205u8, 154u8, 120u8, 86u8, 52u8])), 1);
    assert_eq!(assert_eg(eg_mul(e0, e1),
      gl_val([10u8, 238u8, 162u8, 36u8, 224u8, 127u8, 182u8, 134u8]),
      gl_val([215u8, 234u8, 152u8, 224u8, 219u8, 254u8, 32u8, 67u8])), 1);
    assert_eq!(assert_eg(eg_inverse(e0),
      gl_val([221u8, 238u8, 29u8, 131u8, 179u8, 89u8, 214u8, 216u8]),
      gl_val([114u8, 99u8, 206u8, 108u8, 15u8, 88u8, 161u8, 246u8])), 1);
    assert_eq!(assert_eg(eg_div(e0, e1),
      gl_val([42u8, 59u8, 64u8, 77u8, 226u8, 214u8, 95u8, 63u8]),
      gl_val([200u8, 46u8, 148u8, 147u8, 124u8, 180u8, 248u8, 140u8])), 1);
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
    assert_eq!(bits_to_num(bits), 1019203);
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
    assert_eq!(apcs[0], 17795849114622667264);
    assert_eq!(apcs[1], 4116843485681689527);
    assert_eq!(afri[0], 11768399386651893439);
    assert_eq!(afri[1], 10948618071942561750);
    -- observe commit (clears output), sample β.
    let v2 = [239u8, 190u8, 173u8, 222u8, 0u8, 0u8, 0u8, 0u8]; -- 0x00000000deadbeef
    let (input, _oc) = ch_observe_val(input, v2);
    let (beta, input, _ob) = pcs_sample_ext(input, store(ListNode.Nil));
    assert_eq!(beta[0], 12096272534537655203);
    assert_eq!(beta[1], 11431251745744402868);
    -- observe final_poly coeff + log_arity (each a Val), then sample the index.
    let v3 = [4u8, 3u8, 2u8, 1u8, 13u8, 12u8, 11u8, 10u8]; -- 0x0a0b0c0d01020304
    let v4 = [2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];     -- 0x0000000000000002
    let (input, _o3) = ch_observe_val(input, v3);
    let (input, _o4) = ch_observe_val(input, v4);
    let (bits, _bi, _bo) = ch_sample_bits(input, store(ListNode.Nil), 20);
    assert_eq!(bits_to_num(bits), 458922);
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
    let e0 = [gl_val([17u8, 17u8, 17u8, 17u8, 17u8, 17u8, 17u8, 17u8]),
              gl_val([34u8, 34u8, 34u8, 34u8, 34u8, 34u8, 34u8, 34u8])];
    let e1 = [gl_val([51u8, 51u8, 51u8, 51u8, 51u8, 51u8, 51u8, 51u8]),
              gl_val([68u8, 68u8, 68u8, 68u8, 68u8, 68u8, 68u8, 68u8])];
    let beta = [gl_val([85u8, 85u8, 85u8, 85u8, 85u8, 85u8, 85u8, 85u8]),
                gl_val([102u8, 102u8, 102u8, 102u8, 102u8, 102u8, 102u8, 102u8])];
    let folded = fri_fold2(index_bits, 3, beta, e0, e1);
    assert_eq!(folded[0], 9349172584842537206);
    assert_eq!(folded[1], 984486879173118962);
    1
  }

  -- Self-test vs `ro_fold_ref`: x at index 5 / log_height 3, then accumulate
  -- (p_z − p_x)/(z − x) over 3 columns with alpha powers.
  pub fn ro_fold_test() -> G {
    let index_bits = store(ListNode.Cons(1, store(ListNode.Cons(0,
                       store(ListNode.Cons(1, store(ListNode.Nil)))))));
    let x = ro_x(index_bits, 3);
    assert_eq!(x, 117440512);
    let z = [gl_val([154u8, 120u8, 86u8, 52u8, 18u8, 0u8, 0u8, 0u8]),
             gl_val([1u8, 239u8, 205u8, 171u8, 0u8, 0u8, 0u8, 0u8])];
    let alpha = [gl_val([17u8, 17u8, 17u8, 17u8, 17u8, 17u8, 17u8, 17u8]),
                 gl_val([2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8])];
    let px0 = gl_val([11u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
    let px1 = gl_val([22u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
    let px2 = gl_val([33u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
    let p_x = store(ListNode.Cons(px0, store(ListNode.Cons(px1,
                store(ListNode.Cons(px2, store(ListNode.Nil)))))));
    let pz0 = [gl_val([100u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]), gl_val([1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8])];
    let pz1 = [gl_val([200u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]), gl_val([2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8])];
    let pz2 = [gl_val([44u8, 1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]), gl_val([3u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8])];
    let p_z = store(ListNode.Cons(pz0, store(ListNode.Cons(pz1,
                store(ListNode.Cons(pz2, store(ListNode.Nil)))))));
    let q = eg_inverse(eg_sub(z, [x, gl_zero()]));
    let (ro, _ap) = ro_fold(p_x, p_z, q, alpha, [gl_zero(), gl_zero()], [gl_one(), gl_zero()]);
    assert_eq!(ro[0], 7130765474285082575);
    assert_eq!(ro[1], 12254464995725315436);
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
    -- Leaf hashes: `blake3` over the row's canonical 8-LE-byte serialization
    -- (`SerializingHasher<Blake3>`). Reference digests from the `gen_pcs_refs`
    -- generator in `multi-stark`, cross-checked with `b3sum`.
    let d3 = mmcs_hash_row(build_range(0, 3));
    assert_eq!(assert_digest(d3, 4163513704854067712, 9384471110237386207,
                                 13671380075168847140, 1533933974187331481), 1);
    let d17 = mmcs_hash_row(build_range(0, 17));
    assert_eq!(assert_digest(d17, 8431665677194841246, 4495111673672851816,
                                  7709594803249897978, 12683511314940902790), 1);
    let d22 = mmcs_hash_row(build_range(0, 22));
    assert_eq!(assert_digest(d22, 14017803411919507972, 9236340131056405306,
                                  11356520758956579629, 2008168271701183309), 1);
    let d20 = mmcs_hash_row(build_range(0, 20));
    assert_eq!(assert_digest(d20, 8822819174011220231, 9835070768970864367,
                                  9646176123001837413, 1210344881395534089), 1);
    -- Compression: `blake3(a_bytes || b_bytes)` of two 32-byte child digests.
    let c = mmcs_compress([u64_of(1u8), u64_of(2u8), u64_of(3u8), u64_of(4u8)],
                          [u64_of(5u8), u64_of(6u8), u64_of(7u8), u64_of(8u8)]);
    assert_eq!(assert_digest(c, 16432952784711837466, 12565756115161032165,
                                6915939387221618258, 11123773279136987111), 1);
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
    let sib0 = [[229u8, 114u8, 223u8, 248u8, 35u8, 4u8, 112u8, 11u8],
                [133u8, 106u8, 85u8, 90u8, 195u8, 164u8, 85u8, 141u8],
                [13u8, 243u8, 100u8, 106u8, 55u8, 39u8, 129u8, 101u8],
                [0u8, 39u8, 10u8, 147u8, 198u8, 106u8, 172u8, 30u8]];
    let sib1 = [[234u8, 150u8, 163u8, 93u8, 30u8, 78u8, 129u8, 226u8],
                [24u8, 27u8, 220u8, 33u8, 92u8, 142u8, 194u8, 191u8],
                [193u8, 63u8, 223u8, 131u8, 67u8, 230u8, 55u8, 63u8],
                [169u8, 209u8, 214u8, 101u8, 245u8, 28u8, 141u8, 193u8]];
    let sib2 = [[167u8, 176u8, 170u8, 74u8, 66u8, 157u8, 36u8, 153u8],
                [220u8, 192u8, 39u8, 69u8, 198u8, 24u8, 123u8, 147u8],
                [63u8, 5u8, 74u8, 98u8, 77u8, 73u8, 181u8, 252u8],
                [134u8, 86u8, 33u8, 32u8, 240u8, 13u8, 134u8, 153u8]];
    let proof = store(ListNode.Cons(sib0, store(ListNode.Cons(sib1,
                  store(ListNode.Cons(sib2, store(ListNode.Nil)))))));
    let (root, capidx) = mmcs_root(rows, lhs, ibits, proof, 3);
    assert_eq!(capidx, 0);
    assert_eq!(assert_digest(root, 4722047561722553901, 2839201037098837684,
                                   4926058068911485563, 1219861215742277604), 1);
    -- tamper: perturb m0's first opened value → root must change.
    let bad0 = store(ListNode.Cons(u64_of(99u8), store(ListNode.Cons(u64_of(12u8), store(ListNode.Nil)))));
    let bad_rows = store(ListNode.Cons(bad0, store(ListNode.Cons(row1,
                     store(ListNode.Cons(row2, store(ListNode.Nil)))))));
    let cap = store(ListNode.Cons([[45u8, 230u8, 248u8, 40u8, 61u8, 21u8, 136u8, 65u8],
                                   [180u8, 102u8, 50u8, 238u8, 76u8, 222u8, 102u8, 39u8],
                                   [123u8, 114u8, 106u8, 220u8, 182u8, 223u8, 92u8, 68u8],
                                   [228u8, 55u8, 152u8, 7u8, 80u8, 209u8, 237u8, 16u8]],
                    store(ListNode.Nil)));
    assert_eq!(mmcs_verify(cap, rows, lhs, ibits, proof, 3), 1);
    assert_eq!(mmcs_verify(cap, bad_rows, lhs, ibits, proof, 3), 0);
    1
  }

  -- Differential test for the lane-granular leaf hasher: `b3_lanes` must
  -- agree with byte-granular `blake3` over the lanes' LE bytes at every
  -- structural boundary — empty input, partial block, exact block (8 lanes),
  -- block + 1, exact chunk (128 lanes), chunk + 1, a 2-chunk input with
  -- varied bytes, and a 4-chunk input (deeper layer fold). Lane bytes vary
  -- with the index so lane- or word-order bugs change the digest.
  fn lane_test_row(n: G) -> List‹U64› {
    match n {
      0 => store(ListNode.Nil),
      _ =>
        -- n mod 256, valid for n ≤ 511 (largest size used below is 500).
        let lo = u8_from_field_unsafe(n - 256 * u32_less_than(255, n));
        store(ListNode.Cons([lo, 1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8],
                            lane_test_row(n - 1))),
    }
  }
  fn lane_hash_check(n: G) -> G {
    let row = lane_test_row(n);
    digest_eq(b3_to_digest(b3_lanes(row)),
              b3_to_digest(blake3(b3_row_onto(row, store(ListNode.Nil)))))
  }
  pub fn lane_hash_test() -> G {
    lane_hash_check(0) * lane_hash_check(1) * lane_hash_check(7)
      * lane_hash_check(8) * lane_hash_check(9) * lane_hash_check(127)
      * lane_hash_check(128) * lane_hash_check(129) * lane_hash_check(255)
      * lane_hash_check(500)
  }

  -- Differential test for the IO-slice hasher: `b3_io` over the bytes the
  -- test writes to a channel arena must agree with byte-granular `blake3`
  -- over the same bytes, at the same structural boundaries as the lane test
  -- (empty, partial/exact/over block, partial/exact/over chunk, multi-chunk
  -- with layer fold). Uses `io_write` to populate channel 9 (unused by any
  -- production stream), with each length's bytes at a distinct offset.
  fn io_test_fill(n: G, off: G, b: G) -> G {
    match n {
      0 => off,
      _ =>
        -- `b` cycles 255 → 0 → 255 → …, so any length gets varied,
        -- always-in-range bytes.
        io_write(9, [b]);
        let z = eq_zero(b);
        io_test_fill(n - 1, off + 1, ((b - 1) * (1 - z)) + (255 * z)),
    }
  }
  fn io_test_bytes(n: G, off: G) -> ByteStream {
    match n {
      0 => store(ListNode.Nil),
      _ =>
        let [b] = io_read(9, off, 1);
        store(ListNode.Cons(u8_from_field_unsafe(b), io_test_bytes(n - 1, off + 1))),
    }
  }
  fn io_hash_check(n: G, off: G) -> (G, G) {
    let stop = io_test_fill(n, off, 173);
    let a = b3_io(9, off, n);
    let b = blake3(io_test_bytes(n, off));
    (digest_eq(b3_to_digest(a), b3_to_digest(b)), stop)
  }
  pub fn io_hash_test() -> G {
    let (r0, o0) = io_hash_check(0, 0);
    let (r1, o1) = io_hash_check(1, o0);
    let (r2, o2) = io_hash_check(7, o1);
    let (r3, o3) = io_hash_check(8, o2);
    let (r4, o4) = io_hash_check(63, o3);
    let (r5, o5) = io_hash_check(64, o4);
    let (r6, o6) = io_hash_check(65, o5);
    let (r7, o7) = io_hash_check(1023, o6);
    let (r8, o8) = io_hash_check(1024, o7);
    let (r9, o9) = io_hash_check(1025, o8);
    let (r10, _o10) = io_hash_check(2500, o9);
    r0 * r1 * r2 * r3 * r4 * r5 * r6 * r7 * r8 * r9 * r10
  }
⟧

end MultiStark

end
