//! CPU BN254 multi-scalar multiplication using the GLV 2D endomorphism,
//! signed-digit window recoding, bucket sharding and batched affine additions.
//!
//! On BN254 (`y^2 = x^3 + 3`), the endomorphism `ψ(x, y) = (β·x, y)` satisfies
//! `ψ(P) = λ·P` for every `P ∈ G1`. Babai rounding on the 2D GLV lattice splits
//! any scalar `s ∈ [0, r)` into `s ≡ k1 + k2·λ (mod r)` with `|k1|, |k2| < 2^126`,
//! halving the scalar bit-width and number of Pippenger windows. Signed digits
//! halve the bucket count per window (`2^{c-1}`), and sharding buckets into
//! L2-cache-sized ranges exposes full core parallelism without duplicating
//! buckets across threads.

use std::collections::HashMap;

use ark_bn254::g1::Config as Bn254G1Config;
use ark_ec::scalar_mul::glv::GLVConfig;
use ark_ec::{AdditiveGroup, VariableBaseMSM};
use ark_ff::{Field as ArkField, PrimeField, Zero};
use p3_maybe_rayon::prelude::*;

use super::curve::{Fq, Fr, G1Affine, G1Projective};

/// Primitive cube root of unity `β ∈ Fq` satisfying `(β·x, y) = λ·(x, y)`.
const BETA: Fq = Bn254G1Config::ENDO_COEFFS[0];

// BN254 GLV short lattice basis `(v1, v2)` matching `ark_bn254::g1::Config`:
//   v1 = (-A1, +B1),  v2 = (-A2, -B2)   with A2 == B1, B2 == A1 + B1,
//   -A1 + B1·λ ≡ 0 (mod r), -A2 - B2·λ ≡ 0 (mod r), A1·B2 + A2·B1 = r.
const A1: u128 = 0x6f4d_8248_eeb8_59fc_8211_bbeb_7d4f_1128;
const B1: u64 = 0x89d3_2568_94d2_13e3;
const B2: u128 = 0x6f4d_8248_eeb8_59fd_0be4_e154_1221_250b;

// Precomputed Babai multipliers scaled by 2^260:
//   G1 = round(B2 · 2^260 / r),  G2 = round(B1 · 2^260 / r).
// With shift = 260, rounding error is <= 0.5 + 0.5·r/2^260 < 0.506, guaranteeing
// |k1|, |k2| < 0.88 · 2^126 < 2^126 for every scalar s ∈ [0, r).
const G1: [u64; 3] = [0x398f_d030_0ff6_5651, 0xccef_014a_773d_2d25, 0x24];
const G2: [u64; 2] = [0x91d2_32ec_7e0b_3d77, 0x2d];

/// Bit bound on `|k1|` and `|k2|` (strictly `< 2^126`).
const HALF_SCALAR_BITS: usize = 126;
/// Sign bit packed in the MSB of a `u128` half-scalar (`|k| < 2^126`).
const SIGN_BIT: u128 = 1u128 << 127;
const MAG_MASK: u128 = SIGN_BIT - 1;

/// Flags packed into each `u32` scatter entry.
const NEG_BIT: u32 = 1u32 << 31;
const GLV_BIT: u32 = 1u32 << 30;
const IDX_MASK: u32 = (1u32 << 30) - 1;

/// Maximum point slice processed in a single scatter pass (fits 30-bit index).
const MAX_PASS_POINTS: usize = 1 << 28;

/// Batch size for Montgomery-batched affine bucket additions.
const AFFINE_BATCH: usize = 512;

/// Software prefetch lead distance (in points) for `bases` reads during
/// shard accumulation.
const PREFETCH_DIST: usize = 16;

/// Target buckets per shard (8192 × 64 B = 512 KiB, L2-resident).
const MAX_SHARD_BITS: usize = 13;
const MIN_SHARD_BITS: usize = 6;

/// Small-window threshold below which direct thread-local reduction beats scatter.
const DIRECT_WINDOW_MAX_BUCKETS: usize = 128;

/// Decomposed scalar `s ≡ ±k1 ± k2·λ (mod r)`, with sign packed in bit 127.
#[derive(Clone, Copy, Default)]
struct GlvScalar {
  k1: u128,
  k2: u128,
}

/// 64-byte cache-line-aligned affine bucket coordinates (occupancy tracked in a
/// separate compact bitset so empty buckets take zero field multiplications).
#[derive(Clone, Copy, Default)]
#[repr(C, align(64))]
struct AffineBucket {
  x: Fq,
  y: Fq,
}

#[derive(Clone, Copy)]
struct BatchOp {
  bucket: u16,
  qx: Fq,
  qy: Fq,
}

#[derive(Clone, Copy)]
struct SendMutPtr<T>(*mut T);

// SAFETY: Used only to scatter into disjoint index ranges verified by prefix sum.
unsafe impl<T: Send> Send for SendMutPtr<T> {}
unsafe impl<T: Send> Sync for SendMutPtr<T> {}

#[inline]
#[allow(clippy::cast_possible_truncation)]
const fn split_u128(x: u128) -> (u64, u64) {
  (x as u64, (x >> 64) as u64)
}

/// Compute `((s * g) + 2^259) >> 260` for a 4-limb canonical scalar `s < r`
/// and a 3-limb constant `g`.
#[inline]
fn mul_4x3_shr260_round(s: [u64; 4], g: [u64; 3]) -> u128 {
  let mut p = [0u64; 7];
  for i in 0..4 {
    let si = u128::from(s[i]);
    let mut carry = 0u64;
    for j in 0..3 {
      let acc =
        u128::from(p[i + j]) + si * u128::from(g[j]) + u128::from(carry);
      let (lo, hi) = split_u128(acc);
      p[i + j] = lo;
      carry = hi;
    }
    p[i + 3] = carry;
  }
  // Add 2^259 (bit 3 of limb 4) for nearest-integer rounding before >> 260.
  let (r4, c4) = p[4].overflowing_add(1u64 << 3);
  let (r5, c5) = p[5].overflowing_add(u64::from(c4));
  let r6 = p[6].wrapping_add(u64::from(c5));
  let lo = (r4 >> 4) | (r5 << 60);
  let hi = (r5 >> 4) | (r6 << 60);
  u128::from(lo) | (u128::from(hi) << 64)
}

/// Compute `((s * g) + 2^259) >> 260` for a 4-limb canonical scalar `s < r`
/// and a 2-limb constant `g`.
#[inline]
fn mul_4x2_shr260_round(s: [u64; 4], g: [u64; 2]) -> u64 {
  let mut p = [0u64; 6];
  for i in 0..4 {
    let si = u128::from(s[i]);
    let mut carry = 0u64;
    for j in 0..2 {
      let acc =
        u128::from(p[i + j]) + si * u128::from(g[j]) + u128::from(carry);
      let (lo, hi) = split_u128(acc);
      p[i + j] = lo;
      carry = hi;
    }
    p[i + 2] = carry;
  }
  let (r4, c4) = p[4].overflowing_add(1u64 << 3);
  let r5 = p[5].wrapping_add(u64::from(c4));
  (r4 >> 4) | (r5 << 60)
}

/// Decompose a BN254 scalar into `(k1, k2)` with `s ≡ k1 + k2·λ (mod r)` and
/// `|k1|, |k2| < 2^126`, returning `(k1, k2)` packed with sign in bit 127.
#[inline]
fn decompose_glv(scalar: Fr) -> GlvScalar {
  if scalar.is_zero() {
    return GlvScalar::default();
  }
  let s = scalar.into_bigint().0;
  let c1 = mul_4x3_shr260_round(s, G1);
  let c2 = mul_4x2_shr260_round(s, G2);
  // Both |k1| and |k2| are strictly < 2^126 < 2^127, so their exact signed
  // values are uniquely determined by their low 128 bits as i128.
  let s_lo = u128::from(s[0]) | (u128::from(s[1]) << 64);
  let c2_128 = u128::from(c2);
  let b1_128 = u128::from(B1);
  let k1 = i128::from_ne_bytes(
    s_lo
      .wrapping_sub(c1.wrapping_mul(A1))
      .wrapping_sub(c2_128.wrapping_mul(b1_128))
      .to_ne_bytes(),
  );
  let k2 = i128::from_ne_bytes(
    c1.wrapping_mul(b1_128).wrapping_sub(c2_128.wrapping_mul(B2)).to_ne_bytes(),
  );
  let mag1 = k1.unsigned_abs();
  let mag2 = k2.unsigned_abs();
  debug_assert!(mag1 < (1u128 << HALF_SCALAR_BITS));
  debug_assert!(mag2 < (1u128 << HALF_SCALAR_BITS));
  GlvScalar {
    k1: if k1 < 0 { mag1 | SIGN_BIT } else { mag1 },
    k2: if k2 < 0 { mag2 | SIGN_BIT } else { mag2 },
  }
}

/// Number of signed windows of width `c` covering `[0, 2^126)` with digits in
/// `[-(2^{c-1}-1), 2^{c-1}]` (top window in `[0, 2^{c-1}]`).
#[inline]
const fn num_windows_for(c: usize) -> usize {
  (HALF_SCALAR_BITS + 1).div_ceil(c)
}

/// Maximum positive bucket index needed by window `w` (`0..num_windows`).
#[inline]
const fn buckets_for_window(w: usize, c: usize, num_windows: usize) -> usize {
  let half = 1usize << (c - 1);
  if w + 1 < num_windows {
    half
  } else {
    let shift = w * c;
    let rem_bits = HALF_SCALAR_BITS - shift;
    // `k < 2^126`, so `(k >> shift) + carry <= 2^rem_bits <= 2^{c-1}`.
    let top = 1usize << rem_bits;
    if top < half { top } else { half }
  }
}

/// Precomputed O(1) signed-digit extraction parameters for one window `w`.
#[derive(Clone, Copy)]
struct WindowParams {
  shift: usize,
  mask: u128,
  half: u128,
  lo_mask: u128,
  carry_threshold: u128,
  is_last: bool,
}

impl WindowParams {
  const fn new(w: usize, c: usize, num_windows: usize) -> Self {
    let shift = w * c;
    let mask = (1u128 << c) - 1;
    let half = 1u128 << (c - 1);
    let lo_mask = if shift == 0 { 0 } else { (1u128 << shift) - 1 };
    // Max value of `k mod 2^(w*c)` that produces zero carry into window `w`:
    //   Σ_{j=0}^{w-1} 2^(j*c + c - 1).
    let mut carry_threshold = 0u128;
    let mut j = 0usize;
    while j < w {
      carry_threshold |= 1u128 << (j * c + c - 1);
      j += 1;
    }
    Self {
      shift,
      mask,
      half,
      lo_mask,
      carry_threshold,
      is_last: w + 1 >= num_windows,
    }
  }

  /// Extract the `w`-th signed digit of unsigned `k < 2^126` in O(1) time.
  /// Returns a value in `[-(2^{c-1}-1), 2^{c-1}]` for `w + 1 < num_windows`,
  /// and in `[0, buckets_for_window(w, c, num_windows)]` for the top window.
  #[inline]
  #[allow(clippy::cast_possible_truncation)]
  const fn digit(self, k: u128) -> i32 {
    let carry = ((k & self.lo_mask) > self.carry_threshold) as u128;
    let raw = ((k >> self.shift) & self.mask) + carry;
    if !self.is_last && raw > self.half {
      -((self.mask + 1 - raw) as i32)
    } else {
      raw as i32
    }
  }
}

/// Extract the `w`-th signed digit of unsigned `k < 2^126` in radix `2^c`.
#[cfg(test)]
#[inline]
fn window_digit(k: u128, w: usize, c: usize, num_windows: usize) -> i32 {
  WindowParams::new(w, c, num_windows).digit(k)
}

/// Choose a Pareto-optimal signed-digit window width for `n` BN254 points
/// (`2n` 126-bit GLV half-scalars).
fn choose_window(n: usize) -> usize {
  // Pareto-optimal widths for 127-bit signed recoding:
  //   c=8 (W=16), c=10 (W=13), c=12 (W=11), c=13 (W=10),
  //   c=15 (W=9), c=16 (W=8), c=19 (W=7), c=21 (6 full + 1-bucket top), c=22 (W=6).
  match n {
    0..=255 => 8,
    256..=1023 => 10,
    1024..=4095 => 12,
    4096..=16_383 => 13,
    16_384..=65_535 => 15,
    65_536..=2_097_151 => 16,
    2_097_152..=8_388_607 => 19,
    8_388_608..=33_554_432 => 21,
    _ => 22,
  }
}

/// Compute `Σ bases[i] * scalars[i]` on CPU using GLV + signed-digit
/// bucket-sharded Pippenger with batched affine additions.
pub(super) fn msm(bases: &[G1Affine], scalars: &[Fr]) -> G1Projective {
  assert_eq!(bases.len(), scalars.len());
  let n = bases.len();
  if n == 0 {
    return G1Projective::zero();
  }
  if n < 64 {
    return G1Projective::msm(bases, scalars).expect("equal lengths");
  }
  let mut total = G1Projective::zero();
  for (b_chunk, s_chunk) in
    bases.chunks(MAX_PASS_POINTS).zip(scalars.chunks(MAX_PASS_POINTS))
  {
    let c = choose_window(b_chunk.len());
    total += msm_with_window(b_chunk, s_chunk, c);
  }
  total
}

/// Core GLV + signed-digit MSM parameterized by window width `c` (`2..=22`).
fn msm_with_window(
  bases: &[G1Affine],
  scalars: &[Fr],
  c: usize,
) -> G1Projective {
  debug_assert_eq!(bases.len(), scalars.len());
  debug_assert!((2..=22).contains(&c));
  let n = bases.len();
  if n == 0 {
    return G1Projective::zero();
  }
  debug_assert!(n <= MAX_PASS_POINTS);

  // Phase 0: parallel GLV decomposition of all scalars (zeroing any scalar
  // paired with the point at infinity so later phases skip infinity checks).
  let mut glv = vec![GlvScalar::default(); n];
  let chunk = n.div_ceil(current_num_threads().max(1) * 4).max(1 << 12);
  glv
    .par_chunks_mut(chunk)
    .zip(scalars.par_chunks(chunk))
    .zip(bases.par_chunks(chunk))
    .for_each(|((out, s_chunk), b_chunk)| {
      for ((dst, &s), base) in out.iter_mut().zip(s_chunk).zip(b_chunk) {
        if !base.infinity && !s.is_zero() {
          *dst = decompose_glv(s);
        }
      }
    });

  let num_windows = num_windows_for(c);
  // Reusable scatter buffers shared across all windows to bound peak RSS.
  let mut shard_points: Vec<u32> = Vec::new();
  let mut shard_buckets: Vec<u16> = Vec::new();

  let mut window_sums = vec![G1Projective::zero(); num_windows];
  for (w, slot) in window_sums.iter_mut().enumerate() {
    let num_buckets = buckets_for_window(w, c, num_windows);
    *slot = if num_buckets <= DIRECT_WINDOW_MAX_BUCKETS {
      accumulate_small_window(bases, &glv, w, c, num_windows, num_buckets)
    } else {
      accumulate_sharded_window(
        bases,
        &glv,
        w,
        c,
        num_windows,
        num_buckets,
        &mut shard_points,
        &mut shard_buckets,
      )
    };
  }

  // Combine window sums via Horner's method from highest window to lowest.
  let mut total = G1Projective::zero();
  for &sum in window_sums[1..].iter().rev() {
    total += sum;
    for _ in 0..c {
      total.double_in_place();
    }
  }
  total + window_sums[0]
}

/// Direct thread-local reduction for tiny top windows (`<= 128` buckets).
fn accumulate_small_window(
  bases: &[G1Affine],
  glv: &[GlvScalar],
  w: usize,
  c: usize,
  num_windows: usize,
  num_buckets: usize,
) -> G1Projective {
  let n = bases.len();
  let wp = WindowParams::new(w, c, num_windows);
  let chunk = n.div_ceil(current_num_threads().max(1) * 4).max(1 << 12);
  let buckets = glv
    .par_chunks(chunk)
    .zip(bases.par_chunks(chunk))
    .fold(
      || vec![G1Projective::zero(); num_buckets],
      |mut local, (g_chunk, b_chunk)| {
        for (g, base) in g_chunk.iter().zip(b_chunk) {
          let mag1 = g.k1 & MAG_MASK;
          if mag1 != 0 {
            let d = wp.digit(mag1);
            if d != 0 {
              let neg = ((g.k1 & SIGN_BIT) != 0) ^ (d < 0);
              let bucket = usize::try_from(d.unsigned_abs()).unwrap() - 1;
              let pt = if neg { -*base } else { *base };
              local[bucket] += pt;
            }
          }
          let mag2 = g.k2 & MAG_MASK;
          if mag2 != 0 {
            let d = wp.digit(mag2);
            if d != 0 {
              let neg = ((g.k2 & SIGN_BIT) != 0) ^ (d < 0);
              let bucket = usize::try_from(d.unsigned_abs()).unwrap() - 1;
              let qx = base.x * BETA;
              let qy = if neg { -base.y } else { base.y };
              local[bucket] += G1Affine::new_unchecked(qx, qy);
            }
          }
        }
        local
      },
    )
    .reduce(
      || vec![G1Projective::zero(); num_buckets],
      |mut a, b| {
        for (x, y) in a.iter_mut().zip(b) {
          *x += y;
        }
        a
      },
    );
  let mut running = G1Projective::zero();
  let mut triangle = G1Projective::zero();
  for b in buckets.into_iter().rev() {
    running += b;
    triangle += running;
  }
  triangle
}

/// Choose `shard_bits` so each shard owns `1 << shard_bits` buckets, fits in
/// L2 cache (`<= 8192` buckets = 512 KiB), and provides enough shards to keep
/// all Rayon threads busy with low straggler tail.
fn choose_shard_bits(num_buckets: usize) -> usize {
  let threads = current_num_threads().max(1);
  let target_shards = (threads * 4).max(1);
  let mut bits = MAX_SHARD_BITS;
  while bits > MIN_SHARD_BITS
    && num_buckets.div_ceil(1usize << bits) < target_shards
  {
    bits -= 1;
  }
  bits
}

/// Bucket-sharded accumulation for one window `w`.
#[allow(clippy::too_many_arguments)]
fn accumulate_sharded_window(
  bases: &[G1Affine],
  glv: &[GlvScalar],
  w: usize,
  c: usize,
  num_windows: usize,
  num_buckets: usize,
  shard_points: &mut Vec<u32>,
  shard_buckets: &mut Vec<u16>,
) -> G1Projective {
  let n = bases.len();
  let wp = WindowParams::new(w, c, num_windows);
  let shard_bits = choose_shard_bits(num_buckets);
  let stride = 1usize << shard_bits;
  let local_mask = stride - 1;
  let num_shards = num_buckets.div_ceil(stride);

  // Partition input indices into blocks for lock-free parallel count + scatter.
  let threads = current_num_threads().max(1);
  let num_blocks = (threads * 2).min(n.div_ceil(1 << 12)).max(1);
  let block_len = n.div_ceil(num_blocks);

  // Pass 1: count entries per (block, shard).
  let block_counts: Vec<Vec<usize>> = (0..num_blocks)
    .into_par_iter()
    .map(|block| {
      let start = block * block_len;
      let end = (start + block_len).min(n);
      let mut counts = vec![0usize; num_shards];
      for g in &glv[start..end] {
        let mag1 = g.k1 & MAG_MASK;
        if mag1 != 0 {
          let d = wp.digit(mag1);
          if d != 0 {
            let b = usize::try_from(d.unsigned_abs()).unwrap() - 1;
            counts[b >> shard_bits] += 1;
          }
        }
        let mag2 = g.k2 & MAG_MASK;
        if mag2 != 0 {
          let d = wp.digit(mag2);
          if d != 0 {
            let b = usize::try_from(d.unsigned_abs()).unwrap() - 1;
            counts[b >> shard_bits] += 1;
          }
        }
      }
      counts
    })
    .collect();

  // Prefix-sum counts into shard ranges and per-(block, shard) write offsets.
  let mut shard_starts = vec![0usize; num_shards + 1];
  let mut block_offsets = vec![vec![0usize; num_shards]; num_blocks];
  let mut cursor = 0usize;
  for shard in 0..num_shards {
    shard_starts[shard] = cursor;
    for block in 0..num_blocks {
      block_offsets[block][shard] = cursor;
      cursor += block_counts[block][shard];
    }
  }
  shard_starts[num_shards] = cursor;
  let total_entries = cursor;
  if total_entries == 0 {
    return G1Projective::zero();
  }

  // Reserve reusable scatter buffers without serial zero-fill; Pass 2 writes
  // every index in `0..total_entries` exactly once before Pass 3 reads them.
  shard_points.clear();
  shard_points.reserve(total_entries);
  shard_buckets.clear();
  shard_buckets.reserve(total_entries);

  // Pass 2: parallel lock-free scatter into disjoint per-(block, shard) spans.
  // Each (block, shard) writes exclusively to `[offset, offset + count)`, which
  // are mutually disjoint across all blocks by the prefix sum above.
  let pts_ptr = SendMutPtr(shard_points.as_mut_ptr());
  let bkts_ptr = SendMutPtr(shard_buckets.as_mut_ptr());
  block_offsets.into_par_iter().enumerate().for_each(|(block, mut offsets)| {
    let start = block * block_len;
    let end = (start + block_len).min(n);
    let pts = pts_ptr;
    let bkts = bkts_ptr;
    for (idx, g) in glv[start..end].iter().enumerate() {
      let point_idx = u32::try_from(start + idx).expect("index fits u30");
      let mag1 = g.k1 & MAG_MASK;
      if mag1 != 0 {
        let d = wp.digit(mag1);
        if d != 0 {
          let neg = ((g.k1 & SIGN_BIT) != 0) ^ (d < 0);
          let b = usize::try_from(d.unsigned_abs()).unwrap() - 1;
          let shard = b >> shard_bits;
          let pos = offsets[shard];
          offsets[shard] = pos + 1;
          let entry = point_idx | if neg { NEG_BIT } else { 0 };
          let local_b = u16::try_from(b & local_mask).expect("fits u16");
          // SAFETY: Every (block, shard) owns a unique, non-overlapping range
          // within `0..total_entries` constructed by the prefix sum above.
          unsafe {
            pts.0.add(pos).write(entry);
            bkts.0.add(pos).write(local_b);
          }
        }
      }
      let mag2 = g.k2 & MAG_MASK;
      if mag2 != 0 {
        let d = wp.digit(mag2);
        if d != 0 {
          let neg = ((g.k2 & SIGN_BIT) != 0) ^ (d < 0);
          let b = usize::try_from(d.unsigned_abs()).unwrap() - 1;
          let shard = b >> shard_bits;
          let pos = offsets[shard];
          offsets[shard] = pos + 1;
          let entry = point_idx | GLV_BIT | if neg { NEG_BIT } else { 0 };
          let local_b = u16::try_from(b & local_mask).expect("fits u16");
          // SAFETY: Same disjoint range invariant as above.
          unsafe {
            pts.0.add(pos).write(entry);
            bkts.0.add(pos).write(local_b);
          }
        }
      }
    }
  });
  // SAFETY: Pass 2 initialized every index `0..total_entries` in both buffers
  // (`u32` and `u16` are `Copy` and `reserve(total_entries)` ensured capacity).
  unsafe {
    shard_points.set_len(total_entries);
    shard_buckets.set_len(total_entries);
  }

  // Pass 3: accumulate and reduce each shard in parallel with L2-resident
  // affine buckets.
  let pts_slice: &[u32] = shard_points;
  let bkts_slice: &[u16] = shard_buckets;
  let overload_threshold = (total_entries / 2).max(65_536);

  let shard_results: Vec<(G1Projective, G1Projective)> = (0..num_shards)
    .into_par_iter()
    .map_init(
      || ShardScratch::new(stride),
      |scratch, shard| {
        let lo = shard_starts[shard];
        let hi = shard_starts[shard + 1];
        if lo == hi {
          return (G1Projective::zero(), G1Projective::zero());
        }
        let b_len = (num_buckets - shard * stride).min(stride);
        let pts = &pts_slice[lo..hi];
        let bkts = &bkts_slice[lo..hi];
        if num_shards > 1 && pts.len() > overload_threshold {
          // Heavily skewed scalars (e.g. all-ones columns) can funnel most
          // entries into a single shard; split that shard across cores.
          let sub_chunk = pts.len().div_ceil(threads * 2).max(1 << 14);
          return pts
            .par_chunks(sub_chunk)
            .zip(bkts.par_chunks(sub_chunk))
            .map_init(
              || ShardScratch::new(b_len),
              |sub, (p, b)| sub.accumulate_and_reduce(bases, p, b, b_len),
            )
            .reduce(
              || (G1Projective::zero(), G1Projective::zero()),
              |(r0, t0), (r1, t1)| (r0 + r1, t0 + t1),
            );
        }
        scratch.accumulate_and_reduce(bases, pts, bkts, b_len)
      },
    )
    .collect();

  // Fold shard `(running, triangle)` pairs into the window sum:
  //   Σ_{s=0}^{S-1} triangle_s + stride · Σ_{s=1}^{S-1} s · running_s.
  let mut total = G1Projective::zero();
  for &(_, triangle) in &shard_results {
    total += triangle;
  }
  let mut shard_run = G1Projective::zero();
  let mut shard_tri = G1Projective::zero();
  for &(running, _) in shard_results[1..].iter().rev() {
    shard_run += running;
    shard_tri += shard_run;
  }
  for _ in 0..shard_bits {
    shard_tri.double_in_place();
  }
  total + shard_tri
}

/// Thread-local reusable buffers for accumulating one bucket shard.
struct ShardScratch {
  buckets: Vec<AffineBucket>,
  occupied: Vec<u64>,
  in_batch: Vec<u64>,
  batch_ops: Vec<BatchOp>,
  batch_dx: Vec<Fq>,
  batch_inv: Vec<Fq>,
  deferred: Vec<BatchOp>,
  deferred_tmp: Vec<BatchOp>,
  hot_proj: HashMap<u16, G1Projective>,
}

#[inline]
fn prefetch_point(ptr: *const G1Affine) {
  #[cfg(target_arch = "x86_64")]
  // SAFETY: `_mm_prefetch` is a non-faulting hint instruction on x86_64.
  unsafe {
    std::arch::x86_64::_mm_prefetch(
      ptr.cast::<i8>(),
      std::arch::x86_64::_MM_HINT_T0,
    );
  }
  #[cfg(not(target_arch = "x86_64"))]
  let _ = ptr;
}

impl ShardScratch {
  fn new(max_buckets: usize) -> Self {
    let words = max_buckets.div_ceil(64);
    Self {
      buckets: vec![AffineBucket::default(); max_buckets],
      occupied: vec![0u64; words],
      in_batch: vec![0u64; words],
      batch_ops: Vec::with_capacity(AFFINE_BATCH),
      batch_dx: Vec::with_capacity(AFFINE_BATCH),
      batch_inv: vec![Fq::ZERO; AFFINE_BATCH],
      deferred: Vec::with_capacity(AFFINE_BATCH),
      deferred_tmp: Vec::with_capacity(AFFINE_BATCH),
      hot_proj: HashMap::new(),
    }
  }

  fn accumulate_and_reduce(
    &mut self,
    bases: &[G1Affine],
    pts: &[u32],
    bkts: &[u16],
    b_len: usize,
  ) -> (G1Projective, G1Projective) {
    let words = b_len.div_ceil(64);
    self.occupied[..words].fill(0);
    self.in_batch[..words].fill(0);
    self.batch_ops.clear();
    self.batch_dx.clear();
    self.deferred.clear();
    self.hot_proj.clear();

    for (i, (&entry, &local_b)) in pts.iter().zip(bkts).enumerate() {
      if let Some(&next) = pts.get(i + PREFETCH_DIST) {
        let next_idx = usize::try_from(next & IDX_MASK).unwrap();
        prefetch_point(std::ptr::from_ref(&bases[next_idx]));
      }
      let base = &bases[usize::try_from(entry & IDX_MASK).unwrap()];
      let qx = if (entry & GLV_BIT) != 0 { base.x * BETA } else { base.x };
      let qy = if (entry & NEG_BIT) != 0 { -base.y } else { base.y };
      self.push_entry(local_b, qx, qy, true);
      if self.batch_ops.len() == AFFINE_BATCH {
        self.flush_batch();
      }
      if self.deferred.len() >= AFFINE_BATCH {
        self.flush_batch();
        self.drain_deferred();
      }
    }
    self.flush_batch();
    if !self.deferred.is_empty() {
      self.drain_deferred();
    }

    let mut running = G1Projective::zero();
    let mut triangle = G1Projective::zero();
    let has_hot = !self.hot_proj.is_empty();
    for j in (0..b_len).rev() {
      if (self.occupied[j >> 6] & (1u64 << (j & 63))) != 0 {
        let b = self.buckets[j];
        running += G1Affine::new_unchecked(b.x, b.y);
      }
      if has_hot {
        let key = u16::try_from(j).expect("bucket fits u16");
        if let Some(&extra) = self.hot_proj.get(&key) {
          running += extra;
        }
      }
      triangle += running;
    }
    (running, triangle)
  }

  #[inline]
  fn push_entry(&mut self, local_b: u16, qx: Fq, qy: Fq, allow_defer: bool) {
    let idx = usize::from(local_b);
    let word = idx >> 6;
    let bit = 1u64 << (idx & 63);
    if (self.occupied[word] & bit) == 0 {
      self.buckets[idx] = AffineBucket { x: qx, y: qy };
      self.occupied[word] |= bit;
      return;
    }
    if (self.in_batch[word] & bit) != 0 {
      if allow_defer {
        self.deferred.push(BatchOp { bucket: local_b, qx, qy });
      } else {
        *self.hot_proj.entry(local_b).or_insert_with(G1Projective::zero) +=
          G1Affine::new_unchecked(qx, qy);
      }
      return;
    }
    let p = &self.buckets[idx];
    let dx = qx - p.x;
    if dx.is_zero() {
      if (qy + p.y).is_zero() {
        // Exact inverse: P + (-P) = ∞.
        self.occupied[word] &= !bit;
      } else {
        // Doubling (P == Q): keep P in `buckets[idx]` and accumulate Q in
        // `hot_proj` so their sum equals 2P without a separate inversion.
        *self.hot_proj.entry(local_b).or_insert_with(G1Projective::zero) +=
          G1Affine::new_unchecked(qx, qy);
      }
      return;
    }
    self.in_batch[word] |= bit;
    self.batch_ops.push(BatchOp { bucket: local_b, qx, qy });
    self.batch_dx.push(dx);
  }

  fn drain_deferred(&mut self) {
    std::mem::swap(&mut self.deferred, &mut self.deferred_tmp);
    for i in 0..self.deferred_tmp.len() {
      let op = self.deferred_tmp[i];
      self.push_entry(op.bucket, op.qx, op.qy, false);
      if self.batch_ops.len() == AFFINE_BATCH {
        self.flush_batch();
      }
    }
    self.deferred_tmp.clear();
    self.flush_batch();
  }

  fn flush_batch(&mut self) {
    let len = self.batch_ops.len();
    if len == 0 {
      return;
    }
    let mut acc = Fq::ONE;
    for (slot, &dx) in
      self.batch_inv[..len].iter_mut().zip(&self.batch_dx[..len])
    {
      *slot = acc;
      acc *= dx;
    }
    let mut inv = acc.inverse().expect("batched dx values are nonzero");
    for i in (0..len).rev() {
      let inv_dx = self.batch_inv[i] * inv;
      inv *= self.batch_dx[i];
      let op = self.batch_ops[i];
      let idx = usize::from(op.bucket);
      self.in_batch[idx >> 6] &= !(1u64 << (idx & 63));
      let p = &mut self.buckets[idx];
      let lambda = (op.qy - p.y) * inv_dx;
      let x3 = lambda.square() - p.x - op.qx;
      let y3 = lambda * (p.x - x3) - p.y;
      p.x = x3;
      p.y = y3;
    }
    self.batch_ops.clear();
    self.batch_dx.clear();
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use ark_ec::{AffineRepr, CurveGroup};

  fn seeded_scalars(n: usize, seed: &[u8]) -> Vec<Fr> {
    (0..n)
      .into_par_iter()
      .map(|i| {
        let mut bytes = [0u8; 64];
        blake3::Hasher::new()
          .update(seed)
          .update(&u64::try_from(i).unwrap().to_le_bytes())
          .finalize_xof()
          .fill(&mut bytes);
        Fr::from_le_bytes_mod_order(&bytes)
      })
      .collect()
  }

  fn seeded_points(n: usize, seed: &[u8]) -> Vec<G1Affine> {
    let basis_len = n.clamp(1, 256);
    let basis_scalars = seeded_scalars(basis_len, seed);
    let basis: Vec<_> = basis_scalars
      .par_iter()
      .map(|&s| (G1Affine::generator() * s).into_affine())
      .collect();
    if n <= basis_len {
      return basis;
    }
    let blocks = n.div_ceil(basis_len);
    let step = Fr::from(257u64);
    let chunks: Vec<Vec<G1Affine>> = (0..blocks)
      .into_par_iter()
      .map(|block| {
        let shift = (G1Affine::generator()
          * (step * Fr::from(u64::try_from(block).unwrap())))
        .into_affine();
        let take = (n - block * basis_len).min(basis_len);
        let proj: Vec<G1Projective> = basis[..take]
          .iter()
          .map(|&p| G1Projective::from(p) + shift)
          .collect();
        G1Projective::normalize_batch(&proj)
      })
      .collect();
    let mut out = Vec::with_capacity(n);
    for chunk in chunks {
      out.extend(chunk);
    }
    out
  }

  #[test]
  fn glv_decomposition_preserves_scalar_and_126_bit_bound() {
    let lambda = Bn254G1Config::LAMBDA;
    let mut cases = vec![
      Fr::ZERO,
      Fr::ONE,
      -Fr::ONE,
      Fr::from(2u64),
      -Fr::from(2u64),
      lambda,
      -lambda,
      lambda + Fr::ONE,
      Fr::from(A1),
      Fr::from(B1),
      Fr::from(B2),
      Fr::from(A1) - Fr::ONE,
      Fr::from(B2) + Fr::ONE,
    ];
    cases.extend(seeded_scalars(10_000, b"glv-decomp-test"));
    for s in cases {
      let g = decompose_glv(s);
      let mag1 = g.k1 & MAG_MASK;
      let mag2 = g.k2 & MAG_MASK;
      assert!(mag1 < (1u128 << HALF_SCALAR_BITS));
      assert!(mag2 < (1u128 << HALF_SCALAR_BITS));
      let f1 =
        if (g.k1 & SIGN_BIT) != 0 { -Fr::from(mag1) } else { Fr::from(mag1) };
      let f2 =
        if (g.k2 & SIGN_BIT) != 0 { -Fr::from(mag2) } else { Fr::from(mag2) };
      assert_eq!(f1 + f2 * lambda, s, "GLV identity failed for {s}");
    }
  }

  #[test]
  fn signed_window_digits_reconstruct_all_half_scalars() {
    let samples = [
      0u128,
      1,
      2,
      (1u128 << 126) - 1,
      (1u128 << 125),
      (1u128 << 125) - 1,
      (1u128 << 125) + 1,
      0x2aaa_aaaa_aaaa_aaaa_aaaa_aaaa_aaaa_aaaa,
      0x1555_5555_5555_5555_5555_5555_5555_5555,
      A1 >> 1,
      B2 >> 1,
    ];
    for c in [4usize, 6, 8, 10, 12, 13, 15, 16, 18, 19, 20, 21, 22] {
      let w_count = num_windows_for(c);
      for &k in &samples {
        assert!(k < (1u128 << HALF_SCALAR_BITS));
        let mut reconstructed = 0i128;
        for w in 0..w_count {
          let d = window_digit(k, w, c, w_count);
          let max_b = buckets_for_window(w, c, w_count);
          assert!(
            usize::try_from(d.unsigned_abs()).unwrap() <= max_b,
            "digit {d} exceeded {max_b} at c={c}, w={w}"
          );
          if w + 1 == w_count {
            assert!(d >= 0, "top digit must be nonnegative at c={c}");
          }
          reconstructed += i128::from(d) << (w * c);
        }
        assert_eq!(
          reconstructed,
          i128::try_from(k).unwrap(),
          "mismatch at c={c}, k={k:#x}"
        );
      }
    }
  }

  #[test]
  fn cpu_msm_matches_arkworks_on_edge_cases_and_random_inputs() {
    let generator = G1Affine::generator();
    let lambda = Bn254G1Config::LAMBDA;

    // Edge cases: empty, 1, infinity bases, s=0, s=1, s=r-1, P+P, P+(-P),
    // lambda multiples, repeated bases, and sizes spanning thresholds.
    assert_eq!(msm(&[], &[]), G1Projective::zero());
    assert_eq!(msm(&[generator], &[Fr::ZERO]), G1Projective::zero());
    assert_eq!(msm(&[generator], &[Fr::ONE]), G1Projective::from(generator));
    assert_eq!(msm(&[generator], &[-Fr::ONE]), -G1Projective::from(generator));
    assert_eq!(
      msm(&[G1Affine::identity()], &[Fr::from(42u64)]),
      G1Projective::zero()
    );

    for n in [64usize, 65, 255, 256, 257, 1024, 4099, 16_385] {
      let mut points = seeded_points(n, b"msm-pts");
      let mut scalars = seeded_scalars(n, b"msm-scalars");
      // Inject adversarial edge cases into every size.
      points[0] = G1Affine::identity();
      points[1] = generator;
      points[2] = -generator;
      points[3] = generator;
      points[4] = generator;
      points[5] = Bn254G1Config::endomorphism_affine(&generator);
      scalars[0] = -Fr::ONE;
      scalars[1] = Fr::ONE;
      scalars[2] = Fr::ONE;
      scalars[3] = Fr::ZERO;
      scalars[4] = -Fr::ONE;
      scalars[5] = lambda;
      let expected = G1Projective::msm(&points, &scalars).unwrap();
      assert_eq!(msm(&points, &scalars), expected, "n={n}");
      // Exercise multiple window widths directly including tiny top windows.
      if n == 4099 {
        for c in [8usize, 10, 13, 15, 16, 19] {
          assert_eq!(
            msm_with_window(&points, &scalars, c),
            expected,
            "n={n}, c={c}"
          );
        }
      }
    }
  }

  #[test]
  fn cpu_msm_handles_all_equal_and_all_zero_scalars() {
    let n = 4096;
    let points = seeded_points(n, b"msm-skew");
    for scalar in [Fr::ZERO, Fr::ONE, -Fr::ONE, Fr::from(7u64)] {
      let scalars = vec![scalar; n];
      let expected = G1Projective::msm(&points, &scalars).unwrap();
      assert_eq!(msm(&points, &scalars), expected);
    }
    // Single repeated point (triggers heavy P == Q doubling + cancellation).
    let repeated = vec![G1Affine::generator(); n];
    let alternating: Vec<Fr> =
      (0..n).map(|i| if i % 2 == 0 { Fr::ONE } else { -Fr::ONE }).collect();
    assert_eq!(msm(&repeated, &alternating), G1Projective::zero());
    let ones = vec![Fr::ONE; n];
    assert_eq!(
      msm(&repeated, &ones),
      G1Projective::from(G1Affine::generator())
        * Fr::from(u64::try_from(n).unwrap())
    );
  }

  #[test]
  #[ignore = "CPU MSM microbenchmark vs legacy 2^18-chunked arkworks MSM"]
  fn bench_cpu_msm_vs_legacy_arkworks() {
    use std::time::Instant;
    let legacy_msm = |bases: &[G1Affine], coeffs: &[Fr]| -> G1Projective {
      const CHUNK: usize = 1 << 18;
      let concurrency = current_num_threads().div_ceil(8).min(4);
      let mut result = G1Projective::zero();
      for (batch, values) in coeffs.chunks(CHUNK * concurrency).enumerate() {
        let partial: G1Projective = values
          .par_chunks(CHUNK)
          .enumerate()
          .map(|(i, scalars)| {
            let start = batch * CHUNK * concurrency + i * CHUNK;
            G1Projective::msm(&bases[start..start + scalars.len()], scalars)
              .expect("equal lengths")
          })
          .sum();
        result += partial;
      }
      result
    };
    for log_n in [18usize, 20, 22, 24] {
      let n = 1usize << log_n;
      let points = seeded_points(n, b"bench-pts");
      let scalars = seeded_scalars(n, b"bench-scalars");
      let t0 = Instant::now();
      let expected = legacy_msm(&points, &scalars);
      let legacy_s = t0.elapsed().as_secs_f64();
      let t1 = Instant::now();
      let actual = msm(&points, &scalars);
      let glv_s = t1.elapsed().as_secs_f64();
      assert_eq!(actual, expected, "mismatch at 2^{log_n}");
      eprintln!(
        "MSM 2^{log_n} ({n}): legacy={legacy_s:.3}s glv={glv_s:.3}s speedup={:.2}x (c={})",
        legacy_s / glv_s,
        choose_window(n),
      );
      if log_n == 22 || log_n == 24 {
        for c in [19usize, 21, 22] {
          let tc = Instant::now();
          let res = msm_with_window(&points, &scalars, c);
          assert_eq!(res, expected);
          eprintln!("  2^{log_n} c={c}: {:.3}s", tc.elapsed().as_secs_f64());
        }
      }
    }
  }
}
