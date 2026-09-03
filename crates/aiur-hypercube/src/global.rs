//! The cross-shard adapter chip ("AiurGlobal").
//!
//! Hypercube's LogUp-GKR argument is strictly per-shard: every interaction
//! lands in its shard's sum, and that sum is pinned to the digest of the
//! interactions `eval_public_values` emits — there is no residual a shard
//! could "owe" another. Sharding an Aiur execution therefore works by
//! balancing every shard locally and committing the *boundary* to a
//! challenge-free, additively homomorphic digest that the shards' public
//! values expose and the top-level verifier sums to zero:
//!
//! - The partitioner (see [`crate::shard`]) splits the circuit traces into
//!   row ranges and computes each shard's residual: the signed multiset of
//!   lookup tuples the shard's rows require but do not provide (or provide
//!   in excess).
//! - Each residual entry becomes one row of an adapter chip. The row
//!   balances the tuple locally (an interaction with the residual's negated
//!   multiplicity) and adds the point `lift(m, tuple)` to a running
//!   septic-curve accumulator, where `lift` is a Poseidon2 hash-to-curve
//!   (the same construction as SP1's global interactions: hash to an
//!   x-coordinate, witness the y). An importing shard (which nets a
//!   *require* of the tuple and needs a local provide) commits the point
//!   with its y in the "receive" half-plane; the exporting shard (surplus
//!   provide) commits the same x with y in the "send" half-plane, i.e. the
//!   negated point. Matched flows cancel on the curve.
//! - The accumulator is threaded through the rows as a lookup counter chain
//!   (Hypercube AIRs are row-local, so, exactly like the memory circuit's
//!   pointer chain, row `i` pulls `(CHAIN, i, acc)` and pushes
//!   `(CHAIN, i+1, acc + P_i)`). `eval_public_values` pushes the chain start
//!   `(CHAIN, 0, START)` and pulls the end `(CHAIN, n, digest)` from the
//!   shard's public values. A shard with no boundary exposes `n = 0` and
//!   `digest = START`, and the pair self-cancels — the single-shard case
//!   degenerates to today's behavior.
//! - The top-level verifier (outside the per-shard argument) checks
//!   `Σ_shards (digest_s ⊖ START) = ∞`.
//!
//! Soundness of the multiset argument: per-shard LogUp forces every local
//! imbalance through adapter rows, so summing the per-shard (identically
//! zero) balances shows that a tuple required `c` times without a real
//! provider needs `imports = exports + c` while the digest sum forces
//! `imports = exports` (up to a Poseidon2 collision or a septic discrete
//! log), hence `c = 0`. The multiplicity is the hash's first limb, so a
//! flow only cancels against a flow of the same amount, and the tuple limbs
//! are zero-padded — which is exactly LogUp's own equivalence, since
//! trailing zeros do not change a fingerprint.
//!
//! Everything stays within Hypercube's `MAX_CONSTRAINT_DEGREE = 3`: the
//! curve equation and chain-addition checks carry intermediate witness
//! columns (`x²`, `(Δx)²`), and the Poseidon2 rounds are the crate's own
//! degree-3 operation, kept valid on padding rows by populating them with a
//! genuine permutation of zeroes.
//!
//! Adapter rows also need range checks (the hash-to-curve offset byte and
//! the y-half-plane decomposition). Routing those through Aiur's byte
//! tables would couple the adapter's content back into the residuals it was
//! built from (the multiplicity is hashed, so counts would chase their own
//! tail); instead every shard carries a tiny self-contained byte table on a
//! dedicated channel (see [`adapter_bytes_circuit`]).

use std::borrow::Borrow;

use slop_air::{AirBuilder, PairBuilder};
use slop_algebra::{AbstractField, PrimeField32};
use slop_matrix::Matrix;
use slop_matrix::dense::RowMajorMatrix;
use sp1_hypercube::{
  air::{AirInteraction, InteractionScope, SP1AirBuilder},
  operations::poseidon2::{
    NUM_EXTERNAL_ROUNDS, WIDTH,
    air::{eval_external_round, eval_internal_rounds},
    permutation::{NUM_POSEIDON2_DEGREE3_COLS, Poseidon2Degree3Cols},
    trace::populate_perm,
  },
  septic_curve::SepticCurve,
  septic_digest::SepticDigest,
  septic_extension::SepticExtension,
};

use crate::{F, air::AIUR_INTERACTION_KIND};

/// Channel of the accumulator counter chain. Aiur's own channels are small
/// constants; these two are far outside that range (and below the KoalaBear
/// modulus).
pub const CHAIN_CHANNEL: u32 = 2_000_000_001;

/// Channel of the per-shard adapter byte table.
pub const ADAPTER_BYTE_CHANNEL: u32 = 2_000_000_002;

/// `63 * 2^24`: y-coordinates whose last limb is in `[1, HALF_PLANE]` mark
/// "receive" points, those with the negated limb in that range mark "send"
/// points (the crate's `SepticExtension::is_receive`/`is_send` convention;
/// everything else is the exception zone the range check excludes).
const HALF_PLANE: u32 = 63 * (1 << 24);

/// One residual entry, to become one adapter row.
#[derive(Clone, Debug)]
pub struct AdapterRow {
  /// `true` if the shard nets a require of the tuple (the adapter provides
  /// it locally and commits the "receive" point); `false` for a surplus
  /// provide (the adapter consumes it and commits the "send" point).
  pub import: bool,
  /// The flow amount, the hash's first limb. Both endpoints of a flow
  /// carry the same amount.
  pub amount: F,
  /// The lookup tuple, trailing zeroes stripped.
  pub tuple: Vec<F>,
}

/// The running accumulator threaded through every adapter chip of a shard.
pub struct ChainState {
  pub idx: usize,
  pub acc: SepticCurve<F>,
  /// Byte usage of the adapter rows built so far (offset + half-plane
  /// decomposition), to become the shard's adapter byte table
  /// multiplicities.
  pub byte_counts: [u64; 256],
}

impl ChainState {
  pub fn start() -> Self {
    Self { idx: 0, acc: SepticDigest::<F>::zero().0, byte_counts: [0; 256] }
  }
}

/// The adapter chip for tuples of up to `8 * chunks - 1` limbs (one hash
/// chunk is reserved for the flow amount).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GlobalSpec {
  pub chunks: usize,
}

// Column layout: a fixed head, `chunks` Poseidon2 permutations, and a tail
// of septic witnesses and range-check bytes.
const IS_REAL: usize = 0;
const IS_IMPORT: usize = 1;
const AMOUNT: usize = 2;
const SIGNED_MULT: usize = 3;
const IDX: usize = 4;
const TUPLE: usize = 5;

impl GlobalSpec {
  /// Smallest chip class whose tuple capacity fits `len` limbs.
  pub fn class_for(len: usize) -> usize {
    (len + 1).div_ceil(8).max(1)
  }

  pub fn tuple_capacity(&self) -> usize {
    8 * self.chunks - 1
  }

  fn perm_start(&self, i: usize) -> usize {
    TUPLE + self.tuple_capacity() + i * NUM_POSEIDON2_DEGREE3_COLS
  }

  fn tail(&self) -> usize {
    self.perm_start(self.chunks)
  }

  // Tail offsets: y (7), x² (7), (Δx)² (7), acc_prev (14), acc_next (14),
  // half-plane bytes b0..b3 and 62−b3 (5).
  fn y(&self) -> usize {
    self.tail()
  }

  fn x2(&self) -> usize {
    self.tail() + 7
  }

  fn dx2(&self) -> usize {
    self.tail() + 14
  }

  fn acc_prev(&self) -> usize {
    self.tail() + 21
  }

  fn acc_next(&self) -> usize {
    self.tail() + 35
  }

  fn bytes(&self) -> usize {
    self.tail() + 49
  }

  pub fn width(&self) -> usize {
    self.tail() + 54
  }

  /// The chip's constraints and interactions.
  pub fn eval<AB>(&self, builder: &mut AB)
  where
    AB: SP1AirBuilder<F = F> + PairBuilder,
  {
    let main = builder.main();
    let row = main.row_slice(0);
    let row: &[AB::Var] = &row;

    let is_real = row[IS_REAL];
    let is_import = row[IS_IMPORT];
    let amount = row[AMOUNT];
    let signed_mult = row[SIGNED_MULT];
    let idx = row[IDX];
    let tuple = &row[TUPLE..TUPLE + self.tuple_capacity()];

    builder.assert_bool(is_real);
    builder.assert_bool(is_import);

    // The local balancing multiplicity: `-amount` when importing (a
    // provide, by Aiur's pull-is-negative convention), `+amount` when
    // exporting; zero on padding rows so the lookups below can use the
    // column directly.
    let sign = AB::Expr::one() - is_import.into() * AB::Expr::two();
    builder.assert_eq(signed_mult, is_real.into() * sign * amount.into());

    // ── Poseidon2 sponge over [amount, tuple...], one chunk per
    // permutation; the offset byte sits in the first capacity slot, the
    // chip class in the second (domain separation between classes).
    let perms: Vec<&Poseidon2Degree3Cols<AB::Var>> = (0..self.chunks)
      .map(|i| {
        let s = self.perm_start(i);
        row[s..s + NUM_POSEIDON2_DEGREE3_COLS].borrow()
      })
      .collect();
    for perm in &perms {
      for r in 0..NUM_EXTERNAL_ROUNDS {
        eval_external_round(builder, *perm, r);
      }
      eval_internal_rounds(builder, *perm);
    }

    let input0 = &perms[0].state.external_rounds_state[0];
    builder.when(is_real).assert_eq(input0[0], amount);
    for j in 0..7 {
      builder.when(is_real).assert_eq(input0[1 + j], tuple[j]);
    }
    // input0[8] is the hash-to-curve offset, range-checked below.
    builder
      .when(is_real)
      .assert_eq(input0[9], AB::Expr::from_canonical_usize(self.chunks));
    for slot in &input0[10..WIDTH] {
      builder.when(is_real).assert_zero(*slot);
    }
    for i in 1..self.chunks {
      let prev = &perms[i - 1].state.output_state;
      let cur = &perms[i].state.external_rounds_state[0];
      for j in 0..8 {
        let limb = tuple[7 + 8 * (i - 1) + j];
        builder.when(is_real).assert_eq(cur[j], prev[j].into() + limb.into());
      }
      for j in 8..WIDTH {
        builder.when(is_real).assert_eq(cur[j], prev[j]);
      }
    }

    // ── The septic point: x is the hash output, y is witnessed on the
    // curve, `x²` keeps the equation at degree 3.
    let septic = |start: usize| -> SepticExtension<AB::Expr> {
      SepticExtension(core::array::from_fn(|k| row[start + k].into()))
    };
    let out = &perms[self.chunks - 1].state.output_state;
    let x =
      SepticExtension::<AB::Expr>(core::array::from_fn(|k| out[k].into()));
    let y = septic(self.y());
    let x2 = septic(self.x2());
    let dx2 = septic(self.dx2());
    let assert_septic_zero =
      |builder: &mut AB, e: SepticExtension<AB::Expr>| {
        for limb in e.0 {
          builder.when(is_real).assert_zero(limb);
        }
      };
    assert_septic_zero(builder, x2.clone() - x.clone() * x.clone());
    let z3 = SepticExtension::<AB::Expr>(core::array::from_fn(|k| {
      if k == 3 { AB::Expr::from_canonical_u32(41) } else { AB::Expr::zero() }
    }));
    let forty_five = AB::Expr::from_canonical_u32(45);
    assert_septic_zero(
      builder,
      y.clone() * y.clone() - (x2 * x.clone() + x.clone() * forty_five + z3),
    );

    // ── Chain addition `acc_next = acc_prev + (x, y)` via the crate's
    // incomplete-addition checkers, with `(Δx)²` witnessed to stay at
    // degree 3.
    let acc_prev = SepticCurve {
      x: septic(self.acc_prev()),
      y: septic(self.acc_prev() + 7),
    };
    let acc_next = SepticCurve {
      x: septic(self.acc_next()),
      y: septic(self.acc_next() + 7),
    };
    let dx = x.clone() - acc_prev.x.clone();
    assert_septic_zero(builder, dx2.clone() - dx.clone() * dx.clone());
    let dy = y.clone() - acc_prev.y.clone();
    assert_septic_zero(
      builder,
      (acc_prev.x.clone() + x.clone() + acc_next.x.clone()) * dx2
        - dy.clone() * dy.clone(),
    );
    assert_septic_zero(
      builder,
      (acc_prev.y.clone() + acc_next.y.clone()) * dx
        - dy * (acc_prev.x.clone() - acc_next.x.clone()),
    );

    // ── Direction: importing rows commit y in the receive half-plane,
    // exporting rows in the send half-plane, i.e.
    // `(2·is_import − 1)·y₆ ∈ [1, HALF_PLANE]`, enforced by a byte
    // decomposition with the top byte capped at 62 via its complement.
    let b = &row[self.bytes()..self.bytes() + 5];
    let decomposed = b[0].into()
      + b[1].into() * AB::Expr::from_canonical_u32(1 << 8)
      + b[2].into() * AB::Expr::from_canonical_u32(1 << 16)
      + b[3].into() * AB::Expr::from_canonical_u32(1 << 24)
      + AB::Expr::one();
    let y6: AB::Expr = row[self.y() + 6].into();
    builder.when(is_real).assert_eq(
      decomposed,
      (is_import.into() * AB::Expr::two() - AB::Expr::one()) * y6,
    );
    builder
      .when(is_real)
      .assert_eq(b[3].into() + b[4].into(), AB::Expr::from_canonical_u32(62));

    // ── Lookups. All multiplicities are plain columns or `±is_real`, so
    // padding rows are inert.
    let send = |builder: &mut AB, values: Vec<AB::Expr>, mult: AB::Expr| {
      builder.send(
        AirInteraction::new(values, mult, AIUR_INTERACTION_KIND),
        InteractionScope::Local,
      );
    };
    // The balancing lookup: the tuple itself (trailing padding zeroes do
    // not change a LogUp fingerprint).
    send(
      builder,
      tuple.iter().map(|v| (*v).into()).collect(),
      signed_mult.into(),
    );
    // Byte range checks on the adapter byte table.
    let byte = |builder: &mut AB, v: AB::Expr| {
      send(
        builder,
        vec![AB::Expr::from_canonical_u32(ADAPTER_BYTE_CHANNEL), v],
        is_real.into(),
      );
    };
    byte(builder, input0[8].into());
    for bit in b {
      byte(builder, (*bit).into());
    }
    // The accumulator chain: pull `(idx, acc_prev)`, push
    // `(idx + 1, acc_next)`.
    let chain = |acc: &SepticCurve<AB::Expr>, at: AB::Expr| -> Vec<AB::Expr> {
      let mut values = vec![AB::Expr::from_canonical_u32(CHAIN_CHANNEL), at];
      values.extend(acc.x.0.iter().cloned());
      values.extend(acc.y.0.iter().cloned());
      values
    };
    send(builder, chain(&acc_prev, idx.into()), -is_real.into());
    send(
      builder,
      chain(&acc_next, idx.into() + AB::Expr::one()),
      is_real.into(),
    );
  }

  /// The row's lookups as `(values, multiplicity)`, mirroring [`Self::eval`]
  /// — for the partitioner's balance simulation.
  pub(crate) fn row_lookups(&self, row: &[F]) -> Vec<(Vec<F>, F)> {
    let is_real = row[IS_REAL];
    let cap = self.tuple_capacity();
    let mut out = vec![(row[TUPLE..TUPLE + cap].to_vec(), row[SIGNED_MULT])];
    let abc = F::from_canonical_u32(ADAPTER_BYTE_CHANNEL);
    let offset = row[self.perm_start(0) + 8];
    for v in [offset]
      .into_iter()
      .chain(row[self.bytes()..self.bytes() + 5].iter().copied())
    {
      out.push((vec![abc, v], is_real));
    }
    let chain = |idx: F, at: usize| {
      let mut v = vec![F::from_canonical_u32(CHAIN_CHANNEL), idx];
      v.extend_from_slice(&row[at..at + 14]);
      v
    };
    out.push((chain(row[IDX], self.acc_prev()), -is_real));
    out.push((chain(row[IDX] + F::one(), self.acc_next()), is_real));
    out
  }

  /// Builds the chip's trace for this shard's rows of this class,
  /// threading the accumulator chain (and byte usage) through `chain`.
  pub fn build_trace(
    &self,
    rows: &[AdapterRow],
    chain: &mut ChainState,
  ) -> RowMajorMatrix<F> {
    let width = self.width();
    let height =
      rows.len().max(1).next_multiple_of(crate::machine::ROW_ALIGNMENT);
    let mut values = vec![F::zero(); height * width];

    // A genuine permutation of zeroes keeps the (ungated) Poseidon2
    // constraints valid on padding rows.
    let mut zero_perm = vec![F::zero(); NUM_POSEIDON2_DEGREE3_COLS];
    populate_perm::<F, 3>([F::zero(); WIDTH], None, &mut zero_perm);
    for r in 0..height {
      let row = &mut values[r * width..(r + 1) * width];
      for i in 0..self.chunks {
        let s = self.perm_start(i);
        row[s..s + NUM_POSEIDON2_DEGREE3_COLS].copy_from_slice(&zero_perm);
      }
    }

    for (r, entry) in rows.iter().enumerate() {
      assert!(
        entry.tuple.len() <= self.tuple_capacity(),
        "adapter tuple exceeds the chip class"
      );
      let row_start = r * width;
      let (point, offset) = {
        let row = &mut values[row_start..row_start + width];
        self.populate_hash(row, entry)
      };
      let row = &mut values[row_start..row_start + width];
      row[IS_REAL] = F::one();
      row[IS_IMPORT] = F::from_bool(entry.import);
      row[AMOUNT] = entry.amount;
      row[SIGNED_MULT] =
        if entry.import { -entry.amount } else { entry.amount };
      row[IDX] = F::from_canonical_usize(chain.idx);
      for (j, v) in entry.tuple.iter().enumerate() {
        row[TUPLE + j] = *v;
      }

      let acc_prev = chain.acc;
      assert!(
        acc_prev.x != point.x,
        "septic chain hit an x-collision; reorder the adapter rows"
      );
      let acc_next = acc_prev.add_incomplete(point);
      let write_septic = |row: &mut [F], at: usize, e: &SepticExtension<F>| {
        row[at..at + 7].copy_from_slice(&e.0);
      };
      write_septic(row, self.y(), &point.y);
      write_septic(row, self.x2(), &(point.x * point.x));
      let dx = point.x - acc_prev.x;
      write_septic(row, self.dx2(), &(dx * dx));
      write_septic(row, self.acc_prev(), &acc_prev.x);
      write_septic(row, self.acc_prev() + 7, &acc_prev.y);
      write_septic(row, self.acc_next(), &acc_next.x);
      write_septic(row, self.acc_next() + 7, &acc_next.y);

      // Half-plane decomposition of `±y₆`.
      let y6 = point.y.0[6].as_canonical_u32();
      let t = if entry.import { y6 } else { F::ORDER_U32 - y6 };
      debug_assert!((1..=HALF_PLANE).contains(&t), "y outside its half-plane");
      let tm1 = t - 1;
      let bytes = [
        tm1 & 0xFF,
        (tm1 >> 8) & 0xFF,
        (tm1 >> 16) & 0xFF,
        tm1 >> 24,
        62 - (tm1 >> 24),
      ];
      for (j, v) in bytes.into_iter().enumerate() {
        row[self.bytes() + j] = F::from_canonical_u32(v);
      }
      for v in &bytes[..4] {
        chain.byte_counts[*v as usize] += 1;
      }
      chain.byte_counts[bytes[4] as usize] += 1;
      chain.byte_counts[offset as usize] += 1;

      chain.idx += 1;
      chain.acc = acc_next;
    }

    RowMajorMatrix::new(values, width)
  }

  /// Fills the row's permutation columns for the sponge over
  /// `[amount, tuple...]`, retrying the offset byte until the hash lifts
  /// to a curve point whose y (in the row's half-plane) exists. Returns
  /// the point and the offset used.
  fn populate_hash(
    &self,
    row: &mut [F],
    entry: &AdapterRow,
  ) -> (SepticCurve<F>, u8) {
    let mut chunk0 = [F::zero(); 8];
    chunk0[0] = entry.amount;
    for (j, v) in entry.tuple.iter().take(7).enumerate() {
      chunk0[1 + j] = *v;
    }
    for offset in 0u16..256 {
      let mut state = [F::zero(); WIDTH];
      state[..8].copy_from_slice(&chunk0);
      state[8] = F::from_canonical_u16(offset);
      state[9] = F::from_canonical_usize(self.chunks);
      for i in 0..self.chunks {
        if i > 0 {
          for (j, slot) in state.iter_mut().enumerate().take(8) {
            let limb = entry
              .tuple
              .get(7 + 8 * (i - 1) + j)
              .copied()
              .unwrap_or(F::zero());
            *slot += limb;
          }
        }
        let s = self.perm_start(i);
        let segment = &mut row[s..s + NUM_POSEIDON2_DEGREE3_COLS];
        populate_perm::<F, 3>(state, None, segment);
        let cols: &Poseidon2Degree3Cols<F> = (*segment).borrow();
        state = cols.state.output_state;
      }
      let x = SepticExtension(core::array::from_fn(|k| state[k]));
      let Some(y) = SepticCurve::curve_formula(x).sqrt() else {
        continue;
      };
      if y.is_exception() {
        continue;
      }
      // `y` and `-y` sit in opposite half-planes; pick the row's.
      let y = if y.is_receive() == entry.import { y } else { -y };
      let offset = u8::try_from(offset).expect("offset fits a byte");
      return (SepticCurve { x, y }, offset);
    }
    panic!("no curve point found for an adapter tuple after 256 offsets");
  }
}
