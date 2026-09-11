//! Partitioning one execution into Hypercube shards.
//!
//! The partitioner is semantics-free: it splits the row ranges of the
//! splittable circuits (those without preprocessed traces) under an area
//! budget, *evaluates every interaction* of every shard to find the shard's
//! residual — the signed multiset of lookup tuples the shard does not
//! balance internally — and then:
//!
//! - absorbs residuals the shard's own tables can provide (the byte tables
//!   are present in full in every shard with free per-shard multiplicity
//!   columns);
//! - matches the remaining residuals across shards into pairwise flows,
//!   each becoming one import and one export row of the adapter chips
//!   (see [`crate::global`]).
//!
//! The memory counter chains, the byte tables, function memoization and the
//! claim all reduce to this one mechanism; nothing here knows what a tuple
//! means.

use hashbrown::HashMap;
use rayon::prelude::*;
use slop_algebra::{AbstractField, Field, PrimeField32};
use slop_matrix::{Matrix, dense::RowMajorMatrix};

use crate::{
  F,
  expr::Col,
  global::{AdapterRow, ChainState, GlobalSpec},
  machine::{
    AiurMachine, BuildError, LoweredCircuit, ROW_ALIGNMENT, fill_materialized,
  },
  record::{AiurRecord, PV_CHAIN_LEN, PV_DIGEST},
};

/// Sharding parameters.
#[derive(Clone, Copy, Debug)]
pub struct ShardingParams {
  /// Cap on a shard's *splittable* main-trace cells. The replicated atomic
  /// tables and the adapter chips come on top, so leave headroom below the
  /// prover's area bound. `usize::MAX` keeps everything in one shard.
  pub max_cells: usize,
  /// No circuit chunk exceeds this many rows.
  pub max_rows: usize,
}

impl Default for ShardingParams {
  fn default() -> Self {
    Self { max_cells: usize::MAX, max_rows: 1 << 20 }
  }
}

/// A shard under construction: chunk row ranges per slot (splittable
/// circuits only; atomic circuits are in every shard).
struct ShardPlan {
  ranges: Vec<std::ops::Range<usize>>,
}

/// A signed multiset of lookup tuples: a shard's demand or residual.
type Residual = HashMap<Vec<u32>, i128>;

/// A read-only map over lookup tuples with ~10^8 entries, built in
/// parallel: the entries are bucketed by a hash of the tuple and each
/// bucket is its own hash map.
struct TupleIndex<V> {
  buckets: Vec<HashMap<Vec<u32>, V>>,
}

impl<V: Send + Sync> TupleIndex<V> {
  const BUCKETS: usize = 256;

  fn bucket_of(key: &[u32]) -> usize {
    use std::hash::{Hash, Hasher};
    let mut h = std::hash::DefaultHasher::new();
    key.hash(&mut h);
    usize::try_from(h.finish() % Self::BUCKETS as u64).expect("bucket")
  }

  fn build(entries: Vec<(Vec<u32>, V)>) -> Self {
    // Bucket in parallel by chunk, then merge each bucket in parallel.
    let chunked: Vec<Vec<Vec<(Vec<u32>, V)>>> = entries
      .into_par_iter()
      .fold(
        || (0..Self::BUCKETS).map(|_| Vec::new()).collect::<Vec<_>>(),
        |mut acc, (key, value)| {
          acc[Self::bucket_of(&key)].push((key, value));
          acc
        },
      )
      .collect();
    let buckets = (0..Self::BUCKETS)
      .into_par_iter()
      .map(|b| {
        let mut map = HashMap::new();
        for chunk in &chunked {
          // The values are moved out below; the chunks are consumed once.
          map.reserve(chunk[b].len());
        }
        map
      })
      .collect::<Vec<_>>();
    let mut buckets: Vec<std::sync::Mutex<HashMap<Vec<u32>, V>>> =
      buckets.into_iter().map(std::sync::Mutex::new).collect();
    chunked.into_par_iter().for_each(|chunk| {
      for (b, entries) in chunk.into_iter().enumerate() {
        if entries.is_empty() {
          continue;
        }
        let mut map = buckets[b].lock().expect("bucket lock");
        map.extend(entries);
      }
    });
    let buckets =
      buckets.drain(..).map(|m| m.into_inner().expect("bucket lock")).collect();
    Self { buckets }
  }

  fn get(&self, key: &[u32]) -> Option<&V> {
    self.buckets[Self::bucket_of(key)].get(key)
  }
}

fn debug_enabled() -> bool {
  std::env::var_os("IX_HC_DEBUG").is_some()
}

/// `IX_HC_TIMING` (or `IX_HC_DEBUG`): report the wall time of the
/// partitioner's rounds and of each shard's assembly.
pub(crate) fn timing_enabled() -> bool {
  std::env::var_os("IX_HC_TIMING").is_some() || debug_enabled()
}

/// The process's resident set, in whole gigabytes (Linux; 0 elsewhere).
fn rss_gb() -> u64 {
  std::fs::read_to_string("/proc/self/statm")
    .ok()
    .and_then(|s| s.split_whitespace().nth(1)?.parse::<u64>().ok())
    .map_or(0, |pages| pages * 4096 / (1 << 30))
}

/// Interprets a field element as a small signed integer (multiplicities are
/// counts, far below the field's midpoint).
fn signed(x: F) -> i128 {
  let c = x.as_canonical_u32();
  if c <= F::ORDER_U32 / 2 {
    i128::from(c)
  } else {
    -i128::from(F::ORDER_U32 - c)
  }
}

fn to_field(x: i128) -> F {
  if x >= 0 {
    let x = u32::try_from(x).expect("flow amount exceeds the field");
    assert!(x < F::ORDER_U32, "flow amount exceeds the field");
    F::from_canonical_u32(x)
  } else {
    -to_field(-x)
  }
}

/// Strips trailing zeroes — LogUp's own tuple equivalence, and the adapter
/// hash's canonical form.
fn canonical_tuple(mut t: Vec<u32>) -> Vec<u32> {
  while t.last() == Some(&0) {
    t.pop();
  }
  t
}

/// A splittable circuit's rows in one shard, as a view into the execution's
/// trace of that circuit: row ranges (one epoch slice, or the blocks a
/// load-affinity circuit was assigned), the multiplicity reductions of the
/// rows whose provides were duplicated elsewhere, and the rows duplicated
/// *into* this shard with their demanded multiplicity. Nothing is copied
/// until [`View::materialize`]; a refinement round therefore costs a few
/// words per row edit rather than a second copy of the execution.
#[derive(Clone)]
struct View {
  slot: usize,
  /// Ascending, disjoint row ranges of `extended[slot]`.
  ranges: Vec<std::ops::Range<usize>>,
  /// `(row, delta)`, ascending by row: `mult_col` of `row` less `delta`.
  reductions: Vec<(usize, F)>,
  /// `(row, mult)`: copies of `row` with `mult_col` set to `mult`, after
  /// the ranges.
  extra: Vec<(usize, F)>,
  /// The provide multiplicity column the edits apply to.
  mult_col: Option<usize>,
}

impl View {
  fn range(slot: usize, range: std::ops::Range<usize>) -> Self {
    Self {
      slot,
      ranges: vec![range],
      reductions: vec![],
      extra: vec![],
      mult_col: None,
    }
  }

  fn height(&self) -> usize {
    self.ranges.iter().map(ExactSizeIterator::len).sum::<usize>()
      + self.extra.len()
  }

  /// Every row of the view, in order, with the edits applied.
  fn for_each_row(&self, trace: &RowMajorMatrix<F>, mut f: impl FnMut(&[F])) {
    let w = trace.width();
    let mut buf: Vec<F> = Vec::with_capacity(w);
    let mut reductions = self.reductions.iter().peekable();
    for range in &self.ranges {
      for r in range.clone() {
        let row = &trace.values[r * w..(r + 1) * w];
        while reductions.peek().is_some_and(|(rr, _)| *rr < r) {
          reductions.next();
        }
        match reductions.peek() {
          Some((rr, delta)) if *rr == r => {
            buf.clear();
            buf.extend_from_slice(row);
            buf[self.mult_col.expect("edits name the multiplicity column")] -=
              *delta;
            f(&buf);
            reductions.next();
          },
          _ => f(row),
        }
      }
    }
    for (r, mult) in &self.extra {
      buf.clear();
      buf.extend_from_slice(&trace.values[r * w..(r + 1) * w]);
      buf[self.mult_col.expect("edits name the multiplicity column")] = *mult;
      f(&buf);
    }
  }

  fn materialize(&self, trace: &RowMajorMatrix<F>) -> RowMajorMatrix<F> {
    let w = trace.width();
    let mut values = Vec::with_capacity(self.height() * w);
    self.for_each_row(trace, |row| values.extend_from_slice(row));
    RowMajorMatrix::new(values, w)
  }
}

/// A circuit's rows in one shard: the atomic circuits (replicated, with
/// per-shard multiplicity columns) are owned copies; the splittable ones
/// are views.
#[derive(Clone)]
enum Chunk {
  Owned(RowMajorMatrix<F>),
  View(View),
}

impl Chunk {
  fn height(&self) -> usize {
    match self {
      Self::Owned(m) => m.height(),
      Self::View(v) => v.height(),
    }
  }

  fn width(&self, extended: &[Option<RowMajorMatrix<F>>]) -> usize {
    match self {
      Self::Owned(m) => m.width(),
      Self::View(v) => extended[v.slot].as_ref().expect("viewed trace").width(),
    }
  }

  fn materialize(
    self,
    extended: &[Option<RowMajorMatrix<F>>],
  ) -> RowMajorMatrix<F> {
    match self {
      Self::Owned(m) => m,
      Self::View(v) => {
        v.materialize(extended[v.slot].as_ref().expect("viewed trace"))
      },
    }
  }
}

/// One shard as the partitioner leaves it: its circuits' chunks and the
/// adapter rows balancing its boundary, not yet laid out as traces.
struct PlannedShard {
  chunks: Vec<Option<Chunk>>,
  adapters: Vec<AdapterRow>,
}

/// A partitioned execution, its shards assembled into records one at a time.
///
/// Assembly is where a shard becomes big: the adapter chips are wide (two
/// Poseidon2 permutations per memory tuple), every shard is padded to the
/// row alignment and, at proving time, to its shape class, so a large
/// execution's records amount to `shards × 2^29` cells — hundreds of
/// gigabytes for a few hundred shards, far more than the planned chunks
/// they come from. [`Partition::into_records`] assembles each record when
/// the prover asks for it, so one record's traces are resident at a time,
/// beside the execution's traces (`extended`) the views point into.
pub struct Partition<'e> {
  extended: &'e [Option<RowMajorMatrix<F>>],
  /// Each shard's plan, taken by whichever thread assembles it.
  shards: Vec<std::sync::Mutex<Option<PlannedShard>>>,
  claim: Vec<F>,
}

impl Partition<'_> {
  /// Number of shards.
  #[must_use]
  pub fn len(&self) -> usize {
    self.shards.len()
  }

  #[must_use]
  pub fn is_empty(&self) -> bool {
    self.shards.is_empty()
  }

  /// Assembles shard `k` (each shard can be assembled once). With
  /// `IX_HC_DEBUG`, simulates the record's full LogUp balance — every chip
  /// plus `eval_public_values` — so a partitioner bug fails here, in
  /// seconds, not inside GKR verification after the whole prove.
  pub fn assemble(&self, machine: &AiurMachine, k: usize) -> AiurRecord {
    let start = std::time::Instant::now();
    let shard = self.shards[k]
      .lock()
      .expect("shard plan lock")
      .take()
      .expect("a shard is assembled once");
    let chunks = shard
      .chunks
      .into_par_iter()
      .map(|chunk| chunk.map(|chunk| chunk.materialize(self.extended)))
      .collect();
    let materialized = start.elapsed();
    let record =
      assemble_shard(machine, chunks, &shard.adapters, &self.claim, k == 0);
    if timing_enabled() {
      eprintln!(
        "hypercube shard {k}: materialized in {materialized:.2?}, assembled \
         ({} adapter rows) in {:.2?}",
        shard.adapters.len(),
        start.elapsed()
      );
    }
    if debug_enabled() {
      debug_check_balance(machine, k, &record);
    }
    record
  }

  /// The shard records, assembled lazily in shard order.
  pub fn into_records(
    self,
    machine: &AiurMachine,
  ) -> impl ExactSizeIterator<Item = AiurRecord> + Send {
    let n = self.len();
    (0..n).map(move |k| self.assemble(machine, k))
  }
}

impl crate::prover::RecordSource for Partition<'_> {
  fn len(&self) -> usize {
    self.shards.len()
  }

  fn take(&self, machine: &AiurMachine, k: usize) -> AiurRecord {
    self.assemble(machine, k)
  }
}

/// Splits an execution into shard records: [`partition_shards`] with every
/// record assembled up front.
pub fn partition_records(
  machine: &AiurMachine,
  extended: &[Option<RowMajorMatrix<F>>],
  claim: &[F],
  params: &ShardingParams,
) -> Result<Vec<AiurRecord>, BuildError> {
  Ok(
    partition_shards(machine, extended, claim, params)?
      .into_records(machine)
      .collect(),
  )
}

/// Splits an execution into shards. `extended` are the outputs of
/// [`AiurMachine::extended_traces`]; the first shard carries the claim (and
/// the memory boundary's chain openings). The shards view `extended`, which
/// must outlive the [`Partition`].
// The refinement fractions and row cuts round through `f64`; shard counts
// and trace heights are far below 2^52, so the casts are exact enough.
#[allow(
  clippy::cast_precision_loss,
  clippy::cast_possible_truncation,
  clippy::cast_sign_loss
)]
pub fn partition_shards<'e>(
  machine: &AiurMachine,
  extended: &'e [Option<RowMajorMatrix<F>>],
  claim: &[F],
  params: &ShardingParams,
) -> Result<Partition<'e>, BuildError> {
  let num_split = machine.num_circuits() + 1;
  assert_eq!(extended.len(), num_split, "one trace per splittable slot");

  // Atomic circuits (preprocessed traces) are replicated into every shard;
  // everything else splits by rows.
  let is_atomic =
    |slot: usize| machine.lowered_at(slot).unwrap().preprocessed.is_some();

  // ── Replicable rows: a memoized row whose lookups, besides its entry
  // provide, only hit the per-shard tables can be *duplicated into the
  // shards that demand its entry*, splitting its multiplicity (LogUp-
  // identical to one provide of the total). That costs one circuit row per
  // demanding shard instead of a hash-to-curve adapter pair per crossing
  // entry — and cross-epoch demand (memo hits to earlier epochs) is exactly
  // what memoization creates. Qualification is per row, so gadget circuits
  // qualify wholesale and mixed circuits partially.
  let table_universe: std::collections::HashSet<Vec<u32>> = (0..num_split)
    .filter(|s| is_atomic(*s))
    .flat_map(|s| table_tuples(machine.lowered_at(s).unwrap()))
    .collect();
  // `IX_HC_DUMB`: plain epoch slices — no row replication, no load
  // affinity — every crossing an adapter row. A baseline for what the
  // optimizations buy (and cost).
  let dumb = std::env::var_os("IX_HC_DUMB").is_some();
  let provides: Vec<Option<ProvideInfo>> = (0..num_split)
    .map(|slot| {
      if dumb || is_atomic(slot) || extended[slot].is_none() {
        return None;
      }
      provide_candidate(machine.lowered_at(slot).unwrap())
    })
    .collect();

  // ── Epoch-sliced row split: every splittable circuit is cut at the same
  // execution fractions. Witness rows are in creation order and requires
  // have strong temporal locality (calls resolve into recently created memo
  // entries), so aligning the cuts across circuits keeps most lookups
  // intra-shard. The fractions start uniform and are refined adaptively:
  // shards whose measured area (circuits + duplicates + adapters) exceeds
  // the jagged bound get their interval split, so boundary-dense regions of
  // the execution take finer slices while cheap regions stay coarse.
  let split_slots: Vec<usize> = (0..num_split)
    .filter(|s| !is_atomic(*s) && extended[*s].is_some())
    .collect();
  let total_cells: usize = split_slots
    .iter()
    .map(|s| extended[*s].as_ref().unwrap().values.len())
    .sum();
  let mut init_shards = total_cells.div_ceil(params.max_cells.max(1)).max(1);
  for slot in &split_slots {
    let height = extended[*slot].as_ref().unwrap().height();
    init_shards = init_shards.max(height.div_ceil(params.max_rows.max(1)));
  }
  let mut boundaries: Vec<f64> =
    (0..=init_shards).map(|k| k as f64 / init_shards as f64).collect();

  // ── Round-independent indexes.
  const AFFINITY_BLOCK: usize = 64;
  let affinity: Vec<bool> = (0..num_split)
    .map(|slot| {
      !dumb
        && machine.affinity_slots.contains(&slot)
        && extended[slot].is_some()
    })
    .collect();
  // tuple → (slot, block), over every interaction of the affinity circuits.
  let index_start = std::time::Instant::now();
  let affinity_index: Vec<(Vec<u32>, (usize, usize))> = (0..num_split)
    .into_par_iter()
    .filter(|slot| affinity[*slot])
    .map(|slot| {
      let circuit = machine.lowered_at(slot).unwrap();
      let trace = extended[slot].as_ref().unwrap();
      let width = trace.width();
      (0..trace.height())
        .into_par_iter()
        .flat_map_iter(|r| {
          let empty: [F; 0] = [];
          let main = &trace.values[r * width..(r + 1) * width];
          circuit
            .lowered
            .interactions
            .iter()
            .filter(|i| i.multiplicity.eval_row(&empty, main) != F::zero())
            .map(|i| {
              let tuple = canonical_tuple(
                i.values
                  .iter()
                  .map(|v| {
                    let empty: [F; 0] = [];
                    v.eval_row(&empty, main).as_canonical_u32()
                  })
                  .collect(),
              );
              (tuple, (slot, r / AFFINITY_BLOCK))
            })
            .collect::<Vec<_>>()
            .into_iter()
        })
        .collect::<Vec<_>>()
    })
    .flatten()
    .collect::<Vec<_>>();
  let affinity_index = TupleIndex::build(affinity_index);
  // Every provide of the candidate circuits, marking which rows qualify for
  // replication (all other lookups table-provided or inert).
  let provide_index: Vec<(Vec<u32>, (usize, usize, bool))> = (0..num_split)
    .into_par_iter()
    .filter(|slot| provides[*slot].is_some())
    .map(|slot| {
      let info = provides[slot].as_ref().unwrap();
      let circuit = machine.lowered_at(slot).unwrap();
      let trace = extended[slot].as_ref().unwrap();
      let width = trace.width();
      (0..trace.height())
        .into_par_iter()
        .map(|r| {
          let empty: [F; 0] = [];
          let main = &trace.values[r * width..(r + 1) * width];
          let interactions = &circuit.lowered.interactions;
          let qual = interactions.iter().enumerate().all(|(i, interaction)| {
            i == info.interaction
              || interaction.multiplicity.eval_row(&empty, main) == F::zero()
              || table_universe.contains(&canonical_tuple(
                interaction
                  .values
                  .iter()
                  .map(|v| v.eval_row(&empty, main).as_canonical_u32())
                  .collect(),
              ))
          });
          let tuple = canonical_tuple(
            interactions[info.interaction]
              .values
              .iter()
              .map(|v| v.eval_row(&empty, main).as_canonical_u32())
              .collect(),
          );
          (tuple, (slot, r, qual))
        })
        .collect::<Vec<_>>()
    })
    .flatten()
    .collect::<Vec<_>>();
  let provide_index = TupleIndex::build(provide_index);
  if timing_enabled() {
    eprintln!(
      "hypercube: provide and affinity indexes built in {:.2?} (rss {} GB)",
      index_start.elapsed(),
      rss_gb()
    );
  }

  // The binding bound is `log_m <= 29` (`slop-jagged` verifier.rs:
  // `log_m >= 30 → AreaOutOfBounds`, `log_m` being the log of the round's
  // stacking-padded area), so the padded area must stay at or below 2^29;
  // leave headroom for the preprocessed round and the stacking round-up.
  const AREA_BOUND: usize = (1 << 29) - (32 << 20);
  // Splitting a shard changes its neighbours' crossings too, so a shard
  // that fit can overflow again; with incremental rounds, converging is
  // cheap, so allow many.
  const MAX_REFINE_ROUNDS: usize = 24;
  let debug = debug_enabled();

  // ── Rounds are incremental. A round only splits the intervals that
  // overflowed, so most shards see the same epoch slice again: their demand
  // is cached by interval, and their chunks and residual by interval plus a
  // fingerprint of the chunks' edits (reductions, duplicates, affinity
  // blocks), which do move when other shards' demands change. Only the
  // shards whose inputs changed are rescanned.
  type Interval = (u64, u64);
  // Cached per interval: the shard's views last round and its *base*
  // residual (every chunk's interactions plus the claim, before the tables
  // absorb anything). When only the edits moved — other shards' demands
  // reduced more home rows in the slice, affinity blocks came or went —
  // the base is updated by those differences alone.
  let mut residual_cache: HashMap<Interval, (Vec<Option<View>>, Residual)> =
    HashMap::new();
  // Per interval: the affinity votes `(slot, block, weight)` its demand
  // casts, and the rows its demand replicates.
  type Votes = std::sync::Arc<Vec<(usize, usize, i128)>>;
  type Replicated = std::sync::Arc<Vec<(usize, usize, i128)>>;
  let mut votes_cache: HashMap<Interval, Votes> = HashMap::new();
  let mut replicated_cache: HashMap<Interval, Replicated> = HashMap::new();

  for refine_round in 0..=MAX_REFINE_ROUNDS {
    let round_start = std::time::Instant::now();
    let timing = timing_enabled();
    let mut step_start = std::time::Instant::now();
    let mut step = |what: &str| {
      if timing {
        eprintln!(
          "hypercube refine round {refine_round}: {what} in {:.2?} (rss {} \
           GB)",
          step_start.elapsed(),
          rss_gb()
        );
      }
      step_start = std::time::Instant::now();
    };
    let num_shards = boundaries.len() - 1;
    let cut = |h: usize, k: usize| (h as f64 * boundaries[k]) as usize;
    let plans: Vec<ShardPlan> = (0..num_shards)
      .map(|k| {
        let ranges = (0..num_split)
          .map(|slot| {
            if is_atomic(slot) || extended[slot].is_none() {
              return 0..0;
            }
            let h = extended[slot].as_ref().unwrap().height();
            cut(h, k)..cut(h, k + 1)
          })
          .collect();
        ShardPlan { ranges }
      })
      .collect();

    let intervals: Vec<Interval> = (0..num_shards)
      .map(|k| (boundaries[k].to_bits(), boundaries[k + 1].to_bits()))
      .collect();

    // ── Demand pass: what does each shard's epoch slice require? Only
    // for the intervals not seen before: a demand is used for the votes
    // and the replicated rows, which are cached per interval, and dropped.
    let mut demands: Vec<Option<Residual>> = plans
      .par_iter()
      .zip(&intervals)
      .map(|(plan, key)| {
        if votes_cache.contains_key(key) && replicated_cache.contains_key(key) {
          return None;
        }
        let mut demand: Residual = HashMap::new();
        for &slot in &split_slots {
          let range = plan.ranges[slot].clone();
          if range.is_empty() {
            continue;
          }
          let circuit = machine.lowered_at(slot).unwrap();
          accumulate_balance(
            circuit,
            &Chunk::View(View::range(slot, range)),
            extended,
            &mut demand,
          );
        }
        // Only what the slice requires and does not provide is used.
        demand.retain(|_, r| *r > 0);
        demand.shrink_to_fit();
        Some(demand)
      })
      .collect();
    // The claim demands the entry function's return tuple in shard 0.
    if let Some(demand) = &mut demands[0] {
      let claim_tuple =
        canonical_tuple(claim.iter().map(|v| v.as_canonical_u32()).collect());
      *demand.entry(claim_tuple).or_default() += 1;
    }

    step("demands");
    // ── Load-affinity assignment for the dependency-free circuits (Aiur's
    // memories): their rows are stored at creation time but loaded much
    // later, so epoch placement makes every load cross. Assign each block
    // of rows to the shard that demands it most (defaulting to the epoch
    // shard), at the price of two counter-chain tuples per block run.
    let mut votes: Vec<Vec<i128>> = (0..num_split)
      .map(|slot| {
        if !affinity[slot] {
          return vec![];
        }
        let h = extended[slot].as_ref().unwrap().height();
        vec![0i128; h.div_ceil(AFFINITY_BLOCK) * num_shards]
      })
      .collect();
    let shard_votes: Vec<Votes> = demands
      .par_iter()
      .zip(&intervals)
      .map(|(demand, key)| {
        if let Some(cached) = votes_cache.get(key) {
          return cached.clone();
        }
        std::sync::Arc::new(
          demand
            .as_ref()
            .expect("a new interval's demand")
            .iter()
            .filter(|(_, r)| **r > 0)
            .filter_map(|(tuple, r)| {
              let (slot, block) = affinity_index.get(tuple)?;
              Some((*slot, *block, *r))
            })
            .collect(),
        )
      })
      .collect();
    votes_cache =
      intervals.iter().copied().zip(shard_votes.iter().cloned()).collect();
    for (shard, cast) in shard_votes.iter().enumerate() {
      for (slot, block, r) in cast.iter() {
        votes[*slot][*block * num_shards + shard] += r;
      }
    }
    let block_home: Vec<Vec<usize>> = (0..num_split)
      .map(|slot| {
        if !affinity[slot] {
          return vec![];
        }
        let h = extended[slot].as_ref().unwrap().height();
        let cuts: Vec<usize> = (0..=num_shards).map(|k| cut(h, k)).collect();
        (0..h.div_ceil(AFFINITY_BLOCK))
          .map(|b| {
            let v = &votes[slot][b * num_shards..(b + 1) * num_shards];
            let (best, best_votes) =
              v.iter().enumerate().max_by_key(|(_, n)| **n).unwrap();
            if *best_votes > 0 {
              best
            } else {
              // Un-demanded block: keep its epoch shard.
              cuts.partition_point(|c| *c <= b * AFFINITY_BLOCK) - 1
            }
          })
          .collect()
      })
      .collect();
    drop(votes);

    step("affinity");
    // ── Duplicate each demanded, qualifying row into its demanding shards;
    // the home copy's multiplicity is reduced by what the duplicates took.
    let replicated: Vec<Replicated> = demands
      .par_iter()
      .zip(&intervals)
      .map(|(demand, key)| {
        if let Some(cached) = replicated_cache.get(key) {
          return cached.clone();
        }
        let mut rows: Vec<(usize, usize, i128)> = demand
          .as_ref()
          .expect("a new interval's demand")
          .iter()
          .filter(|(_, r)| **r > 0)
          .filter_map(|(tuple, r)| {
            let (slot, row, qual) = provide_index.get(tuple)?;
            qual.then_some((*slot, *row, *r))
          })
          .collect();
        rows.sort_unstable();
        std::sync::Arc::new(rows)
      })
      .collect();
    replicated_cache =
      intervals.iter().copied().zip(replicated.iter().cloned()).collect();
    drop(demands);
    // Per slot, ascending by row, so a shard's slice of them is a range:
    // every duplicated row, sorted, then summed per home row.
    let reductions: Vec<Vec<(usize, F)>> = (0..num_split)
      .map(|slot| {
        if provides[slot].is_none() {
          return vec![];
        }
        // A dense accumulator over the circuit's rows (one slot at a time,
        // so the largest circuit's rows bound the transient memory); each
        // shard's list is sorted by slot, so its rows for `slot` are a
        // slice. Multiplicities fit an `i64` comfortably.
        let height = extended[slot].as_ref().map_or(0, Matrix::height);
        let mut dense = vec![0i64; height];
        for rows in &replicated {
          let lo = rows.partition_point(|(s, _, _)| *s < slot);
          let hi = rows.partition_point(|(s, _, _)| *s <= slot);
          for (_, row, r) in &rows[lo..hi] {
            dense[*row] += i64::try_from(*r).expect("multiplicity fits i64");
          }
        }
        dense
          .into_iter()
          .enumerate()
          .filter(|(_, d)| *d != 0)
          .map(|(row, d)| (row, to_field(i128::from(d))))
          .collect()
      })
      .collect();

    step("replication");
    // ── Per-shard chunks and residuals.
    let cache_hits = std::sync::atomic::AtomicUsize::new(0);
    let cached: Vec<Option<(Vec<Option<View>>, Residual)>> =
      intervals.iter().map(|key| residual_cache.remove(key)).collect();
    let per_shard: Vec<(
      Vec<Option<View>>,
      Residual,
      Vec<Option<Chunk>>,
      Residual,
    )> = plans
      .par_iter()
      .zip(&replicated)
      .zip(cached.into_par_iter())
      .enumerate()
      .map(|(shard_index, ((plan, replicated), cached))| {
        let is_claim_shard = shard_index == 0;
        let pv = machine.base_public_values(claim, is_claim_shard);
        let mut chunks: Vec<Option<Chunk>> = Vec::with_capacity(num_split);
        for slot in 0..num_split {
          let circuit = machine.lowered_at(slot).unwrap();
          let chunk = if is_atomic(slot) {
            extended[slot].clone().map(|mut m| {
              refresh_public_columns(circuit, &mut m, &pv);
              Chunk::Owned(m)
            })
          } else if affinity[slot] {
            let h = extended[slot].as_ref().unwrap().height();
            let mut ranges: Vec<std::ops::Range<usize>> = Vec::new();
            for (b, home) in block_home[slot].iter().enumerate() {
              if *home == shard_index {
                let lo = b * AFFINITY_BLOCK;
                let hi = ((b + 1) * AFFINITY_BLOCK).min(h);
                match ranges.last_mut() {
                  Some(last) if last.end == lo => last.end = hi,
                  _ => ranges.push(lo..hi),
                }
              }
            }
            (!ranges.is_empty()).then(|| {
              Chunk::View(View {
                slot,
                ranges,
                reductions: vec![],
                extra: vec![],
                mult_col: None,
              })
            })
          } else {
            // The epoch slice, with home multiplicities reduced by what
            // the duplicates below took over.
            let range = plan.ranges[slot].clone();
            (extended[slot].is_some() && !range.is_empty()).then(|| {
              let mut view = View::range(slot, range.clone());
              if let Some(info) = &provides[slot]
                && !reductions[slot].is_empty()
              {
                let all = &reductions[slot];
                let lo = all.partition_point(|(r, _)| *r < range.start);
                let hi = all.partition_point(|(r, _)| *r < range.end);
                view.mult_col = Some(info.mult_col);
                view.reductions = all[lo..hi].to_vec();
              }
              Chunk::View(view)
            })
          };
          chunks.push(chunk);
        }
        // The duplicated rows, appended to their circuits' chunks with the
        // demanded multiplicity (`replicated` is sorted by slot).
        for group in replicated.chunk_by(|(a, _, _), (b, _, _)| a == b) {
          let slot = group[0].0;
          let info = provides[slot].as_ref().unwrap();
          let extra: Vec<(usize, F)> =
            group.iter().map(|(_, row, r)| (*row, to_field(*r))).collect();
          match &mut chunks[slot] {
            Some(Chunk::View(view)) => {
              view.mult_col = Some(info.mult_col);
              view.extra.extend(extra);
            },
            Some(Chunk::Owned(_)) => {
              unreachable!("duplicated rows belong to splittable circuits")
            },
            none => {
              *none = Some(Chunk::View(View {
                slot,
                ranges: vec![],
                reductions: vec![],
                extra,
                mult_col: Some(info.mult_col),
              }));
            },
          }
        }

        let views: Vec<Option<View>> = chunks
          .iter()
          .map(|chunk| match chunk {
            Some(Chunk::View(v)) => Some(v.clone()),
            _ => None,
          })
          .collect();
        let updated = cached.and_then(|(old, base)| {
          update_base(machine, extended, &provides, &old, &views, base)
        });
        let base = match updated {
          Some(base) => {
            cache_hits.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            base
          },
          None => {
            let mut base: Residual = HashMap::new();
            for (slot, chunk) in chunks.iter().enumerate() {
              let Some(chunk) = chunk else { continue };
              let circuit = machine.lowered_at(slot).unwrap();
              accumulate_balance(circuit, chunk, extended, &mut base);
            }
            if is_claim_shard {
              // The claim send from the public values is a require of the
              // entry function's return tuple.
              let claim_tuple = canonical_tuple(
                claim.iter().map(|v| v.as_canonical_u32()).collect(),
              );
              *base.entry(claim_tuple).or_default() += 1;
            }
            // Tuples balanced within the shard are not part of the base
            // (a later delta re-creates an entry if it needs one).
            base.retain(|_, r| *r != 0);
            base.shrink_to_fit();
            base
          },
        };

        // Absorb what the shard's own tables can provide (the tables are
        // atomic circuits, hence owned chunks, fresh every round).
        let mut residual = base.clone();
        for (slot, chunk) in chunks.iter_mut().enumerate() {
          let Some(Chunk::Owned(chunk)) = chunk else { continue };
          let circuit = machine.lowered_at(slot).unwrap();
          absorb_into_tables(circuit, chunk, &mut residual);
        }
        residual.retain(|_, r| *r != 0);

        (views, base, chunks, residual)
      })
      .collect();
    let mut bases = Vec::with_capacity(per_shard.len());
    let mut shard_chunks = Vec::with_capacity(per_shard.len());
    let mut residuals = Vec::with_capacity(per_shard.len());
    for (views, base, chunks, residual) in per_shard {
      bases.push((views, base));
      shard_chunks.push(chunks);
      residuals.push(residual);
    }

    step(&format!(
      "residuals ({} of {num_shards} shards cached)",
      cache_hits.load(std::sync::atomic::Ordering::Relaxed)
    ));
    // ── Match residuals into pairwise flows. Tuples are independent, so
    // the matching runs in parallel over hash buckets of them.
    const BUCKETS: usize = 512;
    let bucket_of = |tuple: &Vec<u32>| -> usize {
      use std::hash::{Hash, Hasher};
      let mut h = std::hash::DefaultHasher::new();
      tuple.hash(&mut h);
      usize::try_from(h.finish() % BUCKETS as u64).expect("bucket index")
    };
    let per_shard_buckets: Vec<Vec<Vec<(&Vec<u32>, i128)>>> = residuals
      .par_iter()
      .map(|residual| {
        let mut buckets = vec![Vec::new(); BUCKETS];
        for (tuple, r) in residual {
          buckets[bucket_of(tuple)].push((tuple, *r));
        }
        buckets
      })
      .collect();
    let matched: Vec<Vec<(usize, AdapterRow)>> = (0..BUCKETS)
      .into_par_iter()
      .map(|b| {
        let mut by_tuple: HashMap<&Vec<u32>, Vec<(usize, i128)>> =
          HashMap::new();
        for (shard, buckets) in per_shard_buckets.iter().enumerate() {
          for (tuple, r) in &buckets[b] {
            by_tuple.entry(tuple).or_default().push((shard, *r));
          }
        }
        let mut out: Vec<(usize, AdapterRow)> = Vec::new();
        for (tuple, mut entries) in by_tuple {
          let total: i128 = entries.iter().map(|(_, r)| r).sum();
          assert_eq!(
            total, 0,
            "unbalanced residual for tuple {tuple:?}: the partitioner lost \
             flow"
          );
          let field_tuple: Vec<F> =
            tuple.iter().map(|v| F::from_canonical_u32(*v)).collect();
          entries.sort_unstable();
          let (mut needs, mut gives): (Vec<_>, Vec<_>) =
            entries.into_iter().partition(|(_, r)| *r > 0);
          let mut give = gives.pop();
          for (shard, mut need) in needs.drain(..) {
            while need > 0 {
              let (giver, avail) =
                give.as_mut().expect("flow matching exhausted");
              let amount = need.min(-*avail);
              let row = |import| AdapterRow {
                import,
                amount: to_field(amount),
                tuple: field_tuple.clone(),
              };
              out.push((shard, row(true)));
              out.push((*giver, row(false)));
              need -= amount;
              *avail += amount;
              if *avail == 0 {
                give = gives.pop();
              }
            }
          }
          assert!(
            give.is_none() && gives.is_empty(),
            "flow matching left surplus"
          );
        }
        out
      })
      .collect();
    drop(per_shard_buckets);
    let mut adapters: Vec<Vec<AdapterRow>> = vec![vec![]; plans.len()];
    for rows in matched {
      for (shard, row) in rows {
        adapters[shard].push(row);
      }
    }

    step("flow matching");
    // ── Measure every shard against the area bound; split the intervals of
    // the shards that do not fit and try again.
    let totals: Vec<usize> = shard_chunks
      .iter()
      .zip(&adapters)
      .map(|(chunks, rows)| {
        let chunk_cells: usize = chunks
          .iter()
          .flatten()
          .map(|t| {
            t.height().max(1).next_multiple_of(ROW_ALIGNMENT)
              * t.width(extended)
          })
          .sum();
        let mut class_rows = vec![0usize; machine.global_classes.len()];
        for row in rows {
          class_rows[GlobalSpec::class_for(row.tuple.len()) - 1] += 1;
        }
        let adapter_cells: usize = machine
          .global_classes
          .iter()
          .zip(&class_rows)
          .map(|(spec, rows)| {
            rows.max(&1).next_multiple_of(ROW_ALIGNMENT) * spec.width()
          })
          .sum();
        chunk_cells + adapter_cells + 256 + ROW_ALIGNMENT
      })
      .collect();
    // The row cap is a per-chunk bound the prover asserts on (a padded MLE
    // of `max_log_row_count` variables), and the epoch seed only sized the
    // ORIGINAL heights: affinity moves and the duplicated rows appended
    // above can push a chunk past it, as can an adapter class. Treat that
    // like an area overflow — the shard's interval gets split.
    let tallest: Vec<usize> = shard_chunks
      .iter()
      .zip(&adapters)
      .map(|(chunks, rows)| {
        let chunk_rows = chunks
          .iter()
          .flatten()
          .map(|t| t.height().max(1).next_multiple_of(ROW_ALIGNMENT))
          .max()
          .unwrap_or(0);
        let mut class_rows = vec![0usize; machine.global_classes.len()];
        for row in rows {
          class_rows[GlobalSpec::class_for(row.tuple.len()) - 1] += 1;
        }
        let adapter_rows = class_rows
          .iter()
          .map(|rows| rows.max(&1).next_multiple_of(ROW_ALIGNMENT))
          .max()
          .unwrap_or(0);
        chunk_rows.max(adapter_rows)
      })
      .collect();
    // A shard within a few percent of a bound is split too: splitting a
    // neighbour moves affinity blocks and crossings, and a shard left right
    // at the bound comes back over it next round, one round per shard.
    const SLACK: f64 = 0.97;
    let area_limit = (AREA_BOUND as f64 * SLACK) as usize;
    let rows_limit = (params.max_rows as f64 * SLACK) as usize;
    let over: Vec<usize> = (0..num_shards)
      .filter(|k| totals[*k] > area_limit || tallest[*k] > rows_limit)
      .collect();

    if timing_enabled() {
      let dup: usize = replicated.iter().map(|r| r.len()).sum();
      let crossings: usize = adapters.iter().map(Vec::len).sum();
      eprintln!(
        "hypercube refine round {refine_round}: {num_shards} shards, \
         {dup} duplicated rows, {crossings} adapter rows, peak \
         ~{} cells, tallest chunk {} rows (cap {}), {} shard(s) over the \
         bound; {:.2?}",
        totals.iter().max().unwrap_or(&0),
        tallest.iter().max().unwrap_or(&0),
        params.max_rows,
        over.len(),
        round_start.elapsed()
      );
    }

    if over.is_empty() {
      if debug {
        // Crossing composition: which providers dominate the boundary?
        let mut by_kind: HashMap<(u32, u32), u64> = HashMap::new();
        for rows in &adapters {
          for row in rows {
            let key = (
              row.tuple.first().map_or(0, |v| v.as_canonical_u32()),
              row.tuple.get(1).map_or(0, |v| v.as_canonical_u32()),
            );
            *by_kind.entry(key).or_default() += 1;
          }
        }
        let mut top: Vec<_> = by_kind.into_iter().collect();
        top.sort_unstable_by_key(|(_, n)| std::cmp::Reverse(*n));
        top.truncate(12);
        eprintln!(
          "hypercube crossing composition (channel, second limb) → rows:"
        );
        for ((ch, second), n) in top {
          eprintln!("  ({ch}, {second}): {n}");
        }
        for (shard, ((chunks, rows), total)) in
          shard_chunks.iter().zip(&adapters).zip(&totals).enumerate()
        {
          let chunk_cells: usize = chunks
            .iter()
            .flatten()
            .map(|t| {
              t.height().max(1).next_multiple_of(ROW_ALIGNMENT)
                * t.width(extended)
            })
            .sum();
          eprintln!(
            "hypercube shard {shard}: {chunk_cells} circuit cells, {} \
             adapter rows, {} residual tuples, ~{total} total cells",
            rows.len(),
            residuals[shard].len(),
          );
        }
      }
      // Assembly is deferred to `Partition::assemble`.
      let shards = shard_chunks
        .into_iter()
        .zip(adapters)
        .map(|(chunks, adapters)| {
          std::sync::Mutex::new(Some(PlannedShard { chunks, adapters }))
        })
        .collect();
      return Ok(Partition { extended, shards, claim: claim.to_vec() });
    }
    if refine_round == MAX_REFINE_ROUNDS {
      let worst = *over.iter().max_by_key(|k| totals[**k]).unwrap();
      return Err(BuildError::ShardTooLarge {
        shard: worst,
        cells: totals[worst],
      });
    }
    residual_cache = intervals.into_iter().zip(bases).collect();
    // Split an overflowing interval into as many parts as its overflow
    // calls for (area and row cap alike) rather than in two, aiming below
    // the bounds: splitting creates crossings, in the parts and in their
    // neighbours, so a part landing right at the bound comes back as a
    // straggler the next round, each costing a round.
    const SPLIT_TARGET: f64 = 0.9;
    let mut refined = Vec::with_capacity(boundaries.len() + over.len());
    for k in 0..num_shards {
      refined.push(boundaries[k]);
      if over.contains(&k) {
        let by_area = totals[k] as f64 / (AREA_BOUND as f64 * SPLIT_TARGET);
        let by_rows =
          tallest[k] as f64 / (params.max_rows as f64 * SPLIT_TARGET);
        let parts = by_area.max(by_rows).ceil().max(2.0);
        let (lo, hi) = (boundaries[k], boundaries[k + 1]);
        for j in 1..parts as usize {
          refined.push(lo + (hi - lo) * j as f64 / parts);
        }
      }
    }
    refined.push(1.0);
    boundaries = refined;
  }
  unreachable!("refinement loop always returns")
}

/// The ranges in `new` not in `old` and vice versa (both ascending and
/// disjoint).
fn range_diff(
  old: &[std::ops::Range<usize>],
  new: &[std::ops::Range<usize>],
) -> (Vec<std::ops::Range<usize>>, Vec<std::ops::Range<usize>>) {
  let mut points: Vec<usize> =
    old.iter().chain(new).flat_map(|r| [r.start, r.end]).collect();
  points.sort_unstable();
  points.dedup();
  let covers = |ranges: &[std::ops::Range<usize>], lo: usize| {
    let i = ranges.partition_point(|r| r.end <= lo);
    ranges.get(i).is_some_and(|r| r.start <= lo)
  };
  let (mut added, mut removed) = (Vec::new(), Vec::new());
  for w in points.windows(2) {
    let (lo, hi) = (w[0], w[1]);
    match (covers(old, lo), covers(new, lo)) {
      (false, true) => added.push(lo..hi),
      (true, false) => removed.push(lo..hi),
      _ => {},
    }
  }
  (added, removed)
}

/// A cached base residual brought up to date with this round's views, or
/// `None` when the change is not one this handles (the duplicated rows
/// differ, or a chunk appeared or vanished): rows that joined or left an
/// affinity view are added or subtracted, and a home row whose reduction
/// changed moves its provide tuple by the difference.
fn update_base(
  machine: &AiurMachine,
  extended: &[Option<RowMajorMatrix<F>>],
  provides: &[Option<ProvideInfo>],
  old: &[Option<View>],
  new: &[Option<View>],
  mut base: Residual,
) -> Option<Residual> {
  for (slot, (old, new)) in old.iter().zip(new).enumerate() {
    let (old, new) = match (old, new) {
      (None, None) => continue,
      (Some(old), Some(new)) => (old, new),
      _ => return None,
    };
    if old.slot != new.slot || old.extra != new.extra {
      return None;
    }
    let circuit = machine.lowered_at(slot).unwrap();
    let trace = extended[slot].as_ref().expect("viewed trace");
    // Rows that moved in or out.
    let (added, removed) = range_diff(&old.ranges, &new.ranges);
    for (ranges, sign) in [(added, 1i128), (removed, -1i128)] {
      if ranges.is_empty() {
        continue;
      }
      let view = View {
        slot,
        ranges,
        reductions: vec![],
        extra: vec![],
        mult_col: None,
      };
      let mut delta: Residual = HashMap::new();
      accumulate_balance(circuit, &Chunk::View(view), extended, &mut delta);
      for (tuple, r) in delta {
        *base.entry(tuple).or_default() += sign * r;
      }
    }
    // Reductions that changed: the row's provide multiplicity is
    // `-(orig - delta)`, so its residual moves by the delta's change.
    if old.reductions != new.reductions {
      let info = provides[slot].as_ref()?;
      let interaction = &circuit.lowered.interactions[info.interaction];
      let empty: [F; 0] = [];
      let w = trace.width();
      let (mut i, mut j) = (0, 0);
      while i < old.reductions.len() || j < new.reductions.len() {
        let (row, change) = match (old.reductions.get(i), new.reductions.get(j))
        {
          (Some((ro, d0)), Some((rn, d1))) if ro == rn => {
            i += 1;
            j += 1;
            (*ro, *d1 - *d0)
          },
          (Some((ro, d0)), Some((rn, _))) if ro < rn => {
            i += 1;
            (*ro, -*d0)
          },
          (Some((ro, d0)), None) => {
            i += 1;
            (*ro, -*d0)
          },
          (_, Some((rn, d1))) => {
            j += 1;
            (*rn, *d1)
          },
          (None, None) => unreachable!(),
        };
        if change == F::zero() {
          continue;
        }
        let main = &trace.values[row * w..(row + 1) * w];
        let tuple = canonical_tuple(
          interaction
            .values
            .iter()
            .map(|v| v.eval_row(&empty, main).as_canonical_u32())
            .collect(),
        );
        *base.entry(tuple).or_default() += signed(change);
      }
    }
  }
  Some(base)
}

/// Panics if a shard record's interactions do not balance (see the call
/// site above). Mirrors what the chips and `eval_public_values` emit.
/// Rows are checked in parallel chunks (records are assembled, and so
/// checked, one at a time).
pub(crate) fn debug_check_balance(
  machine: &AiurMachine,
  shard: usize,
  record: &AiurRecord,
) {
  use crate::record::{CLAIM_WIDTH, PV_CHAIN_LEN, PV_CLAIM_FLAG, PV_DIGEST};
  use sp1_hypercube::septic_digest::SepticDigest;
  fn add(balance: &mut HashMap<Vec<u32>, i128>, values: &[F], mult: F) {
    if mult == F::zero() {
      return;
    }
    let tuple =
      canonical_tuple(values.iter().map(|v| v.as_canonical_u32()).collect());
    *balance.entry(tuple).or_default() += signed(mult);
  }
  const CHUNK: usize = 1 << 12;
  let items: Vec<(usize, usize, usize)> = (0..machine.num_slots())
    .flat_map(|slot| {
      let h = record.traces[slot].as_ref().map_or(0, Matrix::height);
      (0..h).step_by(CHUNK).map(move |lo| (slot, lo, (lo + CHUNK).min(h)))
    })
    .collect();
  let partial: Vec<HashMap<Vec<u32>, i128>> = items
    .par_iter()
    .map(|&(slot, lo, hi)| {
      let mut balance: HashMap<Vec<u32>, i128> = HashMap::new();
      let trace = record.traces[slot].as_ref().expect("slot has a trace");
      let width = trace.width();
      if let Some(circuit) = machine.lowered_at(slot) {
        let empty: [F; 0] = [];
        for r in lo..hi {
          let main = &trace.values[r * width..(r + 1) * width];
          let prep: &[F] = match &circuit.preprocessed {
            Some(p) if r < p.height() => {
              &p.values[r * p.width()..(r + 1) * p.width()]
            },
            _ => &empty,
          };
          for interaction in &circuit.lowered.interactions {
            let values: Vec<F> = interaction
              .values
              .iter()
              .map(|v| v.eval_row(prep, main))
              .collect();
            add(
              &mut balance,
              &values,
              interaction.multiplicity.eval_row(prep, main),
            );
          }
        }
      } else {
        let spec =
          machine.global_classes[slot - machine.idx_adapter_bytes() - 1];
        for r in lo..hi {
          let row = &trace.values[r * width..(r + 1) * width];
          for (values, mult) in spec.row_lookups(row) {
            add(&mut balance, &values, mult);
          }
        }
      }
      balance
    })
    .collect();
  let mut balance: HashMap<Vec<u32>, i128> = HashMap::new();
  for part in partial {
    for (tuple, r) in part {
      *balance.entry(tuple).or_default() += r;
    }
  }
  // `eval_public_values`.
  let pv = &record.public_values;
  add(&mut balance, &pv[..CLAIM_WIDTH], pv[PV_CLAIM_FLAG]);
  let chain_channel = F::from_canonical_u32(crate::global::CHAIN_CHANNEL);
  let start = SepticDigest::<F>::zero().0;
  let mut values = vec![chain_channel, F::zero()];
  values.extend_from_slice(&start.x.0);
  values.extend_from_slice(&start.y.0);
  add(&mut balance, &values, F::one());
  let mut values = vec![chain_channel, pv[PV_CHAIN_LEN]];
  values.extend_from_slice(&pv[PV_DIGEST..PV_DIGEST + 14]);
  add(&mut balance, &values, -F::one());

  let bad: Vec<_> = balance.iter().filter(|(_, r)| **r != 0).take(4).collect();
  assert!(
    bad.is_empty(),
    "shard {shard}: record does not balance; offending tuples: {bad:?}"
  );
}

/// The provide interaction of a relocation candidate: a single interaction
/// whose multiplicity is exactly `-1` times a free frontend column (no
/// constraint or other interaction reads it).
struct ProvideInfo {
  interaction: usize,
  mult_col: usize,
}

fn references_main(ast: &crate::expr::Ast, col: usize) -> bool {
  use crate::expr::Ast;
  match ast {
    Ast::Const(_) | Ast::Public(_) => false,
    Ast::Col(c) => *c == Col::Main(col),
    Ast::Add(x, y) | Ast::Sub(x, y) | Ast::Mul(x, y) => {
      references_main(x, col) || references_main(y, col)
    },
    Ast::Neg(x) => references_main(x, col),
  }
}

fn provide_candidate(circuit: &LoweredCircuit) -> Option<ProvideInfo> {
  let lowered = &circuit.lowered;
  let mut found = None;
  for (i, interaction) in lowered.interactions.iter().enumerate() {
    let m = &interaction.multiplicity;
    if m.constant == F::zero()
      && let [(Col::Main(col), coef)] = m.terms.as_slice()
      && *coef == -F::one()
      && *col < lowered.frontend_width
    {
      if found.is_some() {
        return None;
      }
      found = Some(ProvideInfo { interaction: i, mult_col: *col });
    }
  }
  let info = found?;
  let col_free =
    !lowered.constraints.iter().any(|c| references_main(c, info.mult_col))
      && !lowered.interactions.iter().enumerate().any(|(i, interaction)| {
        let in_values = interaction
          .values
          .iter()
          .any(|v| v.terms.iter().any(|(c, _)| *c == Col::Main(info.mult_col)));
        in_values
          || (i != info.interaction
            && interaction
              .multiplicity
              .terms
              .iter()
              .any(|(c, _)| *c == Col::Main(info.mult_col)))
      });
  col_free.then_some(info)
}

/// The tuples a table circuit provides (see [`absorb_into_tables`] for the
/// pattern), or nothing if the circuit is not a pure table.
fn table_tuples(circuit: &LoweredCircuit) -> Vec<Vec<u32>> {
  let Some(prep) = &circuit.preprocessed else { return vec![] };
  for interaction in &circuit.lowered.interactions {
    let m = &interaction.multiplicity;
    let ok = m.constant == F::zero()
      && matches!(m.terms.as_slice(), [(Col::Main(c), _)]
        if *c < circuit.lowered.frontend_width)
      && interaction.values.iter().all(|v| {
        v.terms.iter().all(|(c, _)| matches!(c, Col::Preprocessed(_)))
      });
    if !ok {
      return vec![];
    }
  }
  let empty: [F; 0] = [];
  let mut out = vec![];
  for interaction in &circuit.lowered.interactions {
    for r in 0..prep.height() {
      let prep_row: &[F] =
        &prep.values[r * prep.width()..(r + 1) * prep.width()];
      let _ = &empty;
      out.push(canonical_tuple(
        interaction
          .values
          .iter()
          .map(|v| v.eval_row(prep_row, &[]).as_canonical_u32())
          .collect(),
      ));
    }
  }
  out
}

/// Re-evaluates the materialized columns that read public values (the
/// boundary's flag gate), which differ per shard.
fn refresh_public_columns(
  circuit: &LoweredCircuit,
  trace: &mut RowMajorMatrix<F>,
  pv: &[F],
) {
  if !circuit.lowered.materialized.iter().any(|(_, e)| e.references_public()) {
    return;
  }
  let width = trace.width();
  for r in 0..trace.height() {
    let row = &mut trace.values[r * width..(r + 1) * width];
    fill_materialized(circuit, r, row, pv);
  }
}

/// Adds a chunk's interaction multiplicities to the shard's residual.
fn accumulate_balance(
  circuit: &LoweredCircuit,
  chunk: &Chunk,
  extended: &[Option<RowMajorMatrix<F>>],
  residual: &mut HashMap<Vec<u32>, i128>,
) {
  let mut row = |prep: &[F], main: &[F]| {
    for interaction in &circuit.lowered.interactions {
      let mult = interaction.multiplicity.eval_row(prep, main);
      if mult == F::zero() {
        continue;
      }
      let tuple = canonical_tuple(
        interaction
          .values
          .iter()
          .map(|v| v.eval_row(prep, main).as_canonical_u32())
          .collect(),
      );
      *residual.entry(tuple).or_default() += signed(mult);
    }
  };
  let empty: [F; 0] = [];
  match chunk {
    Chunk::Owned(m) => {
      let width = m.width();
      for r in 0..m.height() {
        let main = &m.values[r * width..(r + 1) * width];
        let prep: &[F] = match &circuit.preprocessed {
          Some(p) if r < p.height() => {
            &p.values[r * p.width()..(r + 1) * p.width()]
          },
          _ => &empty,
        };
        row(prep, main);
      }
    },
    Chunk::View(view) => {
      // Splittable circuits have no preprocessed trace.
      let trace = extended[view.slot].as_ref().expect("viewed trace");
      view.for_each_row(trace, |main| row(&empty, main));
    },
  }
}

/// If the circuit is a pure table — every interaction's multiplicity is a
/// single main column and its tuple reads only preprocessed columns and
/// constants — set the multiplicity columns to absorb the matching
/// residuals. The byte tables have this shape.
fn absorb_into_tables(
  circuit: &LoweredCircuit,
  chunk: &mut RowMajorMatrix<F>,
  residual: &mut HashMap<Vec<u32>, i128>,
) {
  let Some(prep) = &circuit.preprocessed else { return };
  // Validate the whole circuit first: a free multiplicity must be a real
  // witness column (materialized columns are pinned by their defining
  // constraint — the boundary's flag gate must not be touched).
  for interaction in &circuit.lowered.interactions {
    let mult = &interaction.multiplicity;
    let [(Col::Main(col), _)] = mult.terms.as_slice() else { return };
    if mult.constant != F::zero()
      || *col >= circuit.lowered.frontend_width
      || interaction
        .values
        .iter()
        .any(|v| v.terms.iter().any(|(c, _)| matches!(c, Col::Main(_))))
    {
      return;
    }
  }
  let mut cells: Vec<(usize, F)> = Vec::new();
  for interaction in &circuit.lowered.interactions {
    let [(Col::Main(col), coef)] = interaction.multiplicity.terms.as_slice()
    else {
      unreachable!("validated above")
    };
    let inv = coef.inverse();
    let empty: [F; 0] = [];
    for r in 0..chunk.height() {
      let prep_row: &[F] = if r < prep.height() {
        &prep.values[r * prep.width()..(r + 1) * prep.width()]
      } else {
        &empty
      };
      let tuple = canonical_tuple(
        interaction
          .values
          .iter()
          .map(|v| v.eval_row(prep_row, &[]).as_canonical_u32())
          .collect(),
      );
      let Some(need) = residual.remove(&tuple) else { continue };
      // The table contributes `coef · value` and the cloned trace already
      // carries the whole execution's counts (which the residual includes),
      // so adjust the cell rather than overwrite it.
      let at = r * chunk.width() + col;
      cells.push((at, chunk.values[at] + to_field(-need) * inv));
    }
  }
  for (at, v) in cells {
    chunk.values[at] = v;
  }
}

/// Builds one shard's record from its chunks (splittable slices and full
/// atomic traces, multiplicities already absorbed) and adapter rows.
pub(crate) fn assemble_shard(
  machine: &AiurMachine,
  chunks: Vec<Option<RowMajorMatrix<F>>>,
  adapters: &[AdapterRow],
  claim: &[F],
  is_claim_shard: bool,
) -> AiurRecord {
  let mut pv = machine.base_public_values(claim, is_claim_shard);

  let mut traces: Vec<Option<RowMajorMatrix<F>>> = chunks
    .into_par_iter()
    .enumerate()
    .map(|(slot, chunk)| {
      let circuit = machine.lowered_at(slot).unwrap();
      let chunk = chunk.unwrap_or_else(|| {
        RowMajorMatrix::new(vec![], circuit.lowered.main_width)
      });
      Some(pad_chunk(circuit, chunk, &pv))
    })
    .collect();

  // Adapter chips, threading the accumulator chain and byte usage.
  let mut chain = ChainState::start();
  let mut per_class: Vec<Vec<AdapterRow>> =
    vec![vec![]; machine.global_classes.len()];
  for row in adapters {
    let class = GlobalSpec::class_for(row.tuple.len());
    per_class[class - 1].push(row.clone());
  }
  let global_traces: Vec<RowMajorMatrix<F>> = machine
    .global_classes
    .iter()
    .zip(&per_class)
    .map(|(spec, rows)| spec.build_trace(rows, &mut chain))
    .collect();

  // The adapter byte table's multiplicities come from the rows just built.
  let byte_mults: Vec<F> =
    chain.byte_counts.iter().map(|c| F::from_canonical_u64(*c)).collect();
  debug_assert_eq!(traces.len(), machine.idx_adapter_bytes());
  traces.push(Some(RowMajorMatrix::new(byte_mults, 1)));
  traces.extend(global_traces.into_iter().map(Some));
  debug_assert_eq!(traces.len(), machine.idx_constants());
  traces.push(Some(RowMajorMatrix::new(vec![F::zero(); ROW_ALIGNMENT], 1)));
  // The pad chip is filled by `shape::pad_record` at proving time.
  traces.push(None);
  debug_assert_eq!(traces.len(), machine.num_slots());

  pv[PV_CHAIN_LEN] = F::from_canonical_usize(chain.idx);
  pv[PV_DIGEST..PV_DIGEST + 7].copy_from_slice(&chain.acc.x.0);
  pv[PV_DIGEST + 7..PV_DIGEST + 14].copy_from_slice(&chain.acc.y.0);

  AiurRecord { traces, public_values: pv }
}

/// Pads a chunk to the row alignment, evaluating the materialized columns
/// on the padding rows (and re-evaluating the publics-dependent ones
/// everywhere, since they differ per shard).
fn pad_chunk(
  circuit: &LoweredCircuit,
  chunk: RowMajorMatrix<F>,
  pv: &[F],
) -> RowMajorMatrix<F> {
  let width = circuit.lowered.main_width;
  let real = chunk.height();
  let height = real.max(1).next_multiple_of(ROW_ALIGNMENT);
  let mut values = chunk.values;
  values.resize(height * width, F::zero());
  let refresh_all =
    circuit.lowered.materialized.iter().any(|(_, e)| e.references_public());
  let start = if refresh_all { 0 } else { real };
  for r in start..height {
    let row = &mut values[r * width..(r + 1) * width];
    fill_materialized(circuit, r, row, pv);
  }
  RowMajorMatrix::new(values, width)
}
