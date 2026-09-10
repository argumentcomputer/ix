//! Trace shards: row partitions of one execution's traces, proven as a batch
//! of multi-stark proofs under shared lookup challenges.
//!
//! Aiur's soundness is one LogUp identity over every row of every circuit,
//! and the only cross-row constraint in the system is the memory table's
//! pointer increment. So the rows of a record may be dealt out to several
//! proofs — each small enough for a given prover budget — provided all of
//! them evaluate the lookup argument under the same challenges and their
//! residuals sum to zero, which is exactly what [`multi_stark::batch`]
//! provides. This module decides the partition ([`ShardPlan`]), builds each
//! shard's witness, and states the verifier-side policy that makes a batch
//! mean what a single proof means.
//!
//! # Partition rules
//!
//! - **Function circuits**: any row partition. Rows are the queries with a
//!   nonzero multiplicity, in record order.
//! - **Memory circuits**: contiguous pointer ranges, one per shard, in
//!   pointer order. Contiguity keeps the `ptr + 1` transition satisfiable
//!   inside a shard; the two `memseg` lookups every memory row carries make
//!   the ranges' end points visible to the lookup argument, and the batch
//!   messages of [`boundary_messages`] close them so that only a partition
//!   tiling `[0, N)` balances (see the tiling argument below).
//! - **Byte tables**: present in every shard — the plan's `0..height` range
//!   marks the shard whose copy carries the record's multiplicities (shard
//!   0), and an empty range a copy with zero multiplicities, which adds
//!   nothing to the lookup sum. Deactivating the tables instead would save
//!   their (small, fixed) commitment per shard, but the in-circuit PCS
//!   verifier only handles preprocessed matrices of active circuits, so the
//!   tables stay active until that changes.
//! - **The entry claim** is carried by shard 0. Balance is global, so any
//!   shard could carry it; one fixed place keeps the policy simple.
//!
//! # Why the memory ranges must tile
//!
//! Every real memory row pushes `(memseg, w, ptr)` and pulls
//! `(memseg, w, ptr + 1)`. Over a shard's contiguous run `[a, b)` the
//! interior terms cancel, leaving one push of `a` and one pull of `b`. The
//! verifier pulls `A_j` and pushes `B_j` once per memory interval
//! `[A_j, B_j)` a record holds (a record's width-`w` table sits at its
//! pointer base, see `QueryRecord::pointer_base`). Balance on the channel
//! is then, as multisets, `{a_k} ∪ {B_j} = {b_k} ∪ {A_j}`. Viewing each
//! shard as an edge `a_k → b_k` of length `b_k − a_k ≥ 1` on the residues
//! mod `p`, that says every residue has equal in- and out-degree except a
//! unit source at each `A_j` and a unit sink at each `B_j`; the edges
//! decompose into source-to-sink paths plus directed cycles, and a directed
//! cycle on `Z_p` has total length at least `p`. [`AiurSystem::verify`]
//! checks that the shards' padded heights sum below `p`, which rules the
//! cycles out, and requires the intervals sorted and disjoint, so a path
//! from `A_j` can only end at `B_j` (reaching any other sink would wrap
//! around `Z_p`): the ranges tile each interval exactly. Hence `(w, ptr)` is
//! unique across the batch, and the memory channel means what it means in
//! a single proof.
//!
//! Two conditions carry that argument and are checked by the verifier, not
//! assumed: the intervals are inside the preamble the challenges are
//! derived from (two end points chosen after the challenges could solve
//! the two coordinates of any target imbalance), and no two intervals of
//! one width overlap (overlap would admit two paths through the same
//! pointers, i.e. two shards claiming them). The verifier does not need to
//! know which widths or intervals the records use: a missing pair leaves
//! the batch unbalanced, and a pair no shard fills balances only as the
//! zero contribution `A_j = B_j` (see [`AiurSystem::check_batch_policy`]).

use std::ops::Range;

use multi_stark::{
  batch::{BatchMessage, BatchPreamble, BatchProof, Retention},
  p3_field::{Field, PrimeCharacteristicRing, PrimeField64},
  system::SystemWitness,
};
use rayon::iter::{
  IndexedParallelIterator, IntoParallelIterator, ParallelIterator,
};

use crate::{
  G,
  execute::{IOBuffer, QueryRecord, record_retained_bytes},
  gadgets::{AiurGadget, bytes1::Bytes1, bytes2::Bytes2},
  memory::Memory,
  memseg_channel,
  synthesis::{
    AiurConfig, AiurSystem, CircuitType, EXTENSION_DEGREE, PeakProveBytes,
    calibrate_prover_rss,
  },
  trace::QueryPosition,
};

/// Upper bound on the shards of one batch, so the verifier's per-shard work
/// is bounded by a constant it knows.
pub const MAX_SHARDS: usize = 1 << 16;

/// Goldilocks characteristic, for the height-sum bound.
const GOLDILOCKS_ORDER: u128 = 0xffff_ffff_0000_0001;

/// Which rows of each circuit one shard carries, indexed by system circuit
/// order (see [`AiurSystem::circuit_types`]). Function and memory circuits
/// hold a row range; a byte-table circuit holds either its whole table
/// (`0..height`) or nothing (`0..0`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShardRows {
  pub rows: Vec<Range<usize>>,
}

/// A row partition of one record across K shards.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShardPlan {
  pub shards: Vec<ShardRows>,
  /// `(width, first pointer, rows)` for every memory interval the batch's
  /// records hold, ascending by width then pointer: the intervals the batch
  /// messages close the `memseg` channel with.
  pub memory_totals: Vec<(usize, usize, usize)>,
}

impl ShardPlan {
  pub fn num_shards(&self) -> usize {
    self.shards.len()
  }
}

/// Positions in the record of a plan's function-circuit row boundaries
/// ([`AiurSystem::row_index`]): per circuit, ascending `(row, position)`
/// pairs for every range start and end the plan uses; empty for
/// non-function circuits, whose ranges index their tables directly.
pub struct RowIndex {
  spans: Vec<Vec<(usize, QueryPosition)>>,
}

impl RowIndex {
  /// The query span of function circuit `circuit`'s rows `rows`.
  fn queries(
    &self,
    circuit: usize,
    rows: &Range<usize>,
  ) -> (QueryPosition, QueryPosition) {
    let spans = &self.spans[circuit];
    let position = |row: usize| {
      let i = spans
        .binary_search_by_key(&row, |&(r, _)| r)
        .expect("row boundary is in the index");
      spans[i].1
    };
    (position(rows.start), position(rows.end))
  }
}

/// Per-circuit row counts of a record, in system circuit order.
fn circuit_rows(system: &AiurSystem, record: &QueryRecord) -> Vec<usize> {
  system
    .circuit_types()
    .iter()
    .map(|ct| match ct {
      CircuitType::Function { idx } => {
        system.toplevel().function_rows(*idx, record)
      },
      CircuitType::Memory { width } => {
        record.memory_queries.get(width).map_or(0, |m| m.len())
      },
      CircuitType::Bytes1 => 256,
      CircuitType::Bytes2 => 65536,
    })
    .collect()
}

/// Committed cells a circuit with `rows` real rows occupies: its padded
/// height times its committed width (main + stage 2 + quotient). Zero for an
/// empty circuit, which is deactivated.
fn committed_cells(rows: usize, committed_width: usize) -> usize {
  if rows == 0 { 0 } else { rows.next_power_of_two() * committed_width }
}

impl AiurSystem {
  /// The single-shard plan: every row in shard 0.
  pub fn single_shard_plan(&self, record: &QueryRecord) -> ShardPlan {
    let rows = circuit_rows(self, record);
    ShardPlan {
      shards: vec![ShardRows { rows: rows.iter().map(|&r| 0..r).collect() }],
      memory_totals: self.memory_totals(record),
    }
  }

  /// `(width, first pointer, rows)` for each memory width with rows,
  /// ascending by width: the record's table of width `w` holds pointers
  /// `[base, base + rows)`.
  fn memory_totals(&self, record: &QueryRecord) -> Vec<(usize, usize, usize)> {
    let mut totals: Vec<(usize, usize, usize)> = self
      .toplevel()
      .memory_sizes
      .iter()
      .filter_map(|&w| {
        let rows = record.memory_queries.get(&w).map_or(0, |m| m.len());
        (rows > 0).then_some((w, record.pointer_base, rows))
      })
      .collect();
    totals.sort_unstable();
    totals
  }

  /// Partitions the record's rows into the fewest shards whose committed
  /// cells each fit `max_cells`, or the single-shard plan when `max_cells`
  /// is `None`. When no shard count meets the budget, the plan with the
  /// lightest heaviest shard found is returned.
  ///
  /// See [`plan_rows`] for the placement rules. The plan is a pure function
  /// of the record and the budget, so any prover derives the same shards,
  /// commitments and preamble.
  pub fn plan_shards(
    &self,
    record: &QueryRecord,
    max_cells: Option<usize>,
  ) -> ShardPlan {
    let Some(max_cells) = max_cells else {
      return self.single_shard_plan(record);
    };
    let rows = circuit_rows(self, record);
    self.plan_shards_from_rows(record, &rows, max_cells)
  }

  /// [`Self::plan_shards`] with the record's per-circuit row counts already
  /// taken, for callers that plan the same record repeatedly.
  fn plan_shards_from_rows(
    &self,
    record: &QueryRecord,
    rows: &[usize],
    max_cells: usize,
  ) -> ShardPlan {
    let widths = self.committed_widths();
    let shards = plan_rows(rows, &widths, &self.circuit_types(), max_cells);
    ShardPlan { shards, memory_totals: self.memory_totals(record) }
  }

  /// Committed cells of each shard of `plan`, the byte tables charged to
  /// every shard.
  pub(crate) fn shard_committed_cells(&self, plan: &ShardPlan) -> Vec<usize> {
    let widths = self.committed_widths();
    let types = self.circuit_types();
    plan
      .shards
      .iter()
      .map(|shard| {
        shard
          .rows
          .iter()
          .zip(&widths)
          .zip(&types)
          .map(|((range, &width), circuit_type)| {
            let rows = match circuit_type {
              CircuitType::Bytes1 => 256,
              CircuitType::Bytes2 => 65536,
              _ => range.len(),
            };
            committed_cells(rows, width)
          })
          .sum()
      })
      .collect()
  }

  /// Per-circuit committed width: main, stage 2 and quotient columns.
  pub(crate) fn committed_widths(&self) -> Vec<usize> {
    self
      .circuit_shapes()
      .iter()
      .map(|shape| {
        shape.main_width
          + shape.stage2_width
          + shape.quotient_degree * EXTENSION_DEGREE
      })
      .collect()
  }

  /// Where each function circuit's row ranges of `plan` sit in the record:
  /// one pass over each function's queries, so that building a shard's
  /// witness indexes its queries directly rather than counting rows from
  /// the start of the function (which, over K shards built twice, would
  /// visit every query 2K times).
  pub fn row_index(&self, record: &QueryRecord, plan: &ShardPlan) -> RowIndex {
    let circuit_types = self.circuit_types();
    let spans = circuit_types
      .into_par_iter()
      .enumerate()
      .map(|(ci, ct)| {
        let CircuitType::Function { idx } = ct else {
          return Vec::new();
        };
        // The logical boundaries every shard's range for this circuit
        // needs, ascending; then their positions in the query map.
        let mut bounds: Vec<usize> = plan
          .shards
          .iter()
          .flat_map(|s| [s.rows[ci].start, s.rows[ci].end])
          .collect();
        bounds.sort_unstable();
        bounds.dedup();
        let members = &self.toplevel().circuits[idx].members;
        let mut positions = Vec::with_capacity(bounds.len());
        let mut next = bounds.iter().peekable();
        let mut row = 0usize;
        for (m, &member) in members.iter().enumerate() {
          let queries = &record.function_queries[member];
          for (pos, (_, res)) in queries.iter().enumerate() {
            while next.peek().is_some_and(|&&b| b == row) {
              positions.push((row, (m, pos)));
              next.next();
            }
            if !res.multiplicity.is_zero() {
              row += 1;
            }
          }
        }
        // Boundaries at or past the last row map to one past the last
        // member's last query (an empty tail of zero-multiplicity queries
        // is skipped).
        for &b in next {
          assert_eq!(b, row, "plan range exceeds the circuit's rows");
          positions.push((row, (members.len(), 0)));
        }
        positions
      })
      .collect();
    RowIndex { spans }
  }

  /// The witness of shard `shard` of `plan`: each circuit's rows in the
  /// plan's ranges, built in parallel across circuits. `index` is
  /// [`Self::row_index`] of the same record and plan.
  pub fn shard_witness(
    &self,
    record: &QueryRecord,
    io_buffer: &IOBuffer,
    plan: &ShardPlan,
    index: &RowIndex,
    shard: usize,
  ) -> SystemWitness<G> {
    let circuit_types = self.circuit_types();
    let ranges = &plan.shards[shard].rows;
    assert_eq!(ranges.len(), circuit_types.len(), "plan/system circuit count");
    // A record with no queries: the source of a zero-multiplicity byte table.
    let zero_record = QueryRecord::new(self.toplevel());
    let witness_data = circuit_types
      .into_par_iter()
      .enumerate()
      .map(|(circuit_idx, circuit_type)| {
        let slot_arg_widths = self.slot_arg_widths(circuit_idx);
        let range = ranges[circuit_idx].clone();
        match circuit_type {
          CircuitType::Function { idx } => {
            let (start, end) = index.queries(circuit_idx, &range);
            self.toplevel().witness_data_range(
              idx,
              record,
              io_buffer,
              &slot_arg_widths,
              start,
              end,
              range.len(),
            )
          },
          CircuitType::Memory { width } => {
            Memory::witness_data_range(width, record, &slot_arg_widths, range)
          },
          // The byte tables are present in every shard; the shard the plan
          // assigns them carries the record's multiplicities, every other
          // shard a copy with zero multiplicities (see the module docs).
          CircuitType::Bytes1 => {
            let source = if range.is_empty() { &zero_record } else { record };
            Bytes1.witness_data(source, &slot_arg_widths)
          },
          CircuitType::Bytes2 => {
            let source = if range.is_empty() { &zero_record } else { record };
            Bytes2.witness_data(source, &slot_arg_widths)
          },
        }
      })
      .collect::<Vec<_>>();
    let (traces, lookups) = witness_data.into_iter().unzip();
    SystemWitness { traces, lookups }
  }

  /// Checks the batch-level policy that makes a [`BatchProof`] the proof of
  /// one execution. Besides the claim, it constrains the batch messages to
  /// the shape of the `memseg` closure and bounds the batch's rows:
  ///
  /// - exactly one claim across all shards, equal to `claim`;
  /// - the messages are consecutive pairs `pull (memseg, w, a)`,
  ///   `push (memseg, w, b)` with `a ≤ b` — nothing else — sorted by width
  ///   and, within a width, by disjoint intervals (`b` of one pair at most
  ///   `a` of the next), all compared as the integers the canonical field
  ///   elements are;
  /// - the padded heights of every active circuit of every shard sum to
  ///   less than the field characteristic.
  ///
  /// The verifier need not know which widths or intervals the records use:
  /// a missing pair leaves an interval's end points unmatched and the batch
  /// unbalanced, and a pair no shard fills balances only at `a = b`, where
  /// it is the zero contribution. What must be excluded is two pairs whose
  /// intervals overlap (two paths through the same pointers, i.e. two
  /// shards claiming them), a pair of any other shape, and a message on
  /// any other channel; the height bound is what lets the tiling argument
  /// treat `ptr + 1` as an integer increment (see the module docs).
  pub(crate) fn check_batch_policy(
    &self,
    claim: &[G],
    preamble: &BatchPreamble<AiurConfig>,
  ) -> Result<(), String> {
    let num_shards = preamble.headers.len();
    if num_shards == 0 || num_shards > MAX_SHARDS {
      return Err(format!("batch has {num_shards} shards"));
    }
    let num_circuits = self.system.circuits.len();
    let mut claims = preamble.headers.iter().flat_map(|h| h.claims.iter());
    match (claims.next(), claims.next()) {
      (Some(only), None) if only.as_slice() == claim => {},
      (Some(_), None) => return Err("batch carries a different claim".into()),
      (None, _) => return Err("batch carries no claim".into()),
      (Some(_), Some(_)) => {
        return Err("batch carries more than one claim".into());
      },
    }

    let mut height_sum: u128 = 0;
    for header in &preamble.headers {
      if header.active.len() != num_circuits {
        return Err("shard activation bitmap has the wrong length".into());
      }
      let active = header.active.iter().filter(|&&a| a).count();
      if header.log_degrees.len() != active {
        return Err("shard header heights do not match its activation".into());
      }
      for &log_degree in &header.log_degrees {
        height_sum += 1u128 << log_degree.min(127);
      }
    }
    if height_sum >= GOLDILOCKS_ORDER {
      return Err("batch rows exceed the field characteristic".into());
    }

    if !preamble.messages.len().is_multiple_of(2) {
      return Err("batch messages do not pair up".into());
    }
    let memseg = memseg_channel();
    // The previous pair's width and end; every width is at least one, so
    // `(0, 0)` precedes any first pair.
    let mut previous = (0u64, 0u64);
    for [pull, push] in preamble.messages.as_chunks::<2>().0 {
      let well_formed = pull.multiplicity == G::NEG_ONE
        && push.multiplicity == G::ONE
        && pull.args.len() == 3
        && push.args.len() == 3
        && pull.args[0] == memseg
        && push.args[0] == memseg
        && pull.args[1] == push.args[1];
      if !well_formed {
        return Err("batch messages are not memseg closure pairs".into());
      }
      let width = pull.args[1].as_canonical_u64();
      let start = pull.args[2].as_canonical_u64();
      let end = push.args[2].as_canonical_u64();
      if start > end {
        return Err("memseg closure interval ends before it starts".into());
      }
      let (previous_width, previous_end) = previous;
      let ordered = previous_width < width
        || (previous_width == width && previous_end <= start);
      if !ordered {
        return Err("memseg closure intervals are not sorted and disjoint".into());
      }
      previous = (width, end);
    }
    Ok(())
  }

  /// The projected prover peak of shard `shard` of `plan` with the record
  /// (`record_bytes` retained) resident for the shard's whole proof, as it
  /// is under `Retention::Regenerate`: the phase model over the shard's
  /// rows, the byte tables at full height, plus the record in every phase.
  pub fn shard_peak_bytes(
    &self,
    plan: &ShardPlan,
    shard: usize,
    record_bytes: usize,
  ) -> usize {
    let phases = self.shard_phases(plan, shard);
    let analytic =
      phases.phase_witness.max(phases.phase_stage2).max(phases.phase_open)
        + phases.preprocessed
        + record_bytes;
    calibrate_prover_rss(analytic)
  }

  /// The plan with the fewest shards whose projected peaks
  /// ([`Self::shard_peak_bytes`]) all fit `max_bytes`, with the heaviest
  /// shard's projected peak. When no shard count fits — the record plus
  /// the smallest shard the planner can cut already exceeds the budget —
  /// the error carries the lowest heaviest-shard peak any plan reached,
  /// the floor a budget would have to clear.
  ///
  /// The cell budget handed to [`Self::plan_shards`] is halved until a plan
  /// fits, then the largest fitting cell budget is found by bisection: a
  /// larger budget means fewer shards, and every shard is a fixed price in
  /// proof size and verification.
  pub fn plan_shards_within(
    &self,
    record: &QueryRecord,
    max_bytes: usize,
  ) -> Result<(ShardPlan, usize), usize> {
    let record_bytes = record_retained_bytes(record);
    let peak_of = |plan: &ShardPlan| {
      (0..plan.num_shards())
        .map(|shard| self.shard_peak_bytes(plan, shard, record_bytes))
        .max()
        .unwrap_or(0)
    };
    let single = self.single_shard_plan(record);
    let single_peak = peak_of(&single);
    if single_peak <= max_bytes {
      return Ok((single, single_peak));
    }

    let rows = circuit_rows(self, record);
    let widths = self.committed_widths();
    let total: usize =
      rows.iter().zip(&widths).map(|(&r, &w)| committed_cells(r, w)).sum();

    // Halve the cell budget until a plan fits. The shard count need not
    // grow with every halving (a piece-height cap can pin it at one
    // circuit's piece count while the room still shrinks), so the search
    // runs the budget down to zero before giving up; planning is cheap.
    let mut hi = total;
    let mut cells = total / 2;
    let mut floor = single_peak;
    let (mut lo, mut best, mut best_peak) = loop {
      if cells == 0 {
        return Err(floor);
      }
      let plan = self.plan_shards_from_rows(record, &rows, cells);
      let peak = peak_of(&plan);
      floor = floor.min(peak);
      if peak <= max_bytes {
        break (cells, plan, peak);
      }
      hi = cells;
      cells /= 2;
    };

    // Bisect for the largest fitting cell budget, to one part in sixteen.
    while hi - lo > lo / 16 + 1 {
      let mid = lo + (hi - lo) / 2;
      let plan = self.plan_shards_from_rows(record, &rows, mid);
      let peak = peak_of(&plan);
      if peak <= max_bytes {
        lo = mid;
        if plan.num_shards() <= best.num_shards() {
          best = plan;
          best_peak = peak;
        }
      } else {
        hi = mid;
      }
    }
    Ok((best, best_peak))
  }

  /// The retention policy for proving `plan` under `max_bytes`: retain
  /// every shard's stage 1 across the batch barrier when the model says the
  /// whole retained batch fits beside the heaviest shard's proving
  /// workspace, since retaining recomputes nothing; regenerate otherwise.
  /// A one-shard plan has nothing to save by regenerating and always
  /// retains.
  pub fn retention_for(
    &self,
    plan: &ShardPlan,
    record_bytes: usize,
    max_bytes: usize,
  ) -> Retention {
    if plan.num_shards() == 1 {
      return Retention::Retain;
    }
    let phases: Vec<_> = (0..plan.num_shards())
      .map(|shard| self.shard_phases(plan, shard))
      .collect();
    // Round one builds every witness with the record alive; round two holds
    // every shard's stage 1 while the heaviest shard proves.
    let witnesses =
      record_bytes + phases.iter().map(|p| p.phase_witness).sum::<usize>();
    let retained = phases.iter().map(|p| p.retained_stage_1).sum::<usize>()
      + phases
        .iter()
        .map(|p| p.phase_stage2.max(p.phase_open))
        .max()
        .unwrap_or(0);
    let preprocessed = phases.first().map_or(0, |p| p.preprocessed);
    let peak = calibrate_prover_rss(witnesses.max(retained) + preprocessed);
    if peak <= max_bytes { Retention::Retain } else { Retention::Regenerate }
  }

  /// The phase model over shard `shard` of `plan` alone: its rows, the byte
  /// tables at full height, and no record term.
  fn shard_phases(&self, plan: &ShardPlan, shard: usize) -> PeakProveBytes {
    let ranges = &plan.shards[shard].rows;
    self.peak_prove_bytes_by(
      |ci, ct| match ct {
        CircuitType::Bytes1 => 256,
        CircuitType::Bytes2 => 65536,
        _ => ranges[ci].len(),
      },
      0,
    )
  }

  /// The batch messages closing the `memseg` channel for `plan`: per memory
  /// interval, one pull of its first pointer and one push of one past its
  /// last.
  pub fn boundary_messages(plan: &ShardPlan) -> Vec<BatchMessage<AiurConfig>> {
    let mut messages = Vec::with_capacity(2 * plan.memory_totals.len());
    for &(width, base, total) in &plan.memory_totals {
      let w = G::from_usize(width);
      messages.push(BatchMessage::pull(
        Memory::memseg_args(w, G::from_usize(base)).to_vec(),
      ));
      messages.push(BatchMessage::push(
        Memory::memseg_args(w, G::from_usize(base + total)).to_vec(),
      ));
    }
    messages
  }
}

/// The `memseg` channel identifier, exposed for hosts that assemble or audit
/// batch messages.
pub fn memseg_channel_value() -> G {
  memseg_channel()
}

/// Convenience: the number of shards of a proof.
pub fn num_shards(proof: &BatchProof<AiurConfig>) -> usize {
  proof.proofs.len()
}

fn is_byte_table(circuit_type: &CircuitType) -> bool {
  matches!(circuit_type, CircuitType::Bytes1 | CircuitType::Bytes2)
}

/// Committed cells of one shard of a plan. Every shard commits the byte
/// tables whole, whether or not its copy carries multiplicities, so their
/// cells are charged regardless of the shard's (marker) range for them.
#[cfg(test)]
fn shard_cells(
  shard: &ShardRows,
  rows: &[usize],
  widths: &[usize],
  circuit_types: &[CircuitType],
) -> usize {
  shard
    .rows
    .iter()
    .zip(rows)
    .zip(widths)
    .zip(circuit_types)
    .map(|(((range, &rows), &width), circuit_type)| {
      let rows = if is_byte_table(circuit_type) { rows } else { range.len() };
      committed_cells(rows, width)
    })
    .sum()
}

/// Partitions per-circuit row counts into shards whose committed cells
/// ([`shard_cells`]) each fit `max_cells`, opening as few shards as the
/// packing needs.
///
/// Every circuit is cut into the fewest pieces that each fit the room a
/// shard has beside the byte tables ([`piece_rows`]): a circuit that fits
/// whole is one piece, a larger one is cut into full pieces of the largest
/// fitting power of two, which pad nothing, and a remainder. The pieces are
/// packed first-fit in decreasing size, a new shard opening only when no
/// shard has room; two pieces of one circuit never share a shard, since a
/// shard holds one row range per circuit. A circuit's width is charged to
/// proof size and verification once per shard it appears in, so the fewest
/// pieces and the fewest shards are what the packing minimizes, and padding
/// costs at most one doubling per piece. Byte tables are marked whole in
/// shard 0 and charged to every shard. Memory circuits are cut in pointer
/// order, so every piece is a contiguous pointer range.
///
/// A room no piece can meet (a single row wider than it) still yields a
/// plan: every such row is a piece of its own, and the shards those open
/// exceed the budget by exactly that row.
fn plan_rows(
  rows: &[usize],
  widths: &[usize],
  circuit_types: &[CircuitType],
  max_cells: usize,
) -> Vec<ShardRows> {
  let num_circuits = rows.len();
  let table_cells: usize = (0..num_circuits)
    .filter(|&ci| is_byte_table(&circuit_types[ci]))
    .map(|ci| committed_cells(rows[ci], widths[ci]))
    .sum();
  // What a shard can hold besides the tables it commits in any case.
  let room = max_cells.saturating_sub(table_cells);

  // Every circuit's pieces: (cells, circuit, rows).
  let mut pieces: Vec<(usize, usize, Range<usize>)> = Vec::new();
  for ci in 0..num_circuits {
    if is_byte_table(&circuit_types[ci]) || rows[ci] == 0 {
      continue;
    }
    // Full pieces of the largest fitting power of two pad nothing; only the
    // remainder pads, so this is the least padded cut with this many
    // pieces.
    let per_piece = piece_rows(rows[ci], widths[ci], room);
    let mut start = 0;
    while start < rows[ci] {
      let end = (start + per_piece).min(rows[ci]);
      pieces.push((committed_cells(end - start, widths[ci]), ci, start..end));
      start = end;
    }
  }
  pieces.sort_by_key(|(cells, ci, range)| {
    (std::cmp::Reverse(*cells), *ci, range.start)
  });

  let mut shards: Vec<ShardRows> = Vec::new();
  let mut loads: Vec<usize> = Vec::new();
  for (cells, ci, range) in pieces {
    let k = (0..shards.len())
      .find(|&k| loads[k] + cells <= room && shards[k].rows[ci].is_empty())
      .unwrap_or_else(|| {
        shards.push(ShardRows { rows: vec![0..0; num_circuits] });
        loads.push(0);
        shards.len() - 1
      });
    shards[k].rows[ci] = range;
    loads[k] += cells;
  }
  if shards.is_empty() {
    shards.push(ShardRows { rows: vec![0..0; num_circuits] });
  }
  for ci in 0..num_circuits {
    if is_byte_table(&circuit_types[ci]) {
      shards[0].rows[ci] = 0..rows[ci];
    }
  }
  shards
}

/// Log2 of the tallest piece the planner cuts. The prover's cost per
/// committed cell rises with a shard's tallest matrix once its FFTs leave
/// cache (2026-09-09, Init at 200 GiB on the 64-core Xeon 6975P-C: ~21 ns
/// per cell at 2^22 rows, ~30 ns at 2^24, ~40 ns at 2^25), so a tall circuit
/// is cut shorter than the room alone would require, at the price of one
/// activation per extra piece. `AIUR_MAX_PIECE_LOG_HEIGHT` overrides it.
const MAX_PIECE_LOG_HEIGHT: u32 = 22;

fn max_piece_rows() -> usize {
  let log_height = std::env::var("AIUR_MAX_PIECE_LOG_HEIGHT")
    .ok()
    .and_then(|v| v.parse().ok())
    .unwrap_or(MAX_PIECE_LOG_HEIGHT);
  1 << log_height
}

/// The most rows of a width-`width` circuit with `rows` rows one piece may
/// hold: within `room` committed cells and at most [`max_piece_rows`], the
/// largest power of two meeting both, at least one row; all of the rows when
/// the circuit meets both whole.
fn piece_rows(rows: usize, width: usize, room: usize) -> usize {
  let cap = max_piece_rows();
  if rows <= cap && committed_cells(rows, width) <= room {
    return rows;
  }
  let fit = (room / width.max(1)).min(cap);
  if fit == 0 { 1 } else { 1 << (usize::BITS - 1 - fit.leading_zeros()) }
}

#[cfg(test)]
mod tests {
  use super::*;

  const WIDTHS: [usize; 5] = [24, 6, 5, 3, 4];

  fn circuit_types() -> Vec<CircuitType> {
    vec![
      CircuitType::Function { idx: 0 },
      CircuitType::Function { idx: 1 },
      CircuitType::Memory { width: 1 },
      CircuitType::Bytes1,
      CircuitType::Bytes2,
    ]
  }

  fn heaviest(shards: &[ShardRows], rows: &[usize]) -> usize {
    shards
      .iter()
      .map(|s| shard_cells(s, rows, &WIDTHS, &circuit_types()))
      .max()
      .unwrap()
  }

  fn covers(shards: &[ShardRows], rows: &[usize]) {
    for (ci, &r) in rows.iter().enumerate() {
      let covered: usize = shards.iter().map(|s| s.rows[ci].len()).sum();
      assert_eq!(covered, r, "circuit {ci}");
    }
  }

  #[test]
  fn oversize_circuit_is_cut_into_the_fewest_fitting_pieces() {
    let rows = [100_000, 0, 0, 256, 65_536];
    let tables =
      committed_cells(256, WIDTHS[3]) + committed_cells(65_536, WIDTHS[4]);
    // Room for 32,768 padded rows: three full pieces of 32,768 rows, which
    // pad nothing, and a remainder of 1,696, one per shard.
    let budget = tables + committed_cells(25_000, WIDTHS[0]);
    let shards = plan_rows(&rows, &WIDTHS, &circuit_types(), budget);
    assert_eq!(shards.len(), 4);
    let mut lengths: Vec<usize> =
      shards.iter().map(|s| s.rows[0].len()).collect();
    lengths.sort_unstable();
    assert_eq!(lengths, vec![1_696, 32_768, 32_768, 32_768]);
    assert!(heaviest(&shards, &rows) <= budget);
    covers(&shards, &rows);
  }

  #[test]
  fn cold_circuit_appears_once() {
    // The widest circuit needs four pieces (three full, one remainder); the
    // second fits whole, shares the remainder's shard, and must not be
    // spread across the shards the first opens.
    let rows = [100_000, 40_000, 3_000, 256, 65_536];
    let tables =
      committed_cells(256, WIDTHS[3]) + committed_cells(65_536, WIDTHS[4]);
    let budget = tables + committed_cells(32_768, WIDTHS[0]);
    let shards = plan_rows(&rows, &WIDTHS, &circuit_types(), budget);
    assert_eq!(shards.len(), 4);
    assert_eq!(shards.iter().filter(|s| !s.rows[1].is_empty()).count(), 1);
    assert_eq!(shards.iter().filter(|s| !s.rows[2].is_empty()).count(), 1);
    assert!(heaviest(&shards, &rows) <= budget);
    covers(&shards, &rows);
  }

  #[test]
  fn byte_tables_are_charged_to_every_shard() {
    let rows = [3, 2, 1, 256, 65_536];
    let tables =
      committed_cells(256, WIDTHS[3]) + committed_cells(65_536, WIDTHS[4]);
    // Room for the tables plus one row of the widest circuit, and nothing
    // more: each of its three rows takes a shard of its own, and the next
    // circuit and the memory row share a fourth.
    let budget = tables + committed_cells(1, WIDTHS[0]);
    let shards = plan_rows(&rows, &WIDTHS, &circuit_types(), budget);
    assert_eq!(shards.len(), 4);
    assert!(heaviest(&shards, &rows) <= budget);
    covers(&shards, &rows);
    // The marker range for the tables is shard 0's alone.
    assert_eq!(shards[0].rows[4], 0..65_536);
    assert!(shards[1..].iter().all(|s| s.rows[4].is_empty()));
  }

  #[test]
  fn unattainable_budget_still_covers_every_row() {
    let rows = [3, 2, 1, 256, 65_536];
    let shards = plan_rows(&rows, &WIDTHS, &circuit_types(), 1);
    assert_eq!(shards.len(), 6);
    covers(&shards, &rows);
  }

  /// Plans a measured system offline. `AIUR_PLAN_FILE` holds one `rows
  /// width` pair per circuit in system order, the last two being the byte
  /// tables; `AIUR_PLAN_CELLS` the per-shard cell budgets to sweep. Prints,
  /// per budget and piece-height cap, the shard count, activations, summed
  /// active width, padded cells and the tallest-piece histogram.
  #[test]
  #[ignore]
  fn plan_file() {
    let file = std::env::var("AIUR_PLAN_FILE").expect("AIUR_PLAN_FILE");
    let (rows, widths): (Vec<usize>, Vec<usize>) =
      std::fs::read_to_string(file)
        .expect("readable plan file")
        .lines()
        .map(|l| {
          let mut it = l.split_whitespace().map(|x| x.parse::<usize>().unwrap());
          (it.next().unwrap(), it.next().unwrap())
        })
        .unzip();
    let n = rows.len();
    let types: Vec<CircuitType> = (0..n)
      .map(|ci| match n - ci {
        1 => CircuitType::Bytes2,
        2 => CircuitType::Bytes1,
        _ => CircuitType::Function { idx: ci },
      })
      .collect();
    let budgets: Vec<usize> = std::env::var("AIUR_PLAN_CELLS")
      .expect("AIUR_PLAN_CELLS")
      .split(',')
      .map(|x| x.parse().unwrap())
      .collect();
    let real: usize =
      rows.iter().zip(&widths).map(|(&r, &w)| r * w).sum();
    println!("{n} circuits, real cells {real}");
    for &cells in &budgets {
      for cap in 20..=26 {
        // SAFETY: single-threaded test; the planner reads the override.
        unsafe { std::env::set_var("AIUR_MAX_PIECE_LOG_HEIGHT", cap.to_string()) };
        let shards = plan_rows(&rows, &widths, &types, cells);
        let mut activations = 0;
        let mut width = 0;
        let mut padded = 0;
        let mut tallest = std::collections::BTreeMap::new();
        for s in &shards {
          let mut tall = 0;
          for (ci, r) in s.rows.iter().enumerate() {
            let rr = if is_byte_table(&types[ci]) { rows[ci] } else { r.len() };
            if rr == 0 {
              continue;
            }
            activations += 1;
            width += widths[ci];
            padded += committed_cells(rr, widths[ci]);
            tall = tall.max(rr.next_power_of_two());
          }
          *tallest.entry(tall.trailing_zeros()).or_insert(0) += 1;
        }
        // Padding over the real cells, in tenths of a percent.
        let pad_permille = padded.saturating_sub(real) * 1000 / real.max(1);
        println!(
          "cells {cells} cap 2^{cap}: K {} act {activations} width {width} \
           padded {padded} pad {}.{}% tallest {:?}",
          shards.len(),
          pad_permille / 10,
          pad_permille % 10,
          tallest
        );
      }
    }
  }
}
