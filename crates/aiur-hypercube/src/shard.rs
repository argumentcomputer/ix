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

/// Splits an execution into shard records. `extended` are the outputs of
/// [`AiurMachine::extended_traces`]; the first shard carries the claim (and
/// the memory boundary's chain openings).
pub fn partition_records(
  machine: &AiurMachine,
  extended: &[Option<RowMajorMatrix<F>>],
  claim: &[F],
  params: &ShardingParams,
) -> Result<Vec<AiurRecord>, BuildError> {
  let num_split = machine.num_circuits() + 1;
  assert_eq!(extended.len(), num_split, "one trace per splittable slot");

  // Atomic circuits (preprocessed traces) are replicated into every shard;
  // everything else splits by rows.
  let is_atomic =
    |slot: usize| machine.lowered_at(slot).unwrap().preprocessed.is_some();

  // ── Relocatable circuits: a memoized gadget (e.g. `u32_add`) whose rows,
  // besides their entry provide, only look up per-shard tables can have its
  // rows *duplicated into the shards that demand them* (with split
  // multiplicities — LogUp-identical to one provide of the total). That
  // costs a circuit row per demanding shard instead of a hash-to-curve
  // adapter pair per crossing entry, and such gadget entries dominate the
  // cross-epoch boundary (memo hits to earlier epochs are exactly what
  // memoization creates).
  let table_universe: std::collections::HashSet<Vec<u32>> = (0..num_split)
    .filter(|s| is_atomic(*s))
    .flat_map(|s| table_tuples(machine.lowered_at(s).unwrap()))
    .collect();
  let relocatable: Vec<Option<ProvideInfo>> = (0..num_split)
    .into_par_iter()
    .map(|slot| {
      if is_atomic(slot) {
        return None;
      }
      let circuit = machine.lowered_at(slot).unwrap();
      let trace = extended[slot].as_ref()?;
      let info = provide_candidate(circuit)?;
      relocation_scan(circuit, trace, &info, &table_universe).then_some(info)
    })
    .collect();

  // ── Epoch-sliced row split: every remaining splittable circuit is cut at
  // the same execution fractions. Witness rows are in creation order and
  // requires have strong temporal locality (calls resolve into recently
  // created memo entries), so aligning the cuts across circuits keeps most
  // lookups intra-shard; filling shards circuit-by-circuit instead
  // separates providers from their consumers and explodes the boundary.
  let split_slots: Vec<usize> = (0..num_split)
    .filter(|s| {
      !is_atomic(*s) && relocatable[*s].is_none() && extended[*s].is_some()
    })
    .collect();
  let total_cells: usize = split_slots
    .iter()
    .map(|s| extended[*s].as_ref().unwrap().values.len())
    .sum();
  let mut num_shards = total_cells.div_ceil(params.max_cells.max(1)).max(1);
  for slot in &split_slots {
    let height = extended[*slot].as_ref().unwrap().height();
    num_shards = num_shards.max(height.div_ceil(params.max_rows.max(1)));
  }
  let plans: Vec<ShardPlan> = (0..num_shards)
    .map(|k| {
      let ranges = (0..num_split)
        .map(|slot| {
          if is_atomic(slot)
            || relocatable[slot].is_some()
            || extended[slot].is_none()
          {
            return 0..0;
          }
          let h = extended[slot].as_ref().unwrap().height();
          h * k / num_shards..h * (k + 1) / num_shards
        })
        .collect();
      ShardPlan { ranges }
    })
    .collect();

  // ── Demand pass: what does each shard's epoch slice require? Evaluated
  // over the non-relocatable splittable chunks only (relocatable rows never
  // demand each other — the relocation scan restricts them to table
  // lookups — and the atomic circuits' tuples are not relocatable).
  let epoch_chunk = |plan: &ShardPlan, slot: usize| {
    let range = plan.ranges[slot].clone();
    extended[slot].as_ref().filter(|_| !range.is_empty()).map(|t| {
      let w = t.width();
      RowMajorMatrix::new(t.values[range.start * w..range.end * w].to_vec(), w)
    })
  };
  let mut demands: Vec<HashMap<Vec<u32>, i128>> = plans
    .par_iter()
    .map(|plan| {
      let mut demand: HashMap<Vec<u32>, i128> = HashMap::new();
      for &slot in &split_slots {
        if let Some(chunk) = epoch_chunk(plan, slot) {
          let circuit = machine.lowered_at(slot).unwrap();
          accumulate_balance(circuit, &chunk, &mut demand);
        }
      }
      demand
    })
    .collect();
  // The claim demands the entry function's return tuple in shard 0 (the
  // entry circuit itself may be relocatable).
  let claim_tuple =
    canonical_tuple(claim.iter().map(|v| v.as_canonical_u32()).collect());
  *demands[0].entry(claim_tuple).or_default() += 1;

  // Index the relocatable provides, then place each demanded row into the
  // demanding shards with the demanded multiplicity.
  let provide_index: Vec<Option<HashMap<Vec<u32>, usize>>> = (0..num_split)
    .into_par_iter()
    .map(|slot| {
      let info = relocatable[slot].as_ref()?;
      let circuit = machine.lowered_at(slot).unwrap();
      let trace = extended[slot].as_ref()?;
      Some(provide_map(circuit, trace, info))
    })
    .collect();
  let relocated: Vec<Vec<Option<RowMajorMatrix<F>>>> = demands
    .par_iter()
    .map(|demand| {
      (0..num_split)
        .map(|slot| {
          let info = relocatable[slot].as_ref()?;
          let index = provide_index[slot].as_ref()?;
          let trace = extended[slot].as_ref()?;
          let width = trace.width();
          let mut rows: Vec<(usize, i128)> = demand
            .iter()
            .filter(|(_, r)| **r > 0)
            .filter_map(|(tuple, r)| index.get(tuple).map(|row| (*row, *r)))
            .collect();
          if rows.is_empty() {
            return None;
          }
          rows.sort_unstable();
          let mut values = Vec::with_capacity(rows.len() * width);
          for (row, mult) in rows {
            let at = values.len();
            values
              .extend_from_slice(&trace.values[row * width..(row + 1) * width]);
            values[at + info.mult_col] = to_field(mult);
          }
          Some(RowMajorMatrix::new(values, width))
        })
        .collect()
    })
    .collect();

  // ── Per-shard chunks and residuals.
  let per_shard: Vec<(
    Vec<Option<RowMajorMatrix<F>>>,
    HashMap<Vec<u32>, i128>,
  )> = plans
    .par_iter()
    .zip(&relocated)
    .enumerate()
    .map(|(shard_index, (plan, relocated))| {
      let is_claim_shard = shard_index == 0;
      let pv = machine.base_public_values(claim, is_claim_shard);
      let mut chunks: Vec<Option<RowMajorMatrix<F>>> =
        Vec::with_capacity(num_split);
      for slot in 0..num_split {
        let circuit = machine.lowered_at(slot).unwrap();
        let chunk = if is_atomic(slot) {
          let mut full = extended[slot].clone();
          if let Some(m) = &mut full {
            refresh_public_columns(circuit, m, &pv);
          }
          full
        } else if relocatable[slot].is_some() {
          relocated[slot].clone()
        } else {
          epoch_chunk(plan, slot)
        };
        chunks.push(chunk);
      }

      let mut residual: HashMap<Vec<u32>, i128> = HashMap::new();
      for (slot, chunk) in chunks.iter().enumerate() {
        let Some(chunk) = chunk else { continue };
        let circuit = machine.lowered_at(slot).unwrap();
        accumulate_balance(circuit, chunk, &mut residual);
      }
      if is_claim_shard {
        // The claim send from the public values is a require of the entry
        // function's return tuple.
        let claim_tuple =
          canonical_tuple(claim.iter().map(|v| v.as_canonical_u32()).collect());
        *residual.entry(claim_tuple).or_default() += 1;
      }

      // Absorb what the shard's own tables can provide.
      for (slot, chunk) in chunks.iter_mut().enumerate() {
        let Some(chunk) = chunk else { continue };
        let circuit = machine.lowered_at(slot).unwrap();
        absorb_into_tables(circuit, chunk, &mut residual);
      }
      residual.retain(|_, r| *r != 0);

      (chunks, residual)
    })
    .collect();
  let (shard_chunks, residuals): (Vec<_>, Vec<_>) =
    per_shard.into_iter().unzip();

  // ── Match residuals into pairwise flows.
  let mut adapters: Vec<Vec<AdapterRow>> = vec![vec![]; plans.len()];
  let mut by_tuple: HashMap<&Vec<u32>, Vec<(usize, i128)>> = HashMap::new();
  for (shard, residual) in residuals.iter().enumerate() {
    for (tuple, r) in residual {
      by_tuple.entry(tuple).or_default().push((shard, *r));
    }
  }
  for (tuple, mut entries) in by_tuple {
    let total: i128 = entries.iter().map(|(_, r)| r).sum();
    assert_eq!(
      total, 0,
      "unbalanced residual for tuple {tuple:?}: the partitioner lost flow"
    );
    let field_tuple: Vec<F> =
      tuple.iter().map(|v| F::from_canonical_u32(*v)).collect();
    entries.sort_unstable();
    let (mut needs, mut gives): (Vec<_>, Vec<_>) =
      entries.into_iter().partition(|(_, r)| *r > 0);
    let mut give = gives.pop();
    for (shard, mut need) in needs.drain(..) {
      while need > 0 {
        let (giver, avail) = give.as_mut().expect("flow matching exhausted");
        let amount = need.min(-*avail);
        let row = |import| AdapterRow {
          import,
          amount: to_field(amount),
          tuple: field_tuple.clone(),
        };
        adapters[shard].push(row(true));
        adapters[*giver].push(row(false));
        need -= amount;
        *avail += amount;
        if *avail == 0 {
          give = gives.pop();
        }
      }
    }
    assert!(give.is_none() && gives.is_empty(), "flow matching left surplus");
  }

  // ── Sanity: estimate every shard's main-trace area against the jagged
  // PCS's hard bound before spending prover time on it, and report the
  // partition under `IX_HC_DEBUG`. The binding bound is `log_m <= 29`
  // (`slop-jagged` verifier.rs: `log_m >= 30 → AreaOutOfBounds`, where
  // `log_m` is the log of the round's stacking-padded area), so the padded
  // area must stay at or below 2^29; leave headroom for the preprocessed
  // round and the stacking round-up.
  const AREA_BOUND: usize = (1 << 29) - (32 << 20);
  let debug = std::env::var_os("IX_HC_DEBUG").is_some();
  for (shard, (chunks, rows)) in shard_chunks.iter().zip(&adapters).enumerate()
  {
    let chunk_cells: usize = chunks
      .iter()
      .flatten()
      .map(|t| t.height().max(1).next_multiple_of(ROW_ALIGNMENT) * t.width())
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
    let total = chunk_cells + adapter_cells + 256 + ROW_ALIGNMENT;
    if debug {
      eprintln!(
        "hypercube shard {shard}: {chunk_cells} circuit cells, {} adapter \
         rows {class_rows:?} ({adapter_cells} cells), {} residual tuples, \
         ~{total} total cells",
        rows.len(),
        residuals[shard].len(),
      );
    }
    if total > AREA_BOUND {
      return Err(BuildError::ShardTooLarge { shard, cells: total });
    }
  }

  // ── Assemble.
  let records: Vec<AiurRecord> = shard_chunks
    .into_iter()
    .zip(adapters)
    .enumerate()
    .map(|(shard_index, (chunks, rows))| {
      assemble_shard(machine, chunks, &rows, claim, shard_index == 0)
    })
    .collect();
  if debug {
    // Simulate the full LogUp balance of every shard — every chip plus
    // `eval_public_values` — so a partitioner bug fails here, in seconds,
    // not inside GKR verification after the whole prove.
    records
      .par_iter()
      .enumerate()
      .for_each(|(shard, record)| debug_check_balance(machine, shard, record));
  }
  Ok(records)
}

/// Panics if a shard record's interactions do not balance (see the call
/// site above). Mirrors what the chips and `eval_public_values` emit.
pub(crate) fn debug_check_balance(
  machine: &AiurMachine,
  shard: usize,
  record: &AiurRecord,
) {
  use crate::record::{CLAIM_WIDTH, PV_CHAIN_LEN, PV_CLAIM_FLAG, PV_DIGEST};
  use sp1_hypercube::septic_digest::SepticDigest;
  let mut balance: HashMap<Vec<u32>, i128> = HashMap::new();
  let add = |balance: &mut HashMap<Vec<u32>, i128>, values: Vec<F>, mult: F| {
    if mult == F::zero() {
      return;
    }
    let tuple =
      canonical_tuple(values.iter().map(|v| v.as_canonical_u32()).collect());
    *balance.entry(tuple).or_default() += signed(mult);
  };
  for slot in 0..machine.num_slots() {
    let Some(trace) = &record.traces[slot] else { continue };
    let width = trace.width();
    if let Some(circuit) = machine.lowered_at(slot) {
      let empty: [F; 0] = [];
      for r in 0..trace.height() {
        let main = &trace.values[r * width..(r + 1) * width];
        let prep: &[F] = match &circuit.preprocessed {
          Some(p) if r < p.height() => {
            &p.values[r * p.width()..(r + 1) * p.width()]
          },
          _ => &empty,
        };
        for interaction in &circuit.lowered.interactions {
          add(
            &mut balance,
            interaction.values.iter().map(|v| v.eval_row(prep, main)).collect(),
            interaction.multiplicity.eval_row(prep, main),
          );
        }
      }
    } else {
      let spec = machine.global_classes[slot - machine.idx_adapter_bytes() - 1];
      for r in 0..trace.height() {
        let row = &trace.values[r * width..(r + 1) * width];
        for (values, mult) in spec.row_lookups(row) {
          add(&mut balance, values, mult);
        }
      }
    }
  }
  // `eval_public_values`.
  let pv = &record.public_values;
  add(&mut balance, pv[..CLAIM_WIDTH].to_vec(), pv[PV_CLAIM_FLAG]);
  let chain_channel = F::from_canonical_u32(crate::global::CHAIN_CHANNEL);
  let start = SepticDigest::<F>::zero().0;
  let mut values = vec![chain_channel, F::zero()];
  values.extend_from_slice(&start.x.0);
  values.extend_from_slice(&start.y.0);
  add(&mut balance, values, F::one());
  let mut values = vec![chain_channel, pv[PV_CHAIN_LEN]];
  values.extend_from_slice(&pv[PV_DIGEST..PV_DIGEST + 14]);
  add(&mut balance, values, -F::one());

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

/// Checks that every row's non-provide lookups hit the replicated tables
/// (or are inert), so a copy of the row is self-contained in any shard.
fn relocation_scan(
  circuit: &LoweredCircuit,
  trace: &RowMajorMatrix<F>,
  info: &ProvideInfo,
  table_universe: &std::collections::HashSet<Vec<u32>>,
) -> bool {
  let width = trace.width();
  (0..trace.height()).into_par_iter().all(|r| {
    let main = &trace.values[r * width..(r + 1) * width];
    circuit.lowered.interactions.iter().enumerate().all(|(i, interaction)| {
      if i == info.interaction
        || interaction.multiplicity.eval_row(&[], main) == F::zero()
      {
        return true;
      }
      let tuple = canonical_tuple(
        interaction
          .values
          .iter()
          .map(|v| v.eval_row(&[], main).as_canonical_u32())
          .collect(),
      );
      table_universe.contains(&tuple)
    })
  })
}

/// Maps each provided tuple to its row.
fn provide_map(
  circuit: &LoweredCircuit,
  trace: &RowMajorMatrix<F>,
  info: &ProvideInfo,
) -> HashMap<Vec<u32>, usize> {
  let width = trace.width();
  let interaction = &circuit.lowered.interactions[info.interaction];
  let pairs: Vec<(Vec<u32>, usize)> = (0..trace.height())
    .into_par_iter()
    .map(|r| {
      let main = &trace.values[r * width..(r + 1) * width];
      let tuple = canonical_tuple(
        interaction
          .values
          .iter()
          .map(|v| v.eval_row(&[], main).as_canonical_u32())
          .collect(),
      );
      (tuple, r)
    })
    .collect();
  pairs.into_iter().collect()
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
  chunk: &RowMajorMatrix<F>,
  residual: &mut HashMap<Vec<u32>, i128>,
) {
  let width = chunk.width();
  let empty: [F; 0] = [];
  for r in 0..chunk.height() {
    let main = &chunk.values[r * width..(r + 1) * width];
    let prep: &[F] = match &circuit.preprocessed {
      Some(p) if r < p.height() => {
        &p.values[r * p.width()..(r + 1) * p.width()]
      },
      _ => &empty,
    };
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

  let mut traces: Vec<Option<RowMajorMatrix<F>>> =
    Vec::with_capacity(machine.num_slots());
  for (slot, chunk) in chunks.into_iter().enumerate() {
    let circuit = machine.lowered_at(slot).unwrap();
    let chunk = chunk.unwrap_or_else(|| {
      RowMajorMatrix::new(vec![], circuit.lowered.main_width)
    });
    traces.push(Some(pad_chunk(circuit, chunk, &pv)));
  }

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
