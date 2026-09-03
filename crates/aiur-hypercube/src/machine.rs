//! Assembling a Hypercube [`Machine`] from Aiur circuit specifications, and
//! building the matching execution records from Aiur traces.
//!
//! Every chip is present in every shard (inactive chips carry zero
//! multiplicities), so all shards share the machine's single chip cluster
//! and the preprocessed traces stay row-aligned:
//!
//! - splittable circuits (functions, memories — no preprocessed traces)
//!   appear with their row range, zero-padded;
//! - the byte tables appear in full, with per-shard multiplicity columns;
//! - the memory boundary appears in full, its multiplicities gated by the
//!   claim-shard public-value flag (so only one shard opens the counter
//!   chains);
//! - the adapter chips (see [`crate::global`]) carry the shard's boundary.

use aiur::AiurField;
use multi_stark::{
  expr::Expr, lookup::Lookup, p3_field::PrimeField64,
  p3_matrix::dense::RowMajorMatrix as FrontendMatrix,
};
use slop_algebra::AbstractField;
use slop_matrix::{Matrix, dense::RowMajorMatrix};
use sp1_hypercube::{Chip, Machine, MachineShape, PROOF_MAX_NUM_PVS};

use crate::{
  F,
  air::{AIUR_INTERACTION_KIND, AirKind, AiurAir},
  expr::{
    Affine, Ast, Col, ConvertError, Interaction, Lowered, check_field,
    convert_element,
  },
  global::GlobalSpec,
  record::{AiurRecord, CLAIM_WIDTH, NUM_AIUR_PVS, PV_CLAIM_FLAG},
};

/// Traces are padded to a multiple of this many rows.
pub const ROW_ALIGNMENT: usize = 32;

/// One frontend circuit, in the shape Aiur's synthesis produces.
pub struct CircuitSpec<FF> {
  pub name: String,
  pub main_width: usize,
  pub preprocessed: Option<FrontendMatrix<FF>>,
  pub constraints: Vec<Expr<FF>>,
  pub lookups: Vec<Lookup<Expr<FF>>>,
}

/// Errors from assembling a machine or a record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BuildError {
  Convert {
    circuit: String,
    error: ConvertError,
  },
  ClaimTooLong {
    len: usize,
    max: usize,
  },
  TraceCount {
    expected: usize,
    got: usize,
  },
  TraceWidth {
    circuit: String,
    expected: usize,
    got: usize,
  },
  ClaimLength {
    expected: usize,
    got: usize,
  },
  /// The requested entry function has no constrained circuit.
  NoCircuit {
    fun_idx: usize,
  },
  /// A shard's estimated main-trace area exceeds the jagged PCS's hard
  /// bound; the boundary is too large for this partition.
  ShardTooLarge {
    shard: usize,
    cells: usize,
  },
}

impl std::fmt::Display for BuildError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Convert { circuit, error } => {
        write!(f, "circuit `{circuit}`: {error}")
      },
      Self::ClaimTooLong { len, max } => {
        write!(f, "claim of {len} elements exceeds the {max} public values")
      },
      Self::TraceCount { expected, got } => {
        write!(f, "expected {expected} circuit traces, got {got}")
      },
      Self::TraceWidth { circuit, expected, got } => {
        write!(
          f,
          "circuit `{circuit}`: expected trace width {expected}, got {got}"
        )
      },
      Self::ClaimLength { expected, got } => {
        write!(f, "expected a claim of {expected} elements, got {got}")
      },
      Self::NoCircuit { fun_idx } => {
        write!(f, "function {fun_idx} has no constrained circuit")
      },
      Self::ShardTooLarge { shard, cells } => {
        write!(
          f,
          "shard {shard} would have ~{cells} main-trace cells, past the \
           jagged area bound (log_m <= 29); lower the shard budget"
        )
      },
    }
  }
}

impl std::error::Error for BuildError {}

/// An Aiur machine: the frontend circuits as Hypercube chips, followed by
/// the internal ones. The top-level claim enters the lookup argument from
/// the public values (see [`CLAIM_WIDTH`]).
pub struct AiurMachine {
  machine: Machine<F, AiurAir>,
  /// Chip slots whose rows have no dependencies of their own (Aiur's memory
  /// circuits): the partitioner assigns their row blocks to the shard that
  /// loads them most, instead of by creation epoch.
  pub(crate) affinity_slots: Vec<usize>,
  /// The interpreted circuits, indexed by chip slot: the synthesis
  /// circuits, the memory boundary, the adapter byte table, the constants
  /// chip. The adapter chips live in `global_classes` between the byte
  /// table and the constants chip.
  pub(crate) circuits: Vec<LoweredCircuit>,
  /// The cross-shard adapter chip classes, `1..=max` hash chunks.
  pub(crate) global_classes: Vec<GlobalSpec>,
  /// Number of synthesis circuits (functions, memories, byte tables).
  num_frontend: usize,
  claim_len: usize,
}

pub(crate) struct LoweredCircuit {
  pub(crate) name: String,
  pub(crate) lowered: Lowered,
  pub(crate) preprocessed: Option<RowMajorMatrix<F>>,
}

impl AiurMachine {
  /// Builds the machine. `claim_len` is the number of elements of the
  /// top-level lookup message (e.g. channel, function index, inputs and
  /// outputs), which the verifier requires from the public values with
  /// multiplicity one on the claim shard. `memory_sizes` shape the memory
  /// boundary chip; `counter_channel` is the memory counter chain's
  /// channel.
  pub fn build<FF: AiurField + PrimeField64>(
    specs: Vec<CircuitSpec<FF>>,
    memory_sizes: &[usize],
    claim_len: usize,
  ) -> Result<Self, BuildError> {
    Self::build_with_affinity(specs, memory_sizes, claim_len, vec![])
  }

  /// [`Self::build`], naming the slots eligible for load-affinity row
  /// assignment (see [`crate::shard`]).
  pub fn build_with_affinity<FF: AiurField + PrimeField64>(
    specs: Vec<CircuitSpec<FF>>,
    memory_sizes: &[usize],
    claim_len: usize,
    affinity_slots: Vec<usize>,
  ) -> Result<Self, BuildError> {
    // The constants chip guarantees a `CLAIM_WIDTH`-value interaction, so
    // the kind's table arity must not push the verifier past it (see
    // `CLAIM_WIDTH`).
    assert!(
      AIUR_INTERACTION_KIND.num_values() <= CLAIM_WIDTH
        && NUM_AIUR_PVS <= PROOF_MAX_NUM_PVS,
      "AIUR_INTERACTION_KIND's arity exceeds CLAIM_WIDTH"
    );
    if claim_len > CLAIM_WIDTH {
      return Err(BuildError::ClaimTooLong {
        len: claim_len,
        max: CLAIM_WIDTH,
      });
    }
    let mut circuits = Vec::with_capacity(specs.len() + 3);
    for spec in specs {
      let convert =
        |error| BuildError::Convert { circuit: spec.name.clone(), error };
      check_field::<FF>().map_err(convert)?;
      let lowered = Lowered::from_frontend(
        spec.main_width,
        &spec.constraints,
        &spec.lookups,
      )
      .map_err(convert)?;
      let preprocessed = spec.preprocessed.as_ref().map(convert_matrix);
      circuits.push(LoweredCircuit { name: spec.name, lowered, preprocessed });
    }
    let num_frontend = circuits.len();

    // Adapter classes: enough hash chunks for the widest tuple any circuit
    // (or the claim) can put on a shard boundary.
    let max_arity = circuits
      .iter()
      .flat_map(|c| c.lowered.interactions.iter().map(|i| i.values.len()))
      .chain([claim_len])
      .max()
      .unwrap_or(1);
    let global_classes: Vec<GlobalSpec> =
      (1..=GlobalSpec::class_for(max_arity))
        .map(|chunks| GlobalSpec { chunks })
        .collect();

    let counter_channel = convert_element(aiur::memory_counter_channel::<FF>());
    circuits.push(boundary_circuit(memory_sizes, counter_channel));
    circuits.push(adapter_bytes_circuit());
    circuits.push(constants_circuit());

    // Chip/trace slot layout: synthesis circuits, boundary, adapter byte
    // table, adapter classes, constants.
    let interpreted = |i: usize| {
      let c = &circuits[i];
      (
        c.name.clone(),
        AirKind::Interpreted(c.lowered.clone()),
        c.preprocessed.clone(),
      )
    };
    let mut chip_parts: Vec<(String, AirKind, Option<RowMajorMatrix<F>>)> =
      (0..num_frontend + 2).map(interpreted).collect();
    for spec in &global_classes {
      chip_parts.push((
        format!("AiurGlobal{}", spec.chunks),
        AirKind::Global(*spec),
        None,
      ));
    }
    chip_parts.push(interpreted(num_frontend + 2));

    let chips = chip_parts
      .into_iter()
      .enumerate()
      .map(|(index, (name, kind, preprocessed))| {
        Chip::new(AiurAir::new(name, index, kind, preprocessed))
      })
      .collect::<Vec<_>>();
    let shape = MachineShape::all(&chips);
    let machine = Machine::new(chips, NUM_AIUR_PVS, shape);
    Ok(Self {
      machine,
      affinity_slots,
      circuits,
      global_classes,
      num_frontend,
      claim_len,
    })
  }

  pub fn machine(&self) -> &Machine<F, AiurAir> {
    &self.machine
  }

  pub fn claim_len(&self) -> usize {
    self.claim_len
  }

  /// Number of synthesis circuits (the traces `record` expects, plus the
  /// boundary trace).
  pub fn num_circuits(&self) -> usize {
    self.num_frontend
  }

  /// Chip/trace slot of the adapter byte table.
  pub(crate) fn idx_adapter_bytes(&self) -> usize {
    self.num_frontend + 1
  }

  /// Chip/trace slot of the constants chip.
  pub(crate) fn idx_constants(&self) -> usize {
    self.num_frontend + 2 + self.global_classes.len()
  }

  /// Total number of chip/trace slots.
  pub(crate) fn num_slots(&self) -> usize {
    self.num_frontend + 3 + self.global_classes.len()
  }

  /// The interpreted circuit at a chip slot (`None` for adapter chips).
  pub(crate) fn lowered_at(&self, slot: usize) -> Option<&LoweredCircuit> {
    if slot < self.num_frontend + 2 {
      Some(&self.circuits[slot])
    } else if slot == self.idx_constants() {
      Some(&self.circuits[self.num_frontend + 2])
    } else {
      None
    }
  }

  /// The public values of a shard: the zero-padded claim, the claim-shard
  /// flag, and the adapter chain end (filled by the partitioner).
  pub(crate) fn base_public_values(
    &self,
    claim: &[F],
    is_claim_shard: bool,
  ) -> Vec<F> {
    let mut pv = vec![F::zero(); NUM_AIUR_PVS];
    pv[..claim.len()].copy_from_slice(claim);
    pv[PV_CLAIM_FLAG] = F::from_bool(is_claim_shard);
    pv
  }

  /// Converts the frontend traces (one per synthesis circuit, in system
  /// order, plus the boundary main trace at the end; `None` for circuits
  /// without rows) to the backend field and appends their materialized
  /// columns, without padding. The publics-dependent materialized columns
  /// are evaluated per shard later (see [`crate::shard`]).
  pub fn extended_traces<FF: PrimeField64>(
    &self,
    traces: Vec<Option<FrontendMatrix<FF>>>,
  ) -> Result<Vec<Option<RowMajorMatrix<F>>>, BuildError> {
    let expected = self.num_frontend + 1;
    if traces.len() != expected {
      return Err(BuildError::TraceCount { expected, got: traces.len() });
    }
    let mut out = Vec::with_capacity(expected);
    for (circuit, trace) in self.circuits[..expected].iter().zip(traces) {
      let Some(trace) = trace else {
        out.push(None);
        continue;
      };
      if trace.width != circuit.lowered.frontend_width {
        return Err(BuildError::TraceWidth {
          circuit: circuit.name.clone(),
          expected: circuit.lowered.frontend_width,
          got: trace.width,
        });
      }
      if trace.values.is_empty() {
        out.push(None);
        continue;
      }
      // Publics-dependent materialized columns (the boundary's flag gate)
      // are evaluated against zeroes here and refreshed per shard.
      let zero_pvs = vec![F::zero(); NUM_AIUR_PVS];
      out.push(Some(extend_trace(circuit, &convert_matrix(&trace), &zero_pvs)));
    }
    Ok(out)
  }

  /// Builds the single-shard record: every trace in one shard, no adapter
  /// rows. `traces` are the synthesis traces plus the boundary main trace.
  pub fn record<FF: PrimeField64>(
    &self,
    traces: Vec<Option<FrontendMatrix<FF>>>,
    claim: &[FF],
  ) -> Result<AiurRecord, BuildError> {
    if claim.len() != self.claim_len {
      return Err(BuildError::ClaimLength {
        expected: self.claim_len,
        got: claim.len(),
      });
    }
    let claim: Vec<F> = claim.iter().map(|x| convert_element(*x)).collect();
    let extended = self.extended_traces(traces)?;
    Ok(crate::shard::assemble_shard(self, extended, &[], &claim, true))
  }
}

/// Converts a frontend matrix to the backend field, element-wise.
fn convert_matrix<FF: PrimeField64>(
  m: &FrontendMatrix<FF>,
) -> RowMajorMatrix<F> {
  let values = m.values.iter().map(|x| convert_element(*x)).collect();
  RowMajorMatrix::new(values, m.width)
}

/// Appends a circuit's materialized columns to a converted frontend trace
/// (no padding).
pub(crate) fn extend_trace(
  circuit: &LoweredCircuit,
  trace: &RowMajorMatrix<F>,
  public_values: &[F],
) -> RowMajorMatrix<F> {
  let lowered = &circuit.lowered;
  let frontend_width = trace.width();
  let rows = trace.height();
  let width = lowered.main_width;
  let mut values = vec![F::zero(); rows * width];
  for r in 0..rows {
    let dst = &mut values[r * width..(r + 1) * width];
    dst[..frontend_width].copy_from_slice(
      &trace.values[r * frontend_width..(r + 1) * frontend_width],
    );
    fill_materialized(circuit, r, dst, public_values);
  }
  RowMajorMatrix::new(values, width)
}

/// Evaluates a circuit's materialized columns into one (already
/// frontend-filled) row.
pub(crate) fn fill_materialized(
  circuit: &LoweredCircuit,
  row_index: usize,
  dst: &mut [F],
  public_values: &[F],
) {
  let empty: [F; 0] = [];
  let prep_row: &[F] = match &circuit.preprocessed {
    Some(p) if row_index < p.height() => {
      &p.values[row_index * p.width()..(row_index + 1) * p.width()]
    },
    _ => &empty,
  };
  for (col, expr) in &circuit.lowered.materialized {
    // Materialized columns depend only on frontend columns (they are
    // appended after them), so evaluating on the prefix is well-defined.
    dst[*col] = expr.eval_row(prep_row, dst, public_values);
  }
}

/// The memory boundary circuit: one preprocessed row per memory size
/// (`[is_real, size]`), whose main column holds that table's row count `N`.
/// Every real row pushes `(counter, size, 0)` and pulls `(counter, size, N)`,
/// opening the memory pointer chains — gated by the claim-shard flag so the
/// chains open exactly once across the shards (the full trace is present in
/// every shard).
fn boundary_circuit(
  memory_sizes: &[usize],
  counter_channel: F,
) -> LoweredCircuit {
  let height = memory_sizes.len().max(1).next_multiple_of(ROW_ALIGNMENT);
  let mut prep = vec![F::zero(); height * 2];
  for (i, &size) in memory_sizes.iter().enumerate() {
    prep[2 * i] = F::one();
    prep[2 * i + 1] = F::from_canonical_usize(size);
  }
  let is_real = Ast::preprocessed(0);
  let size = Ast::preprocessed(1);
  let n = Ast::main(0);
  let flag = Ast::Public(PV_CLAIM_FLAG);
  let active = is_real * flag;
  let counter = Ast::constant(counter_channel);
  let lookups = vec![
    (
      active.clone(),
      vec![counter.clone(), size.clone(), Ast::constant(F::zero())],
    ),
    (-active, vec![counter, size, n]),
  ];
  LoweredCircuit {
    name: "AiurMemoryBoundary".to_string(),
    lowered: Lowered::new(1, vec![], lookups).expect("boundary circuit lowers"),
    preprocessed: Some(RowMajorMatrix::new(prep, 2)),
  }
}

/// The adapter byte table: 256 preprocessed values on a dedicated channel,
/// with a free per-shard multiplicity column, providing the adapter chips'
/// range checks without touching Aiur's own byte tables (whose balance the
/// adapters are built from).
fn adapter_bytes_circuit() -> LoweredCircuit {
  let prep: Vec<F> = (0..256).map(F::from_canonical_u32).collect();
  let mult =
    Affine { constant: F::zero(), terms: vec![(Col::Main(0), -F::one())] };
  let channel = Affine {
    constant: F::from_canonical_u32(crate::global::ADAPTER_BYTE_CHANNEL),
    terms: vec![],
  };
  let value = Affine {
    constant: F::zero(),
    terms: vec![(Col::Preprocessed(0), F::one())],
  };
  LoweredCircuit {
    name: "AiurAdapterBytes".to_string(),
    lowered: Lowered {
      main_width: 1,
      frontend_width: 1,
      constraints: vec![],
      interactions: vec![Interaction {
        multiplicity: mult,
        values: vec![channel, value],
      }],
      materialized: vec![],
    },
    preprocessed: Some(RowMajorMatrix::new(prep, 1)),
  }
}

/// An internal circuit every machine carries, doing three jobs the Hypercube
/// prover needs done by *some* chip:
/// - its zero-multiplicity interaction of [`CLAIM_WIDTH`] values makes the
///   prover and the verifier agree on the fingerprint challenge count that
///   the public-value claim message requires (see [`CLAIM_WIDTH`]);
/// - its preprocessed column guarantees the setup has a preprocessed trace
///   to commit;
/// - its (all-zero) main column pinned to zero gives it the positive
///   constraint degree chips must have.
fn constants_circuit() -> LoweredCircuit {
  let zero = Affine { constant: F::zero(), terms: vec![] };
  LoweredCircuit {
    name: "AiurConstants".to_string(),
    lowered: Lowered {
      main_width: 1,
      frontend_width: 1,
      constraints: vec![Ast::main(0)],
      interactions: vec![Interaction {
        multiplicity: zero.clone(),
        values: vec![zero; CLAIM_WIDTH],
      }],
      materialized: vec![],
    },
    preprocessed: Some(RowMajorMatrix::new(vec![F::zero(); ROW_ALIGNMENT], 1)),
  }
}
