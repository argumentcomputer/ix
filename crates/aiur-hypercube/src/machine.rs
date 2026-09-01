//! Assembling a Hypercube [`Machine`] from Aiur circuit specifications, and
//! building the matching execution records from Aiur traces.

use multi_stark::{
  expr::Expr, lookup::Lookup, p3_field::PrimeField64,
  p3_matrix::dense::RowMajorMatrix as FrontendMatrix,
};
use slop_algebra::AbstractField;
use slop_matrix::{Matrix, dense::RowMajorMatrix};
use sp1_hypercube::{Chip, Machine, MachineShape, PROOF_MAX_NUM_PVS};

use crate::{
  F,
  air::{AIUR_INTERACTION_KIND, AiurAir},
  expr::{
    Affine, Ast, ConvertError, Interaction, Lowered, check_field,
    convert_element,
  },
  record::{AiurRecord, CLAIM_WIDTH},
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
    }
  }
}

impl std::error::Error for BuildError {}

/// An Aiur machine: the frontend circuits as Hypercube chips. The top-level
/// claim enters the lookup argument from the public values (see
/// [`CLAIM_WIDTH`]).
pub struct AiurMachine {
  machine: Machine<F, AiurAir>,
  /// The frontend circuits, followed by internal ones (see
  /// [`constants_circuit`]).
  circuits: Vec<LoweredCircuit>,
  num_frontend: usize,
  claim_len: usize,
}

struct LoweredCircuit {
  name: String,
  lowered: Lowered,
  preprocessed: Option<RowMajorMatrix<F>>,
}

impl AiurMachine {
  /// Builds the machine. `claim_len` is the number of elements of the
  /// top-level lookup message (e.g. channel, function index, inputs and
  /// outputs), which the verifier requires from the public values with
  /// multiplicity one.
  pub fn build<FF: PrimeField64>(
    specs: Vec<CircuitSpec<FF>>,
    claim_len: usize,
  ) -> Result<Self, BuildError> {
    // The constants chip guarantees a `CLAIM_WIDTH`-value interaction, so
    // the kind's table arity must not push the verifier past it (see
    // `CLAIM_WIDTH`).
    assert!(
      AIUR_INTERACTION_KIND.num_values() <= CLAIM_WIDTH
        && CLAIM_WIDTH <= PROOF_MAX_NUM_PVS,
      "AIUR_INTERACTION_KIND's arity exceeds CLAIM_WIDTH"
    );
    if claim_len > CLAIM_WIDTH {
      return Err(BuildError::ClaimTooLong {
        len: claim_len,
        max: CLAIM_WIDTH,
      });
    }
    let mut circuits = Vec::with_capacity(specs.len());
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
    circuits.push(constants_circuit());

    let chips = circuits
      .iter()
      .enumerate()
      .map(|(index, c)| {
        Chip::new(AiurAir::new(
          c.name.clone(),
          index,
          c.lowered.clone(),
          c.preprocessed.clone(),
        ))
      })
      .collect::<Vec<_>>();
    let shape = MachineShape::all(&chips);
    let machine = Machine::new(chips, claim_len, shape);
    Ok(Self { machine, circuits, num_frontend, claim_len })
  }

  pub fn machine(&self) -> &Machine<F, AiurAir> {
    &self.machine
  }

  pub fn claim_len(&self) -> usize {
    self.claim_len
  }

  /// Number of frontend circuits.
  pub fn num_circuits(&self) -> usize {
    self.num_frontend
  }

  /// Builds a record from the frontend traces (one per circuit, in the
  /// order the specs were given; `None` deactivates a circuit) and the
  /// claim. Traces are converted to the backend field, padded to
  /// [`ROW_ALIGNMENT`], and extended with the materialized columns.
  pub fn record<FF: PrimeField64>(
    &self,
    traces: Vec<Option<FrontendMatrix<FF>>>,
    claim: &[FF],
  ) -> Result<AiurRecord, BuildError> {
    let expected = self.num_circuits();
    if traces.len() != expected {
      return Err(BuildError::TraceCount { expected, got: traces.len() });
    }
    if claim.len() != self.claim_len {
      return Err(BuildError::ClaimLength {
        expected: self.claim_len,
        got: claim.len(),
      });
    }
    let public_values: Vec<F> =
      claim.iter().map(|x| convert_element(*x)).collect();

    let mut out = Vec::with_capacity(self.circuits.len());
    for (circuit, trace) in
      self.circuits[..self.num_frontend].iter().zip(traces)
    {
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
      let converted = convert_matrix(&trace);
      out.push(Some(extend_trace(circuit, &converted, &public_values)));
    }

    // Internal circuits carry an all-zero main trace.
    for circuit in &self.circuits[self.num_frontend..] {
      out.push(Some(RowMajorMatrix::new(
        vec![F::zero(); ROW_ALIGNMENT * circuit.lowered.main_width],
        circuit.lowered.main_width,
      )));
    }

    Ok(AiurRecord { traces: out, public_values })
  }
}

/// Converts a frontend matrix to the backend field, element-wise.
fn convert_matrix<FF: PrimeField64>(
  m: &FrontendMatrix<FF>,
) -> RowMajorMatrix<F> {
  let values = m.values.iter().map(|x| convert_element(*x)).collect();
  RowMajorMatrix::new(values, m.width)
}

/// Pads a converted frontend trace to [`ROW_ALIGNMENT`] rows and appends
/// the circuit's materialized columns.
fn extend_trace(
  circuit: &LoweredCircuit,
  trace: &RowMajorMatrix<F>,
  public_values: &[F],
) -> RowMajorMatrix<F> {
  let lowered = &circuit.lowered;
  let frontend_width = trace.width();
  let real_rows = trace.height();
  let height = real_rows.max(1).next_multiple_of(ROW_ALIGNMENT);
  let width = lowered.main_width;
  let mut values = vec![F::zero(); height * width];
  let empty: [F; 0] = [];
  for r in 0..height {
    let dst = &mut values[r * width..(r + 1) * width];
    if r < real_rows {
      dst[..frontend_width].copy_from_slice(
        &trace.values[r * frontend_width..(r + 1) * frontend_width],
      );
    }
    let prep_row: &[F] = match &circuit.preprocessed {
      Some(p) if r < p.height() => {
        &p.values[r * p.width()..(r + 1) * p.width()]
      },
      _ => &empty,
    };
    for (col, expr) in &lowered.materialized {
      // Materialized columns depend only on frontend columns (they are
      // appended after them), so evaluating on the prefix is well-defined.
      dst[*col] = expr.eval_row(prep_row, dst, public_values);
    }
  }
  RowMajorMatrix::new(values, width)
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
