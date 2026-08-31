use ark_bls12_381::Fr;
use ark_ff::{BigInteger, FftField, Field, One, PrimeField, Zero};
use ix_terminal_circuit::{
  CanonicalR1csV1, Constraint, ConstraintPhase, LinearCombination, R1csError,
  R1csProjectionV1, Variable, Witness,
};
use std::{cell::RefCell, collections::BTreeMap, rc::Rc};

/// Rows reserved at the end of the evaluation domain for prover blinding.
pub const FFLONK_BLINDING_ROWS: u64 = 2;

/// Width of one canonical external-memory PLONK gate record.
pub const PLONK_GATE_RECORD_BYTES: usize = 192;

const PLONK_GATE_RECORD_VERSION: u8 = 1;
const PLONK_GATE_RECORD_HEADER_BYTES: usize = 29;
const PLONK_GATE_RECORD_FIELD_BYTES: usize = 32;

/// One copy-permutation identity shared by all occurrences of an R1CS or
/// lowering-generated auxiliary value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PlonkWireV1 {
  R1cs(Variable),
  Auxiliary(u64),
}

/// One cell in the three-column PLONK witness matrix.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PlonkCellV1 {
  pub column: u8,
  pub row: u64,
}

/// One standard three-wire PLONK gate
/// `q_l*a + q_r*b + q_m*a*b + q_o*c + q_c = 0`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlonkGateV1 {
  pub phase: Option<ConstraintPhase>,
  pub wires: [Option<PlonkWireV1>; 3],
  pub ql: Fr,
  pub qr: Fr,
  pub qm: Fr,
  pub qo: Fr,
  pub qc: Fr,
}

impl PlonkGateV1 {
  fn blank() -> Self {
    Self {
      phase: None,
      wires: [None; 3],
      ql: Fr::zero(),
      qr: Fr::zero(),
      qm: Fr::zero(),
      qo: Fr::zero(),
      qc: Fr::zero(),
    }
  }

  fn evaluate(&self, values: [Fr; 3], public_input: Fr) -> Fr {
    self.ql * values[0]
      + self.qr * values[1]
      + self.qm * values[0] * values[1]
      + self.qo * values[2]
      + self.qc
      + public_input
  }

  /// Encodes a gate into the fixed-width external-memory v1 record.
  ///
  /// The record contains a version byte, stable phase tag, three tagged
  /// 64-bit wire identifiers, five canonical little-endian field elements,
  /// and three zero padding bytes. It is independent of Rust object layout.
  #[must_use]
  pub fn to_record_bytes(&self) -> [u8; PLONK_GATE_RECORD_BYTES] {
    let mut record = [0_u8; PLONK_GATE_RECORD_BYTES];
    record[0] = PLONK_GATE_RECORD_VERSION;
    record[1] = self.phase.map_or(0, |phase| phase as u8);
    for (column, wire) in self.wires.iter().enumerate() {
      let offset = 2 + 9 * column;
      let (tag, identifier) = match wire {
        None => (0, 0),
        Some(PlonkWireV1::R1cs(variable)) => (1, u64::from(variable.index())),
        Some(PlonkWireV1::Auxiliary(identifier)) => (2, *identifier),
      };
      record[offset] = tag;
      record[offset + 1..offset + 9].copy_from_slice(&identifier.to_le_bytes());
    }
    for (index, value) in
      [self.ql, self.qr, self.qm, self.qo, self.qc].iter().enumerate()
    {
      let offset =
        PLONK_GATE_RECORD_HEADER_BYTES + index * PLONK_GATE_RECORD_FIELD_BYTES;
      encode_fr_le(value, &mut record[offset..offset + 32]);
    }
    record
  }

  /// Decodes and canonically validates one external-memory v1 gate record.
  pub fn from_record_bytes(
    record: &[u8],
  ) -> Result<Self, PlonkGateRecordError> {
    if record.len() != PLONK_GATE_RECORD_BYTES {
      return Err(PlonkGateRecordError::WrongLength {
        expected: PLONK_GATE_RECORD_BYTES,
        actual: record.len(),
      });
    }
    if record[0] != PLONK_GATE_RECORD_VERSION {
      return Err(PlonkGateRecordError::UnsupportedVersion(record[0]));
    }
    if record[189..].iter().any(|byte| *byte != 0) {
      return Err(PlonkGateRecordError::NonzeroPadding);
    }
    let phase = decode_phase(record[1])?;
    let mut wires = [None; 3];
    for (column, output) in wires.iter_mut().enumerate() {
      let offset = 2 + 9 * column;
      let mut identifier_bytes = [0_u8; 8];
      identifier_bytes.copy_from_slice(&record[offset + 1..offset + 9]);
      let identifier = u64::from_le_bytes(identifier_bytes);
      *output = match record[offset] {
        0 if identifier == 0 => None,
        0 => {
          return Err(PlonkGateRecordError::NoncanonicalEmptyWire { column });
        },
        1 => Some(PlonkWireV1::R1cs(Variable::from_index(
          u32::try_from(identifier)
            .map_err(|_| PlonkGateRecordError::R1csWireOverflow { column })?,
        ))),
        2 => Some(PlonkWireV1::Auxiliary(identifier)),
        tag => {
          return Err(PlonkGateRecordError::InvalidWireTag { column, tag });
        },
      };
    }
    let mut fields = [Fr::zero(); 5];
    for (index, output) in fields.iter_mut().enumerate() {
      let offset =
        PLONK_GATE_RECORD_HEADER_BYTES + index * PLONK_GATE_RECORD_FIELD_BYTES;
      *output = decode_fr_le(&record[offset..offset + 32])
        .ok_or(PlonkGateRecordError::NoncanonicalField { index })?;
    }
    Ok(Self {
      phase,
      wires,
      ql: fields[0],
      qr: fields[1],
      qm: fields[2],
      qo: fields[3],
      qc: fields[4],
    })
  }
}

/// Why an external-memory PLONK gate record failed canonical decoding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PlonkGateRecordError {
  WrongLength { expected: usize, actual: usize },
  UnsupportedVersion(u8),
  InvalidPhaseTag(u8),
  InvalidWireTag { column: usize, tag: u8 },
  NoncanonicalEmptyWire { column: usize },
  R1csWireOverflow { column: usize },
  NoncanonicalField { index: usize },
  NonzeroPadding,
}

impl core::fmt::Display for PlonkGateRecordError {
  fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      Self::WrongLength { expected, actual } => {
        write!(
          formatter,
          "PLONK gate record has {actual} bytes, expected {expected}"
        )
      },
      Self::UnsupportedVersion(version) => {
        write!(formatter, "unsupported PLONK gate record version {version}")
      },
      Self::InvalidPhaseTag(tag) => {
        write!(formatter, "invalid PLONK gate phase tag {tag}")
      },
      Self::InvalidWireTag { column, tag } => {
        write!(formatter, "invalid PLONK wire tag {tag} in column {column}")
      },
      Self::NoncanonicalEmptyWire { column } => write!(
        formatter,
        "empty PLONK wire in column {column} has a nonzero identifier",
      ),
      Self::R1csWireOverflow { column } => write!(
        formatter,
        "R1CS PLONK wire in column {column} exceeds the 32-bit variable space",
      ),
      Self::NoncanonicalField { index } => {
        write!(formatter, "PLONK selector {index} is not a canonical Fr value")
      },
      Self::NonzeroPadding => {
        formatter.write_str("PLONK gate record has nonzero reserved padding")
      },
    }
  }
}

impl std::error::Error for PlonkGateRecordError {}

fn decode_phase(
  tag: u8,
) -> Result<Option<ConstraintPhase>, PlonkGateRecordError> {
  Ok(match tag {
    0 => None,
    1 => Some(ConstraintPhase::Statement),
    2 => Some(ConstraintPhase::Transcript),
    3 => Some(ConstraintPhase::Zerocheck),
    4 => Some(ConstraintPhase::Lincheck),
    5 => Some(ConstraintPhase::Wiring),
    6 => Some(ConstraintPhase::Pcs),
    7 => Some(ConstraintPhase::MatrixFold),
    _ => return Err(PlonkGateRecordError::InvalidPhaseTag(tag)),
  })
}

fn encode_fr_le(value: &Fr, output: &mut [u8]) {
  output.fill(0);
  let bytes = value.into_bigint().to_bytes_le();
  output[..bytes.len()].copy_from_slice(&bytes);
}

fn decode_fr_le(encoded: &[u8]) -> Option<Fr> {
  let value = Fr::from_le_bytes_mod_order(encoded);
  let mut canonical = [0_u8; PLONK_GATE_RECORD_FIELD_BYTES];
  encode_fr_le(&value, &mut canonical);
  (canonical == encoded).then_some(value)
}

/// Exact row and auxiliary-wire census for the deterministic R1CS lowering.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlonkGateCensusV1 {
  pub public_input_rows: u64,
  pub constraint_rows: u64,
  pub padding_rows: u64,
  pub domain_size: u64,
  pub auxiliary_wires: u64,
  pub rows_by_phase: BTreeMap<ConstraintPhase, u64>,
}

impl PlonkGateCensusV1 {
  #[must_use]
  pub fn active_rows(&self) -> u64 {
    self.public_input_rows + self.constraint_rows
  }
}

/// Materialized three-wire arithmetization for preprocessing and small-vector
/// conformance tests. Production sizing should use [`PlonkGateProjectionV1`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlonkArithmetizationV1 {
  r1cs_digest: [u8; 32],
  r1cs_variables: u32,
  census: PlonkGateCensusV1,
  gates: Vec<PlonkGateV1>,
  sigma: [Vec<PlonkCellV1>; 3],
}

impl PlonkArithmetizationV1 {
  #[must_use]
  pub const fn r1cs_digest(&self) -> [u8; 32] {
    self.r1cs_digest
  }

  #[must_use]
  pub const fn r1cs_variables(&self) -> u32 {
    self.r1cs_variables
  }

  pub fn census(&self) -> &PlonkGateCensusV1 {
    &self.census
  }

  pub fn gates(&self) -> &[PlonkGateV1] {
    &self.gates
  }

  pub fn sigma(&self) -> &[Vec<PlonkCellV1>; 3] {
    &self.sigma
  }
}

/// Three witness columns over the padded evaluation domain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlonkWitnessV1 {
  columns: [Vec<Fr>; 3],
}

impl PlonkWitnessV1 {
  pub fn columns(&self) -> &[Vec<Fr>; 3] {
    &self.columns
  }
}

/// Shared constant-memory PLONK census attached to an R1CS projection builder.
#[derive(Clone, Default)]
pub struct PlonkGateProjectionV1 {
  state: Rc<RefCell<ProjectionState>>,
}

impl PlonkGateProjectionV1 {
  #[must_use]
  pub fn new() -> Self {
    Self::default()
  }

  /// Creates a constant-memory projection that also streams each lowered
  /// constraint row to `gate_observer` in deterministic emission order.
  ///
  /// Public-input rows logically precede this stream and padding/blinding rows
  /// follow it. Consequently, streamed row `i` has canonical domain row
  /// `public_input_rows + i` once [`Self::finish`] returns the census. Auxiliary
  /// wire identifiers are global across the stream and start at zero.
  pub fn new_gate_observed(
    gate_observer: impl FnMut(&PlonkGateV1) + 'static,
  ) -> Self {
    Self {
      state: Rc::new(RefCell::new(ProjectionState {
        gate_observer: Some(Box::new(gate_observer)),
        ..ProjectionState::default()
      })),
    }
  }

  /// Returns the callback passed to
  /// [`ix_terminal_circuit::R1csBuilder::new_projection_observed`].
  pub fn observer(&self) -> impl FnMut(&Constraint) + 'static {
    let state = Rc::clone(&self.state);
    move |constraint| state.borrow_mut().observe(constraint)
  }

  pub fn finish(
    &self,
    projection: &R1csProjectionV1,
  ) -> Result<PlonkGateCensusV1, PlonkArithmetizationError> {
    let state = self.state.borrow();
    if state.constraints != projection.census().constraints {
      return Err(PlonkArithmetizationError::ProjectionConstraintMismatch {
        observed: state.constraints,
        projected: projection.census().constraints,
      });
    }
    if state.overflowed {
      return Err(PlonkArithmetizationError::CountOverflow);
    }
    finish_census(
      u64::from(projection.public_variables()),
      state.rows,
      state.auxiliary_wires,
      state.rows_by_phase.clone(),
    )
  }
}

#[derive(Default)]
struct ProjectionState {
  constraints: u64,
  rows: u64,
  auxiliary_wires: u64,
  rows_by_phase: BTreeMap<ConstraintPhase, u64>,
  overflowed: bool,
  gate_observer: Option<Box<dyn FnMut(&PlonkGateV1)>>,
}

impl ProjectionState {
  fn observe(&mut self, constraint: &Constraint) {
    self.constraints = match self.constraints.checked_add(1) {
      Some(value) => value,
      None => {
        self.overflowed = true;
        return;
      },
    };
    if self.overflowed {
      return;
    }
    let mut sink = CountingSink {
      rows: &mut self.rows,
      auxiliary_wires: &mut self.auxiliary_wires,
      rows_by_phase: &mut self.rows_by_phase,
      overflowed: &mut self.overflowed,
      gate_observer: &mut self.gate_observer,
    };
    if lower_constraint(&mut sink, constraint).is_err() {
      self.overflowed = true;
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PlonkArithmetizationError {
  R1cs(R1csError),
  CountOverflow,
  DomainTooLarge { required_rows: u64, maximum_domain: u64 },
  ProjectionConstraintMismatch { observed: u64, projected: u64 },
  R1csDigestMismatch,
  R1csVariableMismatch { expected: u32, actual: u32 },
  UnknownAuxiliaryWire { wire: u64, row: u64 },
  InvalidAuxiliaryDefinition { wire: u64, row: u64 },
  UnsatisfiedGate { row: u64 },
  CopyPermutationMismatch { source: PlonkCellV1, target: PlonkCellV1 },
}

impl core::fmt::Display for PlonkArithmetizationError {
  fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      Self::R1cs(error) => error.fmt(formatter),
      Self::CountOverflow => {
        formatter.write_str("PLONK arithmetization count overflow")
      },
      Self::DomainTooLarge { required_rows, maximum_domain } => write!(
        formatter,
        "PLONK needs {required_rows} rows but BLS12-381 Fr supports at most {maximum_domain}",
      ),
      Self::ProjectionConstraintMismatch { observed, projected } => write!(
        formatter,
        "PLONK observer saw {observed} constraints but R1CS projected {projected}",
      ),
      Self::R1csDigestMismatch => {
        formatter.write_str("PLONK arithmetization belongs to another R1CS")
      },
      Self::R1csVariableMismatch { expected, actual } => write!(
        formatter,
        "PLONK arithmetization expects {expected} R1CS variables, got {actual}",
      ),
      Self::UnknownAuxiliaryWire { wire, row } => write!(
        formatter,
        "PLONK row {row} reads undefined auxiliary wire {wire}",
      ),
      Self::InvalidAuxiliaryDefinition { wire, row } => {
        write!(formatter, "PLONK row {row} cannot solve auxiliary wire {wire}",)
      },
      Self::UnsatisfiedGate { row } => {
        write!(formatter, "PLONK witness does not satisfy row {row}")
      },
      Self::CopyPermutationMismatch { source, target } => write!(
        formatter,
        "PLONK copy permutation maps unequal cells {source:?} and {target:?}",
      ),
    }
  }
}

impl std::error::Error for PlonkArithmetizationError {
  fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
    match self {
      Self::R1cs(error) => Some(error),
      _ => None,
    }
  }
}

impl From<R1csError> for PlonkArithmetizationError {
  fn from(error: R1csError) -> Self {
    Self::R1cs(error)
  }
}

/// Lowers a materialized canonical R1CS into standard three-wire PLONK rows.
pub fn arithmetize_r1cs(
  r1cs: &CanonicalR1csV1,
) -> Result<PlonkArithmetizationV1, PlonkArithmetizationError> {
  let public_input_rows = u64::from(r1cs.public_variables());
  let mut sink = MaterializingSink::default();
  for index in 0..r1cs.public_variables() {
    sink.push(PlonkGateV1 {
      phase: None,
      wires: [
        Some(PlonkWireV1::R1cs(Variable::from_index(index + 1))),
        None,
        None,
      ],
      ql: Fr::one(),
      qr: Fr::zero(),
      qm: Fr::zero(),
      qo: Fr::zero(),
      qc: Fr::zero(),
    })?;
  }
  for constraint in r1cs.constraints() {
    lower_constraint(&mut sink, constraint)?;
  }
  let constraint_rows = u64::try_from(sink.gates.len())
    .map_err(|_| PlonkArithmetizationError::CountOverflow)?
    .checked_sub(public_input_rows)
    .ok_or(PlonkArithmetizationError::CountOverflow)?;
  let census = finish_census(
    public_input_rows,
    constraint_rows,
    sink.next_auxiliary,
    sink.rows_by_phase,
  )?;
  let domain_size = usize::try_from(census.domain_size)
    .map_err(|_| PlonkArithmetizationError::CountOverflow)?;
  sink.gates.resize_with(domain_size, PlonkGateV1::blank);
  let sigma = build_copy_permutation(&sink.gates)?;
  Ok(PlonkArithmetizationV1 {
    r1cs_digest: r1cs.digest(),
    r1cs_variables: r1cs.variables(),
    census,
    gates: sink.gates,
    sigma,
  })
}

/// Lowers a satisfying R1CS assignment into the three PLONK witness columns.
pub fn lower_plonk_witness(
  arithmetization: &PlonkArithmetizationV1,
  r1cs: &CanonicalR1csV1,
  witness: &Witness,
) -> Result<PlonkWitnessV1, PlonkArithmetizationError> {
  if arithmetization.r1cs_digest != r1cs.digest() {
    return Err(PlonkArithmetizationError::R1csDigestMismatch);
  }
  if arithmetization.r1cs_variables != r1cs.variables() {
    return Err(PlonkArithmetizationError::R1csVariableMismatch {
      expected: arithmetization.r1cs_variables,
      actual: r1cs.variables(),
    });
  }
  r1cs.check(witness)?;
  let domain_size = arithmetization.gates.len();
  let public_input_rows =
    usize::try_from(arithmetization.census.public_input_rows)
      .map_err(|_| PlonkArithmetizationError::CountOverflow)?;
  let mut columns = core::array::from_fn(|_| vec![Fr::zero(); domain_size]);
  let mut auxiliary =
    vec![
      None;
      usize::try_from(arithmetization.census.auxiliary_wires,)
        .map_err(|_| PlonkArithmetizationError::CountOverflow)?
    ];

  for (row, gate) in arithmetization.gates.iter().enumerate() {
    let row_u64 = u64::try_from(row)
      .map_err(|_| PlonkArithmetizationError::CountOverflow)?;
    let public_input = if row < public_input_rows {
      -witness.assignment()[row + 1]
    } else {
      Fr::zero()
    };
    let mut values = [None; 3];
    for (column, wire) in gate.wires.iter().enumerate() {
      values[column] = match wire {
        None => Some(Fr::zero()),
        Some(PlonkWireV1::R1cs(variable)) => witness
          .assignment()
          .get(usize::try_from(variable.index()).expect("u32 fits usize"))
          .copied(),
        Some(PlonkWireV1::Auxiliary(index)) => auxiliary
          .get(
            usize::try_from(*index)
              .map_err(|_| PlonkArithmetizationError::CountOverflow)?,
          )
          .copied()
          .flatten(),
      };
    }
    if values[2].is_none()
      && let Some(PlonkWireV1::Auxiliary(index)) = gate.wires[2]
    {
      let (Some(a), Some(b), Some(qo_inverse)) =
        (values[0], values[1], gate.qo.inverse())
      else {
        return Err(PlonkArithmetizationError::InvalidAuxiliaryDefinition {
          wire: index,
          row: row_u64,
        });
      };
      let value =
        -(gate.ql * a + gate.qr * b + gate.qm * a * b + gate.qc + public_input)
          * qo_inverse;
      let slot = auxiliary
        .get_mut(
          usize::try_from(index)
            .map_err(|_| PlonkArithmetizationError::CountOverflow)?,
        )
        .ok_or(PlonkArithmetizationError::UnknownAuxiliaryWire {
          wire: index,
          row: row_u64,
        })?;
      *slot = Some(value);
      values[2] = Some(value);
    }
    for (column, value) in values.iter().enumerate() {
      columns[column][row] = value.ok_or_else(|| match gate.wires[column] {
        Some(PlonkWireV1::Auxiliary(wire)) => {
          PlonkArithmetizationError::UnknownAuxiliaryWire { wire, row: row_u64 }
        },
        _ => PlonkArithmetizationError::UnsatisfiedGate { row: row_u64 },
      })?;
    }
    if !gate
      .evaluate(
        [columns[0][row], columns[1][row], columns[2][row]],
        public_input,
      )
      .is_zero()
    {
      return Err(PlonkArithmetizationError::UnsatisfiedGate { row: row_u64 });
    }
  }
  validate_copy_values(arithmetization, &columns)?;
  Ok(PlonkWitnessV1 { columns })
}

trait GateSink {
  fn allocate_auxiliary(
    &mut self,
  ) -> Result<PlonkWireV1, PlonkArithmetizationError>;

  fn push(
    &mut self,
    gate: PlonkGateV1,
  ) -> Result<(), PlonkArithmetizationError>;
}

#[derive(Default)]
struct MaterializingSink {
  gates: Vec<PlonkGateV1>,
  next_auxiliary: u64,
  rows_by_phase: BTreeMap<ConstraintPhase, u64>,
}

impl GateSink for MaterializingSink {
  fn allocate_auxiliary(
    &mut self,
  ) -> Result<PlonkWireV1, PlonkArithmetizationError> {
    let index = self.next_auxiliary;
    self.next_auxiliary = self
      .next_auxiliary
      .checked_add(1)
      .ok_or(PlonkArithmetizationError::CountOverflow)?;
    Ok(PlonkWireV1::Auxiliary(index))
  }

  fn push(
    &mut self,
    gate: PlonkGateV1,
  ) -> Result<(), PlonkArithmetizationError> {
    if let Some(phase) = gate.phase {
      let count = self.rows_by_phase.entry(phase).or_default();
      *count =
        count.checked_add(1).ok_or(PlonkArithmetizationError::CountOverflow)?;
    }
    self.gates.push(gate);
    Ok(())
  }
}

struct CountingSink<'a> {
  rows: &'a mut u64,
  auxiliary_wires: &'a mut u64,
  rows_by_phase: &'a mut BTreeMap<ConstraintPhase, u64>,
  overflowed: &'a mut bool,
  gate_observer: &'a mut Option<Box<dyn FnMut(&PlonkGateV1)>>,
}

impl GateSink for CountingSink<'_> {
  fn allocate_auxiliary(
    &mut self,
  ) -> Result<PlonkWireV1, PlonkArithmetizationError> {
    let index = *self.auxiliary_wires;
    let Some(next) = index.checked_add(1) else {
      *self.overflowed = true;
      return Err(PlonkArithmetizationError::CountOverflow);
    };
    *self.auxiliary_wires = next;
    Ok(PlonkWireV1::Auxiliary(index))
  }

  fn push(
    &mut self,
    gate: PlonkGateV1,
  ) -> Result<(), PlonkArithmetizationError> {
    let Some(rows) = self.rows.checked_add(1) else {
      *self.overflowed = true;
      return Err(PlonkArithmetizationError::CountOverflow);
    };
    *self.rows = rows;
    if let Some(phase) = gate.phase {
      let count = self.rows_by_phase.entry(phase).or_default();
      let Some(next) = count.checked_add(1) else {
        *self.overflowed = true;
        return Err(PlonkArithmetizationError::CountOverflow);
      };
      *count = next;
    }
    if let Some(observer) = self.gate_observer {
      observer(&gate);
    }
    Ok(())
  }
}

#[derive(Clone, Copy)]
struct AffineWire {
  constant: Fr,
  term: Option<(PlonkWireV1, Fr)>,
}

fn lower_constraint<S: GateSink>(
  sink: &mut S,
  constraint: &Constraint,
) -> Result<(), PlonkArithmetizationError> {
  if let Some(scale) = constant_value(&constraint.a) {
    let linear = constraint.b.clone().scale(scale).minus(&constraint.c);
    return emit_linear_constraint(sink, constraint.phase, &linear);
  }
  if let Some(scale) = constant_value(&constraint.b) {
    let linear = constraint.a.clone().scale(scale).minus(&constraint.c);
    return emit_linear_constraint(sink, constraint.phase, &linear);
  }
  let a = lower_affine(sink, constraint.phase, &constraint.a)?;
  let b = lower_affine(sink, constraint.phase, &constraint.b)?;
  let c = lower_affine(sink, constraint.phase, &constraint.c)?;
  emit_affine_product(sink, constraint.phase, a, b, c)
}

fn lower_affine<S: GateSink>(
  sink: &mut S,
  phase: ConstraintPhase,
  combination: &LinearCombination,
) -> Result<AffineWire, PlonkArithmetizationError> {
  if let Some(affine) = affine_wire(combination) {
    return Ok(affine);
  }
  let wire = materialize_linear_combination(sink, phase, combination)?;
  Ok(AffineWire { constant: Fr::zero(), term: Some((wire, Fr::one())) })
}

fn emit_affine_product<S: GateSink>(
  sink: &mut S,
  phase: ConstraintPhase,
  a: AffineWire,
  b: AffineWire,
  c: AffineWire,
) -> Result<(), PlonkArithmetizationError> {
  let (a_wire, a_coefficient) =
    a.term.map_or((None, Fr::zero()), |(wire, coefficient)| {
      (Some(wire), coefficient)
    });
  let (b_wire, b_coefficient) =
    b.term.map_or((None, Fr::zero()), |(wire, coefficient)| {
      (Some(wire), coefficient)
    });
  let (c_wire, c_coefficient) =
    c.term.map_or((None, Fr::zero()), |(wire, coefficient)| {
      (Some(wire), coefficient)
    });
  sink.push(PlonkGateV1 {
    phase: Some(phase),
    wires: [a_wire, b_wire, c_wire],
    ql: a_coefficient * b.constant,
    qr: b_coefficient * a.constant,
    qm: a_coefficient * b_coefficient,
    qo: -c_coefficient,
    qc: a.constant * b.constant - c.constant,
  })
}

fn emit_linear_constraint<S: GateSink>(
  sink: &mut S,
  phase: ConstraintPhase,
  combination: &LinearCombination,
) -> Result<(), PlonkArithmetizationError> {
  let (constant, terms) = split_combination(combination);
  if terms.len() <= 3 {
    let mut wires = [None; 3];
    let mut coefficients = [Fr::zero(); 3];
    for (index, (wire, coefficient)) in terms.iter().enumerate() {
      wires[index] = Some(*wire);
      coefficients[index] = *coefficient;
    }
    return sink.push(PlonkGateV1 {
      phase: Some(phase),
      wires,
      ql: coefficients[0],
      qr: coefficients[1],
      qm: Fr::zero(),
      qo: coefficients[2],
      qc: constant,
    });
  }

  let mut accumulator = sink.allocate_auxiliary()?;
  sink.push(PlonkGateV1 {
    phase: Some(phase),
    wires: [Some(terms[0].0), Some(terms[1].0), Some(accumulator)],
    ql: terms[0].1,
    qr: terms[1].1,
    qm: Fr::zero(),
    qo: -Fr::one(),
    qc: constant,
  })?;
  for term in &terms[2..terms.len() - 2] {
    let next = sink.allocate_auxiliary()?;
    sink.push(PlonkGateV1 {
      phase: Some(phase),
      wires: [Some(accumulator), Some(term.0), Some(next)],
      ql: Fr::one(),
      qr: term.1,
      qm: Fr::zero(),
      qo: -Fr::one(),
      qc: Fr::zero(),
    })?;
    accumulator = next;
  }
  let last = &terms[terms.len() - 2..];
  sink.push(PlonkGateV1 {
    phase: Some(phase),
    wires: [Some(accumulator), Some(last[0].0), Some(last[1].0)],
    ql: Fr::one(),
    qr: last[0].1,
    qm: Fr::zero(),
    qo: last[1].1,
    qc: Fr::zero(),
  })
}

fn materialize_linear_combination<S: GateSink>(
  sink: &mut S,
  phase: ConstraintPhase,
  combination: &LinearCombination,
) -> Result<PlonkWireV1, PlonkArithmetizationError> {
  let (constant, terms) = split_combination(combination);
  let first_count = terms.len().min(2);
  let mut accumulator = sink.allocate_auxiliary()?;
  let mut wires = [None; 3];
  let mut coefficients = [Fr::zero(); 2];
  for index in 0..first_count {
    wires[index] = Some(terms[index].0);
    coefficients[index] = terms[index].1;
  }
  wires[2] = Some(accumulator);
  sink.push(PlonkGateV1 {
    phase: Some(phase),
    wires,
    ql: coefficients[0],
    qr: coefficients[1],
    qm: Fr::zero(),
    qo: -Fr::one(),
    qc: constant,
  })?;
  for term in &terms[first_count..] {
    let next = sink.allocate_auxiliary()?;
    sink.push(PlonkGateV1 {
      phase: Some(phase),
      wires: [Some(accumulator), Some(term.0), Some(next)],
      ql: Fr::one(),
      qr: term.1,
      qm: Fr::zero(),
      qo: -Fr::one(),
      qc: Fr::zero(),
    })?;
    accumulator = next;
  }
  Ok(accumulator)
}

fn affine_wire(combination: &LinearCombination) -> Option<AffineWire> {
  let (constant, terms) = split_combination(combination);
  (terms.len() <= 1)
    .then(|| AffineWire { constant, term: terms.first().copied() })
}

fn constant_value(combination: &LinearCombination) -> Option<Fr> {
  let (constant, terms) = split_combination(combination);
  terms.is_empty().then_some(constant)
}

fn split_combination(
  combination: &LinearCombination,
) -> (Fr, Vec<(PlonkWireV1, Fr)>) {
  let mut constant = Fr::zero();
  let mut terms = Vec::with_capacity(combination.terms().len());
  for (variable, coefficient) in combination.terms() {
    if *variable == Variable::ONE {
      constant += coefficient;
    } else {
      terms.push((PlonkWireV1::R1cs(*variable), *coefficient));
    }
  }
  (constant, terms)
}

fn finish_census(
  public_input_rows: u64,
  constraint_rows: u64,
  auxiliary_wires: u64,
  rows_by_phase: BTreeMap<ConstraintPhase, u64>,
) -> Result<PlonkGateCensusV1, PlonkArithmetizationError> {
  let active_rows = public_input_rows
    .checked_add(constraint_rows)
    .ok_or(PlonkArithmetizationError::CountOverflow)?;
  let required_rows = active_rows
    .checked_add(FFLONK_BLINDING_ROWS)
    .ok_or(PlonkArithmetizationError::CountOverflow)?
    .max(8);
  let domain_size = required_rows
    .checked_next_power_of_two()
    .ok_or(PlonkArithmetizationError::CountOverflow)?;
  let maximum_domain = 1_u64 << Fr::TWO_ADICITY;
  if domain_size > maximum_domain {
    return Err(PlonkArithmetizationError::DomainTooLarge {
      required_rows,
      maximum_domain,
    });
  }
  Ok(PlonkGateCensusV1 {
    public_input_rows,
    constraint_rows,
    padding_rows: domain_size - active_rows,
    domain_size,
    auxiliary_wires,
    rows_by_phase,
  })
}

fn build_copy_permutation(
  gates: &[PlonkGateV1],
) -> Result<[Vec<PlonkCellV1>; 3], PlonkArithmetizationError> {
  let mut sigma: [Vec<PlonkCellV1>; 3] = core::array::from_fn(|column| {
    (0..gates.len())
      .map(|row| PlonkCellV1 {
        column: u8::try_from(column).expect("three columns fit u8"),
        row: u64::try_from(row).expect("domain row fits u64"),
      })
      .collect()
  });
  let mut occurrences: BTreeMap<PlonkWireV1, Vec<PlonkCellV1>> =
    BTreeMap::new();
  for (row, gate) in gates.iter().enumerate() {
    for (column, wire) in gate.wires.iter().enumerate() {
      if let Some(wire) = wire {
        occurrences.entry(*wire).or_default().push(PlonkCellV1 {
          column: u8::try_from(column).expect("three columns fit u8"),
          row: u64::try_from(row)
            .map_err(|_| PlonkArithmetizationError::CountOverflow)?,
        });
      }
    }
  }
  for cells in occurrences.values() {
    for (index, source) in cells.iter().enumerate() {
      let target = cells[(index + 1) % cells.len()];
      sigma[usize::from(source.column)][usize::try_from(source.row)
        .map_err(|_| PlonkArithmetizationError::CountOverflow)?] = target;
    }
  }
  Ok(sigma)
}

fn validate_copy_values(
  arithmetization: &PlonkArithmetizationV1,
  columns: &[Vec<Fr>; 3],
) -> Result<(), PlonkArithmetizationError> {
  for (column, targets) in arithmetization.sigma.iter().enumerate() {
    for (row, target) in targets.iter().enumerate() {
      let target_row = usize::try_from(target.row)
        .map_err(|_| PlonkArithmetizationError::CountOverflow)?;
      if columns[column][row] != columns[usize::from(target.column)][target_row]
      {
        return Err(PlonkArithmetizationError::CopyPermutationMismatch {
          source: PlonkCellV1 {
            column: u8::try_from(column).expect("three columns fit u8"),
            row: u64::try_from(row)
              .map_err(|_| PlonkArithmetizationError::CountOverflow)?,
          },
          target: *target,
        });
      }
    }
  }
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use ix_terminal_circuit::R1csBuilder;

  fn build_fixture(builder: &mut R1csBuilder) -> Vec<Variable> {
    let x1 = builder.alloc_public(Fr::from(1_u64)).unwrap();
    let x2 = builder.alloc_private(Fr::from(2_u64)).unwrap();
    let x3 = builder.alloc_private(Fr::from(3_u64)).unwrap();
    let x4 = builder.alloc_private(Fr::from(4_u64)).unwrap();
    let x5 = builder.alloc_private(Fr::from(5_u64)).unwrap();
    let product = builder.alloc_private(Fr::from(2_u64)).unwrap();
    let bit = builder.alloc_private(Fr::one()).unwrap();
    builder.enforce(
      ConstraintPhase::Statement,
      LinearCombination::from_variable(x1),
      LinearCombination::from_variable(x2),
      LinearCombination::from_variable(product),
    );
    builder.enforce_boolean(ConstraintPhase::Transcript, bit);
    let sum = [x1, x2, x3, x4, x5].into_iter().fold(
      LinearCombination::from_constant(-Fr::from(15_u64)),
      |combination, variable| combination.term(variable, Fr::one()),
    );
    builder.enforce_zero(ConstraintPhase::Zerocheck, sum);
    vec![x1, x2, x3, x4, x5, product, bit]
  }

  #[test]
  fn affine_constraints_stay_single_row_and_wide_linear_uses_accumulators() {
    let mut builder = R1csBuilder::new();
    build_fixture(&mut builder);
    let (r1cs, witness) = builder.finish().unwrap();
    let arithmetization = arithmetize_r1cs(&r1cs).unwrap();
    assert_eq!(
      arithmetization.census(),
      &PlonkGateCensusV1 {
        public_input_rows: 1,
        constraint_rows: 5,
        padding_rows: 2,
        domain_size: 8,
        auxiliary_wires: 2,
        rows_by_phase: BTreeMap::from([
          (ConstraintPhase::Statement, 1),
          (ConstraintPhase::Transcript, 1),
          (ConstraintPhase::Zerocheck, 3),
        ]),
      },
    );
    let plonk_witness =
      lower_plonk_witness(&arithmetization, &r1cs, &witness).unwrap();
    assert_eq!(plonk_witness.columns()[0].len(), 8);
  }

  #[test]
  fn streaming_projection_matches_materialized_lowering_exactly() {
    let plonk_projection = PlonkGateProjectionV1::new();
    let mut builder =
      R1csBuilder::new_projection_observed(plonk_projection.observer());
    build_fixture(&mut builder);
    let r1cs_projection = builder.finish_projection().unwrap();
    let projected = plonk_projection.finish(&r1cs_projection).unwrap();

    let mut materialized = R1csBuilder::new();
    build_fixture(&mut materialized);
    let (r1cs, _) = materialized.finish().unwrap();
    let compiled = arithmetize_r1cs(&r1cs).unwrap();
    assert_eq!(&projected, compiled.census());
  }

  #[test]
  fn streaming_gate_observer_matches_canonical_constraint_rows() {
    let streamed = Rc::new(RefCell::new(Vec::new()));
    let output = Rc::clone(&streamed);
    let plonk_projection =
      PlonkGateProjectionV1::new_gate_observed(move |gate| {
        output.borrow_mut().push(gate.clone());
      });
    let mut builder =
      R1csBuilder::new_projection_observed(plonk_projection.observer());
    build_fixture(&mut builder);
    let r1cs_projection = builder.finish_projection().unwrap();
    let census = plonk_projection.finish(&r1cs_projection).unwrap();

    let mut materialized = R1csBuilder::new();
    build_fixture(&mut materialized);
    let (r1cs, _) = materialized.finish().unwrap();
    let compiled = arithmetize_r1cs(&r1cs).unwrap();
    let start = usize::try_from(census.public_input_rows).unwrap();
    let end = start + usize::try_from(census.constraint_rows).unwrap();
    assert_eq!(streamed.borrow().as_slice(), &compiled.gates()[start..end]);
  }

  #[test]
  fn external_gate_records_round_trip_and_reject_malleability() {
    let mut builder = R1csBuilder::new();
    build_fixture(&mut builder);
    let (r1cs, _) = builder.finish().unwrap();
    let compiled = arithmetize_r1cs(&r1cs).unwrap();
    for gate in compiled.gates() {
      let encoded = gate.to_record_bytes();
      assert_eq!(PlonkGateV1::from_record_bytes(&encoded).unwrap(), *gate,);
    }

    let mut bad_padding = compiled.gates()[0].to_record_bytes();
    bad_padding[PLONK_GATE_RECORD_BYTES - 1] = 1;
    assert_eq!(
      PlonkGateV1::from_record_bytes(&bad_padding),
      Err(PlonkGateRecordError::NonzeroPadding),
    );

    let mut noncanonical_field = compiled.gates()[0].to_record_bytes();
    noncanonical_field[PLONK_GATE_RECORD_HEADER_BYTES..][..32].fill(0xff);
    assert_eq!(
      PlonkGateV1::from_record_bytes(&noncanonical_field),
      Err(PlonkGateRecordError::NoncanonicalField { index: 0 }),
    );
  }

  #[test]
  fn copy_permutation_preserves_wire_values() {
    let mut builder = R1csBuilder::new();
    build_fixture(&mut builder);
    let (r1cs, witness) = builder.finish().unwrap();
    let arithmetization = arithmetize_r1cs(&r1cs).unwrap();
    let plonk_witness =
      lower_plonk_witness(&arithmetization, &r1cs, &witness).unwrap();
    validate_copy_values(&arithmetization, plonk_witness.columns()).unwrap();
  }
}
