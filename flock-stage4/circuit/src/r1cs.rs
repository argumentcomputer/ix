use ark_bls12_381::Fr;
use ark_ff::{AdditiveGroup, Field, PrimeField, Zero};
use std::collections::BTreeMap;

const CIRCUIT_DIGEST_DOMAIN: &[u8] = b"ix:stage4:r1cs:bls12-381:v1";
const PROJECTION_DIGEST_DOMAIN: &[u8] =
  b"ix:stage4:r1cs-projection:bls12-381:v1";

/// Index into an R1CS assignment. Variable zero is the constant-one wire.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Variable(u32);

impl Variable {
  pub const ONE: Self = Self(0);

  pub const fn from_index(index: u32) -> Self {
    Self(index)
  }

  pub const fn index(self) -> u32 {
    self.0
  }
}

/// Stable verifier phase identifiers used by the constraint manifest.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum ConstraintPhase {
  Statement = 1,
  Transcript = 2,
  Zerocheck = 3,
  Lincheck = 4,
  Wiring = 5,
  Pcs = 6,
  /// Matrix-free replay which reduces deferred registry claims to roots.
  MatrixFold = 7,
}

impl ConstraintPhase {
  const fn tag(self) -> u8 {
    self as u8
  }
}

/// A canonical sparse linear combination over BLS12-381 `Fr`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LinearCombination {
  terms: Vec<(Variable, Fr)>,
}

impl LinearCombination {
  pub fn zero() -> Self {
    Self::default()
  }

  pub fn one() -> Self {
    Self::from_variable(Variable::ONE)
  }

  pub fn from_variable(variable: Variable) -> Self {
    Self { terms: vec![(variable, Fr::ONE)] }
  }

  pub fn from_constant(constant: Fr) -> Self {
    if constant.is_zero() {
      Self::zero()
    } else {
      Self { terms: vec![(Variable::ONE, constant)] }
    }
  }

  /// Construct and normalize a batch of sparse terms in one pass.
  pub fn from_terms(terms: impl IntoIterator<Item = (Variable, Fr)>) -> Self {
    let mut combination = Self { terms: terms.into_iter().collect() };
    combination.normalize();
    combination
  }

  pub fn term(mut self, variable: Variable, coefficient: Fr) -> Self {
    if !coefficient.is_zero() {
      self.terms.push((variable, coefficient));
    }
    self.normalize();
    self
  }

  pub fn plus(mut self, other: &Self) -> Self {
    self.terms.extend_from_slice(&other.terms);
    self.normalize();
    self
  }

  pub fn minus(mut self, other: &Self) -> Self {
    self.terms.extend(
      other
        .terms
        .iter()
        .map(|(variable, coefficient)| (*variable, -*coefficient)),
    );
    self.normalize();
    self
  }

  pub fn scale(mut self, coefficient: Fr) -> Self {
    if coefficient.is_zero() {
      self.terms.clear();
    } else {
      for (_, value) in &mut self.terms {
        *value *= coefficient;
      }
    }
    self
  }

  pub fn terms(&self) -> &[(Variable, Fr)] {
    &self.terms
  }

  fn evaluate(&self, assignment: &[Fr]) -> Result<Fr, R1csError> {
    self.terms.iter().try_fold(Fr::ZERO, |sum, (variable, coefficient)| {
      let value = assignment
        .get(usize::try_from(variable.0).expect("u32 fits usize"))
        .ok_or(R1csError::UnknownVariable(*variable))?;
      Ok(sum + (*value * coefficient))
    })
  }

  fn normalize(&mut self) {
    self.terms.sort_unstable_by_key(|(variable, _)| *variable);
    let mut normalized: Vec<(Variable, Fr)> =
      Vec::with_capacity(self.terms.len());
    for (variable, coefficient) in self.terms.drain(..) {
      if coefficient.is_zero() {
        continue;
      }
      if let Some((last_variable, last_coefficient)) = normalized.last_mut()
        && *last_variable == variable
      {
        *last_coefficient += coefficient;
        if last_coefficient.is_zero() {
          normalized.pop();
        }
      } else {
        normalized.push((variable, coefficient));
      }
    }
    self.terms = normalized;
  }
}

/// One rank-one constraint `a(z) * b(z) = c(z)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constraint {
  pub phase: ConstraintPhase,
  pub a: LinearCombination,
  pub b: LinearCombination,
  pub c: LinearCombination,
}

fn hash_constraint(hasher: &mut blake3::Hasher, constraint: &Constraint) {
  hasher.update(&[constraint.phase.tag()]);
  for combination in [&constraint.a, &constraint.b, &constraint.c] {
    hasher.update(
      &u64::try_from(combination.terms.len())
        .expect("term count fits u64")
        .to_le_bytes(),
    );
    for (variable, coefficient) in &combination.terms {
      let mut encoded = [0_u8; 36];
      encoded[..4].copy_from_slice(&variable.0.to_le_bytes());
      for (index, limb) in coefficient.into_bigint().as_ref().iter().enumerate()
      {
        encoded[4 + 8 * index..12 + 8 * index]
          .copy_from_slice(&limb.to_le_bytes());
      }
      hasher.update(&encoded);
    }
  }
}

/// Deterministic size report for one canonical relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R1csCensusV1 {
  pub public_variables: u64,
  pub private_variables: u64,
  pub constraints: u64,
  pub nonzero_terms: u64,
  pub constraints_by_phase: BTreeMap<ConstraintPhase, u64>,
}

/// Exact shape metadata produced without retaining the expanded matrices.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R1csProjectionV1 {
  public_variables: u32,
  private_variables: u32,
  census: R1csCensusV1,
  digest: [u8; 32],
}

impl R1csProjectionV1 {
  pub const fn public_variables(&self) -> u32 {
    self.public_variables
  }

  pub const fn private_variables(&self) -> u32 {
    self.private_variables
  }

  pub const fn variables(&self) -> u32 {
    1 + self.public_variables + self.private_variables
  }

  pub fn census(&self) -> &R1csCensusV1 {
    &self.census
  }

  pub const fn digest(&self) -> [u8; 32] {
    self.digest
  }
}

/// Canonical Stage 4 R1CS shape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanonicalR1csV1 {
  public_variables: u32,
  private_variables: u32,
  constraints: Vec<Constraint>,
}

impl CanonicalR1csV1 {
  pub fn public_variables(&self) -> u32 {
    self.public_variables
  }

  pub fn private_variables(&self) -> u32 {
    self.private_variables
  }

  pub fn constraints(&self) -> &[Constraint] {
    &self.constraints
  }

  /// Consume the relation in canonical constraint order. Each yielded
  /// constraint can be dropped after lowering, releasing its sparse terms
  /// instead of retaining the original matrices alongside backend data.
  pub fn into_constraints(self) -> impl ExactSizeIterator<Item = Constraint> {
    self.constraints.into_iter()
  }

  pub fn variables(&self) -> u32 {
    1 + self.public_variables + self.private_variables
  }

  pub fn census(&self) -> R1csCensusV1 {
    let mut constraints_by_phase = BTreeMap::new();
    let mut nonzero_terms = 0u64;
    for constraint in &self.constraints {
      *constraints_by_phase.entry(constraint.phase).or_default() += 1;
      nonzero_terms += u64::try_from(
        constraint.a.terms.len()
          + constraint.b.terms.len()
          + constraint.c.terms.len(),
      )
      .expect("constraint term count fits u64");
    }
    R1csCensusV1 {
      public_variables: u64::from(self.public_variables),
      private_variables: u64::from(self.private_variables),
      constraints: u64::try_from(self.constraints.len())
        .expect("constraint count fits u64"),
      nonzero_terms,
      constraints_by_phase,
    }
  }

  /// Content address of the normalized matrices and variable layout.
  pub fn digest(&self) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(CIRCUIT_DIGEST_DOMAIN);
    hasher.update(&self.public_variables.to_le_bytes());
    hasher.update(&self.private_variables.to_le_bytes());
    hasher.update(
      &u64::try_from(self.constraints.len())
        .expect("constraint count fits u64")
        .to_le_bytes(),
    );
    for constraint in &self.constraints {
      hash_constraint(&mut hasher, constraint);
    }
    *hasher.finalize().as_bytes()
  }

  pub fn check(&self, witness: &Witness) -> Result<(), R1csError> {
    let expected = usize::try_from(self.variables()).expect("u32 fits usize");
    if witness.assignment.len() != expected {
      return Err(R1csError::AssignmentLength {
        actual: witness.assignment.len(),
        expected,
      });
    }
    if witness.assignment.first() != Some(&Fr::ONE) {
      return Err(R1csError::InvalidConstantWire);
    }
    for (index, constraint) in self.constraints.iter().enumerate() {
      let a = constraint.a.evaluate(&witness.assignment)?;
      let b = constraint.b.evaluate(&witness.assignment)?;
      let c = constraint.c.evaluate(&witness.assignment)?;
      if a * b != c {
        return Err(R1csError::Unsatisfied { constraint: index });
      }
    }
    Ok(())
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Witness {
  assignment: Vec<Fr>,
}

impl Witness {
  pub fn assignment(&self) -> &[Fr] {
    &self.assignment
  }

  pub fn set(
    &mut self,
    variable: Variable,
    value: Fr,
  ) -> Result<(), R1csError> {
    let slot = self
      .assignment
      .get_mut(usize::try_from(variable.0).expect("u32 fits usize"))
      .ok_or(R1csError::UnknownVariable(variable))?;
    *slot = value;
    Ok(())
  }
}

pub struct R1csBuilder {
  public_variables: usize,
  private_variables: usize,
  storage: BuilderStorage,
}

enum BuilderStorage {
  Materialized {
    public_values: Vec<Fr>,
    private_values: Vec<Fr>,
    constraints: Vec<Constraint>,
  },
  Projection {
    accumulator: Box<ProjectionAccumulator>,
    observer: Option<Box<dyn FnMut(&Constraint)>>,
  },
}

struct ProjectionAccumulator {
  constraints: u64,
  nonzero_terms: u64,
  constraints_by_phase: BTreeMap<ConstraintPhase, u64>,
  hasher: blake3::Hasher,
}

impl R1csBuilder {
  pub fn new() -> Self {
    Self {
      public_variables: 0,
      private_variables: 0,
      storage: BuilderStorage::Materialized {
        public_values: Vec::new(),
        private_values: Vec::new(),
        constraints: Vec::new(),
      },
    }
  }

  /// Create a builder that hashes and counts constraints without retaining
  /// matrices or the full witness assignment.
  pub fn new_projection() -> Self {
    Self::new_projection_inner(None)
  }

  /// Create a matrix-free builder that also streams every normalized
  /// constraint to `observer` in canonical emission order.
  ///
  /// The observer must not retain borrowed constraints. It can maintain a
  /// backend-specific census or write an external stream while the canonical
  /// projection continues to hash and count the same constraints.
  pub fn new_projection_observed(
    observer: impl FnMut(&Constraint) + 'static,
  ) -> Self {
    Self::new_projection_inner(Some(Box::new(observer)))
  }

  fn new_projection_inner(
    observer: Option<Box<dyn FnMut(&Constraint)>>,
  ) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(PROJECTION_DIGEST_DOMAIN);
    Self {
      public_variables: 0,
      private_variables: 0,
      storage: BuilderStorage::Projection {
        accumulator: Box::new(ProjectionAccumulator {
          constraints: 0,
          nonzero_terms: 0,
          constraints_by_phase: BTreeMap::new(),
          hasher,
        }),
        observer,
      },
    }
  }

  pub fn alloc_public(&mut self, value: Fr) -> Result<Variable, R1csError> {
    if self.private_variables != 0 {
      return Err(R1csError::PublicAfterPrivate);
    }
    let index = 1usize
      .checked_add(self.public_variables)
      .ok_or(R1csError::TooManyVariables)?;
    self.public_variables = self
      .public_variables
      .checked_add(1)
      .ok_or(R1csError::TooManyVariables)?;
    if let BuilderStorage::Materialized { public_values, .. } =
      &mut self.storage
    {
      public_values.push(value);
    }
    Ok(Variable(u32::try_from(index).map_err(|_| R1csError::TooManyVariables)?))
  }

  pub fn alloc_private(&mut self, value: Fr) -> Result<Variable, R1csError> {
    let index = 1usize
      .checked_add(self.public_variables)
      .and_then(|value| value.checked_add(self.private_variables))
      .ok_or(R1csError::TooManyVariables)?;
    self.private_variables = self
      .private_variables
      .checked_add(1)
      .ok_or(R1csError::TooManyVariables)?;
    if let BuilderStorage::Materialized { private_values, .. } =
      &mut self.storage
    {
      private_values.push(value);
    }
    Ok(Variable(u32::try_from(index).map_err(|_| R1csError::TooManyVariables)?))
  }

  pub fn enforce(
    &mut self,
    phase: ConstraintPhase,
    a: LinearCombination,
    b: LinearCombination,
    c: LinearCombination,
  ) {
    let constraint = Constraint { phase, a, b, c };
    match &mut self.storage {
      BuilderStorage::Materialized { constraints, .. } => {
        constraints.push(constraint);
      },
      BuilderStorage::Projection { accumulator, observer } => {
        accumulator.constraints += 1;
        accumulator.nonzero_terms += u64::try_from(
          constraint.a.terms.len()
            + constraint.b.terms.len()
            + constraint.c.terms.len(),
        )
        .expect("constraint term count fits u64");
        *accumulator.constraints_by_phase.entry(phase).or_default() += 1;
        hash_constraint(&mut accumulator.hasher, &constraint);
        if let Some(observer) = observer {
          observer(&constraint);
        }
      },
    }
  }

  pub fn enforce_zero(
    &mut self,
    phase: ConstraintPhase,
    combination: LinearCombination,
  ) {
    self.enforce(
      phase,
      combination,
      LinearCombination::one(),
      LinearCombination::zero(),
    );
  }

  pub fn enforce_boolean(
    &mut self,
    phase: ConstraintPhase,
    variable: Variable,
  ) {
    let value = LinearCombination::from_variable(variable);
    self.enforce(
      phase,
      value.clone(),
      value.minus(&LinearCombination::one()),
      LinearCombination::zero(),
    );
  }

  pub fn finish(self) -> Result<(CanonicalR1csV1, Witness), R1csError> {
    let public_variables = u32::try_from(self.public_variables)
      .map_err(|_| R1csError::TooManyVariables)?;
    let private_variables = u32::try_from(self.private_variables)
      .map_err(|_| R1csError::TooManyVariables)?;
    let BuilderStorage::Materialized {
      public_values,
      private_values,
      constraints,
    } = self.storage
    else {
      return Err(R1csError::WrongBuilderMode);
    };
    let mut assignment =
      Vec::with_capacity(1 + public_values.len() + private_values.len());
    assignment.push(Fr::ONE);
    assignment.extend(public_values);
    assignment.extend(private_values);
    let r1cs =
      CanonicalR1csV1 { public_variables, private_variables, constraints };
    let witness = Witness { assignment };
    r1cs.check(&witness)?;
    Ok((r1cs, witness))
  }

  pub fn finish_projection(self) -> Result<R1csProjectionV1, R1csError> {
    let public_variables = u32::try_from(self.public_variables)
      .map_err(|_| R1csError::TooManyVariables)?;
    let private_variables = u32::try_from(self.private_variables)
      .map_err(|_| R1csError::TooManyVariables)?;
    let BuilderStorage::Projection { accumulator, .. } = self.storage else {
      return Err(R1csError::WrongBuilderMode);
    };
    let mut projection = *accumulator;
    projection.hasher.update(&[0xff]);
    projection.hasher.update(&public_variables.to_le_bytes());
    projection.hasher.update(&private_variables.to_le_bytes());
    projection.hasher.update(&projection.constraints.to_le_bytes());
    let digest = *projection.hasher.finalize().as_bytes();
    Ok(R1csProjectionV1 {
      public_variables,
      private_variables,
      census: R1csCensusV1 {
        public_variables: u64::from(public_variables),
        private_variables: u64::from(private_variables),
        constraints: projection.constraints,
        nonzero_terms: projection.nonzero_terms,
        constraints_by_phase: projection.constraints_by_phase,
      },
      digest,
    })
  }
}

impl Default for R1csBuilder {
  fn default() -> Self {
    Self::new()
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum R1csError {
  TooManyVariables,
  PublicAfterPrivate,
  InternalShape,
  NonInvertibleBinaryFieldElement,
  WrongBuilderMode,
  AssignmentLength { actual: usize, expected: usize },
  InvalidConstantWire,
  UnknownVariable(Variable),
  Unsatisfied { constraint: usize },
}

impl std::fmt::Display for R1csError {
  fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::TooManyVariables => {
        write!(formatter, "R1CS variable count exceeds u32")
      },
      Self::PublicAfterPrivate => {
        write!(formatter, "public variables must precede private variables")
      },
      Self::InternalShape => write!(formatter, "internal R1CS shape mismatch"),
      Self::NonInvertibleBinaryFieldElement => {
        write!(formatter, "cannot invert zero in GF(2^128)")
      },
      Self::WrongBuilderMode => write!(formatter, "wrong R1CS builder mode"),
      Self::AssignmentLength { actual, expected } => write!(
        formatter,
        "R1CS assignment has {actual} values; expected {expected}",
      ),
      Self::InvalidConstantWire => {
        write!(formatter, "R1CS wire zero is not one")
      },
      Self::UnknownVariable(variable) => {
        write!(formatter, "R1CS references unknown variable {}", variable.0)
      },
      Self::Unsatisfied { constraint } => {
        write!(formatter, "R1CS constraint {constraint} is unsatisfied")
      },
    }
  }
}

impl std::error::Error for R1csError {}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn normalization_makes_equivalent_linear_combinations_identical() {
    let variable = Variable(7);
    let left = LinearCombination::zero()
      .term(variable, Fr::from(3u64))
      .term(variable, Fr::from(4u64));
    let right =
      LinearCombination::from_variable(variable).scale(Fr::from(7u64));
    assert_eq!(left, right);
  }

  #[test]
  fn boolean_constraint_rejects_non_boolean_assignment() {
    let mut builder = R1csBuilder::new();
    let bit = builder.alloc_private(Fr::ONE).unwrap();
    builder.enforce_boolean(ConstraintPhase::Statement, bit);
    let (r1cs, mut witness) = builder.finish().unwrap();
    witness.set(bit, Fr::from(2u64)).unwrap();
    assert_eq!(
      r1cs.check(&witness),
      Err(R1csError::Unsatisfied { constraint: 0 })
    );
  }

  #[test]
  fn projection_matches_materialized_census_without_a_witness() {
    fn build(builder: &mut R1csBuilder) {
      let public = builder.alloc_public(Fr::from(7_u64)).unwrap();
      let private = builder.alloc_private(Fr::ONE).unwrap();
      builder.enforce_boolean(ConstraintPhase::Statement, private);
      builder.enforce_zero(
        ConstraintPhase::Transcript,
        LinearCombination::from_variable(public)
          .minus(&LinearCombination::from_constant(Fr::from(7_u64))),
      );
    }

    let mut materialized = R1csBuilder::new();
    build(&mut materialized);
    let (materialized, _) = materialized.finish().unwrap();
    let mut projected = R1csBuilder::new_projection();
    build(&mut projected);
    let projected = projected.finish_projection().unwrap();
    assert_eq!(projected.census(), &materialized.census());
    assert_eq!(projected.variables(), materialized.variables());
    assert_ne!(projected.digest(), [0; 32]);
  }

  #[test]
  fn projection_observer_sees_each_normalized_constraint_once() {
    use std::{cell::RefCell, rc::Rc};

    let observed = Rc::new(RefCell::new(Vec::new()));
    let observer_output = Rc::clone(&observed);
    let mut builder = R1csBuilder::new_projection_observed(move |constraint| {
      observer_output.borrow_mut().push(constraint.clone());
    });
    let variable = builder.alloc_private(Fr::ONE).unwrap();
    builder.enforce_boolean(ConstraintPhase::Statement, variable);
    builder.enforce_zero(
      ConstraintPhase::Transcript,
      LinearCombination::from_variable(variable)
        .term(variable, Fr::ONE)
        .minus(&LinearCombination::from_constant(Fr::from(2_u64))),
    );
    let projection = builder.finish_projection().unwrap();
    let observed = observed.borrow();
    assert_eq!(observed.len(), 2);
    assert_eq!(
      observed[1].a.terms(),
      &[(Variable::ONE, -Fr::from(2_u64)), (variable, Fr::from(2_u64))],
    );
    assert_eq!(projection.census().constraints, 2);
  }
}
