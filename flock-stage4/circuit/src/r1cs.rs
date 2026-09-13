use ark_bls12_381::Fr;
use ark_ff::{AdditiveGroup, Field, PrimeField, Zero};
use std::collections::BTreeMap;

#[path = "r1cs_stream.rs"]
mod stream;
pub use stream::{R1csCheckedStreamV0, R1csShapeStreamV0, R1csStreamedShapeV0};

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

fn canonical_hasher(
  public_variables: u32,
  private_variables: u32,
  constraints: u64,
) -> blake3::Hasher {
  let mut hasher = blake3::Hasher::new();
  hasher.update(CIRCUIT_DIGEST_DOMAIN);
  hasher.update(&public_variables.to_le_bytes());
  hasher.update(&private_variables.to_le_bytes());
  hasher.update(&constraints.to_le_bytes());
  hasher
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
    let mut hasher = canonical_hasher(
      self.public_variables,
      self.private_variables,
      u64::try_from(self.constraints.len()).expect("constraint count fits u64"),
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

/// Hard bounds for materializing setup-only matrices. Counts include the
/// constant-one wire and all sparse A/B/C terms; they are not a peak-RAM model.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct R1csShapeLimitsV0 {
  pub variables: u32,
  pub constraints: u64,
  pub nonzero_terms: u64,
}

pub struct R1csBuilder {
  public_variables: usize,
  private_variables: usize,
  storage: BuilderStorage,
  // A refused stream is never a completed relation, even when emission ends
  // without another fallible allocation to propagate the observer's error.
  error: Option<R1csError>,
  f128_preparations: Option<crate::f128::F128PreparationCache>,
}

enum BuilderStorage {
  Materialized {
    public_values: Vec<Fr>,
    private_values: Vec<Fr>,
    constraints: Vec<Constraint>,
  },
  Shape {
    constraints: Vec<Constraint>,
    nonzero_terms: u64,
    limits: R1csShapeLimitsV0,
  },
  Projection {
    accumulator: Box<ProjectionAccumulator>,
    observer: Option<Box<dyn FnMut(&Constraint) -> Result<(), R1csError>>>,
    shape_only: bool,
  },
  Streamed {
    state: Box<stream::StreamingBuilder>,
  },
}

struct ProjectionAccumulator {
  constraints: u64,
  nonzero_terms: u64,
  constraints_by_phase: BTreeMap<ConstraintPhase, u64>,
  hasher: blake3::Hasher,
}

impl ProjectionAccumulator {
  fn new() -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(PROJECTION_DIGEST_DOMAIN);
    Self {
      constraints: 0,
      nonzero_terms: 0,
      constraints_by_phase: BTreeMap::new(),
      hasher,
    }
  }

  fn observe(&mut self, constraint: &Constraint) -> Result<(), R1csError> {
    let constraints =
      self.constraints.checked_add(1).ok_or(R1csError::CountOverflow)?;
    let terms = constraint
      .a
      .terms
      .len()
      .checked_add(constraint.b.terms.len())
      .and_then(|n| n.checked_add(constraint.c.terms.len()))
      .and_then(|n| u64::try_from(n).ok())
      .and_then(|n| self.nonzero_terms.checked_add(n))
      .ok_or(R1csError::CountOverflow)?;
    let phase_count = self
      .constraints_by_phase
      .get(&constraint.phase)
      .copied()
      .unwrap_or(0)
      .checked_add(1)
      .ok_or(R1csError::CountOverflow)?;
    self.constraints = constraints;
    self.nonzero_terms = terms;
    self.constraints_by_phase.insert(constraint.phase, phase_count);
    hash_constraint(&mut self.hasher, constraint);
    Ok(())
  }

  fn finish(
    mut self,
    public_variables: u32,
    private_variables: u32,
  ) -> R1csProjectionV1 {
    self.hasher.update(&[0xff]);
    self.hasher.update(&public_variables.to_le_bytes());
    self.hasher.update(&private_variables.to_le_bytes());
    self.hasher.update(&self.constraints.to_le_bytes());
    R1csProjectionV1 {
      public_variables,
      private_variables,
      census: R1csCensusV1 {
        public_variables: u64::from(public_variables),
        private_variables: u64::from(private_variables),
        constraints: self.constraints,
        nonzero_terms: self.nonzero_terms,
        constraints_by_phase: self.constraints_by_phase,
      },
      digest: *self.hasher.finalize().as_bytes(),
    }
  }
}

impl R1csBuilder {
  pub fn new() -> Self {
    Self {
      public_variables: 0,
      private_variables: 0,
      error: None,
      f128_preparations: None,
      storage: BuilderStorage::Materialized {
        public_values: Vec::new(),
        private_values: Vec::new(),
        constraints: Vec::new(),
      },
    }
  }

  /// Materialize matrices without an assignment. Gadgets may suppress only
  /// redundant native-value diagnostics in this mode, never constraints or
  /// structural validation. Scratch values are not witnesses and cannot be
  /// exported by `finish`; only `finish_shape` can return these matrices.
  pub fn new_shape(limits: R1csShapeLimitsV0) -> Result<Self, R1csError> {
    if limits.variables == 0 {
      return Err(R1csError::ResourceLimit {
        resource: "R1CS variables",
        limit: 0,
        actual: 1,
      });
    }
    Ok(Self {
      public_variables: 0,
      private_variables: 0,
      storage: BuilderStorage::Shape {
        constraints: Vec::new(),
        nonzero_terms: 0,
        limits,
      },
      error: None,
      f128_preparations: None,
    })
  }

  /// This mode is fixed at construction and never turns into a witness
  /// builder. It is NOT permission to omit any relation constraints.
  pub fn is_shape_only(&self) -> bool {
    match &self.storage {
      BuilderStorage::Shape { .. }
      | BuilderStorage::Projection { shape_only: true, .. } => true,
      BuilderStorage::Streamed { state } => state.is_shape_only(),
      _ => false,
    }
  }

  /// Surface a sticky emission refusal, including one on the final
  /// infallible `enforce`. Finishing also performs this check.
  pub fn check_status(&self) -> Result<(), R1csError> {
    match &self.error {
      Some(error) => Err(error.clone()),
      None => Ok(()),
    }
  }

  /// Opt in BEFORE any allocation or constraint, once per fresh builder.
  /// Default emission is unchanged. The capacity and deterministic FIFO
  /// policy affect geometry and must be pinned by the caller's implementation
  /// identity, identically for setup and assignment. Neither is witness data.
  pub fn enable_f128_preparation_cache(
    &mut self,
    capacity: usize,
  ) -> Result<(), R1csError> {
    self.enable_f128_preparation_cache_with_product(
      capacity,
      crate::F128PreparedProductV1::BooleanCarriesV0,
    )
  }

  /// As above, also pinning the product's carry encoding. Both settings
  /// become immutable before any allocation or constraint. No runtime
  /// witness value can switch the arithmetic or the cache policy.
  pub fn enable_f128_preparation_cache_with_product(
    &mut self,
    capacity: usize,
    encoding: crate::F128PreparedProductV1,
  ) -> Result<(), R1csError> {
    self.check_status()?;
    let constraints_started = match &self.storage {
      BuilderStorage::Materialized { constraints, .. }
      | BuilderStorage::Shape { constraints, .. } => !constraints.is_empty(),
      BuilderStorage::Projection { accumulator, .. } => {
        accumulator.constraints != 0
      },
      BuilderStorage::Streamed { state } => state.constraints_started(),
    };
    if self.f128_preparations.is_some()
      || self.public_variables != 0
      || self.private_variables != 0
      || constraints_started
    {
      return Err(R1csError::BuilderConfigurationLocked);
    }
    if capacity == 0 || capacity > crate::F128_PREPARATION_CACHE_MAX_CAPACITY {
      return Err(R1csError::InvalidF128PreparationCacheCapacity { capacity });
    }
    self.f128_preparations =
      Some(crate::f128::F128PreparationCache::new(capacity, encoding));
    Ok(())
  }

  pub fn f128_preparation_cache_capacity(&self) -> Option<usize> {
    self.f128_preparations.as_ref().map(|cache| cache.capacity())
  }

  pub fn f128_prepared_product_encoding(
    &self,
  ) -> Option<crate::F128PreparedProductV1> {
    self.f128_preparations.as_ref().map(|cache| cache.encoding())
  }

  pub(crate) fn f128_preparation_cache(
    &mut self,
  ) -> Option<&mut crate::f128::F128PreparationCache> {
    self.f128_preparations.as_mut()
  }

  /// Create a builder that hashes and counts constraints without retaining
  /// matrices or the full witness assignment.
  pub fn new_projection() -> Self {
    Self::new_projection_inner(None, false)
  }

  /// Create a matrix-free builder that also streams every normalized
  /// constraint to `observer` in canonical emission order.
  ///
  /// The observer must not retain borrowed constraints. It can maintain a
  /// backend-specific census or write an external stream while the canonical
  /// projection continues to hash and count the same constraints.
  pub fn new_projection_observed(
    mut observer: impl FnMut(&Constraint) + 'static,
  ) -> Self {
    Self::new_projection_observed_fallible(move |constraint| {
      observer(constraint);
      Ok(())
    })
  }

  /// Like [`Self::new_projection_observed`], with fail-closed admission.
  /// The first observer error stops subsequent emission and allocation; both
  /// finish methods return that same error instead of exporting a partial
  /// circuit or projection. The observer sees the refused constraint once,
  /// so any externally retained counts describe a prefix, not a full census.
  /// Existing infallible `enforce` calls defer error propagation to the next
  /// allocation or finish. They cannot resume the failed builder.
  pub fn new_projection_observed_fallible(
    observer: impl FnMut(&Constraint) -> Result<(), R1csError> + 'static,
  ) -> Self {
    Self::new_projection_inner(Some(Box::new(observer)), false)
  }

  /// Setup-only matrix-free emission. No assignment is checked or retained;
  /// use a fallible observer to impose backend-specific geometry limits.
  pub fn new_shape_projection() -> Self {
    Self::new_projection_inner(None, true)
  }

  pub fn new_shape_projection_observed(
    mut observer: impl FnMut(&Constraint) + 'static,
  ) -> Self {
    Self::new_shape_projection_observed_fallible(move |constraint| {
      observer(constraint);
      Ok(())
    })
  }

  /// Shape-only counterpart with the same sticky refusal semantics as
  /// [`Self::new_projection_observed_fallible`]. Neither projection mode can
  /// produce an assignment, and a refused stream cannot finish a prefix.
  pub fn new_shape_projection_observed_fallible(
    observer: impl FnMut(&Constraint) -> Result<(), R1csError> + 'static,
  ) -> Self {
    Self::new_projection_inner(Some(Box::new(observer)), true)
  }

  fn new_projection_inner(
    observer: Option<Box<dyn FnMut(&Constraint) -> Result<(), R1csError>>>,
    shape_only: bool,
  ) -> Self {
    Self {
      public_variables: 0,
      private_variables: 0,
      error: None,
      f128_preparations: None,
      storage: BuilderStorage::Projection {
        accumulator: Box::new(ProjectionAccumulator::new()),
        observer,
        shape_only,
      },
    }
  }

  pub fn alloc_public(&mut self, value: Fr) -> Result<Variable, R1csError> {
    if let Some(error) = &self.error {
      return Err(error.clone());
    }
    self.check_streamed_allocation(true)?;
    if self.private_variables != 0 {
      return Err(R1csError::PublicAfterPrivate);
    }
    let index = 1usize
      .checked_add(self.public_variables)
      .ok_or(R1csError::TooManyVariables)?;
    self.check_shape_variable_limit(index)?;
    self.public_variables = self
      .public_variables
      .checked_add(1)
      .ok_or(R1csError::TooManyVariables)?;
    if let BuilderStorage::Materialized { public_values, .. } =
      &mut self.storage
    {
      public_values.push(value);
    }
    if let BuilderStorage::Streamed { state } = &mut self.storage {
      state.push_value(value);
    }
    Ok(Variable(u32::try_from(index).map_err(|_| R1csError::TooManyVariables)?))
  }

  pub fn alloc_private(&mut self, value: Fr) -> Result<Variable, R1csError> {
    if let Some(error) = &self.error {
      return Err(error.clone());
    }
    self.check_streamed_allocation(false)?;
    let index = 1usize
      .checked_add(self.public_variables)
      .and_then(|value| value.checked_add(self.private_variables))
      .ok_or(R1csError::TooManyVariables)?;
    self.check_shape_variable_limit(index)?;
    self.private_variables = self
      .private_variables
      .checked_add(1)
      .ok_or(R1csError::TooManyVariables)?;
    if let BuilderStorage::Materialized { private_values, .. } =
      &mut self.storage
    {
      private_values.push(value);
    }
    if let BuilderStorage::Streamed { state } = &mut self.storage {
      state.push_value(value);
    }
    Ok(Variable(u32::try_from(index).map_err(|_| R1csError::TooManyVariables)?))
  }

  fn check_shape_variable_limit(
    &mut self,
    index: usize,
  ) -> Result<(), R1csError> {
    if let BuilderStorage::Shape { limits, .. } = &self.storage {
      let actual = u64::try_from(index)
        .ok()
        .and_then(|n| n.checked_add(1))
        .ok_or(R1csError::CountOverflow)?;
      if actual > u64::from(limits.variables) {
        let error = R1csError::ResourceLimit {
          resource: "R1CS variables",
          limit: u64::from(limits.variables),
          actual,
        };
        self.error = Some(error.clone());
        return Err(error);
      }
    }
    Ok(())
  }

  pub fn enforce(
    &mut self,
    phase: ConstraintPhase,
    a: LinearCombination,
    b: LinearCombination,
    c: LinearCombination,
  ) {
    if self.error.is_some() {
      return;
    }
    let constraint = Constraint { phase, a, b, c };
    match &mut self.storage {
      BuilderStorage::Materialized { constraints, .. } => {
        constraints.push(constraint);
      },
      BuilderStorage::Shape { constraints, nonzero_terms, limits } => {
        let rows =
          u64::try_from(constraints.len()).ok().and_then(|n| n.checked_add(1));
        let terms = constraint
          .a
          .terms
          .len()
          .checked_add(constraint.b.terms.len())
          .and_then(|n| n.checked_add(constraint.c.terms.len()))
          .and_then(|n| u64::try_from(n).ok())
          .and_then(|n| nonzero_terms.checked_add(n));
        let (Some(rows), Some(terms)) = (rows, terms) else {
          self.error = Some(R1csError::CountOverflow);
          return;
        };
        for (resource, limit, actual) in [
          ("R1CS constraints", limits.constraints, rows),
          ("R1CS nonzero terms", limits.nonzero_terms, terms),
        ] {
          if actual > limit {
            self.error =
              Some(R1csError::ResourceLimit { resource, limit, actual });
            return;
          }
        }
        *nonzero_terms = terms;
        constraints.push(constraint);
      },
      BuilderStorage::Projection { accumulator, observer, .. } => {
        if let Err(error) = accumulator.observe(&constraint) {
          self.error = Some(error);
          return;
        }
        if let Some(observer) = observer
          && let Err(error) = observer(&constraint)
        {
          self.error = Some(error);
        }
      },
      BuilderStorage::Streamed { state } => {
        if let Err(error) = state.observe(
          &constraint,
          1 + self.public_variables + self.private_variables,
        ) {
          self.error = Some(error);
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
    if let Some(error) = self.error {
      return Err(error);
    }
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

  /// Return setup-only matrices, never a made-up satisfying assignment.
  /// Callers must propagate every emitter error before calling this method.
  pub fn finish_shape(self) -> Result<CanonicalR1csV1, R1csError> {
    if let Some(error) = self.error {
      return Err(error);
    }
    let BuilderStorage::Shape { constraints, .. } = self.storage else {
      return Err(R1csError::WrongBuilderMode);
    };
    let public_variables = u32::try_from(self.public_variables)
      .map_err(|_| R1csError::TooManyVariables)?;
    let private_variables = u32::try_from(self.private_variables)
      .map_err(|_| R1csError::TooManyVariables)?;
    let variables = 1u32
      .checked_add(public_variables)
      .and_then(|n| n.checked_add(private_variables))
      .ok_or(R1csError::TooManyVariables)?;
    for constraint in &constraints {
      for (variable, _) in constraint
        .a
        .terms
        .iter()
        .chain(&constraint.b.terms)
        .chain(&constraint.c.terms)
      {
        if variable.index() >= variables {
          return Err(R1csError::UnknownVariable(*variable));
        }
      }
    }
    Ok(CanonicalR1csV1 { public_variables, private_variables, constraints })
  }

  pub fn finish_projection(self) -> Result<R1csProjectionV1, R1csError> {
    if let Some(error) = self.error {
      return Err(error);
    }
    let public_variables = u32::try_from(self.public_variables)
      .map_err(|_| R1csError::TooManyVariables)?;
    let private_variables = u32::try_from(self.private_variables)
      .map_err(|_| R1csError::TooManyVariables)?;
    let BuilderStorage::Projection { accumulator, .. } = self.storage else {
      return Err(R1csError::WrongBuilderMode);
    };
    Ok(accumulator.finish(public_variables, private_variables))
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
  CountOverflow,
  PublicAfterPrivate,
  InternalShape,
  NonInvertibleBinaryFieldElement,
  WrongBuilderMode,
  BuilderConfigurationLocked,
  InvalidF128PreparationCacheCapacity { capacity: usize },
  ResourceLimit { resource: &'static str, limit: u64, actual: u64 },
  ObserverFailure(String),
  StreamMismatch,
  AllocationFailed { resource: &'static str, bytes: u64 },
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
      Self::CountOverflow => write!(formatter, "R1CS count overflow"),
      Self::PublicAfterPrivate => {
        write!(formatter, "public variables must precede private variables")
      },
      Self::InternalShape => write!(formatter, "internal R1CS shape mismatch"),
      Self::NonInvertibleBinaryFieldElement => {
        write!(formatter, "cannot invert zero in GF(2^128)")
      },
      Self::WrongBuilderMode => write!(formatter, "wrong R1CS builder mode"),
      Self::BuilderConfigurationLocked => {
        write!(formatter, "R1CS builder configuration is already fixed")
      },
      Self::InvalidF128PreparationCacheCapacity { capacity } => write!(
        formatter,
        "F128 preparation cache capacity {capacity} is outside 1..={}",
        crate::F128_PREPARATION_CACHE_MAX_CAPACITY,
      ),
      Self::ResourceLimit { resource, limit, actual } => write!(
        formatter,
        "R1CS stream exceeded {resource} limit {limit} (observed {actual})",
      ),
      Self::ObserverFailure(message) => {
        write!(formatter, "R1CS stream observer failed: {message}")
      },
      Self::StreamMismatch => write!(
        formatter,
        "R1CS stream differs from its complete expected census or identity"
      ),
      Self::AllocationFailed { resource, bytes } => {
        write!(formatter, "could not allocate {bytes} bytes for {resource}")
      },
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
pub(crate) fn test_shape_builder() -> R1csBuilder {
  R1csBuilder::new_shape(R1csShapeLimitsV0 {
    variables: 5_000_000,
    constraints: 5_000_000,
    nonzero_terms: 30_000_000,
  })
  .unwrap()
}

#[cfg(test)]
mod tests {
  use super::*;

  fn shape_limits() -> R1csShapeLimitsV0 {
    R1csShapeLimitsV0 { variables: 8, constraints: 8, nonzero_terms: 32 }
  }

  #[test]
  fn setup_matrices_ignore_assignments_and_match_witness_emission() {
    fn emit(builder: &mut R1csBuilder, value: Fr) {
      let public = builder.alloc_public(value).unwrap();
      let private = builder.alloc_private(value).unwrap();
      builder.enforce_boolean(ConstraintPhase::Statement, private);
      builder.enforce_zero(
        ConstraintPhase::Transcript,
        LinearCombination::from_variable(public)
          .minus(&LinearCombination::from_variable(private)),
      );
    }
    let mut setup = R1csBuilder::new_shape(shape_limits()).unwrap();
    assert!(setup.is_shape_only());
    // Deliberately not Boolean: setup must not check or export this scratch.
    emit(&mut setup, Fr::from(42u64));
    let setup = setup.finish_shape().unwrap();
    for value in [Fr::ZERO, Fr::ONE] {
      let mut assigned = R1csBuilder::new();
      assert!(!assigned.is_shape_only());
      emit(&mut assigned, value);
      let (r1cs, mut witness) = assigned.finish().unwrap();
      assert_eq!(setup, r1cs);
      setup.check(&witness).unwrap();
      witness.set(Variable(2), Fr::from(2u64)).unwrap();
      assert!(setup.check(&witness).is_err());
    }
    let mut setup_projection = R1csBuilder::new_shape_projection();
    let mut assigned_projection = R1csBuilder::new_projection();
    emit(&mut setup_projection, Fr::from(42u64));
    emit(&mut assigned_projection, Fr::ONE);
    let projected = setup_projection.finish_projection().unwrap();
    assert_eq!(projected, assigned_projection.finish_projection().unwrap());
    assert_eq!(projected.census(), &setup.census());
  }

  #[test]
  fn setup_modes_cannot_export_witnesses_or_ignore_unknown_wires() {
    assert_eq!(
      R1csBuilder::new_shape(shape_limits()).unwrap().finish().unwrap_err(),
      R1csError::WrongBuilderMode,
    );
    assert_eq!(
      R1csBuilder::new_shape_projection().finish().unwrap_err(),
      R1csError::WrongBuilderMode,
    );
    assert_eq!(
      R1csBuilder::new_shape(shape_limits())
        .unwrap()
        .finish_projection()
        .unwrap_err(),
      R1csError::WrongBuilderMode,
    );
    assert_eq!(
      R1csBuilder::new().finish_shape().unwrap_err(),
      R1csError::WrongBuilderMode,
    );
    assert_eq!(
      R1csBuilder::new_shape_projection().finish_shape().unwrap_err(),
      R1csError::WrongBuilderMode,
    );
    let mut builder = R1csBuilder::new_shape(shape_limits()).unwrap();
    builder.enforce_boolean(ConstraintPhase::Statement, Variable(1));
    assert_eq!(
      builder.finish_shape().unwrap_err(),
      R1csError::UnknownVariable(Variable(1)),
    );
  }

  #[test]
  fn setup_limits_refuse_before_retaining_over_budget_data() {
    assert!(matches!(
      R1csBuilder::new_shape(R1csShapeLimitsV0 {
        variables: 0,
        ..shape_limits()
      }),
      Err(R1csError::ResourceLimit {
        resource: "R1CS variables",
        limit: 0,
        actual: 1,
      }),
    ));
    for public in [false, true] {
      let mut builder = R1csBuilder::new_shape(R1csShapeLimitsV0 {
        variables: 1,
        ..shape_limits()
      })
      .unwrap();
      let expected = R1csError::ResourceLimit {
        resource: "R1CS variables",
        limit: 1,
        actual: 2,
      };
      let result = if public {
        builder.alloc_public(Fr::ZERO)
      } else {
        builder.alloc_private(Fr::ZERO)
      };
      assert_eq!(result, Err(expected.clone()));
      assert_eq!(builder.public_variables, 0);
      assert_eq!(builder.private_variables, 0);
      assert_eq!(builder.finish_shape().unwrap_err(), expected);
    }
    for terms_limit in [false, true] {
      let (limits, expected) = if terms_limit {
        (
          R1csShapeLimitsV0 { nonzero_terms: 3, ..shape_limits() },
          R1csError::ResourceLimit {
            resource: "R1CS nonzero terms",
            limit: 3,
            actual: 6,
          },
        )
      } else {
        (
          R1csShapeLimitsV0 { constraints: 1, ..shape_limits() },
          R1csError::ResourceLimit {
            resource: "R1CS constraints",
            limit: 1,
            actual: 2,
          },
        )
      };
      for finish in 0..3 {
        let mut builder = R1csBuilder::new_shape(limits).unwrap();
        let bit = builder.alloc_private(Fr::ZERO).unwrap();
        for _ in 0..3 {
          builder.enforce_boolean(ConstraintPhase::Statement, bit);
        }
        let BuilderStorage::Shape { constraints, nonzero_terms, .. } =
          &builder.storage
        else {
          panic!("shape mode")
        };
        assert_eq!(constraints.len(), 1);
        assert_eq!(*nonzero_terms, 3);
        assert_eq!(builder.alloc_private(Fr::ZERO), Err(expected.clone()));
        assert_eq!(builder.alloc_public(Fr::ZERO), Err(expected.clone()));
        let error = match finish {
          0 => builder.finish_shape().unwrap_err(),
          1 => builder.finish_projection().unwrap_err(),
          _ => builder.finish().unwrap_err(),
        };
        assert_eq!(error, expected);
      }
    }
  }

  #[test]
  fn shape_projection_refusal_cannot_finish_a_prefix() {
    for finish in 0..3 {
      let mut builder =
        R1csBuilder::new_shape_projection_observed_fallible(|_| {
          Err(R1csError::ObserverFailure("setup refused".into()))
        });
      assert!(builder.is_shape_only());
      let bit = builder.alloc_private(Fr::ZERO).unwrap();
      builder.enforce_boolean(ConstraintPhase::Statement, bit);
      let expected = R1csError::ObserverFailure("setup refused".into());
      assert_eq!(builder.alloc_private(Fr::ZERO), Err(expected.clone()));
      let error = match finish {
        0 => builder.finish_shape().unwrap_err(),
        1 => builder.finish_projection().unwrap_err(),
        _ => builder.finish().unwrap_err(),
      };
      assert_eq!(error, expected);
    }
  }

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

  #[test]
  fn fallible_projection_matches_the_unbounded_stream() {
    fn emit(builder: &mut R1csBuilder) {
      let public = builder.alloc_public(Fr::ONE).unwrap();
      let private = builder.alloc_private(Fr::ONE).unwrap();
      builder.enforce_boolean(ConstraintPhase::Statement, public);
      builder.enforce_boolean(ConstraintPhase::Transcript, private);
    }
    let mut bounded = R1csBuilder::new_projection_observed_fallible(|_| Ok(()));
    let mut unbounded = R1csBuilder::new_projection_observed(|_| {});
    let mut materialized = R1csBuilder::new();
    for builder in [&mut bounded, &mut unbounded, &mut materialized] {
      emit(builder);
    }
    let bounded = bounded.finish_projection().unwrap();
    assert_eq!(bounded, unbounded.finish_projection().unwrap());
    assert_eq!(bounded.census(), &materialized.finish().unwrap().0.census());
  }

  #[test]
  fn refused_projection_is_sticky_and_cannot_finish_a_prefix() {
    use std::{cell::Cell, rc::Rc};
    // Refuse the first or second (final) constraint, then exercise either
    // finish method, with and without a subsequent fallible allocation.
    for refuse_at in [1, 2] {
      for finish_projection in [false, true] {
        for allocate_after in [false, true] {
          let seen = Rc::new(Cell::new(0u64));
          let observed = Rc::clone(&seen);
          let expected = R1csError::ResourceLimit {
            resource: "test constraints",
            limit: refuse_at - 1,
            actual: refuse_at,
          };
          let failure = expected.clone();
          let mut builder =
            R1csBuilder::new_projection_observed_fallible(move |_| {
              observed.set(observed.get() + 1);
              if observed.get() >= refuse_at {
                Err(failure.clone())
              } else {
                Ok(())
              }
            });
          let variable = builder.alloc_private(Fr::ONE).unwrap();
          builder.enforce_boolean(ConstraintPhase::Statement, variable);
          builder.enforce_boolean(ConstraintPhase::Transcript, variable);
          // Even an infallible emission after the refusal must do no work.
          builder.enforce_boolean(ConstraintPhase::MatrixFold, variable);
          if allocate_after {
            assert_eq!(builder.alloc_public(Fr::ONE), Err(expected.clone()));
            assert_eq!(builder.alloc_private(Fr::ONE), Err(expected.clone()));
          }
          assert_eq!(seen.get(), refuse_at);
          assert_eq!(builder.private_variables, 1);
          let error = if finish_projection {
            builder.finish_projection().unwrap_err()
          } else {
            builder.finish().unwrap_err()
          };
          assert_eq!(error, expected);
        }
      }
    }
  }
}
