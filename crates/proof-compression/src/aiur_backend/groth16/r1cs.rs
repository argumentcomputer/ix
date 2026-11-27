//! Rank-1 Constraint System (R1CS) over the BN254 scalar field `Fr`.
//!
//! Wire convention:
//! - Wire `0` is the constant `1` (`Fr::ONE`).
//! - Wires `1..=num_public` are the public inputs (`x_1, ..., x_l`).
//! - Wires `(1 + num_public)..num_wires` are private witness variables.
//!
//! Each constraint enforces `(A · z) * (B · z) = (C · z)` for the full wire
//! assignment `z = [1, x_1, ..., x_l, w_1, ..., w_k]`.

use ark_bn254::Fr;
use ark_ff::{AdditiveGroup, Field, Zero};
use std::collections::BTreeMap;

/// Linear combination `Σ coeff_i · z[wire_i]` over BN254 `Fr`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LinearCombination {
  terms: Vec<(usize, Fr)>,
}

impl LinearCombination {
  /// The zero linear combination.
  pub const fn zero() -> Self {
    Self { terms: Vec::new() }
  }

  /// Constant term `c · z[0]`.
  pub fn from_constant(coeff: Fr) -> Self {
    if coeff.is_zero() {
      Self::zero()
    } else {
      Self { terms: vec![(R1cs::ONE_WIRE, coeff)] }
    }
  }

  /// Single wire with unit coefficient `1 · z[wire]`.
  pub fn from_wire(wire: usize) -> Self {
    Self { terms: vec![(wire, Fr::ONE)] }
  }

  /// Single weighted wire `coeff · z[wire]`.
  pub fn from_term(wire: usize, coeff: Fr) -> Self {
    if coeff.is_zero() {
      Self::zero()
    } else {
      Self { terms: vec![(wire, coeff)] }
    }
  }

  /// Append `coeff · z[wire]` to this linear combination.
  pub fn add_term(&mut self, wire: usize, coeff: Fr) -> &mut Self {
    if !coeff.is_zero() {
      self.terms.push((wire, coeff));
    }
    self
  }

  /// Return `self + other` in canonical merged form.
  pub fn add(&self, other: &Self) -> Self {
    let mut out = self.clone();
    out.terms.extend_from_slice(&other.terms);
    out.canonicalize();
    out
  }

  /// Return `self - other` in canonical merged form.
  pub fn sub(&self, other: &Self) -> Self {
    let mut out = self.clone();
    for &(wire, coeff) in &other.terms {
      out.terms.push((wire, -coeff));
    }
    out.canonicalize();
    out
  }

  /// Return `scalar · self` in canonical form.
  pub fn scale(&self, scalar: Fr) -> Self {
    if scalar.is_zero() {
      return Self::zero();
    }
    let mut out = Self {
      terms: self
        .terms
        .iter()
        .map(|&(wire, coeff)| (wire, coeff * scalar))
        .collect(),
    };
    out.canonicalize();
    out
  }

  /// Merge duplicate wire indices and drop zero-coefficient terms.
  pub fn canonicalize(&mut self) {
    let mut merged: BTreeMap<usize, Fr> = BTreeMap::new();
    for &(wire, coeff) in &self.terms {
      if !coeff.is_zero() {
        *merged.entry(wire).or_insert(Fr::ZERO) += coeff;
      }
    }
    self.terms =
      merged.into_iter().filter(|(_, coeff)| !coeff.is_zero()).collect();
  }

  /// View the `(wire_index, coefficient)` pairs.
  pub fn terms(&self) -> &[(usize, Fr)] {
    &self.terms
  }

  /// Evaluate `Σ coeff_i · assignment[wire_i]`.
  pub fn evaluate(&self, assignment: &[Fr]) -> Fr {
    let mut acc = Fr::ZERO;
    for &(wire, coeff) in &self.terms {
      acc += coeff * assignment[wire];
    }
    acc
  }
}

/// A single R1CS multiplicative constraint `(a · z) * (b · z) = (c · z)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constraint {
  pub a: LinearCombination,
  pub b: LinearCombination,
  pub c: LinearCombination,
}

/// Rank-1 Constraint System over BN254 `Fr`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R1cs {
  /// Number of public inputs (wires `1..=num_public`, excluding constant wire 0).
  pub num_public: usize,
  /// Total number of wires (`1 + num_public + num_private`).
  pub num_wires: usize,
  /// Multiplicative constraints `(A · z) ∘ (B · z) = (C · z)`.
  pub constraints: Vec<Constraint>,
}

impl R1cs {
  /// Wire index fixed to the constant `Fr::ONE`.
  pub const ONE_WIRE: usize = 0;

  /// Create an empty R1CS with `num_public` public input wires (`1..=num_public`).
  pub const fn new(num_public: usize) -> Self {
    Self { num_public, num_wires: 1 + num_public, constraints: Vec::new() }
  }

  /// Wire index for public input `index` (`0..num_public`).
  pub fn public_wire(&self, index: usize) -> usize {
    assert!(
      index < self.num_public,
      "public input index {index} out of bounds (num_public = {})",
      self.num_public
    );
    1 + index
  }

  /// Number of instance wires (`1 + num_public`, including constant wire 0).
  pub const fn num_instance_wires(&self) -> usize {
    1 + self.num_public
  }

  /// Number of private witness wires (`num_wires - (1 + num_public)`).
  pub const fn num_private(&self) -> usize {
    self.num_wires.saturating_sub(1 + self.num_public)
  }

  /// Allocate a new private witness wire and return its wire index.
  pub fn alloc_private(&mut self) -> usize {
    let wire = self.num_wires;
    self.num_wires += 1;
    wire
  }

  /// Add a constraint `(a · z) * (b · z) = (c · z)`.
  pub fn add_constraint(
    &mut self,
    mut a: LinearCombination,
    mut b: LinearCombination,
    mut c: LinearCombination,
  ) {
    a.canonicalize();
    b.canonicalize();
    c.canonicalize();
    for &(wire, _) in a.terms().iter().chain(b.terms()).chain(c.terms()) {
      assert!(
        wire < self.num_wires,
        "constraint references wire {wire} >= num_wires ({})",
        self.num_wires
      );
    }
    self.constraints.push(Constraint { a, b, c });
  }

  /// Power-of-two QAP evaluation domain size `N`.
  ///
  /// Includes `1 + num_public` anchoring rows (`z_i · 0 = 0` for `i = 0..=l`)
  /// so public-input QAP polynomials are linearly independent of all private
  /// witness polynomials (Groth16 Section 3.2 soundness condition).
  pub fn domain_size(&self) -> usize {
    let qap_rows = self.constraints.len() + self.num_instance_wires();
    qap_rows.next_power_of_two().max(2)
  }

  /// Validate structural invariants of the R1CS.
  pub fn validate(&self) -> Result<(), String> {
    if self.num_wires < self.num_instance_wires() {
      return Err(format!(
        "invalid R1CS: num_wires ({}) < 1 + num_public ({})",
        self.num_wires,
        self.num_instance_wires()
      ));
    }
    for (idx, con) in self.constraints.iter().enumerate() {
      for &(wire, _) in
        con.a.terms().iter().chain(con.b.terms()).chain(con.c.terms())
      {
        if wire >= self.num_wires {
          return Err(format!(
            "constraint {idx} references wire {wire} >= num_wires ({})",
            self.num_wires
          ));
        }
      }
    }
    Ok(())
  }

  /// Assemble a full wire vector `[1, public_inputs..., private_witness...]`.
  pub fn make_assignment(
    &self,
    public_inputs: &[Fr],
    private_witness: &[Fr],
  ) -> Result<Vec<Fr>, String> {
    if public_inputs.len() != self.num_public {
      return Err(format!(
        "public input length mismatch: got {}, expected {}",
        public_inputs.len(),
        self.num_public
      ));
    }
    if private_witness.len() != self.num_private() {
      return Err(format!(
        "private witness length mismatch: got {}, expected {}",
        private_witness.len(),
        self.num_private()
      ));
    }
    let mut assignment = Vec::with_capacity(self.num_wires);
    assignment.push(Fr::ONE);
    assignment.extend_from_slice(public_inputs);
    assignment.extend_from_slice(private_witness);
    Ok(assignment)
  }

  /// Verify that `assignment` satisfies every constraint in the R1CS.
  pub fn is_satisfied(&self, assignment: &[Fr]) -> Result<(), String> {
    self.validate()?;
    if assignment.len() != self.num_wires {
      return Err(format!(
        "assignment length mismatch: got {}, expected {}",
        assignment.len(),
        self.num_wires
      ));
    }
    if assignment[Self::ONE_WIRE] != Fr::ONE {
      return Err("wire 0 must equal Fr::ONE".into());
    }
    for (idx, con) in self.constraints.iter().enumerate() {
      let a_val = con.a.evaluate(assignment);
      let b_val = con.b.evaluate(assignment);
      let c_val = con.c.evaluate(assignment);
      if a_val * b_val != c_val {
        return Err(format!(
          "R1CS constraint {idx} unsatisfied: ({a_val}) * ({b_val}) != ({c_val})"
        ));
      }
    }
    Ok(())
  }
}
