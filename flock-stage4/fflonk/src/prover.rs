use crate::{
  FFLONK_COMMITMENTS, FFLONK_EVALUATIONS, FflonkEvaluationRootsV1,
  FflonkPreprocessedCircuitV1, FflonkProofV1, FflonkTranscriptError, KzgError,
  KzgUniversalSrsV1, PlonkArithmetizationError, commit_polynomial,
  derive_fflonk_challenges, evaluate_polynomial, lower_plonk_witness,
};
use ark_bls12_381::{Fr, G1Affine};
use ark_ff::{Field, One, Zero};
use ark_poly::{
  DenseUVPolynomial, EvaluationDomain, Radix2EvaluationDomain,
  univariate::DensePolynomial,
};
use ix_terminal_circuit::{CanonicalR1csV1, Witness};
use std::fmt;

/// Explicit zero-knowledge randomness consumed by one FFLONK proof.
///
/// `wire_evaluations` are the two reserved-domain values for A, then B, then
/// C. `z_coefficients[i]` multiplies `X^(n+i) - X^i`, so those terms blind Z
/// without changing any value on the size-`n` roots-of-unity domain.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FflonkBlindingV1 {
  pub wire_evaluations: [Fr; 6],
  pub z_coefficients: [Fr; 3],
}

/// Proof plus the public inputs extracted from its canonical R1CS witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FflonkProverOutputV1 {
  pub proof: FflonkProofV1,
  pub public_inputs: Vec<Fr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FflonkProverError {
  Arithmetization(PlonkArithmetizationError),
  Kzg(KzgError),
  Transcript(FflonkTranscriptError),
  SrsMismatch,
  Shape(&'static str),
  SingularChallenge(&'static str),
  CopyPermutationDoesNotClose,
  PolynomialNotDivisible(&'static str),
}

impl fmt::Display for FflonkProverError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Arithmetization(error) => error.fmt(formatter),
      Self::Kzg(error) => error.fmt(formatter),
      Self::Transcript(error) => error.fmt(formatter),
      Self::SrsMismatch => formatter.write_str(
        "FFLONK proving key and universal SRS have different digests",
      ),
      Self::Shape(reason) => {
        write!(formatter, "invalid FFLONK prover shape: {reason}")
      },
      Self::SingularChallenge(relation) => {
        write!(formatter, "FFLONK prover challenge makes {relation} singular",)
      },
      Self::CopyPermutationDoesNotClose => formatter.write_str(
        "FFLONK witness does not close the copy-permutation grand product",
      ),
      Self::PolynomialNotDivisible(relation) => write!(
        formatter,
        "FFLONK polynomial is not exactly divisible by {relation}",
      ),
    }
  }
}

impl std::error::Error for FflonkProverError {
  fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
    match self {
      Self::Arithmetization(error) => Some(error),
      Self::Kzg(error) => Some(error),
      Self::Transcript(error) => Some(error),
      Self::SrsMismatch
      | Self::Shape(_)
      | Self::SingularChallenge(_)
      | Self::CopyPermutationDoesNotClose
      | Self::PolynomialNotDivisible(_) => None,
    }
  }
}

impl From<PlonkArithmetizationError> for FflonkProverError {
  fn from(error: PlonkArithmetizationError) -> Self {
    Self::Arithmetization(error)
  }
}

impl From<KzgError> for FflonkProverError {
  fn from(error: KzgError) -> Self {
    Self::Kzg(error)
  }
}

impl From<FflonkTranscriptError> for FflonkProverError {
  fn from(error: FflonkTranscriptError) -> Self {
    Self::Transcript(error)
  }
}

/// Produces one Stage 4 FFLONK proof from a preprocessed canonical relation.
pub fn prove_fflonk(
  srs: &KzgUniversalSrsV1,
  preprocessed: &FflonkPreprocessedCircuitV1,
  r1cs: &CanonicalR1csV1,
  witness: &Witness,
  blinding: FflonkBlindingV1,
) -> Result<FflonkProverOutputV1, FflonkProverError> {
  let verification_key = preprocessed.verification_key();
  if srs.digest() != verification_key.kzg().srs_digest {
    return Err(FflonkProverError::SrsMismatch);
  }
  srs.ensure_degree(
    usize::try_from(preprocessed.required_srs_degree())
      .map_err(|_| FflonkProverError::Shape("SRS degree exceeds usize"))?,
  )?;
  let plonk_witness =
    lower_plonk_witness(preprocessed.arithmetization(), r1cs, witness)?;
  let domain_size = usize::try_from(verification_key.domain_size())
    .map_err(|_| FflonkProverError::Shape("domain exceeds usize"))?;
  let domain = Radix2EvaluationDomain::<Fr>::new(domain_size)
    .ok_or(FflonkProverError::Shape("unsupported FFT domain"))?;
  if domain.size() != domain_size
    || plonk_witness.columns()[0].len() != domain_size
  {
    return Err(FflonkProverError::Shape("witness/domain length mismatch"));
  }
  let public_input_count = verification_key.num_public_inputs();
  if public_input_count + 2 > domain_size {
    return Err(FflonkProverError::Shape("missing two reserved blinding rows"));
  }
  let public_inputs = witness
    .assignment()
    .get(1..1 + public_input_count)
    .ok_or(FflonkProverError::Shape("R1CS public-input slice"))?
    .to_vec();

  let mut wire_evaluations = plonk_witness.columns().clone();
  let blind_row0 = domain_size - 2;
  let blind_row1 = domain_size - 1;
  for (column, values) in wire_evaluations.iter_mut().enumerate() {
    values[blind_row0] = blinding.wire_evaluations[2 * column];
    values[blind_row1] = blinding.wire_evaluations[2 * column + 1];
  }
  let a = domain.ifft(&wire_evaluations[0]);
  let b = domain.ifft(&wire_evaluations[1]);
  let c = domain.ifft(&wire_evaluations[2]);
  let polynomials = preprocessed.polynomials();
  let mut public_input_evaluations = vec![Fr::zero(); domain_size];
  for (row, input) in public_inputs.iter().enumerate() {
    public_input_evaluations[row] = -*input;
  }
  let public_input_polynomial = domain.ifft(&public_input_evaluations);

  let mut t0_numerator = poly_mul(polynomials.ql.coefficients(), &a);
  poly_add_assign(
    &mut t0_numerator,
    &poly_mul(polynomials.qr.coefficients(), &b),
  );
  poly_add_assign(
    &mut t0_numerator,
    &poly_mul(polynomials.qm.coefficients(), &poly_mul(&a, &b)),
  );
  poly_add_assign(
    &mut t0_numerator,
    &poly_mul(polynomials.qo.coefficients(), &c),
  );
  poly_add_assign(&mut t0_numerator, polynomials.qc.coefficients());
  poly_add_assign(&mut t0_numerator, &public_input_polynomial);
  let t0 = divide_by_xn_minus(t0_numerator, domain_size, Fr::one(), "Z_H(X)")?;
  let c1 = pack_polynomials(4, [&a, &b, &c, &t0])?;

  let mut proof = FflonkProofV1 {
    commitments: [G1Affine::identity(); FFLONK_COMMITMENTS],
    evaluations: [Fr::zero(); FFLONK_EVALUATIONS],
  };
  proof.commitments[0] = commit_polynomial(srs, &c1)?.0;
  let (round1, _) =
    derive_fflonk_challenges(&verification_key, &proof, &public_inputs)?;

  let sigma_evaluations = [
    polynomials.sigma1.evaluations(),
    polynomials.sigma2.evaluations(),
    polynomials.sigma3.evaluations(),
  ];
  let omega_powers = domain.elements().collect::<Vec<_>>();
  let mut z_evaluations = vec![Fr::zero(); domain_size];
  z_evaluations[0] = Fr::one();
  let mut current_z = Fr::one();
  for row in 0..domain_size {
    let x = omega_powers[row];
    let numerator = (wire_evaluations[0][row] + round1.beta * x + round1.gamma)
      * (wire_evaluations[1][row]
        + round1.beta * verification_key.k1() * x
        + round1.gamma)
      * (wire_evaluations[2][row]
        + round1.beta * verification_key.k2() * x
        + round1.gamma);
    let denominator = (wire_evaluations[0][row]
      + round1.beta * sigma_evaluations[0][row]
      + round1.gamma)
      * (wire_evaluations[1][row]
        + round1.beta * sigma_evaluations[1][row]
        + round1.gamma)
      * (wire_evaluations[2][row]
        + round1.beta * sigma_evaluations[2][row]
        + round1.gamma);
    let denominator_inverse = denominator.inverse().ok_or(
      FflonkProverError::SingularChallenge("the permutation denominator"),
    )?;
    current_z *= numerator * denominator_inverse;
    if row + 1 < domain_size {
      z_evaluations[row + 1] = current_z;
    }
  }
  if current_z != Fr::one() {
    return Err(FflonkProverError::CopyPermutationDoesNotClose);
  }
  let mut z = domain.ifft(&z_evaluations);
  blind_z(&mut z, blinding.z_coefficients, domain_size)?;

  let mut lagrange1_evaluations = vec![Fr::zero(); domain_size];
  lagrange1_evaluations[0] = Fr::one();
  let lagrange1 = domain.ifft(&lagrange1_evaluations);
  let t1 = divide_by_xn_minus(
    poly_mul(&poly_sub_constant(&z, Fr::one()), &lagrange1),
    domain_size,
    Fr::one(),
    "Z_H(X) in T1",
  )?;

  let identity_a =
    poly_add_scaled_x_and_constant(&a, round1.beta, round1.gamma);
  let identity_b = poly_add_scaled_x_and_constant(
    &b,
    round1.beta * verification_key.k1(),
    round1.gamma,
  );
  let identity_c = poly_add_scaled_x_and_constant(
    &c,
    round1.beta * verification_key.k2(),
    round1.gamma,
  );
  let identity_product =
    poly_mul(&poly_mul(&poly_mul(&identity_a, &identity_b), &identity_c), &z);
  let copy_a = poly_add(
    &poly_add(&a, &poly_scale(polynomials.sigma1.coefficients(), round1.beta)),
    &[round1.gamma],
  );
  let copy_b = poly_add(
    &poly_add(&b, &poly_scale(polynomials.sigma2.coefficients(), round1.beta)),
    &[round1.gamma],
  );
  let copy_c = poly_add(
    &poly_add(&c, &poly_scale(polynomials.sigma3.coefficients(), round1.beta)),
    &[round1.gamma],
  );
  let z_shifted = shift_argument(&z, verification_key.omega());
  let copy_product =
    poly_mul(&poly_mul(&poly_mul(&copy_a, &copy_b), &copy_c), &z_shifted);
  let t2 = divide_by_xn_minus(
    poly_sub(&identity_product, &copy_product),
    domain_size,
    Fr::one(),
    "Z_H(X) in T2",
  )?;
  let c2 = pack_polynomials(3, [&z, &t1, &t2])?;
  proof.commitments[1] = commit_polynomial(srs, &c2)?.0;

  let (round3, roots) =
    derive_fflonk_challenges(&verification_key, &proof, &public_inputs)?;
  proof.evaluations = [
    evaluate_polynomial(polynomials.ql.coefficients(), round3.xi),
    evaluate_polynomial(polynomials.qr.coefficients(), round3.xi),
    evaluate_polynomial(polynomials.qm.coefficients(), round3.xi),
    evaluate_polynomial(polynomials.qo.coefficients(), round3.xi),
    evaluate_polynomial(polynomials.qc.coefficients(), round3.xi),
    evaluate_polynomial(polynomials.sigma1.coefficients(), round3.xi),
    evaluate_polynomial(polynomials.sigma2.coefficients(), round3.xi),
    evaluate_polynomial(polynomials.sigma3.coefficients(), round3.xi),
    evaluate_polynomial(&a, round3.xi),
    evaluate_polynomial(&b, round3.xi),
    evaluate_polynomial(&c, round3.xi),
    evaluate_polynomial(&z, round3.xi),
    evaluate_polynomial(&z, round3.xi_omega),
    evaluate_polynomial(&t1, round3.xi_omega),
    evaluate_polynomial(&t2, round3.xi_omega),
  ];
  let (round4, roots_after_evaluations) =
    derive_fflonk_challenges(&verification_key, &proof, &public_inputs)?;
  debug_assert_eq!(roots, roots_after_evaluations);

  let r0 = interpolate_from_polynomial(
    &roots.h0_omega8,
    preprocessed.c0_coefficients(),
  )?;
  let r1 = interpolate_from_polynomial(&roots.h1_omega4, &c1)?;
  let r2_roots = combined_r2_roots(&roots);
  let r2 = interpolate_from_polynomial(&r2_roots, &c2)?;
  let mut f = divide_by_xn_minus(
    poly_sub(preprocessed.c0_coefficients(), &r0),
    8,
    round4.xi,
    "X^8 - xi",
  )?;
  let f1 = poly_scale(
    &divide_by_xn_minus(poly_sub(&c1, &r1), 4, round4.xi, "X^4 - xi")?,
    round4.alpha,
  );
  poly_add_assign(&mut f, &f1);
  let f2 = poly_scale(
    &divide_by_xn_minus(
      divide_by_xn_minus(poly_sub(&c2, &r2), 3, round4.xi, "X^3 - xi")?,
      3,
      round4.xi_omega,
      "X^3 - xi*omega",
    )?,
    round4.alpha.square(),
  );
  poly_add_assign(&mut f, &f2);
  proof.commitments[2] = commit_polynomial(srs, &f)?.0;

  let (round5, roots_after_w1) =
    derive_fflonk_challenges(&verification_key, &proof, &public_inputs)?;
  debug_assert_eq!(roots, roots_after_w1);
  let z0 = vanishing_polynomial(&roots.h0_omega8);
  let z1 = vanishing_polynomial(&roots.h1_omega4);
  let z2 = vanishing_polynomial(&r2_roots);
  let z0_at_y = evaluate_polynomial(&z0, round5.y);
  let z1_at_y = evaluate_polynomial(&z1, round5.y);
  let z2_at_y = evaluate_polynomial(&z2, round5.y);
  let pre0 = z1_at_y * z2_at_y;
  let pre1 = round5.alpha * z0_at_y * z2_at_y;
  let pre2 = round5.alpha.square() * z0_at_y * z1_at_y;
  let mut l = poly_scale(
    &poly_sub_constant(
      preprocessed.c0_coefficients(),
      evaluate_polynomial(&r0, round5.y),
    ),
    pre0,
  );
  poly_add_assign(
    &mut l,
    &poly_scale(
      &poly_sub_constant(&c1, evaluate_polynomial(&r1, round5.y)),
      pre1,
    ),
  );
  poly_add_assign(
    &mut l,
    &poly_scale(
      &poly_sub_constant(&c2, evaluate_polynomial(&r2, round5.y)),
      pre2,
    ),
  );
  let zt = poly_mul(&poly_mul(&z0, &z1), &z2);
  poly_sub_assign(&mut l, &poly_scale(&f, evaluate_polynomial(&zt, round5.y)));
  let zts2_at_y = evaluate_polynomial(&poly_mul(&z1, &z2), round5.y);
  let zts2_inverse = zts2_at_y
    .inverse()
    .ok_or(FflonkProverError::SingularChallenge("Z_1(y) * Z_2(y)"))?;
  l = poly_scale(&l, zts2_inverse);
  let w2 = divide_by_xn_minus(l, 1, round5.y, "X - y")?;
  proof.commitments[3] = commit_polynomial(srs, &w2)?.0;

  Ok(FflonkProverOutputV1 { proof, public_inputs })
}

fn combined_r2_roots(roots: &FflonkEvaluationRootsV1) -> [Fr; 6] {
  [
    roots.h2_omega3[0],
    roots.h2_omega3[1],
    roots.h2_omega3[2],
    roots.h3_omega3[0],
    roots.h3_omega3[1],
    roots.h3_omega3[2],
  ]
}

fn blind_z(
  polynomial: &mut Vec<Fr>,
  factors: [Fr; 3],
  domain_size: usize,
) -> Result<(), FflonkProverError> {
  let required = domain_size
    .checked_add(factors.len())
    .ok_or(FflonkProverError::Shape("blinded Z degree overflow"))?;
  polynomial.resize(required, Fr::zero());
  for (degree, factor) in factors.into_iter().enumerate() {
    polynomial[degree] -= factor;
    polynomial[domain_size + degree] += factor;
  }
  trim(polynomial);
  Ok(())
}

fn interpolate_from_polynomial<const N: usize>(
  points: &[Fr; N],
  polynomial: &[Fr],
) -> Result<Vec<Fr>, FflonkProverError> {
  let values = core::array::from_fn(|index| {
    evaluate_polynomial(polynomial, points[index])
  });
  interpolate(points, &values)
}

fn interpolate<const N: usize>(
  points: &[Fr; N],
  values: &[Fr; N],
) -> Result<Vec<Fr>, FflonkProverError> {
  let mut output = Vec::new();
  for (index, point) in points.iter().enumerate() {
    let mut basis = vec![Fr::one()];
    let mut denominator = Fr::one();
    for (other_index, other) in points.iter().enumerate() {
      if index != other_index {
        basis = poly_mul(&basis, &[-*other, Fr::one()]);
        denominator *= point - other;
      }
    }
    let inverse = denominator.inverse().ok_or(
      FflonkProverError::SingularChallenge("an interpolation denominator"),
    )?;
    poly_add_assign(&mut output, &poly_scale(&basis, values[index] * inverse));
  }
  Ok(output)
}

fn vanishing_polynomial<const N: usize>(points: &[Fr; N]) -> Vec<Fr> {
  points.iter().fold(vec![Fr::one()], |polynomial, point| {
    poly_mul(&polynomial, &[-*point, Fr::one()])
  })
}

fn pack_polynomials<const N: usize>(
  stride: usize,
  polynomials: [&[Fr]; N],
) -> Result<Vec<Fr>, FflonkProverError> {
  if stride != N {
    return Err(FflonkProverError::Shape("packed polynomial stride"));
  }
  let max_len =
    polynomials.iter().map(|polynomial| polynomial.len()).max().unwrap_or(0);
  let packed_len = max_len
    .checked_mul(stride)
    .ok_or(FflonkProverError::Shape("packed polynomial length overflow"))?;
  let mut packed = vec![Fr::zero(); packed_len];
  for (offset, polynomial) in polynomials.into_iter().enumerate() {
    for (degree, coefficient) in polynomial.iter().enumerate() {
      packed[stride * degree + offset] = *coefficient;
    }
  }
  trim(&mut packed);
  Ok(packed)
}

fn poly_mul(left: &[Fr], right: &[Fr]) -> Vec<Fr> {
  if left.is_empty() || right.is_empty() {
    return Vec::new();
  }
  let left = DensePolynomial::from_coefficients_vec(left.to_vec());
  let right = DensePolynomial::from_coefficients_vec(right.to_vec());
  (&left * &right).coeffs
}

fn poly_add(left: &[Fr], right: &[Fr]) -> Vec<Fr> {
  let mut output = left.to_vec();
  poly_add_assign(&mut output, right);
  output
}

fn poly_add_assign(output: &mut Vec<Fr>, addend: &[Fr]) {
  output.resize(output.len().max(addend.len()), Fr::zero());
  for (target, value) in output.iter_mut().zip(addend) {
    *target += value;
  }
  trim(output);
}

fn poly_sub(left: &[Fr], right: &[Fr]) -> Vec<Fr> {
  let mut output = left.to_vec();
  poly_sub_assign(&mut output, right);
  output
}

fn poly_sub_assign(output: &mut Vec<Fr>, subtrahend: &[Fr]) {
  output.resize(output.len().max(subtrahend.len()), Fr::zero());
  for (target, value) in output.iter_mut().zip(subtrahend) {
    *target -= value;
  }
  trim(output);
}

fn poly_sub_constant(polynomial: &[Fr], constant: Fr) -> Vec<Fr> {
  let mut output = polynomial.to_vec();
  if output.is_empty() {
    output.push(-constant);
  } else {
    output[0] -= constant;
  }
  trim(&mut output);
  output
}

fn poly_scale(polynomial: &[Fr], scalar: Fr) -> Vec<Fr> {
  if scalar.is_zero() {
    return Vec::new();
  }
  let mut output = polynomial.to_vec();
  for coefficient in &mut output {
    *coefficient *= scalar;
  }
  trim(&mut output);
  output
}

fn poly_add_scaled_x_and_constant(
  polynomial: &[Fr],
  x_coefficient: Fr,
  constant: Fr,
) -> Vec<Fr> {
  let mut output = polynomial.to_vec();
  output.resize(output.len().max(2), Fr::zero());
  output[0] += constant;
  output[1] += x_coefficient;
  trim(&mut output);
  output
}

fn shift_argument(polynomial: &[Fr], factor: Fr) -> Vec<Fr> {
  let mut power = Fr::one();
  let mut output = Vec::with_capacity(polynomial.len());
  for coefficient in polynomial {
    output.push(*coefficient * power);
    power *= factor;
  }
  trim(&mut output);
  output
}

fn divide_by_xn_minus(
  polynomial: Vec<Fr>,
  n: usize,
  beta: Fr,
  relation: &'static str,
) -> Result<Vec<Fr>, FflonkProverError> {
  if n == 0 {
    return Err(FflonkProverError::Shape("zero-degree divisor"));
  }
  let mut remainder = polynomial;
  trim(&mut remainder);
  if remainder.len() <= n {
    if remainder.iter().any(|coefficient| !coefficient.is_zero()) {
      return Err(FflonkProverError::PolynomialNotDivisible(relation));
    }
    return Ok(Vec::new());
  }
  let mut quotient = vec![Fr::zero(); remainder.len() - n];
  for degree in (n..remainder.len()).rev() {
    let coefficient = remainder[degree];
    quotient[degree - n] = coefficient;
    remainder[degree] = Fr::zero();
    remainder[degree - n] += beta * coefficient;
  }
  if remainder[..n].iter().any(|coefficient| !coefficient.is_zero()) {
    return Err(FflonkProverError::PolynomialNotDivisible(relation));
  }
  trim(&mut quotient);
  Ok(quotient)
}

fn trim(polynomial: &mut Vec<Fr>) {
  while polynomial.last().is_some_and(Zero::is_zero) {
    polynomial.pop();
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    KzgUniversalSrsV1, arithmetize_r1cs, preprocess_fflonk,
    required_fflonk_srs_degree, verify_fflonk,
  };
  use ark_bls12_381::{G1Affine, G2Affine};
  use ark_ec::{AffineRepr, CurveGroup};
  use ark_ff::PrimeField;
  use ix_terminal_circuit::{ConstraintPhase, LinearCombination, R1csBuilder};

  fn test_srs(max_degree: usize, tau: Fr) -> KzgUniversalSrsV1 {
    let mut scalar = Fr::one();
    let powers = (0..=max_degree)
      .map(|_| {
        let point = G1Affine::generator().mul_bigint(scalar.into_bigint());
        scalar *= tau;
        point.into_affine()
      })
      .collect();
    let tau_g2 =
      G2Affine::generator().mul_bigint(tau.into_bigint()).into_affine();
    KzgUniversalSrsV1::new(powers, G2Affine::generator(), tau_g2).unwrap()
  }

  fn fixture() -> (CanonicalR1csV1, Witness) {
    let mut builder = R1csBuilder::new();
    let public = builder.alloc_public(Fr::from(3_u64)).unwrap();
    let private = builder.alloc_private(Fr::from(5_u64)).unwrap();
    let product = builder.alloc_private(Fr::from(15_u64)).unwrap();
    let bit = builder.alloc_private(Fr::one()).unwrap();
    builder.enforce(
      ConstraintPhase::Statement,
      LinearCombination::from_variable(public),
      LinearCombination::from_variable(private),
      LinearCombination::from_variable(product),
    );
    builder.enforce_boolean(ConstraintPhase::Transcript, bit);
    builder.finish().unwrap()
  }

  #[test]
  fn development_prover_round_trips_through_the_native_verifier() {
    let (r1cs, witness) = fixture();
    let arithmetization = arithmetize_r1cs(&r1cs).unwrap();
    let required =
      required_fflonk_srs_degree(arithmetization.census().domain_size).unwrap();
    let srs = test_srs(usize::try_from(required).unwrap(), Fr::from(29_u64));
    let preprocessed = preprocess_fflonk(&srs, arithmetization).unwrap();
    let blinding = FflonkBlindingV1 {
      wire_evaluations: core::array::from_fn(|index| {
        Fr::from(index as u64 + 31)
      }),
      z_coefficients: [Fr::from(41_u64), Fr::from(43_u64), Fr::from(47_u64)],
    };
    let output =
      prove_fflonk(&srs, &preprocessed, &r1cs, &witness, blinding).unwrap();
    assert_eq!(output.public_inputs, vec![Fr::from(3_u64)]);
    assert_eq!(
      verify_fflonk(
        &preprocessed.verification_key(),
        &output.proof,
        &output.public_inputs,
      ),
      Ok(true),
    );
    assert_eq!(
      FflonkProofV1::from_bytes(&output.proof.to_bytes()),
      Ok(output.proof.clone()),
    );

    let mut mutated = output.proof;
    mutated.evaluations[0] += Fr::one();
    assert_eq!(
      verify_fflonk(
        &preprocessed.verification_key(),
        &mutated,
        &output.public_inputs,
      ),
      Ok(false),
    );
  }

  #[test]
  fn exact_division_rejects_a_nonzero_remainder() {
    assert_eq!(
      divide_by_xn_minus(
        vec![Fr::one(), Fr::one()],
        1,
        Fr::from(2_u64),
        "fixture",
      ),
      Err(FflonkProverError::PolynomialNotDivisible("fixture")),
    );
  }
}
