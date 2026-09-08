use crate::polynomial_storage::{
  evaluate_polynomial_source, for_each_polynomial_chunk, load_polynomial,
};
use crate::{
  FFLONK_COMMITMENTS, FFLONK_EVALUATIONS, FFLONK_POLYNOMIAL_CHUNK_FIELDS,
  FFLONK_POLYNOMIAL_FFT_DOMAIN_MULTIPLIER, FflonkEvaluationRootsV1,
  FflonkFixedPolynomialV1, FflonkPolynomialSourceV1, FflonkProofV1,
  FflonkProvingKeyV1, FflonkStorageError, FflonkTranscriptError,
  KzgCommitmentSourceV1, KzgError, PlonkArithmetizationError,
  commit_polynomial, derive_fflonk_challenges, evaluate_polynomial,
  lower_plonk_witness,
};
use ark_bls12_381::{Fr, G1Affine};
use ark_ff::{FftField, Field, One, Zero, batch_inversion};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
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
  Storage(FflonkStorageError),
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
      Self::Storage(error) => error.fmt(formatter),
    }
  }
}

impl std::error::Error for FflonkProverError {
  fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
    match self {
      Self::Arithmetization(error) => Some(error),
      Self::Kzg(error) => Some(error),
      Self::Transcript(error) => Some(error),
      Self::Storage(error) => Some(error),
      Self::SrsMismatch
      | Self::Shape(_)
      | Self::SingularChallenge(_)
      | Self::CopyPermutationDoesNotClose
      | Self::PolynomialNotDivisible(_) => None,
    }
  }
}

impl From<FflonkStorageError> for FflonkProverError {
  fn from(error: FflonkStorageError) -> Self {
    Self::Storage(error)
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
  srs: &(impl KzgCommitmentSourceV1 + ?Sized),
  preprocessed: &(impl FflonkProvingKeyV1 + ?Sized),
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
  let domain_size = usize::try_from(verification_key.domain_size())
    .map_err(|_| FflonkProverError::Shape("domain exceeds usize"))?;
  validate_polynomial_domain(domain_size)?;
  let plonk_witness =
    lower_plonk_witness(preprocessed.arithmetization(), r1cs, witness)?;
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

  let mut wire_evaluations = plonk_witness.into_columns();
  let blind_row0 = domain_size - 2;
  let blind_row1 = domain_size - 1;
  for (column, values) in wire_evaluations.iter_mut().enumerate() {
    values[blind_row0] = blinding.wire_evaluations[2 * column];
    values[blind_row1] = blinding.wire_evaluations[2 * column + 1];
  }
  let a = domain.ifft(&wire_evaluations[0]);
  let b = domain.ifft(&wire_evaluations[1]);
  let c = domain.ifft(&wire_evaluations[2]);
  let mut public_input_evaluations = vec![Fr::zero(); domain_size];
  for (row, input) in public_inputs.iter().enumerate() {
    public_input_evaluations[row] = -*input;
  }
  let public_input_polynomial = domain.ifft(&public_input_evaluations);
  drop(public_input_evaluations);

  let mut t0_numerator = poly_mul_source(
    &preprocessed.coefficient_source(FflonkFixedPolynomialV1::Ql),
    &a,
  )?;
  poly_add_assign(
    &mut t0_numerator,
    &poly_mul_source(
      &preprocessed.coefficient_source(FflonkFixedPolynomialV1::Qr),
      &b,
    )?,
  );
  poly_add_assign(
    &mut t0_numerator,
    &poly_mul_source(
      &preprocessed.coefficient_source(FflonkFixedPolynomialV1::Qm),
      &poly_mul(&a, &b),
    )?,
  );
  poly_add_assign(
    &mut t0_numerator,
    &poly_mul_source(
      &preprocessed.coefficient_source(FflonkFixedPolynomialV1::Qo),
      &c,
    )?,
  );
  poly_add_scaled_source(
    &mut t0_numerator,
    &preprocessed.coefficient_source(FflonkFixedPolynomialV1::Qc),
    Fr::one(),
  )?;
  poly_add_assign(&mut t0_numerator, &public_input_polynomial);
  let t0 = divide_by_xn_minus(t0_numerator, domain_size, Fr::one(), "Z_H(X)")?;
  let c1 = pack_polynomials(4, [&a, &b, &c, &t0])?;
  drop(t0);
  drop(public_input_polynomial);

  let mut proof = FflonkProofV1 {
    commitments: [G1Affine::identity(); FFLONK_COMMITMENTS],
    evaluations: [Fr::zero(); FFLONK_EVALUATIONS],
  };
  proof.commitments[0] = commit_polynomial(srs, &c1)?.0;
  let (round1, _) =
    derive_fflonk_challenges(&verification_key, &proof, &public_inputs)?;

  let mut z = permutation_grand_product(
    &domain,
    &wire_evaluations,
    preprocessed.sigma_sources(),
    round1.beta,
    round1.gamma,
    verification_key.k1(),
    verification_key.k2(),
  )?;
  drop(wire_evaluations);
  domain.ifft_in_place(&mut z);
  blind_z(&mut z, blinding.z_coefficients, domain_size)?;

  // L_1(X) = Z_H(X)/(n*(X-1)); cancel Z_H before multiplication.
  let mut t1 = divide_by_xn_minus(
    poly_sub_constant(&z, Fr::one()),
    1,
    Fr::one(),
    "X - 1 in T1",
  )?;
  for coefficient in &mut t1 {
    *coefficient *= domain.size_inv();
  }

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
  drop(identity_a);
  drop(identity_b);
  drop(identity_c);
  let copy_a = copy_factor(
    &a,
    &preprocessed.coefficient_source(FflonkFixedPolynomialV1::Sigma1),
    round1.beta,
    round1.gamma,
  )?;
  let copy_b = copy_factor(
    &b,
    &preprocessed.coefficient_source(FflonkFixedPolynomialV1::Sigma2),
    round1.beta,
    round1.gamma,
  )?;
  let copy_c = copy_factor(
    &c,
    &preprocessed.coefficient_source(FflonkFixedPolynomialV1::Sigma3),
    round1.beta,
    round1.gamma,
  )?;
  let z_shifted = shift_argument(&z, verification_key.omega());
  let copy_product =
    poly_mul(&poly_mul(&poly_mul(&copy_a, &copy_b), &copy_c), &z_shifted);
  drop(copy_a);
  drop(copy_b);
  drop(copy_c);
  drop(z_shifted);
  let t2 = divide_by_xn_minus(
    poly_sub(&identity_product, &copy_product),
    domain_size,
    Fr::one(),
    "Z_H(X) in T2",
  )?;
  drop(identity_product);
  drop(copy_product);
  let c2 = pack_polynomials(3, [&z, &t1, &t2])?;
  proof.commitments[1] = commit_polynomial(srs, &c2)?.0;

  let (round3, roots) =
    derive_fflonk_challenges(&verification_key, &proof, &public_inputs)?;
  for (index, id) in FflonkFixedPolynomialV1::ALL.into_iter().enumerate() {
    proof.evaluations[index] = evaluate_polynomial_source(
      &preprocessed.coefficient_source(id),
      &[round3.xi],
    )?[0];
  }
  proof.evaluations[8..].copy_from_slice(&[
    evaluate_polynomial(&a, round3.xi),
    evaluate_polynomial(&b, round3.xi),
    evaluate_polynomial(&c, round3.xi),
    evaluate_polynomial(&z, round3.xi),
    evaluate_polynomial(&z, round3.xi_omega),
    evaluate_polynomial(&t1, round3.xi_omega),
    evaluate_polynomial(&t2, round3.xi_omega),
  ]);
  drop(a);
  drop(b);
  drop(c);
  drop(z);
  drop(t1);
  drop(t2);
  let (round4, roots_after_evaluations) =
    derive_fflonk_challenges(&verification_key, &proof, &public_inputs)?;
  debug_assert_eq!(roots, roots_after_evaluations);

  let c0_source = preprocessed.c0_source();
  let r0 = interpolate(
    &roots.h0_omega8,
    &evaluate_polynomial_source(&c0_source, &roots.h0_omega8)?,
  )?;
  let r1 = interpolate_from_polynomial(&roots.h1_omega4, &c1)?;
  let r2_roots = combined_r2_roots(&roots);
  let r2 = interpolate_from_polynomial(&r2_roots, &c2)?;
  let mut f_source =
    Vec::with_capacity(c0_source.len().max(c1.len()).max(c2.len()));
  for_each_polynomial_chunk(&c0_source, |_, values| {
    f_source.extend_from_slice(values)
  })?;
  poly_sub_assign(&mut f_source, &r0);
  let mut f = divide_by_xn_minus(f_source, 8, round4.xi, "X^8 - xi")?;
  let f1 = divide_by_xn_minus(poly_sub(&c1, &r1), 4, round4.xi, "X^4 - xi")?;
  poly_add_scaled_assign(&mut f, &f1, round4.alpha);
  drop(f1);
  let f2 = divide_by_xn_minus(
    divide_by_xn_minus(poly_sub(&c2, &r2), 3, round4.xi, "X^3 - xi")?,
    3,
    round4.xi_omega,
    "X^3 - xi*omega",
  )?;
  poly_add_scaled_assign(&mut f, &f2, round4.alpha.square());
  drop(f2);
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
  let zt = poly_mul(&poly_mul(&z0, &z1), &z2);
  // W2 can consume C1, C2, and F. Reuse the largest allocation for their
  // linear combination, avoiding another full packed-polynomial buffer.
  let mut parts =
    [(c1, pre1), (c2, pre2), (f, -evaluate_polynomial(&zt, round5.y))];
  let largest = parts
    .iter()
    .enumerate()
    .max_by_key(|(_, (poly, _))| poly.capacity())
    .map(|(index, _)| index)
    .expect("three polynomial buffers");
  parts.swap(0, largest);
  let mut parts = parts.into_iter();
  let (mut l, scale) = parts.next().expect("three polynomial buffers");
  for coefficient in &mut l {
    *coefficient *= scale;
  }
  for (polynomial, scale) in parts {
    poly_add_scaled_assign(&mut l, &polynomial, scale);
  }
  poly_add_scaled_source(&mut l, &c0_source, pre0)?;
  l.resize(l.len().max(1), Fr::zero());
  l[0] -= evaluate_polynomial(&r0, round5.y) * pre0
    + evaluate_polynomial(&r1, round5.y) * pre1
    + evaluate_polynomial(&r2, round5.y) * pre2;
  let zts2_at_y = evaluate_polynomial(&poly_mul(&z1, &z2), round5.y);
  let zts2_inverse = zts2_at_y
    .inverse()
    .ok_or(FflonkProverError::SingularChallenge("Z_1(y) * Z_2(y)"))?;
  for coefficient in &mut l {
    *coefficient *= zts2_inverse;
  }
  let w2 = divide_by_xn_minus(l, 1, round5.y, "X - y")?;
  proof.commitments[3] = commit_polynomial(srs, &w2)?.0;

  Ok(FflonkProverOutputV1 { proof, public_inputs })
}

const PERMUTATION_BATCH_ROWS: usize = 16_384;

fn permutation_grand_product(
  domain: &Radix2EvaluationDomain<Fr>,
  wires: &[Vec<Fr>; 3],
  sigma: [impl FflonkPolynomialSourceV1; 3],
  beta: Fr,
  gamma: Fr,
  k1: Fr,
  k2: Fr,
) -> Result<Vec<Fr>, FflonkProverError> {
  let size = domain.size();
  if wires.iter().any(|column| column.len() != size)
    || sigma.iter().any(|column| column.len() != size)
  {
    return Err(FflonkProverError::Shape("permutation column length"));
  }
  let batch_rows = PERMUTATION_BATCH_ROWS.min(size);
  // Cache one authenticated chunk per file-backed sigma column across the
  // smaller inversion batches, avoiding repeated reads of the same bytes.
  debug_assert!(
    FFLONK_POLYNOMIAL_CHUNK_FIELDS.is_multiple_of(PERMUTATION_BATCH_ROWS)
  );
  let chunk_rows = FFLONK_POLYNOMIAL_CHUNK_FIELDS.min(size);
  let mut sigma_buffers: [Vec<Fr>; 3] = core::array::from_fn(|index| {
    if sigma[index].as_slice().is_some() {
      Vec::new()
    } else {
      vec![Fr::zero(); chunk_rows]
    }
  });
  let mut numerators = Vec::with_capacity(batch_rows);
  let mut denominators = Vec::with_capacity(batch_rows);
  let mut evaluations = Vec::with_capacity(size);
  evaluations.push(Fr::one());
  let mut current = Fr::one();
  let mut x = Fr::one();
  for start in (0..size).step_by(batch_rows) {
    let chunk_start = start / chunk_rows * chunk_rows;
    let chunk_end = (chunk_start + chunk_rows).min(size);
    let mut sigma_chunk = [&[][..]; 3];
    for (index, (source, buffer)) in
      sigma.iter().zip(&mut sigma_buffers).enumerate()
    {
      sigma_chunk[index] = if let Some(values) = source.as_slice() {
        &values[chunk_start..chunk_end]
      } else {
        if start == chunk_start {
          source
            .read_fields(chunk_start, &mut buffer[..chunk_end - chunk_start])?;
        }
        &buffer[..chunk_end - chunk_start]
      };
    }
    numerators.clear();
    denominators.clear();
    let end = (start + batch_rows).min(size);
    for row in start..end {
      numerators.push(
        (wires[0][row] + beta * x + gamma)
          * (wires[1][row] + beta * k1 * x + gamma)
          * (wires[2][row] + beta * k2 * x + gamma),
      );
      let denominator =
        (wires[0][row] + beta * sigma_chunk[0][row - chunk_start] + gamma)
          * (wires[1][row] + beta * sigma_chunk[1][row - chunk_start] + gamma)
          * (wires[2][row] + beta * sigma_chunk[2][row - chunk_start] + gamma);
      if denominator.is_zero() {
        return Err(FflonkProverError::SingularChallenge(
          "the permutation denominator",
        ));
      }
      denominators.push(denominator);
      x *= domain.group_gen();
    }
    batch_inversion(&mut denominators);
    for (offset, (&numerator, &inverse)) in
      numerators.iter().zip(&denominators).enumerate()
    {
      current *= numerator * inverse;
      if start + offset + 1 < size {
        evaluations.push(current);
      }
    }
  }
  if current != Fr::one() {
    return Err(FflonkProverError::CopyPermutationDoesNotClose);
  }
  Ok(evaluations)
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

fn poly_mul_source(
  source: &impl FflonkPolynomialSourceV1,
  right: &[Fr],
) -> Result<Vec<Fr>, FflonkStorageError> {
  Ok(poly_mul(&load_polynomial(source)?, right))
}

fn copy_factor(
  wire: &[Fr],
  sigma: &impl FflonkPolynomialSourceV1,
  beta: Fr,
  gamma: Fr,
) -> Result<Vec<Fr>, FflonkStorageError> {
  let mut output = wire.to_vec();
  poly_add_scaled_source(&mut output, sigma, beta)?;
  poly_add_assign(&mut output, &[gamma]);
  Ok(output)
}

fn poly_add_scaled_source(
  output: &mut Vec<Fr>,
  source: &impl FflonkPolynomialSourceV1,
  scalar: Fr,
) -> Result<(), FflonkStorageError> {
  if scalar.is_zero() {
    return Ok(());
  }
  output.reserve_exact(source.len().saturating_sub(output.len()));
  output.resize(output.len().max(source.len()), Fr::zero());
  for_each_polynomial_chunk(source, |start, values| {
    for (target, coefficient) in
      output[start..start + values.len()].iter_mut().zip(values)
    {
      *target += *coefficient * scalar;
    }
  })?;
  trim(output);
  Ok(())
}

fn poly_mul(left: &[Fr], right: &[Fr]) -> Vec<Fr> {
  let live_len = |polynomial: &[Fr]| {
    polynomial
      .iter()
      .rposition(|coefficient| !coefficient.is_zero())
      .map_or(0, |degree| degree + 1)
  };
  let left = &left[..live_len(left)];
  let right = &right[..live_len(right)];
  if left.is_empty() || right.is_empty() {
    return Vec::new();
  }
  let length = left.len() + right.len() - 1;
  let domain = Radix2EvaluationDomain::<Fr>::new(length)
    .expect("polynomial domain checked before proving");
  let mut product = Vec::with_capacity(domain.size());
  product.extend_from_slice(left);
  domain.fft_in_place(&mut product);
  let mut right_evaluations = Vec::with_capacity(domain.size());
  right_evaluations.extend_from_slice(right);
  domain.fft_in_place(&mut right_evaluations);
  for (value, right) in product.iter_mut().zip(&right_evaluations) {
    *value *= right;
  }
  drop(right_evaluations);
  domain.ifft_in_place(&mut product);
  product.truncate(length);
  trim(&mut product);
  product
}

fn validate_polynomial_domain(
  domain_size: usize,
) -> Result<(), FflonkProverError> {
  // A/B/C have degree at most n-1 and blinded Z has degree at most n+2.
  // Their four-factor product therefore needs an FFT domain of size 4*n.
  let maximum =
    (1_u64 << Fr::TWO_ADICITY) / FFLONK_POLYNOMIAL_FFT_DOMAIN_MULTIPLIER;
  if domain_size as u64 > maximum {
    return Err(FflonkProverError::Shape(
      "materialized polynomial products require a supported 4*n FFT domain",
    ));
  }
  Ok(())
}

fn poly_add_assign(output: &mut Vec<Fr>, addend: &[Fr]) {
  output.reserve_exact(addend.len().saturating_sub(output.len()));
  output.resize(output.len().max(addend.len()), Fr::zero());
  for (target, value) in output.iter_mut().zip(addend) {
    *target += value;
  }
  trim(output);
}

fn poly_add_scaled_assign(output: &mut Vec<Fr>, addend: &[Fr], scalar: Fr) {
  if scalar.is_zero() {
    return;
  }
  output.reserve_exact(addend.len().saturating_sub(output.len()));
  output.resize(output.len().max(addend.len()), Fr::zero());
  for (target, coefficient) in output.iter_mut().zip(addend) {
    *target += *coefficient * scalar;
  }
  trim(output);
}

fn poly_sub(left: &[Fr], right: &[Fr]) -> Vec<Fr> {
  let mut output = left.to_vec();
  poly_sub_assign(&mut output, right);
  output
}

fn poly_sub_assign(output: &mut Vec<Fr>, subtrahend: &[Fr]) {
  output.reserve_exact(subtrahend.len().saturating_sub(output.len()));
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
  let mut polynomial = polynomial;
  trim(&mut polynomial);
  if polynomial.len() <= n {
    if polynomial.iter().any(|coefficient| !coefficient.is_zero()) {
      return Err(FflonkProverError::PolynomialNotDivisible(relation));
    }
    return Ok(Vec::new());
  }
  // The processed high coefficients already are the quotient. Preserve
  // them while accumulating the remainder in lower positions, then slide
  // the quotient over the remainder without allocating another polynomial.
  for degree in (n..polynomial.len()).rev() {
    let coefficient = polynomial[degree];
    polynomial[degree - n] += beta * coefficient;
  }
  if polynomial[..n].iter().any(|coefficient| !coefficient.is_zero()) {
    return Err(FflonkProverError::PolynomialNotDivisible(relation));
  }
  let quotient_len = polynomial.len() - n;
  polynomial.copy_within(n.., 0);
  polynomial.truncate(quotient_len);
  trim(&mut polynomial);
  Ok(polynomial)
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
  use ark_ff::{FftField, PrimeField};
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

  #[test]
  fn polynomial_fft_matches_schoolbook_with_zero_padding() {
    for left_length in [0u64, 1, 2, 5, 16, 17, 65] {
      for right_length in [0u64, 1, 3, 8, 33] {
        for trailing_zeros in [0, 4] {
          let mut left = (0..left_length)
            .map(|index| Fr::from(7 * index + 3) - Fr::from(19u64))
            .collect::<Vec<_>>();
          let mut right = (0..right_length)
            .map(|index| Fr::from(5 * index + 11) - Fr::from(31u64))
            .collect::<Vec<_>>();
          left.resize(left.len() + trailing_zeros, Fr::zero());
          right.resize(right.len() + trailing_zeros, Fr::zero());
          let mut expected = vec![Fr::zero(); left.len() + right.len()];
          for (i, a) in left.iter().enumerate() {
            for (j, b) in right.iter().enumerate() {
              expected[i + j] += *a * b;
            }
          }
          while expected.last().is_some_and(Zero::is_zero) {
            expected.pop();
          }
          assert_eq!(poly_mul(&left, &right), expected);
        }
      }
    }
  }

  #[test]
  fn polynomial_domain_limit_is_checked_without_allocating() {
    let maximum = 1usize << (Fr::TWO_ADICITY - 2);
    validate_polynomial_domain(maximum).unwrap();
    assert!(matches!(
      validate_polynomial_domain(2 * maximum),
      Err(FflonkProverError::Shape(_))
    ));
  }

  #[test]
  fn monic_division_reuses_the_input_allocation() {
    let quotient = (1..=33u64).map(Fr::from).collect::<Vec<_>>();
    for n in [1, 3, 8, 16] {
      for beta in [Fr::zero(), Fr::one(), Fr::from(11u64)] {
        let mut product = vec![Fr::zero(); quotient.len() + n];
        for (degree, &coefficient) in quotient.iter().enumerate() {
          product[degree + n] += coefficient;
          product[degree] -= beta * coefficient;
        }
        let allocation = product.as_ptr();
        let actual =
          divide_by_xn_minus(product, n, beta, "monic product").unwrap();
        assert_eq!(actual, quotient);
        assert_eq!(actual.as_ptr(), allocation);
      }
    }
  }

  #[test]
  fn boundary_quotient_matches_the_lagrange_identity() {
    let domain = Radix2EvaluationDomain::<Fr>::new(16).unwrap();
    let mut z = (1..=19u64).map(Fr::from).collect::<Vec<_>>();
    let at_one = evaluate_polynomial(&z, Fr::one());
    z[0] += Fr::one() - at_one;
    let numerator = poly_sub_constant(&z, Fr::one());
    let expected = divide_by_xn_minus(
      poly_mul(&numerator, &vec![domain.size_inv(); domain.size()]),
      domain.size(),
      Fr::one(),
      "Lagrange boundary identity",
    )
    .unwrap();
    let mut actual =
      divide_by_xn_minus(numerator, 1, Fr::one(), "boundary quotient").unwrap();
    for coefficient in &mut actual {
      *coefficient *= domain.size_inv();
    }
    assert_eq!(actual, expected);
  }

  #[test]
  fn batched_permutation_satisfies_every_row_and_rejects_zero_denominators() {
    for size in
      [8, 2 * PERMUTATION_BATCH_ROWS, 2 * FFLONK_POLYNOMIAL_CHUNK_FIELDS]
    {
      let domain = Radix2EvaluationDomain::<Fr>::new(size).unwrap();
      let k1 = Fr::GENERATOR;
      let k2 = k1.square();
      let labels = [Fr::one(), k1, k2].map(|scale| {
        domain.elements().map(|point| point * scale).collect::<Vec<_>>()
      });
      let wires = core::array::from_fn(|_| {
        (0..size).map(|row| Fr::from((row % 8) as u64)).collect::<Vec<_>>()
      });
      let sigma: [Vec<Fr>; 3] = core::array::from_fn(|column| {
        (0..size)
          .map(|row| {
            labels[(column + 1) % 3][(row + PERMUTATION_BATCH_ROWS) % size]
          })
          .collect()
      });
      let beta = Fr::from(3u64);
      let gamma = Fr::from(5u64);
      let evaluations = permutation_grand_product(
        &domain,
        &wires,
        sigma.each_ref().map(Vec::as_slice),
        beta,
        gamma,
        k1,
        k2,
      )
      .unwrap();
      assert_eq!(evaluations.len(), size);
      assert_eq!(evaluations[0], Fr::one());
      // Exercise file sources across authentication and inversion boundaries.
      let file = crate::polynomial_storage::PolynomialFile::new(
        std::io::Cursor::new(Vec::new()),
      )
      .unwrap();
      let mut offset = 0;
      let stored: [_; 3] = core::array::from_fn(|column| {
        let stored = file
          .write_polynomial(
            offset,
            sigma[column].as_slice(),
            FFLONK_POLYNOMIAL_CHUNK_FIELDS,
          )
          .unwrap();
        offset = stored.end();
        stored
      });
      assert_eq!(
        permutation_grand_product(
          &domain,
          &wires,
          stored.each_ref().map(|stored| file.source(stored)),
          beta,
          gamma,
          k1,
          k2,
        )
        .unwrap(),
        evaluations
      );
      for row in 0..size {
        let numerator = (0..3).fold(Fr::one(), |product, column| {
          product * (wires[column][row] + beta * labels[column][row] + gamma)
        });
        let denominator = (0..3).fold(Fr::one(), |product, column| {
          product * (wires[column][row] + beta * sigma[column][row] + gamma)
        });
        assert_eq!(
          evaluations[(row + 1) % size] * denominator,
          evaluations[row] * numerator
        );
      }
      let bad_gamma = -wires[0][size - 1] - beta * sigma[0][size - 1];
      assert_eq!(
        permutation_grand_product(
          &domain,
          &wires,
          sigma.each_ref().map(Vec::as_slice),
          beta,
          bad_gamma,
          k1,
          k2
        ),
        Err(FflonkProverError::SingularChallenge(
          "the permutation denominator"
        ))
      );
    }
  }
}
