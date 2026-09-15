use crate::arithmetization::lower_checked_plonk_witness;
use crate::polynomial_storage::{
  evaluate_polynomial_source, for_each_polynomial_chunk,
};
use crate::prover_workspace::{ProverPolynomial, ProverWorkspace};
use crate::{
  FFLONK_COMMITMENTS, FFLONK_EVALUATIONS, FFLONK_POLYNOMIAL_CHUNK_FIELDS,
  FFLONK_POLYNOMIAL_FFT_DOMAIN_MULTIPLIER, FflonkCheckedWitnessV1,
  FflonkEvaluationRootsV1, FflonkFixedPolynomialV1, FflonkPolynomialSourceV1,
  FflonkProofV1, FflonkProvingKeyV1, FflonkStorageError, FflonkTranscriptError,
  KzgCommitmentSourceV1, KzgError, PlonkArithmetizationError,
  PlonkArithmetizationV1, PlonkWitnessV1, derive_fflonk_challenges,
  evaluate_polynomial, lower_plonk_witness,
};
use ark_bls12_381::{Fr, G1Affine};
use ark_ff::{FftField, Field, One, Zero, batch_inversion};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ix_terminal_circuit::{CanonicalR1csV1, Witness};
use std::fmt;
use std::io::{Read, Seek, Write};

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
  prove_in_workspace(
    srs,
    preprocessed,
    ProverWitness::Borrowed { r1cs, witness },
    blinding,
    &ProverWorkspace::<std::fs::File>::Memory,
  )
}

/// Proves with authenticated file storage for wire values and temporary
/// polynomials. The storage must be empty, readable, writable, and seekable.
///
/// With `R = std::fs::File`, polynomial payloads live on disk. The caller owns
/// file protection and cleanup: the scratch data includes private witness
/// values, and failures can leave a partial file. Live regions are recycled
/// when their polynomials are dropped. The file is never truncated.
///
/// Arithmetic uses one resident FFT array (at most 4*n fields), bounded roots
/// and I/O buffers, and at most n fields for quotient division. Witness
/// lowering still materializes three columns. The relation, original witness,
/// proving key, SRS, allocator, and OS cache have additional memory costs;
/// this function does not enforce an aggregate RAM budget.
pub fn prove_fflonk_with_file_workspace<R: Read + Write + Seek>(
  srs: &(impl KzgCommitmentSourceV1 + ?Sized),
  preprocessed: &(impl FflonkProvingKeyV1 + ?Sized),
  r1cs: &CanonicalR1csV1,
  witness: &Witness,
  blinding: FflonkBlindingV1,
  storage: R,
) -> Result<FflonkProverOutputV1, FflonkProverError> {
  let workspace = ProverWorkspace::file(storage)?;
  prove_in_workspace(
    srs,
    preprocessed,
    ProverWitness::Borrowed { r1cs, witness },
    blinding,
    &workspace,
  )
}

/// Prove from an immutable assignment already checked against its canonical
/// relation. The relation can be released before preprocessing. This function
/// consumes the checked assignment and releases it after witness lowering,
/// before polynomial work. An error also consumes the assignment.
pub fn prove_fflonk_checked(
  srs: &(impl KzgCommitmentSourceV1 + ?Sized),
  preprocessed: &(impl FflonkProvingKeyV1 + ?Sized),
  witness: FflonkCheckedWitnessV1,
  blinding: FflonkBlindingV1,
) -> Result<FflonkProverOutputV1, FflonkProverError> {
  prove_in_workspace(
    srs,
    preprocessed,
    ProverWitness::Checked(witness),
    blinding,
    &ProverWorkspace::<std::fs::File>::Memory,
  )
}

/// Prove from a consumed checked assignment with authenticated temporary
/// polynomial storage. The relation can be released before preprocessing;
/// the original assignment is released after lowering and before FFTs.
/// An error also consumes the assignment.
///
/// Storage ownership, cleanup, and polynomial memory bounds are the same as
/// [`prove_fflonk_with_file_workspace`]. The lowering step still materializes
/// three columns and auxiliary values. No aggregate RAM budget is enforced.
pub fn prove_fflonk_checked_with_file_workspace<R: Read + Write + Seek>(
  srs: &(impl KzgCommitmentSourceV1 + ?Sized),
  preprocessed: &(impl FflonkProvingKeyV1 + ?Sized),
  witness: FflonkCheckedWitnessV1,
  blinding: FflonkBlindingV1,
  storage: R,
) -> Result<FflonkProverOutputV1, FflonkProverError> {
  let workspace = ProverWorkspace::file(storage)?;
  prove_in_workspace(
    srs,
    preprocessed,
    ProverWitness::Checked(witness),
    blinding,
    &workspace,
  )
}

enum ProverWitness<'a> {
  Borrowed { r1cs: &'a CanonicalR1csV1, witness: &'a Witness },
  Checked(FflonkCheckedWitnessV1),
}

impl ProverWitness<'_> {
  fn assignment(&self) -> &[Fr] {
    match self {
      Self::Borrowed { witness, .. } => witness.assignment(),
      Self::Checked(witness) => witness.assignment(),
    }
  }

  fn lower(
    &self,
    arithmetization: &PlonkArithmetizationV1,
  ) -> Result<PlonkWitnessV1, PlonkArithmetizationError> {
    match self {
      Self::Borrowed { r1cs, witness } => {
        lower_plonk_witness(arithmetization, r1cs, witness)
      },
      Self::Checked(witness) => {
        lower_checked_plonk_witness(arithmetization, witness)
      },
    }
  }
}

fn prove_in_workspace<R: Read + Write + Seek>(
  srs: &(impl KzgCommitmentSourceV1 + ?Sized),
  preprocessed: &(impl FflonkProvingKeyV1 + ?Sized),
  witness: ProverWitness<'_>,
  blinding: FflonkBlindingV1,
  ws: &ProverWorkspace<R>,
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
  let plonk_witness = witness.lower(preprocessed.arithmetization())?;
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
  drop(witness);

  let mut wire_evaluations = plonk_witness.into_columns();
  let blind_row0 = domain_size - 2;
  let blind_row1 = domain_size - 1;
  for (column, values) in wire_evaluations.iter_mut().enumerate() {
    values[blind_row0] = blinding.wire_evaluations[2 * column];
    values[blind_row1] = blinding.wire_evaluations[2 * column + 1];
  }
  let [wa, wb, wc] = wire_evaluations;
  let wire_evaluations = [
    ws.store_vec(wa, false)?,
    ws.store_vec(wb, false)?,
    ws.store_vec(wc, false)?,
  ];
  let a = ws.ifft(&wire_evaluations[0], &domain)?;
  let b = ws.ifft(&wire_evaluations[1], &domain)?;
  let c = ws.ifft(&wire_evaluations[2], &domain)?;
  let mut public_input_evaluations = vec![Fr::zero(); domain_size];
  for (row, input) in public_inputs.iter().enumerate() {
    public_input_evaluations[row] = -*input;
  }
  let public_input_polynomial =
    ws.ifft_vec(public_input_evaluations, &domain, None)?;

  let mut t0_numerator =
    ws.mul(&preprocessed.coefficient_source(FflonkFixedPolynomialV1::Ql), &a)?;
  ws.add_assign(
    &mut t0_numerator,
    &ws
      .mul(&preprocessed.coefficient_source(FflonkFixedPolynomialV1::Qr), &b)?,
    Fr::one(),
  )?;
  ws.add_assign(
    &mut t0_numerator,
    &ws.mul(
      &preprocessed.coefficient_source(FflonkFixedPolynomialV1::Qm),
      &ws.mul(&a, &b)?,
    )?,
    Fr::one(),
  )?;
  ws.add_assign(
    &mut t0_numerator,
    &ws
      .mul(&preprocessed.coefficient_source(FflonkFixedPolynomialV1::Qo), &c)?,
    Fr::one(),
  )?;
  ws.add_assign(
    &mut t0_numerator,
    &preprocessed.coefficient_source(FflonkFixedPolynomialV1::Qc),
    Fr::one(),
  )?;
  ws.add_assign(&mut t0_numerator, &public_input_polynomial, Fr::one())?;
  let t0 = ws.divide(t0_numerator, domain_size, Fr::one(), "Z_H(X)")?;
  let c1 = ws.pack([&a, &b, &c, &t0])?;
  drop(t0);
  drop(public_input_polynomial);

  let mut proof = FflonkProofV1 {
    commitments: [G1Affine::identity(); FFLONK_COMMITMENTS],
    evaluations: [Fr::zero(); FFLONK_EVALUATIONS],
  };
  proof.commitments[0] = ws.commit(srs, &c1)?;
  let (round1, _) =
    derive_fflonk_challenges(&verification_key, &proof, &public_inputs)?;

  let z_evaluations = permutation_grand_product_in_workspace(
    ws,
    &domain,
    [&wire_evaluations[0], &wire_evaluations[1], &wire_evaluations[2]],
    preprocessed.sigma_sources(),
    round1.beta,
    round1.gamma,
    verification_key.k1(),
    verification_key.k2(),
  )?;
  drop(wire_evaluations);
  let z = ws.ifft_owned(z_evaluations, &domain, blinding.z_coefficients)?;

  // L_1(X) = Z_H(X)/(n*(X-1)); cancel Z_H before multiplication.
  let t1 = ws.scale(
    ws.divide(
      ws.sum(&[(&z, Fr::one()), (&[Fr::one()].as_slice(), -Fr::one())])?,
      1,
      Fr::one(),
      "X - 1 in T1",
    )?,
    domain.size_inv(),
  )?;

  let identity_a = ws.sum(&[
    (&a, Fr::one()),
    (&[round1.gamma, round1.beta].as_slice(), Fr::one()),
  ])?;
  let identity_b = ws.sum(&[
    (&b, Fr::one()),
    (
      &[round1.gamma, round1.beta * verification_key.k1()].as_slice(),
      Fr::one(),
    ),
  ])?;
  let identity_c = ws.sum(&[
    (&c, Fr::one()),
    (
      &[round1.gamma, round1.beta * verification_key.k2()].as_slice(),
      Fr::one(),
    ),
  ])?;
  let identity_product =
    ws.mul(&ws.mul(&ws.mul(&identity_a, &identity_b)?, &identity_c)?, &z)?;
  drop(identity_a);
  drop(identity_b);
  drop(identity_c);
  let copy_a = ws.sum(&[
    (&a, Fr::one()),
    (
      &preprocessed.coefficient_source(FflonkFixedPolynomialV1::Sigma1),
      round1.beta,
    ),
    (&[round1.gamma].as_slice(), Fr::one()),
  ])?;
  let copy_b = ws.sum(&[
    (&b, Fr::one()),
    (
      &preprocessed.coefficient_source(FflonkFixedPolynomialV1::Sigma2),
      round1.beta,
    ),
    (&[round1.gamma].as_slice(), Fr::one()),
  ])?;
  let copy_c = ws.sum(&[
    (&c, Fr::one()),
    (
      &preprocessed.coefficient_source(FflonkFixedPolynomialV1::Sigma3),
      round1.beta,
    ),
    (&[round1.gamma].as_slice(), Fr::one()),
  ])?;
  let z_shifted = ws.shift(&z, verification_key.omega())?;
  let copy_product =
    ws.mul(&ws.mul(&ws.mul(&copy_a, &copy_b)?, &copy_c)?, &z_shifted)?;
  drop(copy_a);
  drop(copy_b);
  drop(copy_c);
  drop(z_shifted);
  let t2 = ws.divide(
    ws.sum(&[(&identity_product, Fr::one()), (&copy_product, -Fr::one())])?,
    domain_size,
    Fr::one(),
    "Z_H(X) in T2",
  )?;
  drop(identity_product);
  drop(copy_product);
  let c2 = ws.pack([&z, &t1, &t2])?;
  proof.commitments[1] = ws.commit(srs, &c2)?;

  let (round3, roots) =
    derive_fflonk_challenges(&verification_key, &proof, &public_inputs)?;
  for (index, id) in FflonkFixedPolynomialV1::ALL.into_iter().enumerate() {
    proof.evaluations[index] = evaluate_polynomial_source(
      &preprocessed.coefficient_source(id),
      &[round3.xi],
    )?[0];
  }
  proof.evaluations[8..].copy_from_slice(&[
    evaluate_polynomial_source(&a, &[round3.xi])?[0],
    evaluate_polynomial_source(&b, &[round3.xi])?[0],
    evaluate_polynomial_source(&c, &[round3.xi])?[0],
    evaluate_polynomial_source(&z, &[round3.xi])?[0],
    evaluate_polynomial_source(&z, &[round3.xi_omega])?[0],
    evaluate_polynomial_source(&t1, &[round3.xi_omega])?[0],
    evaluate_polynomial_source(&t2, &[round3.xi_omega])?[0],
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
  let r1 = interpolate(
    &roots.h1_omega4,
    &evaluate_polynomial_source(&c1, &roots.h1_omega4)?,
  )?;
  let r2_roots = combined_r2_roots(&roots);
  let r2 =
    interpolate(&r2_roots, &evaluate_polynomial_source(&c2, &r2_roots)?)?;
  let mut f = ws.divide(
    ws.sum(&[(&c0_source, Fr::one()), (&r0.as_slice(), -Fr::one())])?,
    8,
    round4.xi,
    "X^8 - xi",
  )?;
  let f1 = ws.divide(
    ws.sum(&[(&c1, Fr::one()), (&r1.as_slice(), -Fr::one())])?,
    4,
    round4.xi,
    "X^4 - xi",
  )?;
  ws.add_assign(&mut f, &f1, round4.alpha)?;
  drop(f1);
  let f2 = ws.divide(
    ws.divide(
      ws.sum(&[(&c2, Fr::one()), (&r2.as_slice(), -Fr::one())])?,
      3,
      round4.xi,
      "X^3 - xi",
    )?,
    3,
    round4.xi_omega,
    "X^3 - xi*omega",
  )?;
  ws.add_assign(&mut f, &f2, round4.alpha.square())?;
  drop(f2);
  proof.commitments[2] = ws.commit(srs, &f)?;

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
  let constant = evaluate_polynomial(&r0, round5.y) * pre0
    + evaluate_polynomial(&r1, round5.y) * pre1
    + evaluate_polynomial(&r2, round5.y) * pre2;
  let zts2_at_y = evaluate_polynomial(&poly_mul(&z1, &z2), round5.y);
  let zts2_inverse = zts2_at_y
    .inverse()
    .ok_or(FflonkProverError::SingularChallenge("Z_1(y) * Z_2(y)"))?;
  let l = ws.opening_combination(
    [(c1, pre1), (c2, pre2), (f, -evaluate_polynomial(&zt, round5.y))],
    &c0_source,
    pre0,
    constant,
    zts2_inverse,
  )?;
  let w2 = ws.divide(l, 1, round5.y, "X - y")?;
  proof.commitments[3] = ws.commit(srs, &w2)?;

  Ok(FflonkProverOutputV1 { proof, public_inputs })
}

const PERMUTATION_BATCH_ROWS: usize = 16_384;

#[allow(clippy::too_many_arguments)]
fn permutation_grand_product_in_workspace<R: Read + Write + Seek>(
  ws: &ProverWorkspace<R>,
  domain: &Radix2EvaluationDomain<Fr>,
  wires: [&dyn FflonkPolynomialSourceV1; 3],
  sigma: [impl FflonkPolynomialSourceV1; 3],
  beta: Fr,
  gamma: Fr,
  k1: Fr,
  k2: Fr,
) -> Result<ProverPolynomial<R>, FflonkProverError> {
  let size = domain.size();
  if wires.iter().any(|column| column.len() != size)
    || sigma.iter().any(|column| column.len() != size)
  {
    return Err(FflonkProverError::Shape("permutation column length"));
  }
  let sources = [wires[0], wires[1], wires[2], &sigma[0], &sigma[1], &sigma[2]];
  let chunk_rows = FFLONK_POLYNOMIAL_CHUNK_FIELDS.min(size);
  let mut buffers: [Vec<Fr>; 6] = core::array::from_fn(|index| {
    if sources[index].as_slice().is_some() {
      Vec::new()
    } else {
      vec![Fr::zero(); chunk_rows]
    }
  });
  let mut numerators = Vec::with_capacity(PERMUTATION_BATCH_ROWS.min(size));
  let mut denominators = Vec::with_capacity(PERMUTATION_BATCH_ROWS.min(size));
  let mut current = Fr::one();
  let mut x = Fr::one();
  let evaluations = ws.generate(size, false, |start, output| {
    let mut columns = [&[][..]; 6];
    for (index, (source, buffer)) in
      sources.iter().zip(&mut buffers).enumerate()
    {
      columns[index] = if let Some(values) = source.as_slice() {
        &values[start..start + output.len()]
      } else {
        source.read_fields(start, &mut buffer[..output.len()])?;
        &buffer[..output.len()]
      };
    }
    for first in (0..output.len()).step_by(PERMUTATION_BATCH_ROWS) {
      let end = (first + PERMUTATION_BATCH_ROWS).min(output.len());
      numerators.clear();
      denominators.clear();
      for (row, &a) in columns[0].iter().enumerate().take(end).skip(first) {
        numerators.push(
          (a + beta * x + gamma)
            * (columns[1][row] + beta * k1 * x + gamma)
            * (columns[2][row] + beta * k2 * x + gamma),
        );
        let denominator = (a + beta * columns[3][row] + gamma)
          * (columns[1][row] + beta * columns[4][row] + gamma)
          * (columns[2][row] + beta * columns[5][row] + gamma);
        if denominator.is_zero() {
          return Err(FflonkProverError::SingularChallenge(
            "the permutation denominator",
          ));
        }
        denominators.push(denominator);
        x *= domain.group_gen();
      }
      batch_inversion(&mut denominators);
      for ((value, numerator), inverse) in
        output[first..end].iter_mut().zip(&numerators).zip(&denominators)
      {
        *value = current;
        current *= *numerator * inverse;
      }
    }
    Ok(())
  })?;
  if current != Fr::one() {
    return Err(FflonkProverError::CopyPermutationDoesNotClose);
  }
  Ok(evaluations)
}

#[cfg(test)]
fn permutation_grand_product(
  domain: &Radix2EvaluationDomain<Fr>,
  wires: &[Vec<Fr>; 3],
  sigma: [impl FflonkPolynomialSourceV1; 3],
  beta: Fr,
  gamma: Fr,
  k1: Fr,
  k2: Fr,
) -> Result<Vec<Fr>, FflonkProverError> {
  let result = permutation_grand_product_in_workspace(
    &ProverWorkspace::<std::fs::File>::Memory,
    domain,
    [&wires[0].as_slice(), &wires[1].as_slice(), &wires[2].as_slice()],
    sigma,
    beta,
    gamma,
    k1,
    k2,
  )?;
  Ok(crate::polynomial_storage::load_polynomial(&result)?.into_owned())
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

pub(crate) fn blind_z(
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

pub(crate) fn poly_add_scaled_source(
  output: &mut Vec<Fr>,
  source: &(impl FflonkPolynomialSourceV1 + ?Sized),
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

pub(crate) fn poly_mul(left: &[Fr], right: &[Fr]) -> Vec<Fr> {
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
      "polynomial products require a supported 4*n FFT domain",
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

#[cfg(test)]
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

pub(crate) fn divide_by_xn_minus(
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

pub(crate) fn trim(polynomial: &mut Vec<Fr>) {
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
  fn checked_proof_releases_relation_before_preprocessing_and_rejects_mismatch()
  {
    let (r1cs, witness) = fixture();
    let checked = FflonkCheckedWitnessV1::new(&r1cs, witness).unwrap();
    let arithmetization = crate::arithmetize_r1cs_owned(r1cs).unwrap();
    let required =
      required_fflonk_srs_degree(arithmetization.census().domain_size).unwrap();
    let srs = test_srs(usize::try_from(required).unwrap(), Fr::from(29u64));
    let key = preprocess_fflonk(&srs, arithmetization).unwrap();
    let (other, other_witness) = R1csBuilder::new().finish().unwrap();
    let wrong = FflonkCheckedWitnessV1::new(&other, other_witness).unwrap();
    let blinding = FflonkBlindingV1::default();
    assert_eq!(
      prove_fflonk_checked(&srs, &key, wrong.clone(), blinding),
      Err(FflonkProverError::Arithmetization(
        PlonkArithmetizationError::R1csDigestMismatch
      ))
    );
    assert_eq!(
      prove_fflonk_checked_with_file_workspace(
        &srs,
        &key,
        wrong,
        blinding,
        std::io::Cursor::new(Vec::new())
      ),
      Err(FflonkProverError::Arithmetization(
        PlonkArithmetizationError::R1csDigestMismatch
      ))
    );
    let output = prove_fflonk_checked(&srs, &key, checked, blinding).unwrap();
    assert_eq!(
      verify_fflonk(
        &key.verification_key(),
        &output.proof,
        &output.public_inputs
      ),
      Ok(true)
    );
  }

  #[test]
  fn file_workspace_propagates_corruption_and_read_failures_through_proof_rounds()
   {
    use std::cell::Cell;
    use std::io::{self, Cursor, SeekFrom};
    struct FaultyStorage<'a> {
      bytes: Cursor<Vec<u8>>,
      reads: &'a Cell<usize>,
      fail_at: Option<usize>,
      corrupt: bool,
    }
    impl Read for FaultyStorage<'_> {
      fn read(&mut self, output: &mut [u8]) -> io::Result<usize> {
        let index = self.reads.get();
        self.reads.set(index + 1);
        let fail = self.fail_at == Some(index);
        if fail && !self.corrupt {
          return Err(io::ErrorKind::BrokenPipe.into());
        }
        let count = self.bytes.read(output)?;
        if fail && count != 0 {
          output[0] ^= 1;
        }
        Ok(count)
      }
    }
    impl Write for FaultyStorage<'_> {
      fn write(&mut self, input: &[u8]) -> io::Result<usize> {
        self.bytes.write(input)
      }
      fn flush(&mut self) -> io::Result<()> {
        Ok(())
      }
    }
    impl Seek for FaultyStorage<'_> {
      fn seek(&mut self, position: SeekFrom) -> io::Result<u64> {
        self.bytes.seek(position)
      }
    }
    let (r1cs, witness) = fixture();
    let arithmetization = arithmetize_r1cs(&r1cs).unwrap();
    let degree = usize::try_from(
      required_fflonk_srs_degree(arithmetization.census().domain_size).unwrap(),
    )
    .unwrap();
    let srs = test_srs(degree, Fr::from(29u64));
    let key = preprocess_fflonk(&srs, arithmetization).unwrap();
    let reads = Cell::new(0);
    let output = prove_fflonk_with_file_workspace(
      &srs,
      &key,
      &r1cs,
      &witness,
      FflonkBlindingV1::default(),
      FaultyStorage {
        bytes: Cursor::new(Vec::new()),
        reads: &reads,
        fail_at: None,
        corrupt: false,
      },
    )
    .unwrap();
    assert_eq!(
      verify_fflonk(
        &key.verification_key(),
        &output.proof,
        &output.public_inputs
      ),
      Ok(true)
    );
    let total_reads = reads.get();
    assert!(total_reads > 2);
    for fail_at in [0, total_reads / 2, total_reads - 1] {
      for corrupt in [false, true] {
        reads.set(0);
        let error = prove_fflonk_with_file_workspace(
          &srs,
          &key,
          &r1cs,
          &witness,
          FflonkBlindingV1::default(),
          FaultyStorage {
            bytes: Cursor::new(Vec::new()),
            reads: &reads,
            fail_at: Some(fail_at),
            corrupt,
          },
        )
        .unwrap_err();
        let storage = match error {
          FflonkProverError::Storage(storage)
          | FflonkProverError::Kzg(KzgError::PolynomialStorage(storage)) => {
            storage
          },
          other => panic!("expected storage error, got {other}"),
        };
        if corrupt {
          assert!(matches!(storage, FflonkStorageError::ChunkChanged { .. }));
        } else {
          assert_eq!(
            storage,
            FflonkStorageError::Io(io::ErrorKind::BrokenPipe)
          );
        }
        assert_eq!(reads.get(), fail_at + 1);
      }
    }
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
      let ws = ProverWorkspace::file(std::io::Cursor::new(Vec::new())).unwrap();
      let disk_wires = wires
        .each_ref()
        .map(|values| ws.store_vec(values.clone(), false).unwrap());
      let disk_result = permutation_grand_product_in_workspace(
        &ws,
        &domain,
        [&disk_wires[0], &disk_wires[1], &disk_wires[2]],
        stored.each_ref().map(|stored| file.source(stored)),
        beta,
        gamma,
        k1,
        k2,
      )
      .unwrap();
      assert_eq!(
        crate::polynomial_storage::load_polynomial(&disk_result)
          .unwrap()
          .as_ref(),
        evaluations
      );
      let bad_sigma =
        [vec![Fr::zero(); size], sigma[1].clone(), sigma[2].clone()];
      assert!(matches!(
        permutation_grand_product_in_workspace(
          &ws,
          &domain,
          [&disk_wires[0], &disk_wires[1], &disk_wires[2]],
          bad_sigma.each_ref().map(Vec::as_slice),
          beta,
          gamma,
          k1,
          k2
        ),
        Err(FflonkProverError::CopyPermutationDoesNotClose)
      ));
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
      assert!(matches!(
        permutation_grand_product_in_workspace(
          &ws,
          &domain,
          [&disk_wires[0], &disk_wires[1], &disk_wires[2]],
          stored.each_ref().map(|stored| file.source(stored)),
          beta,
          bad_gamma,
          k1,
          k2
        ),
        Err(FflonkProverError::SingularChallenge(
          "the permutation denominator"
        ))
      ));
    }
  }
}
