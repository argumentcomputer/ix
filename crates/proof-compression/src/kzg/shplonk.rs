//! SHPLONK opening of interleaved column packs (Boneh–Drake–Fisch–Gabizon,
//! "Efficient polynomial commitment schemes for multiple points and
//! polynomials", 2020, §4) with only `[1]₂` and `[τ]₂`.
//!
//! A pack of `W` columns `f_0 … f_{W-1}` of common length `n` commits
//!
//! ```text
//! P(X) = Σ_j X^j · f_j(X^W)      (coefficient j + W·k of P is f_j[k])
//! ```
//!
//! A pack opened at the distinct points `A = {a_1, …, a_s}` (every column at
//! every point) has point set `S = {x : x^W ∈ A}` and vanishing polynomial
//! `Z_S(X) = Π_a (X^W − a)`. Its remainder modulo `Z_S` is
//! `r(X) = Σ_j X^j · R_j(X^W)` where `R_j` interpolates `f_j` on `A`, so
//!
//! ```text
//! r(z) = Σ_a L_a(z^W) · Σ_j f_j(a) · z^j
//! ```
//!
//! with `L_a` the Lagrange basis on `A`. Neither `Z_S(z)` nor `r(z)` needs a
//! root of `X^W − a`, so `W` is not limited by the field's two-adicity.
//!
//! One batch covers all packs with a single challenge `γ` (as in fflonk's
//! SHPLONK step): the packs are already one polynomial each, so no
//! per-polynomial combination is needed.
//!
//! ```text
//! γ;  W₁ = [Σ_i γ^i (P_i − r_i)/Z_{S_i}];  z;
//! L(X) = Σ_i γ^i/Z_{S_i}(z) · (P_i(X) − r_i(z)) − W₁(X);   W₂ = [L/(X − z)]
//! F    = Σ_i γ^i/Z_{S_i}(z) · (C_i − r_i(z)·[1]₁) − W₁
//! accept iff e(F + z·W₂, [1]₂) = e(W₂, [τ]₂)
//! ```
//!
//! This is the BDFG identity divided by `Z_T(z)`, which is nonzero whenever
//! every `Z_{S_i}(z)` is. The caller must have absorbed every commitment and
//! every claimed evaluation (or a binding commitment to them, see
//! [`committed_evaluations`]) before [`open`]/[`verify_deferred`] sample `γ`.

use ark_ec::{CurveGroup, VariableBaseMSM};
use ark_ff::{AdditiveGroup, Field, Zero};
use p3_maybe_rayon::prelude::*;

use super::curve::{Bn254, G1AffineOf, G1ProjectiveOf, KzgCurve};
use super::pcs::KzgPcs;
use super::transcript::KzgTranscript;

const DOMAIN: &[u8] = b"ix/kzg/packed-shplonk/v1\0";

/// Columns per scatter pass; bounds the per-pass quotient scratch.
const COLUMN_BATCH: usize = 256;

/// Rows per parallel task when a column's packs are combined.
const COMBINE_BLOCK: usize = 1 << 14;

/// One column's monomial coefficients, without materializing constants.
#[derive(Clone, Copy, Debug)]
pub enum Coefficients<'a, C: KzgCurve = Bn254> {
  Constant(C::Fr),
  Dense(&'a [C::Fr]),
}

impl<C: KzgCurve> Coefficients<'_, C> {
  fn get(&self, index: usize) -> C::Fr {
    match self {
      Self::Constant(value) => {
        if index == 0 {
          *value
        } else {
          C::Fr::ZERO
        }
      },
      Self::Dense(values) => values.get(index).copied().unwrap_or(C::Fr::ZERO),
    }
  }

  /// `f(x)` by blocked Horner's rule.
  pub fn evaluate(&self, x: C::Fr) -> C::Fr {
    match self {
      Self::Constant(value) => *value,
      Self::Dense(values) => super::pcs::eval_poly::<C>(values, x),
    }
  }

  /// Floor quotient by `Π_a (Y − a)`; `height − points.len()` coefficients.
  #[cfg(test)]
  fn divide(&self, height: usize, points: &[C::Fr]) -> Vec<C::Fr> {
    let mut current = match self {
      Self::Constant(_) => {
        return vec![C::Fr::ZERO; height.saturating_sub(points.len())];
      },
      Self::Dense(values) => {
        let mut values = values.to_vec();
        values.resize(height, C::Fr::ZERO);
        values
      },
    };
    for &a in points {
      if current.is_empty() {
        break;
      }
      current = super::pcs::divide_by_linear_host::<C>(current, a);
    }
    current
  }
}

/// Prover view of one pack: `columns.len()` columns of `height` coefficients.
pub struct PackPolynomial<'a, C: KzgCurve = Bn254> {
  pub height: usize,
  pub columns: Vec<Coefficients<'a, C>>,
}

impl<C: KzgCurve> PackPolynomial<'_, C> {
  pub fn width(&self) -> usize {
    self.columns.len()
  }

  /// Interleaved coefficients of `P`.
  pub fn interleave(&self) -> Vec<C::Fr> {
    let width = self.width();
    let mut out = vec![C::Fr::ZERO; width * self.height];
    self.scatter(&mut out, C::Fr::ONE);
    out
  }

  /// `target += scale · P`, coefficient-wise.
  fn scatter(&self, target: &mut [C::Fr], scale: C::Fr) {
    let width = self.width();
    assert!(target.len() >= width * self.height);
    target[..width * self.height].par_chunks_mut(width).enumerate().for_each(
      |(k, row)| {
        for (value, column) in row.iter_mut().zip(&self.columns) {
          let c = column.get(k);
          if !c.is_zero() {
            *value += scale * c;
          }
        }
      },
    );
  }

  /// `target += scale · ⌊P / Z_S⌋`, the interleaved per-column quotients:
  /// the per-pack reference for [`scatter_group_quotient`].
  #[cfg(test)]
  fn scatter_quotient(
    &self,
    target: &mut [C::Fr],
    scale: C::Fr,
    points: &[C::Fr],
  ) {
    let width = self.width();
    let rows = self.height.saturating_sub(points.len());
    for (batch, columns) in self.columns.chunks(COLUMN_BATCH).enumerate() {
      let quotients: Vec<_> = columns
        .par_iter()
        .map(|column| column.divide(self.height, points))
        .collect();
      let offset = batch * COLUMN_BATCH;
      target[..width * rows].par_chunks_mut(width).enumerate().for_each(
        |(k, row)| {
          for (j, quotient) in quotients.iter().enumerate() {
            row[offset + j] += scale * quotient[k];
          }
        },
      );
    }
  }

  /// Every column at `point`.
  pub fn evaluate(&self, point: C::Fr) -> Vec<C::Fr> {
    self.columns.par_iter().map(|column| column.evaluate(point)).collect()
  }
}

/// `target += Σ_i scale_i · ⌊P_i / Z_S⌋` for packs of one width sharing the
/// point set `points`, interleaved like [`PackPolynomial::scatter_quotient`].
fn scatter_group_quotient<C: KzgCurve>(
  target: &mut [C::Fr],
  width: usize,
  points: &[C::Fr],
  members: &[(&PackPolynomial<'_, C>, C::Fr)],
) {
  let height = members.iter().map(|(pack, _)| pack.height).max().unwrap_or(0);
  let rows = height.saturating_sub(points.len());
  if rows == 0 {
    return;
  }
  for start in (0..width).step_by(COLUMN_BATCH) {
    let end = (start + COLUMN_BATCH).min(width);
    let quotients: Vec<Vec<C::Fr>> = (start..end)
      .into_par_iter()
      .map(|j| {
        // Constant columns have a zero quotient.
        if !members
          .iter()
          .any(|(pack, _)| matches!(pack.columns[j], Coefficients::Dense(_)))
        {
          return vec![];
        }
        // Row blocks in parallel: a group of few, tall columns otherwise
        // combines its packs on one thread per column.
        let mut combined = vec![C::Fr::ZERO; height];
        combined.par_chunks_mut(COMBINE_BLOCK).enumerate().for_each(
          |(block, chunk)| {
            let offset = block * COMBINE_BLOCK;
            for (pack, scale) in members {
              if let Coefficients::Dense(values) = pack.columns[j] {
                let n = values.len().min(pack.height);
                if offset < n {
                  let end = n.min(offset + chunk.len());
                  for (c, v) in chunk.iter_mut().zip(&values[offset..end]) {
                    *c += *scale * v;
                  }
                }
              }
            }
          },
        );
        let mut current = combined;
        for &a in points {
          if current.is_empty() {
            break;
          }
          current = super::pcs::divide_by_linear_host::<C>(current, a);
        }
        current
      })
      .collect();
    target[..width * rows].par_chunks_mut(width).enumerate().for_each(
      |(k, row)| {
        for (j, quotient) in quotients.iter().enumerate() {
          if let Some(q) = quotient.get(k) {
            row[start + j] += *q;
          }
        }
      },
    );
  }
}

/// Verifier view of one pack's claim: `values[p][j] = f_j(points[p])`.
#[derive(Clone, Debug)]
pub struct PackClaim<C: KzgCurve = Bn254> {
  pub width: usize,
  pub points: Vec<C::Fr>,
  pub values: Vec<Vec<C::Fr>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Proof<C: KzgCurve = Bn254> {
  pub w1: G1AffineOf<C>,
  pub w2: G1AffineOf<C>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
  Shape,
  /// Repeated opening points make the remainder ill-defined.
  RepeatedPoint,
  /// `z` landed on a pack's point set.
  DegenerateChallenge,
  InvalidPoint,
  PairingCheckFailed,
}

impl<C: KzgCurve> PackClaim<C> {
  fn check(&self) -> Result<(), Error> {
    if self.width == 0
      || self.points.is_empty()
      || self.values.len() != self.points.len()
      || self.values.iter().any(|row| row.len() != self.width)
    {
      return Err(Error::Shape);
    }
    for (i, a) in self.points.iter().enumerate() {
      if self.points[..i].contains(a) {
        return Err(Error::RepeatedPoint);
      }
    }
    Ok(())
  }

  /// `Z_S(z) = Π_a (z^W − a)`.
  pub fn vanishing(&self, z: C::Fr) -> C::Fr {
    vanishing::<C>(z, self.width, &self.points)
  }

  /// `r(z)` for the remainder `r = P mod Z_S` fixed by the claimed values.
  pub fn remainder(&self, z: C::Fr) -> C::Fr {
    remainder::<C>(z, self.width, &self.points, &self.values)
  }
}

pub fn vanishing<C: KzgCurve>(
  z: C::Fr,
  width: usize,
  points: &[C::Fr],
) -> C::Fr {
  let y = z.pow([width as u64]);
  points.iter().map(|&a| y - a).product()
}

pub fn remainder<C: KzgCurve>(
  z: C::Fr,
  width: usize,
  points: &[C::Fr],
  values: &[Vec<C::Fr>],
) -> C::Fr {
  let y = z.pow([width as u64]);
  let mut total = C::Fr::ZERO;
  for (i, (&a, row)) in points.iter().zip(values).enumerate() {
    debug_assert_eq!(row.len(), width);
    let mut numerator = C::Fr::ONE;
    let mut denominator = C::Fr::ONE;
    for (k, &b) in points.iter().enumerate() {
      if k != i {
        numerator *= y - b;
        denominator *= a - b;
      }
    }
    let combined = row.iter().rev().fold(C::Fr::ZERO, |acc, v| acc * z + v);
    total +=
      numerator * denominator.inverse().expect("distinct points") * combined;
  }
  total
}

fn sample<C: KzgCurve>(transcript: &mut KzgTranscript<C>) -> C::Fr {
  multi_stark::traits::Transcript::sample_challenge(transcript).0
}

/// Sample `γ` and `z` around `W₁`, mirroring the prover. Returns `(γ, z)`.
fn challenges<C: KzgCurve>(
  transcript: &mut KzgTranscript<C>,
  proof: &Proof<C>,
) -> (C::Fr, C::Fr) {
  transcript.observe_bytes(DOMAIN);
  let gamma = sample(transcript);
  transcript.observe_canonical(&proof.w1);
  let z = sample(transcript);
  transcript.observe_canonical(&proof.w2);
  (gamma, z)
}

/// Per-pack combination weights `γ^i / Z_{S_i}(z)` and `Σ_i weight_i·r_i(z)`.
fn weights<C: KzgCurve>(
  claims: &[&PackClaim<C>],
  gamma: C::Fr,
  z: C::Fr,
) -> Result<(Vec<C::Fr>, C::Fr), Error> {
  let mut weights = Vec::with_capacity(claims.len());
  let mut constant = C::Fr::ZERO;
  let mut power = C::Fr::ONE;
  for claim in claims {
    let inverse =
      claim.vanishing(z).inverse().ok_or(Error::DegenerateChallenge)?;
    let weight = power * inverse;
    constant += weight * claim.remainder(z);
    weights.push(weight);
    power *= gamma;
  }
  Ok((weights, constant))
}

/// Prove every pack's claim. The claims must be exactly the packs'
/// evaluations; the caller has already absorbed commitments and claims.
pub fn open<C: KzgCurve>(
  pcs: &KzgPcs<C>,
  packs: &[(&PackPolynomial<'_, C>, &PackClaim<C>)],
  transcript: &mut KzgTranscript<C>,
) -> Proof<C> {
  transcript.observe_bytes(DOMAIN);
  let gamma = sample(transcript);
  let started = std::time::Instant::now();

  let w1_len = packs
    .iter()
    .map(|(p, c)| p.width() * p.height.saturating_sub(c.points.len()))
    .max()
    .unwrap_or(0);
  let mut w1 = vec![C::Fr::ZERO; w1_len];
  // Division by `Z_S` is linear and the interleaving depends only on the
  // width, so the packs of one width and point set are combined first and
  // divided once: `Σ_i γ^i ⌊P_i/Z_S⌋ = ⌊(Σ_i γ^i P_i)/Z_S⌋`.
  let mut groups: Vec<(usize, &[C::Fr], Vec<(&PackPolynomial<'_, C>, C::Fr)>)> =
    vec![];
  let mut power = C::Fr::ONE;
  for (pack, claim) in packs {
    debug_assert_eq!(pack.width(), claim.width);
    match groups
      .iter_mut()
      .find(|(w, p, _)| *w == pack.width() && *p == claim.points.as_slice())
    {
      Some((_, _, members)) => members.push((pack, power)),
      None => groups.push((pack.width(), &claim.points, vec![(pack, power)])),
    }
    power *= gamma;
  }
  for (width, points, members) in &groups {
    scatter_group_quotient(&mut w1, *width, points, members);
  }
  let quotients_seconds = started.elapsed().as_secs_f64();
  let w1_point = pcs.msm(&w1).into_affine();
  let w1_seconds = started.elapsed().as_secs_f64();
  transcript.observe_canonical(&w1_point);
  let z = sample(transcript);

  let claims: Vec<_> = packs.iter().map(|(_, c)| *c).collect();
  let (weights, constant) =
    weights(&claims, gamma, z).expect("z avoids every pack point set");
  let l_len = packs
    .iter()
    .map(|(p, _)| p.width() * p.height)
    .max()
    .unwrap_or(0)
    .max(w1.len())
    .max(1);
  let mut l = vec![C::Fr::ZERO; l_len];
  for ((pack, _), &weight) in packs.iter().zip(&weights) {
    pack.scatter(&mut l, weight);
  }
  l.par_iter_mut().zip(&w1).for_each(|(value, w)| *value -= w);
  drop(w1);
  l[0] -= constant;
  let combination_seconds = started.elapsed().as_secs_f64();
  let w2_point = pcs.witness(l, z).into_affine();
  tracing::info!(
    packs = packs.len(),
    quotients_seconds,
    w1_seconds,
    combination_seconds,
    seconds = started.elapsed().as_secs_f64(),
    "SHPLONK witnesses"
  );
  transcript.observe_canonical(&w2_point);
  Proof { w1: w1_point, w2: w2_point }
}

/// Reduce the batch to `[A, B]` with acceptance iff
/// `e(A, [1]₂)·e(B, [τ]₂) = 1`.
pub fn verify_deferred<C: KzgCurve>(
  generator: G1AffineOf<C>,
  packs: &[(G1AffineOf<C>, &PackClaim<C>)],
  proof: &Proof<C>,
  transcript: &mut KzgTranscript<C>,
) -> Result<[G1AffineOf<C>; 2], Error> {
  for (_, claim) in packs {
    claim.check()?;
  }
  if packs
    .iter()
    .map(|(c, _)| c)
    .chain([&proof.w1, &proof.w2])
    .any(|p| !p.is_on_curve() || !p.is_in_correct_subgroup_assuming_on_curve())
  {
    return Err(Error::InvalidPoint);
  }
  let (gamma, z) = challenges(transcript, proof);
  let claims: Vec<_> = packs.iter().map(|(_, c)| *c).collect();
  let (weights, constant) = weights(&claims, gamma, z)?;
  let mut bases: Vec<_> = packs.iter().map(|(c, _)| *c).collect();
  let mut scalars = weights;
  bases.extend([generator, proof.w1, proof.w2]);
  scalars.extend([-constant, -C::Fr::ONE, z]);
  let lhs = G1ProjectiveOf::<C>::msm(&bases, &scalars).expect("equal lengths");
  Ok([lhs.into_affine(), (-G1ProjectiveOf::<C>::from(proof.w2)).into_affine()])
}

pub fn verify<C: KzgCurve>(
  params: &super::VerifierParams<C>,
  packs: &[(G1AffineOf<C>, &PackClaim<C>)],
  proof: &Proof<C>,
  transcript: &mut KzgTranscript<C>,
) -> Result<(), Error> {
  let pair = verify_deferred::<C>(params.g1[0], packs, proof, transcript)?;
  if pairing_holds::<C>(params, pair) {
    Ok(())
  } else {
    Err(Error::PairingCheckFailed)
  }
}

/// `e(A, [1]₂) · e(B, [τ]₂) = 1` for a deferred pair `[A, B]`.
pub fn pairing_holds<C: KzgCurve>(
  params: &super::VerifierParams<C>,
  [a, b]: [G1AffineOf<C>; 2],
) -> bool {
  use ark_ec::pairing::Pairing;
  C::PairingCurve::multi_pairing([a, b], [params.g2, params.tau_g2]).is_zero()
}

/// Committed-evaluation binding: the claimed values of all packs, in pack,
/// point, column order, as the coefficients of one polynomial `E`.
///
/// Absorbing `[E]` in place of the values is NOT sufficient for soundness
/// when the values themselves stay out of the transcript: every later check
/// is linear in the values, so a prover can choose them after the
/// challenges (see the `committed_evaluations_without_hashing_are_forgeable`
/// test). This is kept for measurement only.
pub fn committed_evaluations<C: KzgCurve>(
  claims: &[&PackClaim<C>],
) -> Vec<C::Fr> {
  claims
    .iter()
    .flat_map(|claim| claim.values.iter().flatten().copied())
    .collect()
}

#[cfg(test)]
#[path = "shplonk/tests.rs"]
mod tests;
