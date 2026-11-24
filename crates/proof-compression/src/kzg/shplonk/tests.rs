use super::*;
use crate::kzg::{Srs, VerifierParams};
use ark_ff::{FftField, PrimeField};
use std::sync::Arc;

/// Deterministic field elements from a BLAKE3 counter stream.
struct StdRng(u64, u64);

fn rng(seed: u64) -> StdRng {
  StdRng(seed, 0)
}

trait Rand {
  fn rand(rng: &mut StdRng) -> Self;
}

impl Rand for Fr {
  fn rand(rng: &mut StdRng) -> Self {
    rng.1 += 1;
    let mut input = rng.0.to_le_bytes().to_vec();
    input.extend(rng.1.to_le_bytes());
    Fr::from_le_bytes_mod_order(blake3::hash(&input).as_bytes())
  }
}

fn random_columns(
  rng: &mut StdRng,
  width: usize,
  height: usize,
) -> Vec<Vec<Fr>> {
  (0..width)
    .map(|j| {
      if j % 5 == 4 {
        // Exercise compact constant columns.
        let mut column = vec![Fr::ZERO; height];
        column[0] = Fr::rand(rng);
        column
      } else {
        (0..height).map(|_| Fr::rand(rng)).collect()
      }
    })
    .collect()
}

fn view(columns: &[Vec<Fr>]) -> Vec<Coefficients<'_>> {
  columns
    .iter()
    .map(|c| {
      if c.iter().skip(1).all(Zero::is_zero) {
        Coefficients::Constant(c[0])
      } else {
        Coefficients::Dense(c)
      }
    })
    .collect()
}

/// Schoolbook `p mod m` for monic `m`.
fn naive_remainder(p: &[Fr], m: &[Fr]) -> Vec<Fr> {
  let mut r = p.to_vec();
  let d = m.len() - 1;
  assert_eq!(m[d], Fr::ONE);
  while r.len() > d {
    let lead = r.pop().unwrap();
    let shift = r.len() - d;
    for (i, &c) in m[..d].iter().enumerate() {
      r[shift + i] -= lead * c;
    }
  }
  r
}

fn mul(a: &[Fr], b: &[Fr]) -> Vec<Fr> {
  let mut out = vec![Fr::ZERO; a.len() + b.len() - 1];
  for (i, x) in a.iter().enumerate() {
    for (j, y) in b.iter().enumerate() {
      out[i + j] += *x * y;
    }
  }
  out
}

fn horner(p: &[Fr], x: Fr) -> Fr {
  p.iter().rev().fold(Fr::ZERO, |acc, c| acc * x + c)
}

/// `Π_a (X^W − a)` in coefficients.
fn vanishing_poly(width: usize, points: &[Fr]) -> Vec<Fr> {
  points.iter().fold(vec![Fr::ONE], |acc, &a| {
    let mut factor = vec![Fr::ZERO; width + 1];
    factor[0] = -a;
    factor[width] = Fr::ONE;
    mul(&acc, &factor)
  })
}

fn claim_for(pack: &PackPolynomial<'_>, points: &[Fr]) -> PackClaim {
  PackClaim {
    width: pack.width(),
    points: points.to_vec(),
    values: points.iter().map(|&a| pack.evaluate(a)).collect(),
  }
}

#[test]
fn closed_forms_match_polynomial_division() {
  let mut rng = rng(1);
  for width in [1, 2, 3, 4, 5, 8] {
    for height in [1, 2, 4, 8] {
      for count in [1, 2, 3] {
        let columns = random_columns(&mut rng, width, height);
        let pack = PackPolynomial { height, columns: view(&columns) };
        let p = pack.interleave();
        for (j, column) in columns.iter().enumerate() {
          for (k, &c) in column.iter().enumerate() {
            assert_eq!(p[j + width * k], c);
          }
        }
        let points: Vec<_> = (0..count).map(|_| Fr::rand(&mut rng)).collect();
        let claim = claim_for(&pack, &points);
        let z_s = vanishing_poly(width, &points);
        let r = naive_remainder(&p, &z_s);
        let z = Fr::rand(&mut rng);
        assert_eq!(claim.vanishing(z), horner(&z_s, z));
        assert_eq!(claim.remainder(z), horner(&r, z));
        // Floor quotients of the columns interleave to the quotient of P.
        let mut q = vec![Fr::ZERO; width * height.saturating_sub(count)];
        pack.scatter_quotient(&mut q, Fr::ONE, &points);
        let qz =
          mul(&q.iter().copied().chain([Fr::ZERO]).collect::<Vec<_>>(), &z_s);
        for (i, &c) in p.iter().enumerate() {
          let expected = c - r.get(i).copied().unwrap_or(Fr::ZERO);
          assert_eq!(qz.get(i).copied().unwrap_or(Fr::ZERO), expected);
        }
      }
    }
  }
}

/// Where the roots of `X^W = a` exist (`a = b^W`, `W | 2^28`), the remainder
/// is the interpolant of `P` on those explicit roots, as in fflonk.
#[test]
fn closed_forms_match_root_interpolation() {
  let mut rng = rng(2);
  for width in [1usize, 2, 4, 8] {
    let height = 4;
    let columns = random_columns(&mut rng, width, height);
    let pack = PackPolynomial { height, columns: view(&columns) };
    let p = pack.interleave();
    let omega = Fr::get_root_of_unity(width as u64).unwrap();
    let bases = [Fr::rand(&mut rng), Fr::rand(&mut rng)];
    let points: Vec<_> = bases.iter().map(|b| b.pow([width as u64])).collect();
    let roots: Vec<_> = bases
      .iter()
      .flat_map(|&b| (0..width).map(move |t| b * omega.pow([t as u64])))
      .collect();
    let claim = claim_for(&pack, &points);
    let z = Fr::rand(&mut rng);
    let mut interpolated = Fr::ZERO;
    for (i, &x) in roots.iter().enumerate() {
      let mut basis = Fr::ONE;
      for (k, &y) in roots.iter().enumerate() {
        if k != i {
          basis *= (z - y) / (x - y);
        }
      }
      interpolated += basis * horner(&p, x);
    }
    assert_eq!(claim.remainder(z), interpolated);
    let vanishing: Fr = roots.iter().map(|&x| z - x).product();
    assert_eq!(claim.vanishing(z), vanishing);
  }
}

struct Fixture {
  pcs: KzgPcs,
  params: VerifierParams,
  columns: Vec<Vec<Vec<Fr>>>,
  heights: Vec<usize>,
  commitments: Vec<G1Affine>,
  claims: Vec<PackClaim>,
}

const SHAPES: [(usize, usize, bool); 5] =
  [(16, 3, true), (16, 5, true), (8, 7, false), (4, 1, true), (2, 16, false)];

fn absorb(
  transcript: &mut KzgTranscript,
  commitments: &[G1Affine],
  claims: &[PackClaim],
) {
  transcript.observe_bytes(b"test/packs\0");
  for (commitment, claim) in commitments.iter().zip(claims) {
    transcript.observe_canonical(commitment);
    transcript.observe_canonical(&(claim.width as u64));
    transcript.observe_canonical(&claim.points);
    for row in &claim.values {
      transcript.observe_canonical(row);
    }
  }
}

impl Fixture {
  fn new(seed: u64) -> Self {
    let mut rng = rng(seed);
    let srs = Arc::new(Srs::unsafe_dev_setup(128, b"packed-shplonk-pcs"));
    let params = VerifierParams::from_srs(&srs);
    let pcs = KzgPcs::new(srs, 1);
    let zeta = Fr::rand(&mut rng);
    let mut fixture = Self {
      pcs,
      params,
      columns: vec![],
      heights: vec![],
      commitments: vec![],
      claims: vec![],
    };
    for (height, width, next) in SHAPES {
      let columns = random_columns(&mut rng, width, height);
      let pack = PackPolynomial { height, columns: view(&columns) };
      let omega = Fr::get_root_of_unity(height as u64).unwrap();
      let points = if next { vec![zeta, zeta * omega] } else { vec![zeta] };
      fixture.claims.push(claim_for(&pack, &points));
      fixture
        .commitments
        .push(fixture.pcs.msm(&pack.interleave()).into_affine());
      fixture.columns.push(columns);
      fixture.heights.push(height);
    }
    fixture
  }

  fn packs(&self) -> Vec<PackPolynomial<'_>> {
    self
      .columns
      .iter()
      .zip(&self.heights)
      .map(|(columns, &height)| PackPolynomial {
        height,
        columns: view(columns),
      })
      .collect()
  }

  fn prove(&self) -> Proof {
    let packs = self.packs();
    let pairs: Vec<_> = packs.iter().zip(&self.claims).collect();
    let mut transcript = KzgTranscript::default();
    absorb(&mut transcript, &self.commitments, &self.claims);
    open(&self.pcs, &pairs, &mut transcript)
  }

  fn verify(
    &self,
    commitments: &[G1Affine],
    claims: &[PackClaim],
    proof: &Proof,
  ) -> Result<(), Error> {
    let mut transcript = KzgTranscript::default();
    absorb(&mut transcript, commitments, claims);
    let packs: Vec<_> = commitments.iter().copied().zip(claims).collect();
    verify(&self.params, &packs, proof, &mut transcript)
  }
}

#[test]
fn packs_of_several_heights_and_widths_open_together() {
  let fixture = Fixture::new(3);
  let proof = fixture.prove();
  fixture.verify(&fixture.commitments, &fixture.claims, &proof).unwrap();
}

#[test]
fn verifier_rejects_altered_openings() {
  let fixture = Fixture::new(4);
  let proof = fixture.prove();
  let commitments = &fixture.commitments;
  let claims = &fixture.claims;
  let reject =
    |commitments: &[G1Affine], claims: &[PackClaim], proof: &Proof| {
      assert!(fixture.verify(commitments, claims, proof).is_err());
    };

  for (pack, point, column) in [(0, 0, 0), (0, 1, 2), (2, 0, 6), (4, 0, 15)] {
    let mut altered = claims.clone();
    altered[pack].values[point][column] += Fr::ONE;
    reject(commitments, &altered, &proof);
  }

  let mut altered = commitments.clone();
  altered[1] = (altered[1] + fixture.params.g1[0]).into_affine();
  reject(&altered, claims, &proof);

  let generator = G1Projective::from(fixture.params.g1[0]);
  for w in 0..2 {
    let mut altered = proof;
    let target = if w == 0 { &mut altered.w1 } else { &mut altered.w2 };
    *target = (*target + generator).into_affine();
    reject(commitments, claims, &altered);
  }

  // Claimed values at a different point set, consistent with the columns.
  let packs = fixture.packs();
  let mut moved = claims.clone();
  moved[0] =
    claim_for(&packs[0], &[claims[0].points[0], claims[0].points[1] + Fr::ONE]);
  reject(commitments, &moved, &proof);
  let mut dropped = claims.clone();
  dropped[0] = claim_for(&packs[0], &claims[0].points[..1]);
  reject(commitments, &dropped, &proof);

  // Packs 0 and 1 share their height and point set.
  let mut swapped_commitments = commitments.clone();
  swapped_commitments.swap(0, 1);
  let mut swapped_claims = claims.clone();
  swapped_claims.swap(0, 1);
  reject(&swapped_commitments, claims, &proof);
  reject(&swapped_commitments, &swapped_claims, &proof);

  let mut repeated = claims.clone();
  repeated[0].points[1] = repeated[0].points[0];
  assert_eq!(
    fixture.verify(commitments, &repeated, &proof),
    Err(Error::RepeatedPoint)
  );
}

/// Committed-evaluation variant: `[E]` absorbed in place of the values, `E`
/// opened at `ρ` in the same batch, and `E(ρ)` recomputed from the values.
mod committed {
  use super::*;

  pub(super) fn absorb_committed(
    transcript: &mut KzgTranscript,
    commitments: &[G1Affine],
    claims: &[PackClaim],
    e: G1Affine,
  ) -> Fr {
    transcript.observe_bytes(b"test/packs-committed\0");
    for (commitment, claim) in commitments.iter().zip(claims) {
      transcript.observe_canonical(commitment);
      transcript.observe_canonical(&(claim.width as u64));
      transcript.observe_canonical(&claim.points);
    }
    transcript.observe_canonical(&e);
    sample(transcript)
  }

  pub(super) fn e_claim(claims: &[PackClaim], rho: Fr) -> PackClaim {
    let refs: Vec<_> = claims.iter().collect();
    let e = committed_evaluations(&refs);
    PackClaim {
      width: 1,
      points: vec![rho],
      values: vec![vec![horner(&e, rho)]],
    }
  }

  pub(super) fn prove(fixture: &Fixture) -> (G1Affine, Proof) {
    let refs: Vec<_> = fixture.claims.iter().collect();
    let e = committed_evaluations(&refs);
    let e_point = fixture.pcs.msm(&e).into_affine();
    let mut transcript = KzgTranscript::default();
    let rho = absorb_committed(
      &mut transcript,
      &fixture.commitments,
      &fixture.claims,
      e_point,
    );
    let mut packs = fixture.packs();
    packs.push(PackPolynomial {
      height: e.len(),
      columns: vec![Coefficients::Dense(&e)],
    });
    let mut claims = fixture.claims.clone();
    claims.push(e_claim(&fixture.claims, rho));
    let pairs: Vec<_> = packs.iter().zip(&claims).collect();
    (e_point, open(&fixture.pcs, &pairs, &mut transcript))
  }

  pub(super) fn verify_committed(
    fixture: &Fixture,
    claims: &[PackClaim],
    e: G1Affine,
    proof: &Proof,
  ) -> Result<(), Error> {
    let mut transcript = KzgTranscript::default();
    let rho =
      absorb_committed(&mut transcript, &fixture.commitments, claims, e);
    let mut all = claims.to_vec();
    all.push(e_claim(claims, rho));
    let mut commitments = fixture.commitments.clone();
    commitments.push(e);
    let packs: Vec<_> = commitments.iter().copied().zip(&all).collect();
    verify(&fixture.params, &packs, proof, &mut transcript)
  }
}

#[test]
fn committed_evaluations_open_and_reject_naive_changes() {
  let fixture = Fixture::new(5);
  let (e, proof) = committed::prove(&fixture);
  committed::verify_committed(&fixture, &fixture.claims, e, &proof).unwrap();
  let mut altered = fixture.claims.clone();
  altered[2].values[0][3] += Fr::ONE;
  assert!(committed::verify_committed(&fixture, &altered, e, &proof).is_err());
  let other = (e + fixture.params.g1[1]).into_affine();
  assert!(
    committed::verify_committed(&fixture, &fixture.claims, other, &proof)
      .is_err()
  );
}

/// The values are fixed only through `E(ρ)` and the batch constant, both
/// linear in them, and neither is absorbed before `ρ`, `γ`, `z`. A prover
/// that picks values after the challenges changes three of them freely.
#[test]
fn committed_evaluations_without_hashing_are_forgeable() {
  let fixture = Fixture::new(6);
  let (e, proof) = committed::prove(&fixture);
  let mut transcript = KzgTranscript::default();
  let rho = committed::absorb_committed(
    &mut transcript,
    &fixture.commitments,
    &fixture.claims,
    e,
  );
  let (gamma, z) = challenges(&mut transcript, &proof);
  let constant = |claims: &[PackClaim]| {
    let mut all = claims.to_vec();
    all.push(committed::e_claim(claims, rho));
    let refs: Vec<_> = all.iter().collect();
    weights(&refs, gamma, z).unwrap().1
  };
  let base = constant(&fixture.claims);
  // Coordinates (pack, point, column) and their flat index in E.
  let targets = [(0usize, 0usize, 0usize, 0u64), (0, 0, 1, 1), (0, 1, 0, 3)];
  let mut lambda = [Fr::ZERO; 3];
  for (slot, &(pack, point, column, _)) in targets.iter().enumerate() {
    let mut claims = fixture.claims.clone();
    claims[pack].values[point][column] += Fr::ONE;
    lambda[slot] = constant(&claims) - base;
  }
  let mu = targets.map(|(.., index)| rho.pow([index]));
  // δ₀ = 1; solve λ·δ = 0 and μ·δ = 0 for δ₁, δ₂.
  let det = lambda[1] * mu[2] - lambda[2] * mu[1];
  let d1 = (-lambda[0] * mu[2] + lambda[2] * mu[0]) / det;
  let d2 = (-lambda[1] * mu[0] + lambda[0] * mu[1]) / det;
  let mut forged = fixture.claims.clone();
  for (&(pack, point, column, _), delta) in
    targets.iter().zip([Fr::ONE, d1, d2])
  {
    forged[pack].values[point][column] += delta;
  }
  assert_ne!(forged[0].values, fixture.claims[0].values);
  committed::verify_committed(&fixture, &forged, e, &proof).unwrap();

  // Absorbing the values themselves before γ defeats the same forgery.
  let honest = fixture.prove();
  assert!(fixture.verify(&fixture.commitments, &forged, &honest).is_err());
}

#[test]
fn grouped_quotients_match_per_pack_quotients() {
  let mut rng = rng(7);
  for width in [1, 3, 4] {
    for count in [1, 2] {
      let points: Vec<_> = (0..count).map(|_| Fr::rand(&mut rng)).collect();
      let heights = [8, 4, 8, 2];
      let columns: Vec<_> =
        heights.iter().map(|&h| random_columns(&mut rng, width, h)).collect();
      let packs: Vec<_> = columns
        .iter()
        .zip(heights)
        .map(|(c, height)| PackPolynomial { height, columns: view(c) })
        .collect();
      let scales: Vec<_> = packs.iter().map(|_| Fr::rand(&mut rng)).collect();
      let len = width * (8 - count);
      let mut expected = vec![Fr::ZERO; len];
      for (pack, &scale) in packs.iter().zip(&scales) {
        pack.scatter_quotient(&mut expected, scale, &points);
      }
      let members: Vec<_> = packs.iter().zip(scales).collect();
      let mut grouped = vec![Fr::ZERO; len];
      scatter_group_quotient(&mut grouped, width, &points, &members);
      assert_eq!(grouped, expected);
    }
  }
}

#[test]
fn grouped_quotients_of_tall_packs_match_per_pack_quotients() {
  let mut rng = rng(11);
  let block = COMBINE_BLOCK;
  for width in [1, 2] {
    for count in [1, 2] {
      let points: Vec<_> = (0..count).map(|_| Fr::rand(&mut rng)).collect();
      let heights = [4 * block, block / 2, 2 * block];
      let columns: Vec<_> =
        heights.iter().map(|&h| random_columns(&mut rng, width, h)).collect();
      let packs: Vec<_> = columns
        .iter()
        .zip(heights)
        .map(|(c, height)| PackPolynomial { height, columns: view(c) })
        .collect();
      let scales: Vec<_> = packs.iter().map(|_| Fr::rand(&mut rng)).collect();
      let len = width * (4 * block - count);
      let mut expected = vec![Fr::ZERO; len];
      for (pack, &scale) in packs.iter().zip(&scales) {
        pack.scatter_quotient(&mut expected, scale, &points);
      }
      let members: Vec<_> = packs.iter().zip(scales).collect();
      let mut grouped = vec![Fr::ZERO; len];
      scatter_group_quotient(&mut grouped, width, &points, &members);
      assert_eq!(grouped, expected);
    }
  }
}
