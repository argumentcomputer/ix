//! The recursive KZG stage: a circuit verifying a first KZG stage proof with
//! its opening pairing deferred to public operands, the proof of it, and the
//! prepared verifier shared by local and bundled verifying keys.
use crate::kzg::{
  KzgConfig, Srs,
  curve::{Bn254, G1AffineOf, G2AffineOf, KzgCurve, read_g1_compressed_for},
  field::CurveScalar,
};
use crate::pipeline::{
  Result,
  claims::ClaimTemplate,
  lowering,
  stage::{self, KzgVerifier, Prepared, scalar_statement},
};
use crate::recursive::native_verifier;
use crate::recursive::pairing::{self, PUBLIC_VALUES};
use ark_ec::{AffineRepr, pairing::Pairing};
use ark_ff::Zero;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use multi_stark::{prover::Proof, system::System, types::Val};
use std::sync::Arc;

/// Recursive proof and its public pairing operands. Certificate claim values
/// are supplied independently to RecursiveVerifier::verify.
pub struct RecursiveProof<C: KzgCurve = Bn254> {
  pub proof: Proof<KzgConfig<C>>,
  pub pairing_values: Vec<CurveScalar<C>>,
}

fn build_recursive<C: KzgCurve>(
  verifier: &KzgVerifier<C>,
  proof: &Proof<KzgConfig<C>>,
  claims: &[Vec<CurveScalar<C>>],
) -> Result<native_verifier::Built<C>> {
  let plan = lowering::recursive_plan(
    &verifier.system,
    &proof.log_degrees,
    native_verifier::ClaimSchema::from_claims(
      claims,
      &verifier.statement.locations,
    )?,
  )?;
  Ok(plan.build(proof, claims)?)
}

pub struct RecursiveStage<C: KzgCurve = Bn254> {
  prepared: Prepared<CurveScalar<C>>,
  pairings: Pairings<C>,
  claim_len: usize,
}

/// Build the recursive KZG verifier. The original public statement remains
/// public; the opening-check operands are additional publics.
pub fn prepare_recursive<C: KzgCurve>(
  verifier: &KzgVerifier<C>,
  proof: &Proof<KzgConfig<C>>,
  expected: &[Val],
) -> Result<RecursiveStage<C>> {
  let public = scalar_statement::<C>(expected);
  verifier.verify(proof, &public)?;
  let claims = verifier.statement.claims(&public)?;
  let built = build_recursive(verifier, proof, &claims)?;
  let assignment = built.assign()?;
  let pairings = Pairings {
    keys: built
      .pairing_keys
      .try_into()
      .map_err(|_keys| "expected two pairing keys")?,
  };
  pairings.verify(&assignment.public_values()[public.len()..])?;
  Ok(RecursiveStage {
    prepared: Prepared { circuit: built.circuit, assignment },
    pairings,
    claim_len: public.len(),
  })
}

impl<C: KzgCurve> RecursiveStage<C> {
  pub fn circuit(&self) -> &multi_stark::plonkish::Circuit<CurveScalar<C>> {
    self.prepared.circuit()
  }

  pub fn prove(
    self,
    srs: Arc<Srs<C>>,
    max_height: usize,
  ) -> Result<(RecursiveVerifier<C>, RecursiveProof<C>)> {
    let pairing_values =
      self.prepared.public_values()[self.claim_len..].to_vec();
    let compiled =
      lowering::lower_recursive(self.prepared.circuit, max_height)?;
    let height = lowering::max_height(&compiled)?;
    if height > srs.max_len() {
      return Err("recursive trace exceeds the SRS range".into());
    }
    let mut config = KzgConfig::with_max_trace_len(srs, height, 2)
      .with_transcript(crate::kzg::TranscriptKind::Blake3)
      .with_streaming_lookups()
      .with_streaming_quotient();
    if let Some(spill_dir) =
      KzgConfig::<C>::resolve_disk_spill_dir(&std::env::temp_dir())?
    {
      config = config.with_disk_spill(spill_dir);
    }
    let (verifier, proof) = stage::prove_lowered(
      lowering::Lowered { compiled, assignment: self.prepared.assignment },
      config,
    )?;
    Ok((
      RecursiveVerifier {
        verifier,
        pairings: self.pairings,
        claim_len: self.claim_len,
      },
      RecursiveProof { proof, pairing_values },
    ))
  }
}

pub(in crate::pipeline) const fn pairing_bytes_for<C: KzgCurve>() -> usize {
  2 * C::G1_COMPRESSED_BYTES
}

pub(in crate::pipeline) struct Pairings<C: KzgCurve = Bn254> {
  pub(in crate::pipeline) keys: [G2AffineOf<C>; 2],
}

impl<C: KzgCurve> Pairings<C> {
  pub(in crate::pipeline) fn encode(
    &self,
    values: &[CurveScalar<C>],
  ) -> Result<Vec<u8>> {
    pack_pairings(values)
  }

  pub(in crate::pipeline) fn verify(
    &self,
    values: &[CurveScalar<C>],
  ) -> Result<()> {
    self.verify_points(pairing::decode(values)?)
  }
}

pub struct RecursiveVerifier<C: KzgCurve = Bn254> {
  pub(super) verifier: KzgVerifier<C>,
  pub(super) pairings: Pairings<C>,
  pub(super) claim_len: usize,
}

impl<C: KzgCurve> RecursiveVerifier<C> {
  /// Encode all verification data, including both stages' public parameters
  /// and the pairing equations. Authenticate the complete encoding on transport.
  pub fn to_bytes(&self) -> Result<Vec<u8>> {
    let mut keys = vec![];
    for key in &self.pairings.keys {
      key.serialize_compressed(&mut keys)?;
    }
    stage::encode_key(
      C::RECURSIVE_VERIFIER_MAGIC,
      (self.verifier.to_bytes()?, self.claim_len, keys),
    )
  }

  /// Decode an independently trusted verifier with a 64 MiB decoding budget.
  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    let (verifier, claim_len, keys): (Vec<u8>, usize, Vec<u8>) =
      stage::decode_key(C::RECURSIVE_VERIFIER_MAGIC, bytes)?;
    let verifier = KzgVerifier::<C>::from_bytes(&verifier)?;
    if keys.len() != 2 * C::G2_COMPRESSED_BYTES
      || claim_len.checked_add(PUBLIC_VALUES)
        != Some(verifier.statement.locations.len())
    {
      return Err("invalid recursive public statement dimensions".into());
    }
    let encoded_keys = keys;
    #[allow(clippy::chunks_exact_to_as_chunks)]
    let keys = encoded_keys
      .chunks_exact(C::G2_COMPRESSED_BYTES)
      .map(G2AffineOf::<C>::deserialize_compressed)
      .collect::<std::result::Result<Vec<_>, _>>()?;
    let mut canonical_keys = Vec::with_capacity(encoded_keys.len());
    for key in &keys {
      key.serialize_compressed(&mut canonical_keys)?;
    }
    if canonical_keys != encoded_keys {
      return Err("noncanonical recursive pairing keys".into());
    }
    Self::from_parts(verifier.system, verifier.statement, &keys, claim_len)
  }

  /// Pack the public pairing operands followed by the fixed-shape KZG proof.
  /// The expected certificate claim and trusted verifier are supplied separately.
  pub fn encode_proof(&self, proof: &RecursiveProof<C>) -> Result<Vec<u8>> {
    let mut bytes = self.pairings.encode(&proof.pairing_values)?;
    bytes.extend(self.verifier.encode_proof(&proof.proof)?);
    Ok(bytes)
  }

  pub fn verify_bytes(&self, bytes: &[u8], expected: &[Val]) -> Result<()> {
    self.verify_scalar_bytes(bytes, &scalar_statement::<C>(expected))
  }

  /// Verify the recursive proof, expected certificate statement, and the
  /// deferred inner opening pairing. No proving SRS is needed.
  pub fn verify(
    &self,
    proof: &RecursiveProof<C>,
    expected: &[Val],
  ) -> Result<()> {
    if expected.len() != self.claim_len {
      return Err("unexpected certificate claim length".into());
    }
    let mut public = scalar_statement::<C>(expected);
    public.extend_from_slice(&proof.pairing_values);
    self.verifier.verify(&proof.proof, &public)?;
    self.pairings.verify(&proof.pairing_values)
  }
}

impl<C: KzgCurve> RecursiveVerifier<C> {
  pub(in crate::pipeline) fn from_parts(
    system: System<KzgConfig<C>>,
    statement: ClaimTemplate<CurveScalar<C>>,
    keys: &[G2AffineOf<C>],
    claim_len: usize,
  ) -> Result<Self> {
    let keys: [G2AffineOf<C>; 2] =
      keys.try_into().map_err(|_keys| "expected two pairing keys")?;
    if keys.iter().any(|p| {
      p.is_zero()
        || !p.is_on_curve()
        || !p.is_in_correct_subgroup_assuming_on_curve()
    }) || statement.locations.len()
      != claim_len.checked_add(PUBLIC_VALUES).ok_or("public count overflow")?
    {
      return Err("invalid recursive verifier parameters".into());
    }
    Ok(Self {
      verifier: KzgVerifier::new(system, statement)?,
      pairings: Pairings { keys },
      claim_len,
    })
  }

  pub(in crate::pipeline) fn verify_scalar_bytes(
    &self,
    bytes: &[u8],
    expected: &[CurveScalar<C>],
  ) -> Result<()> {
    if expected.len() != self.claim_len {
      return Err("unexpected certificate claim length".into());
    }
    verify_recursive_bytes(
      &self.verifier.system,
      &self.verifier.codec,
      &self.verifier.statement,
      &self.pairings,
      bytes,
      expected,
    )
  }
}

impl<C: KzgCurve> Pairings<C> {
  pub(in crate::pipeline) fn verify_bytes(&self, bytes: &[u8]) -> Result<()> {
    self.verify_points(pairing_points::<C>(bytes)?)
  }

  fn verify_points(&self, points: [G1AffineOf<C>; 2]) -> Result<()> {
    if !C::PairingCurve::multi_pairing(points, self.keys).is_zero() {
      return Err("external opening pairing equation failed".into());
    }
    Ok(())
  }
}

fn pairing_points<C: KzgCurve>(mut bytes: &[u8]) -> Result<[G1AffineOf<C>; 2]> {
  if bytes.len() != pairing_bytes_for::<C>() {
    return Err("pairing point count".into());
  }
  Ok([
    read_g1_compressed_for::<C>(&mut bytes)?,
    read_g1_compressed_for::<C>(&mut bytes)?,
  ])
}

#[cfg(any(test, feature = "plonk", feature = "groth16"))]
pub(in crate::pipeline) fn unpack_pairings<C: KzgCurve>(
  bytes: &[u8],
) -> Result<Vec<CurveScalar<C>>> {
  Ok(pairing::encode::<C>(pairing_points::<C>(bytes)?).to_vec())
}

pub(in crate::pipeline) fn pack_pairings<C: KzgCurve>(
  values: &[CurveScalar<C>],
) -> Result<Vec<u8>> {
  let mut bytes = Vec::with_capacity(pairing_bytes_for::<C>());
  for point in pairing::decode::<C>(values)? {
    point.serialize_compressed(&mut bytes)?;
  }
  Ok(bytes)
}

pub(in crate::pipeline) fn verify_recursive_bytes<C: KzgCurve>(
  system: &System<KzgConfig<C>>,
  codec: &crate::kzg::compact::FixedProofCodec<C>,
  statement: &ClaimTemplate<CurveScalar<C>>,
  pairings: &Pairings<C>,
  bytes: &[u8],
  expected: &[CurveScalar<C>],
) -> Result<()> {
  let width = pairing_bytes_for::<C>();
  if bytes.len() < width {
    return Err("truncated pairing operands".into());
  }
  let points = pairing_points::<C>(&bytes[..width])?;
  let mut public = expected.to_vec();
  public.extend(pairing::encode::<C>(points));
  let claims = statement.claims(&public)?;
  let proof = codec.decode(&bytes[width..])?;
  system
    .verify_multiple_claims(
      &claims.iter().map(Vec::as_slice).collect::<Vec<_>>(),
      &proof,
    )
    .map_err(|e| format!("outer KZG proof: {e:?}"))?;
  pairings.verify_points(points)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::kzg::curve::Bls12381;
  use ark_ec::CurveGroup;
  use multi_stark::plonkish::CircuitBuilder;
  use multi_stark::traits::{Algebra, Field};

  fn check_final_verifier<C: KzgCurve>() -> Result<()> {
    let inner = Srs::<C>::unsafe_dev_setup(8, b"inner-test");
    let outer = Arc::new(Srs::<C>::unsafe_dev_setup(128, b"outer-test"));
    for claim_len in [2, 5] {
      for invalid_pairing in [false, true] {
        let mut points = [inner.g1[1], -inner.g1[0]];
        let keys = [inner.g2, inner.tau_g2];
        if invalid_pairing {
          points[0] = (points[0] * C::Fr::from(2u8)).into_affine();
        }
        let packed = pairing::encode::<C>(points);
        let expected: Vec<_> =
          (0..claim_len).map(|i| Val::from_usize(7 + i)).collect();
        let mut public = scalar_statement::<C>(&expected);
        public.extend_from_slice(&packed);
        let mut b = CircuitBuilder::new();
        let table = b.fixed_table(
          "small",
          vec![vec![CurveScalar::<C>::ONE], vec![CurveScalar::<C>::TWO]],
        );
        let one = b.constant(CurveScalar::<C>::ONE);
        b.lookup(table, &[one]);
        let wires: Vec<_> = (0..public.len())
          .map(|i| b.public_input(format!("public{i}")))
          .collect();
        let circuit = b.finish();
        let mut witness = circuit.witness();
        for (&wire, &value) in wires.iter().zip(&public) {
          witness.set(wire, value)?;
        }
        let assignment = witness.generate()?;
        let stage = RecursiveStage {
          prepared: Prepared { circuit, assignment },
          pairings: Pairings { keys },
          claim_len,
        };
        let (verifier, mut proof) = stage.prove(outer.clone(), 128)?;
        assert_eq!(
          verifier.verify(&proof, &expected).is_err(),
          invalid_pairing
        );
        if !invalid_pairing {
          let key_bytes = verifier.to_bytes()?;
          let verifier = RecursiveVerifier::<C>::from_bytes(&key_bytes)?;
          assert_eq!(verifier.to_bytes()?, key_bytes);
          let mut wrong_magic = key_bytes.clone();
          wrong_magic[7] ^= 1;
          assert!(RecursiveVerifier::<C>::from_bytes(&wrong_magic).is_err());
          assert!(
            RecursiveVerifier::<C>::from_bytes(
              &key_bytes[..key_bytes.len() - 1]
            )
            .is_err()
          );
          let mut extra_key = key_bytes.clone();
          extra_key.push(0);
          assert!(RecursiveVerifier::<C>::from_bytes(&extra_key).is_err());
          let bytes = verifier.encode_proof(&proof)?;
          verifier.verify_bytes(&bytes, &expected)?;
          assert!(
            verifier
              .verify_bytes(&bytes[..bytes.len() - 1], &expected)
              .is_err()
          );
          let mut extra = bytes.clone();
          extra.push(0);
          assert!(verifier.verify_bytes(&extra, &expected).is_err());
          let mut malformed = bytes.clone();
          malformed[..C::G1_COMPRESSED_BYTES].fill(0xff);
          assert!(verifier.verify_bytes(&malformed, &expected).is_err());
          let mut wrong = expected.clone();
          wrong[0] += Val::ONE;
          assert!(verifier.verify(&proof, &wrong).is_err());
          assert!(verifier.verify(&proof, &expected[..claim_len - 1]).is_err());
          proof.pairing_values[0] += CurveScalar::<C>::ONE;
          assert!(verifier.verify(&proof, &expected).is_err());
          proof.pairing_values[0] -= CurveScalar::<C>::ONE;
          proof.proof.stage_1_opened_values[0][0][0] += CurveScalar::<C>::ONE;
          assert!(verifier.verify(&proof, &expected).is_err());
        }
      }
    }
    Ok(())
  }

  #[test]
  fn final_verifier_requires_claim_outer_proof_and_both_pairings() -> Result<()>
  {
    check_final_verifier::<Bn254>()?;
    check_final_verifier::<Bls12381>()?;
    Ok(())
  }

  fn check_pairing_transport<C: KzgCurve>() -> Result<()> {
    let generator = G1AffineOf::<C>::generator();
    let multiple = (generator * C::Fr::from(7u8)).into_affine();
    for points in [
      [generator, multiple],
      [-generator, -multiple],
      [G1AffineOf::<C>::identity(), generator],
      [G1AffineOf::<C>::identity(); 2],
    ] {
      let values = pairing::encode::<C>(points);
      let encoded = pack_pairings(&values)?;
      assert_eq!(encoded.len(), pairing_bytes_for::<C>());
      assert_eq!(pairing_points::<C>(&encoded)?, points);
      assert_eq!(unpack_pairings::<C>(&encoded)?, values);
      assert!(unpack_pairings::<C>(&encoded[..encoded.len() - 1]).is_err());
      let mut extra = encoded.clone();
      extra.push(0);
      assert!(unpack_pairings::<C>(&extra).is_err());
      let mut invalid = encoded;
      invalid[..C::G1_COMPRESSED_BYTES].fill(0xff);
      assert!(unpack_pairings::<C>(&invalid).is_err());
      for i in 0..PUBLIC_VALUES {
        let mut high_limb = [0; 4];
        high_limb[C::POINT_LIMB_BYTES / 8] = 1;
        let mut aliased = values;
        aliased[i] += CurveScalar::<C>::from_limbs_le(high_limb);
        assert!(pack_pairings(&aliased).is_err());
      }
      assert!(pack_pairings(&values[..PUBLIC_VALUES - 1]).is_err());
      assert!(
        pack_pairings(&[CurveScalar::<C>::ZERO; PUBLIC_VALUES + 1]).is_err()
      );
    }
    Ok(())
  }

  #[test]
  fn pairing_transport_preserves_points_and_rejects_noncanonical_values()
  -> Result<()> {
    check_pairing_transport::<Bn254>()?;
    check_pairing_transport::<Bls12381>()?;
    Ok(())
  }

  #[test]
  fn pairing_transport_rejects_infinity_coordinate_aliases() -> Result<()> {
    let values = pairing::encode::<Bn254>([G1AffineOf::<Bn254>::identity(); 2]);
    let mut encoded = pack_pairings(&values)?;
    encoded[0] = 1;
    assert!(unpack_pairings::<Bn254>(&encoded).is_err());
    let mut aliased = values;
    aliased[0] = CurveScalar::<Bn254>::ONE;
    assert!(pack_pairings(&aliased).is_err());

    let bls_values =
      pairing::encode::<Bls12381>([G1AffineOf::<Bls12381>::identity(); 2]);
    let mut bls_encoded = pack_pairings(&bls_values)?;
    bls_encoded[47] = 1;
    assert!(unpack_pairings::<Bls12381>(&bls_encoded).is_err());
    let mut bls_aliased = bls_values;
    bls_aliased[1] = CurveScalar::<Bls12381>::ONE;
    assert!(pack_pairings(&bls_aliased).is_err());
    Ok(())
  }
}
