//! Authenticated, portable verification data for compiler-generated KZG proofs.
//! Proving powers and fixed matrices are excluded. Circuit activation and trace
//! heights remain proof data subject to the same bounds as in-process checking.

use super::{AiurCurve, AiurField, Backend, Proof, check_shape};
use crate::kzg::{
  CurveScalar, KzgCommitment, KzgConfig, KzgCurve, TranscriptKind,
  VerifierParams,
};
use multi_stark::{
  config::ProofConfig,
  system::{Circuit, System},
  traits::TwoAdicField,
};
use serde::{Deserialize, Serialize, de::DeserializeOwned};

const KEY_MAGIC: &[u8; 8] = b"IXAUBK02";
const PROOF_MAGIC: &[u8; 8] = b"IXAUBP01";
const MAX_BYTES: usize = 64 << 20;

#[derive(Serialize, Deserialize)]
#[serde(bound(
  serialize = "Circuits: Serialize, KzgCommitment<C>: Serialize",
  deserialize = "Circuits: Deserialize<'de>, KzgCommitment<C>: Deserialize<'de>"
))]
struct EncodedKey<
  C: KzgCurve = crate::kzg::Bn254,
  Circuits = Vec<Circuit<CurveScalar<C>>>,
> {
  parameters: Vec<u8>,
  transcript: u8,
  quotient_budget: usize,
  circuits: Circuits,
  preprocessing: Option<KzgCommitment<C>>,
  indices: Vec<Option<usize>>,
  key_bound: bool,
}

#[derive(Serialize, Deserialize)]
struct EncodedProof {
  active: Vec<bool>,
  log_degrees: Vec<u8>,
  body: Vec<u8>,
}

pub struct VerifyingKey<C: AiurCurve = crate::kzg::Bn254> {
  system: System<KzgConfig<C>>,
}

impl<F: AiurField> Backend<'_, '_, F> {
  pub fn verifying_key(&self) -> Result<VerifyingKey<F::Curve>, String> {
    VerifyingKey::from_system(self.system())
  }
}

impl<C: AiurCurve> VerifyingKey<C> {
  /// Derive verification data from a system built from trusted compiler output
  /// and setup. Fixed commitments are retained; fixed witness matrices are not.
  pub fn from_system(source: &System<KzgConfig<C>>) -> Result<Self, String> {
    let parameters = source.config.pcs().verifier_params().clone();
    let circuits = source.circuits.iter().map(copy_circuit).collect();
    let mut config = KzgConfig::<C>::verifier_only(
      parameters,
      source.config.max_quotient_degree(),
    )
    .with_transcript(source.config.transcript_kind());
    if let Some(digest) = source.config.key_digest() {
      config = config.with_key_digest(*digest);
    }
    let system = System {
      config,
      circuits,
      preprocessed_commit: source.preprocessed_commit.clone(),
      preprocessed_indices: source.preprocessed_indices.clone(),
      vk_digest: source.vk_digest,
    };
    let key = Self { system };
    key.validate()?;
    Ok(key)
  }

  pub fn system(&self) -> &System<KzgConfig<C>> {
    &self.system
  }

  pub fn to_bytes(&self) -> Result<Vec<u8>, String> {
    self.encode_key(self.is_key_bound())
  }

  pub fn is_key_bound(&self) -> bool {
    self.system.config.key_digest().is_some()
  }

  /// Bind a KZG system's Fiat-Shamir transcript seed to its canonical encoded
  /// verifying-key digest before proving.
  pub fn bind_system(system: &mut System<KzgConfig<C>>) -> Result<(), String> {
    bind_system(system)
  }

  fn encode_key(&self, key_bound: bool) -> Result<Vec<u8>, String> {
    encode(
      KEY_MAGIC,
      &EncodedKey::<C, _> {
        parameters: self
          .system
          .config
          .pcs()
          .verifier_params()
          .to_bytes()
          .map_err(|error| error.to_string())?,
        transcript: match self.system.config.transcript_kind() {
          TranscriptKind::Blake3 => 0,
          TranscriptKind::Keccak256 => 1,
        },
        quotient_budget: self.system.config.max_quotient_degree(),
        circuits: &self.system.circuits,
        preprocessing: self.system.preprocessed_commit.clone(),
        indices: self.system.preprocessed_indices.clone(),
        key_bound,
      },
    )
  }

  /// Authenticate the complete key before decoding for curve `C`.
  pub fn from_bytes_for(
    bytes: &[u8],
    expected_digest: &[u8; 32],
  ) -> Result<Self, String> {
    if blake3::hash(bytes).as_bytes() != expected_digest {
      return Err("Aiur KZG verifying key digest mismatch".into());
    }
    let encoded: EncodedKey<C> = decode(KEY_MAGIC, bytes)?;
    if !encoded.quotient_budget.is_power_of_two()
      || encoded.quotient_budget.ilog2() as usize
        > CurveScalar::<C>::TWO_ADICITY
    {
      return Err("invalid KZG quotient budget".into());
    }
    let parameters = VerifierParams::<C>::from_bytes(&encoded.parameters)
      .map_err(|error| error.to_string())?;
    let transcript = match encoded.transcript {
      0 => TranscriptKind::Blake3,
      1 => TranscriptKind::Keccak256,
      _ => return Err("unsupported KZG transcript".into()),
    };
    if !encoded.key_bound {
      return Err(
        "Aiur KZG verifying key must bind its transcript to the key digest"
          .into(),
      );
    }
    let config =
      KzgConfig::<C>::verifier_only(parameters, encoded.quotient_budget)
        .with_transcript(transcript)
        .with_key_digest(*blake3::hash(bytes).as_bytes());
    let vk_digest = multi_stark::system::compute_vk_digest::<
      CurveScalar<C>,
      CurveScalar<C>,
    >(&encoded.circuits);
    let key = Self {
      system: System {
        config,
        circuits: encoded.circuits,
        preprocessed_commit: encoded.preprocessing,
        preprocessed_indices: encoded.indices,
        vk_digest,
      },
    };
    key.validate()?;
    Ok(key)
  }

  /// `claim` is the independently expected native call message, including its
  /// CALL namespace, compiler callable ID, typed inputs and outputs.
  pub fn verify(
    &self,
    claim: &[CurveScalar<C>],
    proof: &Proof<C>,
  ) -> Result<(), String> {
    check_shape(&self.system, &proof.active, &proof.log_degrees)?;
    self
      .system
      .verify(claim, proof)
      .map_err(|error| format!("Aiur KZG verification failed: {error:?}"))
  }

  pub fn encode_proof(&self, proof: &Proof<C>) -> Result<Vec<u8>, String> {
    check_shape(&self.system, &proof.active, &proof.log_degrees)?;
    let codec = crate::kzg::compact::FixedProofCodec::<C>::new_active(
      &self.system,
      &proof.active,
      &proof.log_degrees,
    )
    .map_err(|error| error.to_string())?;
    encode(
      PROOF_MAGIC,
      &EncodedProof {
        active: proof.active.clone(),
        log_degrees: proof.log_degrees.clone(),
        body: codec.encode(proof).map_err(|error| error.to_string())?,
      },
    )
  }

  pub fn verify_bytes(
    &self,
    claim: &[CurveScalar<C>],
    bytes: &[u8],
  ) -> Result<(), String> {
    self.verify(claim, &self.decode_proof(bytes)?)
  }

  /// Decode canonical transport against this authenticated key's dimensions.
  /// Verification still requires an independently expected public claim.
  pub fn decode_proof(&self, bytes: &[u8]) -> Result<Proof<C>, String> {
    let encoded: EncodedProof = decode(PROOF_MAGIC, bytes)?;
    check_shape(&self.system, &encoded.active, &encoded.log_degrees)?;
    let codec = crate::kzg::compact::FixedProofCodec::<C>::new_active(
      &self.system,
      &encoded.active,
      &encoded.log_degrees,
    )
    .map_err(|error| error.to_string())?;
    codec.decode(&encoded.body).map_err(|error| error.to_string())
  }

  fn validate(&self) -> Result<(), String> {
    let system = &self.system;
    if let Some(digest) = system.config.key_digest()
      && blake3::hash(&self.encode_key(true)?).as_bytes() != digest
    {
      return Err("Aiur KZG transcript is bound to a different key".into());
    }
    if system.circuits.is_empty()
      || system.preprocessed_indices.len() != system.circuits.len()
    {
      return Err("invalid Aiur KZG circuit dimensions".into());
    }
    let fixed =
      system.preprocessed_commit.as_ref().map(|commitment| &commitment.0);
    let mut next_fixed = 0;
    for (circuit, index) in
      system.circuits.iter().zip(&system.preprocessed_indices)
    {
      crate::circuit_metadata::validate_circuit(circuit, 1)?;
      if circuit.preprocessed.is_some()
        || circuit.quotient_degree() > system.config.max_quotient_degree()
        || u32::try_from(circuit.main_width).is_err()
        || u32::try_from(circuit.preprocessed_width).is_err()
      {
        return Err("invalid Aiur KZG circuit metadata".into());
      }
      if circuit.preprocessed_width == 0 {
        if index.is_some() || circuit.preprocessed_height != 0 {
          return Err("unexpected fixed preprocessing".into());
        }
      } else {
        let height = circuit.preprocessed_height;
        if !height.is_power_of_two()
          || height > system.config.pcs().verifier_params().max_trace_len()
          || height.ilog2() as usize
            + circuit.quotient_degree().ilog2() as usize
            > CurveScalar::<C>::TWO_ADICITY
          || *index != Some(next_fixed)
          || fixed
            .and_then(|commitments| commitments.get(next_fixed))
            .map(Vec::len)
            != Some(circuit.preprocessed_width)
        {
          return Err("invalid fixed preprocessing dimensions".into());
        }
        next_fixed += 1;
      }
    }
    if (next_fixed == 0 && fixed.is_some())
      || (next_fixed != 0 && fixed.map(Vec::len) != Some(next_fixed))
    {
      return Err("unused fixed preprocessing commitments".into());
    }
    Ok(())
  }
}

pub(super) fn bind_system<C: AiurCurve>(
  system: &mut System<KzgConfig<C>>,
) -> Result<(), String> {
  let key = VerifyingKey::from_system(system)?;
  let digest = *blake3::hash(&key.encode_key(true)?).as_bytes();
  system.config = system.config.clone().with_key_digest(digest);
  Ok(())
}

fn copy_circuit<C: KzgCurve>(
  source: &Circuit<CurveScalar<C>>,
) -> Circuit<CurveScalar<C>> {
  Circuit {
    graph: source.graph.clone(),
    main_width: source.main_width,
    preprocessed: None,
    preprocessed_width: source.preprocessed_width,
    preprocessed_height: source.preprocessed_height,
    num_lookups: source.num_lookups,
    stage_2_width: source.stage_2_width,
    num_publics: source.num_publics,
    lookup_group_size: source.lookup_group_size,
    constraint_count: source.constraint_count,
    max_constraint_degree: source.max_constraint_degree,
  }
}

fn encode<T: Serialize>(magic: &[u8; 8], value: &T) -> Result<Vec<u8>, String> {
  let mut bytes = magic.to_vec();
  bytes.extend(
    bincode::serde::encode_to_vec(value, bincode::config::standard())
      .map_err(|error| error.to_string())?,
  );
  if bytes.len() > MAX_BYTES {
    return Err("Aiur KZG encoding exceeds 64 MiB".into());
  }
  Ok(bytes)
}

fn decode<T: Serialize + DeserializeOwned>(
  magic: &[u8; 8],
  bytes: &[u8],
) -> Result<T, String> {
  if bytes.len() > MAX_BYTES || !bytes.starts_with(magic) {
    return Err("invalid Aiur KZG encoding tag or size".into());
  }
  let (value, used) = bincode::serde::decode_from_slice(
    &bytes[8..],
    bincode::config::standard().with_limit::<67108864>(),
  )
  .map_err(|error| error.to_string())?;
  if used != bytes.len() - 8 || encode(magic, &value)? != bytes {
    return Err("noncanonical Aiur KZG encoding".into());
  }
  Ok(value)
}

impl VerifyingKey<crate::kzg::Bn254> {
  /// Authenticate the complete key before decoding. The expected digest must
  /// come from trusted compilation or verifier configuration, not the proof.
  pub fn from_bytes(
    bytes: &[u8],
    expected_digest: &[u8; 32],
  ) -> Result<Self, String> {
    Self::from_bytes_for(bytes, expected_digest)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{aiur_backend::Bn254, kzg::Srs};
  use aiur::field::FieldBackend;
  use multi_stark::{expr::Expr, lookup::Lookup, system::CircuitInputs};
  use p3_matrix::dense::RowMajorMatrix;
  use std::sync::Arc;

  fn system() -> (System<KzgConfig>, multi_stark::system::ProverKey<KzgConfig>)
  {
    let config =
      KzgConfig::new(Arc::new(Srs::unsafe_dev_setup(32, b"aiur-key-codec")), 8);
    let circuits: Vec<_> = (0..3)
      .map(|index| CircuitInputs {
        main_width: 1,
        preprocessed: (index == 2)
          .then(|| RowMajorMatrix::new(vec![Bn254.zero(); 2], 1)),
        constraints: vec![if index == 0 {
          Expr::main(0) - Expr::IsFirstRow
        } else {
          Expr::main(0)
        }],
        lookups: if index == 0 {
          vec![Lookup::pull(Expr::main(0), vec![])]
        } else {
          vec![]
        },
        ..Default::default()
      })
      .collect();
    let (mut system, pk) = System::new(config, circuits);
    bind_system(&mut system).unwrap();
    (system, pk)
  }

  #[test]
  fn authenticated_key_still_requires_valid_metadata_and_setup() {
    let (system, _) = system();
    let key = VerifyingKey::from_system(&system).unwrap();
    let bytes = key.to_bytes().unwrap();
    for mutate in [
      |key: &mut EncodedKey| key.key_bound = false,
      |key: &mut EncodedKey| key.indices[2] = Some(1),
      |key: &mut EncodedKey| key.circuits[0].stage_2_width += 1,
      |key: &mut EncodedKey| key.circuits[2].preprocessed_height = 3,
      |key: &mut EncodedKey| {
        key.circuits[2].preprocessed =
          Some(RowMajorMatrix::new(vec![Bn254.zero(); 2], 1))
      },
      |key: &mut EncodedKey| key.preprocessing = None,
      |key: &mut EncodedKey| key.transcript = 255,
      |key: &mut EncodedKey| key.quotient_budget = 3,
      |key: &mut EncodedKey| key.parameters.push(0),
      |key: &mut EncodedKey| key.circuits[0].main_width = usize::MAX,
    ] {
      let mut bad: EncodedKey = decode(KEY_MAGIC, &bytes).unwrap();
      mutate(&mut bad);
      let bad = encode(KEY_MAGIC, &bad).unwrap();
      assert!(
        VerifyingKey::from_bytes(&bad, blake3::hash(&bad).as_bytes()).is_err()
      );
    }
  }

  #[test]
  fn equal_shapes_with_different_constraints_have_distinct_transcripts() {
    let make = |value| {
      let config =
        KzgConfig::new(Arc::new(Srs::unsafe_dev_setup(32, b"key-binding")), 8);
      let (mut system, _) = System::new(
        config,
        [CircuitInputs {
          main_width: 1,
          constraints: vec![
            Expr::main(0) - Expr::constant(Bn254.from_u64(value)),
          ],
          ..Default::default()
        }],
      );
      bind_system(&mut system).unwrap();
      system
    };
    let first = make(7);
    let second = make(8);
    assert_eq!(first.circuits[0].main_width, second.circuits[0].main_width);
    assert_eq!(
      first.circuits[0].constraint_count,
      second.circuits[0].constraint_count
    );
    assert_ne!(first.config.transcript_seed(), second.config.transcript_seed());
    for system in [&first, &second] {
      let key = VerifyingKey::from_system(system).unwrap();
      let bytes = key.to_bytes().unwrap();
      assert!(key.is_key_bound());
      assert_eq!(
        system.config.key_digest().unwrap(),
        blake3::hash(&bytes).as_bytes()
      );
      let decoded =
        VerifyingKey::from_bytes(&bytes, blake3::hash(&bytes).as_bytes())
          .unwrap();
      assert_eq!(
        decoded.system().config.transcript_seed(),
        system.config.transcript_seed()
      );
    }
  }
}
