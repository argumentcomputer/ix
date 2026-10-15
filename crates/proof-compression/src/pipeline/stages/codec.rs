//! Verifier-only transport. These bytes must be authenticated by the caller;
//! decoding a key supplied alongside a proof does not establish trust.
use super::{FriVerifier, KzgVerifier, Result, Statement};
use crate::fri::VerifierKey;
use crate::kzg::{
  KzgCommitment, KzgConfig, Scalar, TranscriptKind, VerifierParams,
};
use multi_stark::system::{Circuit, System};
use multi_stark::types::Val;
use serde::{Serialize, de::DeserializeOwned};

pub(super) fn encode(tag: &[u8; 8], value: impl Serialize) -> Result<Vec<u8>> {
  let mut bytes = tag.to_vec();
  bytes
    .extend(bincode::serde::encode_to_vec(value, bincode::config::standard())?);
  Ok(bytes)
}

pub(super) fn decode<T: DeserializeOwned + Serialize>(
  tag: &[u8; 8],
  bytes: &[u8],
) -> Result<T> {
  if !bytes.starts_with(tag) || bytes.len() > 64 * 1024 * 1024 {
    return Err("invalid compression key tag or size".into());
  }
  let (value, used): (T, usize) = bincode::serde::decode_from_slice(
    &bytes[8..],
    bincode::config::standard().with_limit::<67108864>(),
  )?;
  if used != bytes.len() - 8 || encode(tag, &value)? != bytes {
    return Err("noncanonical compression key".into());
  }
  Ok(value)
}

impl FriVerifier {
  /// Encode the verifier, including its public statement schema. No prover
  /// matrices are included. Authenticate the complete encoding on transport.
  pub fn to_bytes(&self) -> Result<Vec<u8>> {
    encode(b"IXFRIV01", (self.key.to_bytes()?, &self.statement))
  }

  /// Decode an independently trusted verifier with a 64 MiB decoding budget.
  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    let (key, statement): (Vec<u8>, Statement<Val>) =
      decode(b"IXFRIV01", bytes)?;
    statement.validate()?;
    Ok(Self { key: VerifierKey::from_bytes(&key)?, statement })
  }
}

impl KzgVerifier {
  /// Encode verifier parameters, compiled constraints, fixed commitments and
  /// the public statement schema. Proving powers and matrices are excluded.
  pub fn to_bytes(&self) -> Result<Vec<u8>> {
    encode(
      b"IXKZGV02",
      (
        self.params.to_bytes()?,
        match self.system.config.transcript_kind() {
          TranscriptKind::Blake3 => 0u8,
          TranscriptKind::Keccak256 => 1u8,
        },
        &self.system.circuits,
        &self.system.preprocessed_commit,
        &self.statement,
      ),
    )
  }

  /// Decode an independently trusted verifier with a 64 MiB decoding budget.
  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    let (params, transcript, circuits, preprocessing, statement): (
      Vec<u8>,
      u8,
      Vec<Circuit<Scalar>>,
      Option<KzgCommitment>,
      Statement<Scalar>,
    ) = if bytes.starts_with(b"IXKZGV01") {
      let (params, circuits, preprocessing, statement) =
        decode(b"IXKZGV01", bytes)?;
      (params, 0, circuits, preprocessing, statement)
    } else {
      decode(b"IXKZGV02", bytes)?
    };
    let params = VerifierParams::from_bytes(&params)?;
    let transcript = match transcript {
      0 => TranscriptKind::Blake3,
      1 => TranscriptKind::Keccak256,
      _ => return Err("unsupported KZG transcript".into()),
    };
    let indices = (0..circuits.len()).map(Some).collect();
    Self::new(
      System {
        config: KzgConfig::verifier_only(params, 2).with_transcript(transcript),
        circuits,
        preprocessed_commit: preprocessing,
        preprocessed_indices: indices,
      },
      statement,
    )
  }
}
