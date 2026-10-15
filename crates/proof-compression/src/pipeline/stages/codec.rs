//! Verifier-only transport. These bytes must be authenticated by the caller;
//! decoding a key supplied alongside a proof does not establish trust.
use super::{FriVerifier, KzgVerifier, Result, Statement};
use crate::fri::VerifierKey;
use crate::kzg::{KzgCommitment, KzgConfig, Scalar, VerifierParams};
use multi_stark::system::{Circuit, System};
use multi_stark::traits::Field;
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

impl<F: Field> Statement<F> {
  fn validate(&self) -> Result<()> {
    let count = self.locations.len();
    if self.template.len() <= count
      || self.template[..=count].iter().any(|row| row.len() != 4)
      || self.locations.iter().copied().ne((1..=count).map(|i| (i, 3)))
      || self
        .locations
        .iter()
        .any(|&(row, col)| self.template[row][col] != F::ZERO)
    {
      return Err("invalid compression statement schema".into());
    }
    Ok(())
  }
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
      b"IXKZGV01",
      (
        self.params.to_bytes()?,
        &self.system.circuits,
        &self.system.preprocessed_commit,
        &self.statement,
      ),
    )
  }

  /// Decode an independently trusted verifier with a 64 MiB decoding budget.
  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    let (params, circuits, preprocessing, statement): (
      Vec<u8>,
      Vec<Circuit<Scalar>>,
      Option<KzgCommitment>,
      Statement<Scalar>,
    ) = decode(b"IXKZGV01", bytes)?;
    let params = VerifierParams::from_bytes(&params)?;
    statement.validate()?;
    let commitment =
      preprocessing.as_ref().ok_or("missing fixed commitment")?;
    if circuits.is_empty() || commitment.0.len() != circuits.len() {
      return Err("invalid fixed commitment dimensions".into());
    }
    for (i, c) in circuits.iter().enumerate() {
      crate::circuit_metadata::validate_circuit(c, 1)?;
      if c.preprocessed.is_some()
        || c.preprocessed_width == 0
        || !c.preprocessed_height.is_power_of_two()
        || c.preprocessed_height > params.max_trace_len()
        || c.quotient_degree() > 2
        || commitment.0[i].len() != c.preprocessed_width
      {
        return Err("invalid KZG compression circuit metadata".into());
      }
    }
    let indices = (0..circuits.len()).map(Some).collect();
    Ok(Self {
      system: System {
        config: KzgConfig::verifier_only(params.clone(), 2),
        circuits,
        preprocessed_commit: preprocessing,
        preprocessed_indices: indices,
      },
      params,
      statement,
    })
  }
}
