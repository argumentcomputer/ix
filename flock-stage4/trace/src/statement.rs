use std::fmt;

const STATEMENT_BINDING_TOPOLOGY_DIGEST_DOMAIN: &[u8] =
  b"ix:stage4:flock-statement-binding-topology:v1";

/// Backend-neutral wiring from the terminal statement to Flock's circuit
/// statement prefix.
///
/// Flock absorbs the circuit digest and a commitment to its public vector as
/// byte payloads before sampling verifier challenges. The Stage 3 root digest
/// is also present as two words at fixed positions in that public vector.
/// Recording all four locations prevents a backend from relying on host-side
/// ordering conventions when it connects those values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct F128StatementBindingTraceV1 {
  pub statement_domain: [u8; 8],
  pub relation_digest: [u8; 32],
  pub config_digest: [u8; 32],
  pub circuit_digest: [u8; 32],
  pub circuit_digest_payload: u64,
  pub public_values_digest_payload: u64,
  pub stage2_digest_public_values: [u64; 2],
  pub public_value_count: u64,
}

impl F128StatementBindingTraceV1 {
  pub fn validate(
    &self,
    public_values: usize,
    byte_payloads: usize,
  ) -> Result<(), F128StatementBindingTraceError> {
    let expected_public_values = usize::try_from(self.public_value_count)
      .map_err(|_| F128StatementBindingTraceError::PublicValueCount {
        expected: self.public_value_count,
        actual: public_values,
      })?;
    if expected_public_values != public_values {
      return Err(F128StatementBindingTraceError::PublicValueCount {
        expected: self.public_value_count,
        actual: public_values,
      });
    }
    validate_index(
      self.circuit_digest_payload,
      byte_payloads,
      "circuit digest",
    )?;
    validate_index(
      self.public_values_digest_payload,
      byte_payloads,
      "public-values digest",
    )?;
    if self.circuit_digest_payload == self.public_values_digest_payload {
      return Err(F128StatementBindingTraceError::AliasedDigestPayloads);
    }
    for (position, index) in
      self.stage2_digest_public_values.into_iter().enumerate()
    {
      validate_index(index, public_values, "Stage 2 digest public value")
        .map_err(|error| match error {
          F128StatementBindingTraceError::Index { index, count, .. } => {
            F128StatementBindingTraceError::Stage2PublicValueIndex {
              position,
              index,
              count,
            }
          },
          other => other,
        })?;
    }
    if self.stage2_digest_public_values[0]
      == self.stage2_digest_public_values[1]
    {
      return Err(F128StatementBindingTraceError::AliasedStage2PublicValues);
    }
    Ok(())
  }

  pub fn topology_digest(&self) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(STATEMENT_BINDING_TOPOLOGY_DIGEST_DOMAIN);
    hasher.update(&self.statement_domain);
    hasher.update(&self.relation_digest);
    hasher.update(&self.config_digest);
    hasher.update(&self.circuit_digest);
    hasher.update(&self.circuit_digest_payload.to_le_bytes());
    hasher.update(&self.public_values_digest_payload.to_le_bytes());
    for index in self.stage2_digest_public_values {
      hasher.update(&index.to_le_bytes());
    }
    hasher.update(&self.public_value_count.to_le_bytes());
    *hasher.finalize().as_bytes()
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128StatementBindingTraceError {
  PublicValueCount { expected: u64, actual: usize },
  Index { kind: &'static str, index: u64, count: usize },
  Stage2PublicValueIndex { position: usize, index: u64, count: usize },
  AliasedDigestPayloads,
  AliasedStage2PublicValues,
}

impl fmt::Display for F128StatementBindingTraceError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::PublicValueCount { expected, actual } => write!(
        formatter,
        "statement trace has {actual} public values; expected {expected}",
      ),
      Self::Index { kind, index, count } => write!(
        formatter,
        "statement {kind} index {index} is outside {count} entries",
      ),
      Self::Stage2PublicValueIndex { position, index, count } => write!(
        formatter,
        "Stage 2 digest public-value index {position} ({index}) is outside {count} entries",
      ),
      Self::AliasedDigestPayloads => {
        write!(formatter, "statement digest payloads alias")
      },
      Self::AliasedStage2PublicValues => {
        write!(formatter, "Stage 2 digest public values alias")
      },
    }
  }
}

impl std::error::Error for F128StatementBindingTraceError {}

fn validate_index(
  index: u64,
  count: usize,
  kind: &'static str,
) -> Result<(), F128StatementBindingTraceError> {
  if usize::try_from(index).ok().is_none_or(|index| index >= count) {
    return Err(F128StatementBindingTraceError::Index { kind, index, count });
  }
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;

  fn fixture() -> F128StatementBindingTraceV1 {
    F128StatementBindingTraceV1 {
      statement_domain: *b"IXFLK301",
      relation_digest: [1; 32],
      config_digest: [2; 32],
      circuit_digest: [3; 32],
      circuit_digest_payload: 4,
      public_values_digest_payload: 5,
      stage2_digest_public_values: [7, 8],
      public_value_count: 10,
    }
  }

  #[test]
  fn validates_distinct_payload_and_public_bindings() {
    let trace = fixture();
    trace.validate(10, 6).unwrap();
    assert_eq!(trace.topology_digest(), fixture().topology_digest());

    let mut aliased = trace;
    aliased.public_values_digest_payload = aliased.circuit_digest_payload;
    assert_eq!(
      aliased.validate(10, 6),
      Err(F128StatementBindingTraceError::AliasedDigestPayloads),
    );

    let mut omitted = trace;
    omitted.stage2_digest_public_values[1] = 10;
    assert!(matches!(
      omitted.validate(10, 6),
      Err(F128StatementBindingTraceError::Stage2PublicValueIndex {
        position: 1,
        ..
      })
    ));
  }
}
