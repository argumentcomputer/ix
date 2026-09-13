//! Generic Exec binding. The template is verifier-owned; only B, I, O vary.

use std::fmt;

/// One position in the approved native Flock public vector. Fixed zero words
/// are constants too; no position is discovered from a witness value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExecPublicWordV0 {
  Fixed([u8; 16]),
  StatementLow,
  StatementHigh,
}

/// Proof-free statement-prefix and public-vector schema. Flock's pinned
/// circuit protocol observes registry, counts, CAP, circuit, publics in that
/// order, before its first challenge; payload indices are protocol constants.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExecBindingV0 {
  pub profile_digest: [u8; 32],
  pub registry_digest: [u8; 32],
  pub circuit_digest: [u8; 32],
  pub counts: Vec<u64>,
  pub public_template: Vec<ExecPublicWordV0>,
}

/// Private commitment openings within the final compression relation. The
/// Stage 3 proof authenticates S = H4(P, B, I, O). The terminal public digest
/// is Q = H5(P, B, O); the application derives Q from its public canonical
/// claim and approved image/profile, never from an opaque prover assertion.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExecCommitmentsV0 {
  pub program: [u8; 32],
  pub input: [u8; 32],
  pub output: [u8; 32],
}

impl ExecCommitmentsV0 {
  pub fn statement_digest(self, profile: [u8; 32]) -> [u8; 32] {
    commitment_hash(4, &[profile, self.program, self.input, self.output])
  }

  pub fn public_digest(self, profile: [u8; 32]) -> [u8; 32] {
    commitment_hash(5, &[profile, self.program, self.output])
  }
}

fn commitment_hash(tag: u8, components: &[[u8; 32]]) -> [u8; 32] {
  let mut hash = blake3::Hasher::new();
  hash.update(b"IxBy/commit/v0\0");
  hash.update(&[tag]);
  for component in components {
    hash.update(component);
  }
  *hash.finalize().as_bytes()
}

impl ExecBindingV0 {
  pub fn validate(
    &self,
    public_values: usize,
    byte_payloads: usize,
  ) -> Result<(), ExecBindingError> {
    if self.public_template.len() != public_values {
      return Err(ExecBindingError("Exec public-template width"));
    }
    if byte_payloads < 5 || self.counts.is_empty() {
      return Err(ExecBindingError("Exec statement prefix"));
    }
    for limb in
      [ExecPublicWordV0::StatementLow, ExecPublicWordV0::StatementHigh]
    {
      if self.public_template.iter().filter(|word| **word == limb).count() != 1
      {
        return Err(ExecBindingError(
          "Exec must bind exactly two distinct S limbs",
        ));
      }
    }
    Ok(())
  }

  pub fn topology_digest(&self) -> [u8; 32] {
    let mut hash = blake3::Hasher::new();
    hash.update(b"IxBy/Stage4/exec-binding/v0\0");
    for digest in
      [self.profile_digest, self.registry_digest, self.circuit_digest]
    {
      hash.update(&digest);
    }
    hash.update(&(self.counts.len() as u64).to_le_bytes());
    for count in &self.counts {
      hash.update(&count.to_le_bytes());
    }
    hash.update(&(self.public_template.len() as u64).to_le_bytes());
    for word in &self.public_template {
      match word {
        ExecPublicWordV0::Fixed(value) => {
          hash.update(&[0]);
          hash.update(value);
        },
        ExecPublicWordV0::StatementLow => {
          hash.update(&[1]);
        },
        ExecPublicWordV0::StatementHigh => {
          hash.update(&[2]);
        },
      }
    }
    *hash.finalize().as_bytes()
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExecBindingError(pub &'static str);

impl fmt::Display for ExecBindingError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.write_str(self.0)
  }
}
impl std::error::Error for ExecBindingError {}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn private_input_changes_s_but_not_public_q() {
    let first =
      ExecCommitmentsV0 { program: [1; 32], input: [2; 32], output: [3; 32] };
    let second = ExecCommitmentsV0 { input: [4; 32], ..first };
    assert_ne!(
      first.statement_digest([0; 32]),
      second.statement_digest([0; 32])
    );
    assert_eq!(first.public_digest([0; 32]), second.public_digest([0; 32]));
    assert_ne!(first.statement_digest([0; 32]), first.public_digest([0; 32]));
  }

  #[test]
  fn template_pins_zero_constants_limb_order_and_counts() {
    let template = ExecBindingV0 {
      profile_digest: [1; 32],
      registry_digest: [2; 32],
      circuit_digest: [3; 32],
      counts: vec![1, 2],
      public_template: vec![
        ExecPublicWordV0::Fixed([0; 16]),
        ExecPublicWordV0::StatementLow,
        ExecPublicWordV0::StatementHigh,
      ],
    };
    template.validate(3, 5).unwrap();
    for change in 0..4 {
      let mut bad = template.clone();
      match change {
        0 => bad.public_template.swap(1, 2),
        1 => bad.public_template[0] = ExecPublicWordV0::Fixed([1; 16]),
        2 => bad.counts.swap(0, 1),
        _ => bad.profile_digest[0] ^= 1,
      }
      assert_ne!(template.topology_digest(), bad.topology_digest());
    }
    assert!(template.validate(2, 5).is_err());
    assert!(template.validate(3, 4).is_err());
    let mut bad = template.clone();
    bad.public_template[2] = ExecPublicWordV0::StatementLow;
    assert!(bad.validate(3, 5).is_err());
  }
}
