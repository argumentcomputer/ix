use anyhow::{Result, ensure};
use flock_prover::field::F128;

/// Current complete-functional execution profile.
/// Limits are in original IXBF order. Physical Nat128, memory and instruction
/// capacities belong to the proving setup; this does not broaden those limits.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionalProfile {
  limits: [u128; 10],
  max_steps: u64,
}
impl FunctionalProfile {
  pub fn new(limits: [u128; 10], max_steps: u64) -> Result<Self> {
    for at in [3, 5, 7, 9] {
      ensure!(limits[at] <= u64::MAX as u128, "runtime profile limit width");
    }
    ensure!(limits[7] >= 128, "profile must admit physical Nat128 values");
    Ok(Self { limits, max_steps })
  }
  pub fn limits(&self) -> &[u128; 10] {
    &self.limits
  }
  pub fn max_steps(&self) -> u64 {
    self.max_steps
  }
  /// IXFP, profile revision 0, artifact format 1, semantics 2, ten u128
  /// little-endian limits, then the u64 fuel budget: exactly 184 bytes.
  pub fn encode(&self) -> [u8; 184] {
    let mut out = [0; 184];
    out[..4].copy_from_slice(b"IXFP");
    out[8..12].copy_from_slice(&1u32.to_le_bytes());
    out[12..16].copy_from_slice(
      &crate::ixby::ixbf::PROGRAM_SEMANTICS_VERSION.to_le_bytes(),
    );
    for (i, n) in self.limits.iter().enumerate() {
      out[16 + 16 * i..32 + 16 * i].copy_from_slice(&n.to_le_bytes());
    }
    out[176..].copy_from_slice(&self.max_steps.to_le_bytes());
    out
  }
  pub fn decode(bytes: &[u8]) -> Result<Self> {
    ensure!(
      bytes.len() == 184 && &bytes[..4] == b"IXFP",
      "functional profile encoding"
    );
    ensure!(
      bytes[4..8] == [0; 4]
        && bytes[8..12] == 1u32.to_le_bytes()
        && bytes[12..16]
          == crate::ixby::ixbf::PROGRAM_SEMANTICS_VERSION.to_le_bytes(),
      "functional profile revision"
    );
    let limits = std::array::from_fn(|i| {
      u128::from_le_bytes(bytes[16 + 16 * i..32 + 16 * i].try_into().unwrap())
    });
    Self::new(limits, u64::from_le_bytes(bytes[176..].try_into().unwrap()))
  }
  pub fn digest(&self) -> [F128; 2] {
    let mut message = b"IxBy/commit/v0\0\0".to_vec();
    message.extend(self.encode());
    digest(&message)
  }
  pub(super) fn words(&self) -> [F128; 11] {
    let mut out = [F128::ZERO; 11];
    for (v, n) in out.iter_mut().zip(self.limits) {
      *v = F128::new(n as u64, (n >> 64) as u64);
    }
    out[10] = F128::new(self.max_steps, 0);
    out
  }
}
pub(super) fn digest(bytes: &[u8]) -> [F128; 2] {
  let h = blake3::hash(bytes);
  [
    crate::hash::pack_bytes(&h.as_bytes()[..16]),
    crate::hash::pack_bytes(&h.as_bytes()[16..]),
  ]
}
