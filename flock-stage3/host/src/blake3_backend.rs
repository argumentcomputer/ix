//! Explicit setup-owned compression implementation choice. Both variants
//! implement the same raw BLAKE3 function; they do not promise key reuse.
//! This choice is never decoded from proof data or inferred from a guest.

use crate::{
  hash::Blake3Gate, packed_blake3::PackedBlake3, sizing::CircuitEmitter,
};
use anyhow::Result;
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  r1cs::BlockR1cs,
  r1cs_hashes::blake3,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Blake3Backend {
  /// Original pinned flattened compression table and implementation identity.
  LegacyOptionF,
  /// Ten reusable packed-word tables, an explicit backend/key upgrade.
  PackedWordsV0,
}

/// A read-only view is exposed by compiled hash components for their drivers.
/// Slots and fixed wires may only be shared within the same emitter.
#[derive(Clone)]
pub enum Blake3CompressionSlots {
  LegacyOptionF { slot: SlotId, nu: usize },
  PackedWordsV0(PackedBlake3),
}

impl Blake3CompressionSlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    backend: Blake3Backend,
  ) -> Result<Self> {
    Ok(match backend {
      Blake3Backend::LegacyOptionF => {
        Self::LegacyOptionF { slot: b.slot(Blake3Gate { nu }), nu }
      },
      Blake3Backend::PackedWordsV0 => {
        Self::PackedWordsV0(PackedBlake3::declare(b, nu)?)
      },
    })
  }

  pub fn backend(&self) -> Blake3Backend {
    match self {
      Self::LegacyOptionF { .. } => Blake3Backend::LegacyOptionF,
      Self::PackedWordsV0(_) => Blake3Backend::PackedWordsV0,
    }
  }

  pub fn tables(&self) -> Vec<(SlotId, BlockR1cs)> {
    match self {
      Self::LegacyOptionF { slot, nu } => {
        vec![(*slot, blake3::build_block_r1cs(*nu))]
      },
      Self::PackedWordsV0(packed) => {
        packed.gates().iter().map(|(gate, slot)| (*slot, gate.r1cs())).collect()
      },
    }
  }

  pub fn compress(
    &self,
    b: &mut impl CircuitEmitter,
    inputs: [Wire; 7],
  ) -> [Wire; 4] {
    match self {
      Self::LegacyOptionF { slot, .. } => {
        b.gate(*slot, &inputs).try_into().unwrap()
      },
      Self::PackedWordsV0(packed) => packed.compress(
        b,
        [inputs[0], inputs[1]],
        [inputs[2], inputs[3], inputs[4], inputs[5]],
        inputs[6],
      ),
    }
  }
}
