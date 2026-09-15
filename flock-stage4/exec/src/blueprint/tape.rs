//! Symbolic transcript construction. This records instructions and addresses
//! only: there is no sponge state, field value, nonce, proof, or verification.

use super::algebra::Addresses;
use crate::replay::Stage4TranscriptOpV1 as Op;
use anyhow::Result;
use ix_stage4_trace::{F256IndexPairV1, F256LigeritoMessageV1};

pub(super) struct Tape {
  pub(super) ops: Vec<Op>,
  pub(super) address: Addresses,
  pub(super) payload_lengths: Vec<usize>,
}

impl Tape {
  pub(super) fn new() -> Self {
    Self {
      ops: Vec::new(),
      address: Addresses { observed: 0, challenges: 0 },
      payload_lengths: Vec::new(),
    }
  }
  pub(super) fn label(&mut self, label: &[u8]) {
    self.ops.push(Op::Label(label.to_vec()));
  }
  pub(super) fn bytes(&mut self, length: usize) -> u64 {
    let index = self.payload_lengths.len() as u64;
    self.payload_lengths.push(length);
    self.ops.push(Op::ObserveBytes(length as u64));
    index
  }
  pub(super) fn observe(&mut self) -> u64 {
    self.ops.push(Op::ObserveScalar);
    self.address.observe_index()
  }
  pub(super) fn observe_slice(&mut self, count: usize) -> Vec<u64> {
    self.ops.push(Op::ObserveSlice(count as u64));
    (0..count).map(|_| self.address.observe_index()).collect()
  }
  // Some(0) is deliberately distinct from None. Inner Ligerito emits fused
  // PoW even at zero bits; several outer PIOPs omit the nonce when disabled.
  fn pow(&mut self, bits: Option<u32>) {
    if let Some(bits) = bits {
      self.ops.push(Op::Pow { bits });
      self.payload_lengths.push(8);
    }
  }
  pub(super) fn squeeze(&mut self, bits: Option<u32>) -> u64 {
    self.pow(bits);
    self.ops.push(Op::SqueezeScalar);
    self.address.challenge_index()
  }
  pub(super) fn squeeze_slice(
    &mut self,
    count: usize,
    bits: Option<u32>,
  ) -> Vec<u64> {
    self.pow(bits);
    self.ops.push(Op::SqueezeSlice(count as u64));
    (0..count).map(|_| self.address.challenge_index()).collect()
  }
  pub(super) fn message(&mut self) -> F256LigeritoMessageV1 {
    let u0 = self.observe_slice(2);
    let u2 = self.observe_slice(2);
    F256LigeritoMessageV1 {
      u_0: F256IndexPairV1 { c0: u0[0], c1: u0[1] },
      u_2: F256IndexPairV1 { c0: u2[0], c1: u2[1] },
    }
  }
  pub(super) fn fork(
    &mut self,
    label: &[u8],
    body: impl FnOnce(&mut Self) -> Result<()>,
  ) -> Result<u64> {
    self.squeeze(None);
    self.squeeze(None);
    let mut child = Self {
      ops: Vec::new(),
      address: self.address,
      payload_lengths: self.payload_lengths.clone(),
    };
    child.observe();
    child.observe();
    body(&mut child)?;
    child.squeeze(None);
    child.squeeze(None);
    let index =
      self.ops.iter().filter(|op| matches!(op, Op::Forked { .. })).count();
    self.address = child.address;
    self.payload_lengths = child.payload_lengths;
    self.ops.push(Op::Forked { label: label.to_vec(), ops: child.ops });
    Ok(index as u64)
  }
  pub(super) fn merge(&mut self, fork: u64) {
    self.ops.push(Op::Merge { fork });
    self.observe();
    self.observe();
  }
}

pub(super) fn nonzero(bits: u32) -> Option<u32> {
  (bits != 0).then_some(bits)
}

pub(super) fn pow2(bits: usize) -> Result<usize> {
  1usize
    .checked_shl(u32::try_from(bits)?)
    .ok_or_else(|| anyhow::anyhow!("transcript geometry exponent"))
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn absent_pow_zero_bit_pow_and_slice_width_remain_distinct() {
    let mut plain = Tape::new();
    let mut zero_pow = Tape::new();
    let mut vector = Tape::new();
    assert_eq!(plain.squeeze(None), 0);
    assert_eq!(zero_pow.squeeze(Some(0)), 0);
    assert_eq!(vector.squeeze_slice(1, None), [0]);
    assert_eq!(plain.address, zero_pow.address);
    assert_eq!(plain.address, vector.address);
    assert_ne!(plain.ops, zero_pow.ops);
    assert_ne!(plain.ops, vector.ops);
    assert_eq!(zero_pow.ops, [Op::Pow { bits: 0 }, Op::SqueezeScalar]);
    assert_eq!(zero_pow.payload_lengths, [8]);
    assert!(plain.payload_lengths.is_empty());
    assert!(vector.payload_lengths.is_empty());
  }

  #[test]
  fn fork_indices_are_inline_but_merge_is_at_parent_continuation() {
    let mut tape = Tape::new();
    tape.bytes(3);
    assert_eq!(tape.observe(), 0);
    let fork = tape
      .fork(b"test-child", |child| {
        assert_eq!(child.address, Addresses { observed: 3, challenges: 2 });
        assert_eq!(child.squeeze_slice(2, Some(0)), [2, 3]);
        assert_eq!(child.observe_slice(3), [3, 4, 5]);
        Ok(())
      })
      .unwrap();
    assert_eq!(fork, 0);
    assert_eq!(tape.address, Addresses { observed: 6, challenges: 6 });
    assert_eq!(tape.observe(), 6);
    assert_eq!(tape.squeeze(None), 6);
    tape.merge(fork);
    assert_eq!(tape.address, Addresses { observed: 9, challenges: 7 });
    assert_eq!(tape.payload_lengths, [3, 8]);
    assert_eq!(
      &tape.ops[7..],
      [Op::Merge { fork: 0 }, Op::ObserveScalar, Op::ObserveScalar]
    );
    let Op::Forked { label, ops } = &tape.ops[4] else {
      panic!("missing child")
    };
    assert_eq!(label, b"test-child");
    assert_eq!(
      ops,
      &[
        Op::ObserveScalar,
        Op::ObserveScalar,
        Op::Pow { bits: 0 },
        Op::SqueezeSlice(2),
        Op::ObserveSlice(3),
        Op::SqueezeScalar,
        Op::SqueezeScalar,
      ]
    );
  }

  #[test]
  fn extension_messages_are_two_coordinate_vector_observations() {
    let mut tape = Tape::new();
    assert_eq!(
      tape.message(),
      F256LigeritoMessageV1 {
        u_0: F256IndexPairV1 { c0: 0, c1: 1 },
        u_2: F256IndexPairV1 { c0: 2, c1: 3 },
      }
    );
    assert_eq!(tape.ops, [Op::ObserveSlice(2), Op::ObserveSlice(2)]);
    assert_eq!(tape.squeeze_slice(2, None), [0, 1]);
    assert_eq!(tape.ops.last(), Some(&Op::SqueezeSlice(2)));
  }
}
