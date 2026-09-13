//! Full unkeyed BLAKE3 over a private byte prefix in a setup-sized buffer.
//! Every block and tree node is emitted regardless of the private length.
//! Inactive blocks have constrained zero messages, while constrained record
//! selectors retain the last active chunk output and propagate absent right
//! subtrees. Odd physical subtrees are carried, not duplicated or zero-hashed.
//!
//! This builds a reusable byte-authentication component, not a decoder or an
//! IxBy execution proof. Its capacity is a setup limit, not logical guest RAM.

use super::{
  hash_control::{HashBlockGate, HashBlockSlot, RootParamsGate},
  select::{SelectWordsGate, SelectWordsSlot},
};
use crate::{
  hash::{Blake3Gate, IV, PARENT, pack_params, pack8},
  sizing::CircuitEmitter,
};
use anyhow::Result;
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

#[derive(Clone, Copy)]
struct Node {
  // Compression's seven input words, then its two chaining-value outputs.
  record: [Wire; 9],
  present: Wire,
}

pub struct BoundedBlake3 {
  compression_slot: SlotId,
  block_slot: HashBlockSlot,
  select_slot: SelectWordsSlot,
  root_slot: SlotId,
  block_gate: HashBlockGate,
  select_gate: SelectWordsGate,
  root_gate: RootParamsGate,
  zero: Wire,
  iv: [Wire; 2],
  parent_params: Wire,
}

impl BoundedBlake3 {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    capacity: usize,
  ) -> Result<Self> {
    let block_gate = HashBlockGate::new(nu, capacity)?;
    let select_gate = SelectWordsGate::new(nu, 9)?;
    let root_gate = RootParamsGate { nu };
    let compression_slot = b.slot(Blake3Gate { nu });
    let block_slot = HashBlockSlot::declare(b, block_gate.clone());
    let select_slot = SelectWordsSlot::declare(b, select_gate.clone());
    let root_slot = b.slot(root_gate);
    let zero = b.fixed_public_input(F128::ZERO);
    let iv = pack8(&IV).map(|word| b.fixed_public_input(word));
    let parent_params = b.fixed_public_input(pack_params(0, 64, PARENT));
    Ok(Self {
      compression_slot,
      block_slot,
      select_slot,
      root_slot,
      block_gate,
      select_gate,
      root_gate,
      zero,
      iv,
      parent_params,
    })
  }

  pub fn padded_words(&self) -> usize {
    self.block_gate.blocks() * 4
  }

  /// Another byte-capacity bound in the SAME emitter, sharing the existing
  /// compression, selector and ROOT tables. Only the length/padding table
  /// depends on byte capacity. This prevents commitment-chain wiring from
  /// duplicating the large BLAKE3 table for each domain.
  pub fn sharing_primitives(
    &self,
    b: &mut impl CircuitEmitter,
    capacity: usize,
  ) -> Result<Self> {
    let block_gate = HashBlockGate::new(self.root_gate.nu, capacity)?;
    let block_slot = HashBlockSlot::declare(b, block_gate.clone());
    Ok(Self {
      block_slot,
      block_gate,
      compression_slot: self.compression_slot,
      select_slot: self.select_slot,
      root_slot: self.root_slot,
      select_gate: self.select_gate.clone(),
      root_gate: self.root_gate,
      zero: self.zero,
      iv: self.iv,
      parent_params: self.parent_params,
    })
  }
  pub fn compression_slot(&self) -> SlotId {
    self.compression_slot
  }
  pub fn block_slot(&self) -> SlotId {
    self.block_slot.slot()
  }
  pub fn select_slot(&self) -> SlotId {
    self.select_slot.slot()
  }
  pub fn root_slot(&self) -> SlotId {
    self.root_slot
  }
  pub fn block_gate(&self) -> &HashBlockGate {
    &self.block_gate
  }
  pub fn select_gate(&self) -> &SelectWordsGate {
    &self.select_gate
  }
  pub fn root_gate(&self) -> &RootParamsGate {
    &self.root_gate
  }

  /// `length` is a canonical u32 wire. `words` is the entire fixed physical
  /// buffer, including the final block's unused bytes. The block gate checks
  /// both length <= capacity and zero padding. No byte advice is host-hashed.
  pub fn hash(
    &self,
    b: &mut impl CircuitEmitter,
    length: Wire,
    words: &[Wire],
  ) -> [Wire; 2] {
    assert_eq!(words.len(), self.padded_words(), "fixed hash buffer width");
    let mut nodes = Vec::with_capacity(words.len().div_ceil(64));
    for (chunk_index, chunk) in words.chunks(64).enumerate() {
      let mut cv = self.iv;
      let mut node = Node { record: [self.zero; 9], present: self.zero };
      for (local_index, message) in chunk.as_chunks::<4>().0.iter().enumerate()
      {
        let index = b.fixed_public_input(F128::new(
          (chunk_index * 16 + local_index) as u64,
          0,
        ));
        let (params, active) =
          self.block_slot.block(b, length, index, *message);
        let candidate = self.compress(b, cv, *message, params);
        cv = candidate[7..].try_into().unwrap();
        node.record = self
          .select_slot
          .select(b, active, &candidate, &node.record)
          .try_into()
          .unwrap();
        if local_index == 0 {
          node.present = active;
        }
      }
      nodes.push(node);
    }
    while nodes.len() > 1 {
      nodes = nodes
        .chunks(2)
        .map(|pair| {
          let left = pair[0];
          if pair.len() == 1 {
            return left;
          }
          let right = pair[1];
          let message =
            [left.record[7], left.record[8], right.record[7], right.record[8]];
          let candidate =
            self.compress(b, self.iv, message, self.parent_params);
          Node {
            record: self
              .select_slot
              .select(b, right.present, &candidate, &left.record)
              .try_into()
              .unwrap(),
            present: left.present,
          }
        })
        .collect();
    }
    // Chunk zero is always active, including for the empty message. Thus the
    // selected root Output exists; ROOT output counter is independently zero.
    let root = nodes[0].record;
    let params = b.gate(self.root_slot, &[root[6]])[0];
    let output = b.gate(
      self.compression_slot,
      &[root[0], root[1], root[2], root[3], root[4], root[5], params],
    );
    [output[0], output[1]]
  }

  fn compress(
    &self,
    b: &mut impl CircuitEmitter,
    cv: [Wire; 2],
    message: [Wire; 4],
    params: Wire,
  ) -> [Wire; 9] {
    let inputs =
      [cv[0], cv[1], message[0], message[1], message[2], message[3], params];
    let output = b.gate(self.compression_slot, &inputs);
    [
      inputs[0], inputs[1], inputs[2], inputs[3], inputs[4], inputs[5],
      inputs[6], output[0], output[1],
    ]
  }
}

#[cfg(test)]
pub(super) mod tests {
  use super::*;
  use crate::ixby::io::{InputLayout, LayoutEmitter, PublicLayout};
  use crate::{hash::pack_bytes, sizing::CountingEmitter};
  use flock_prover::circuit::builder::{CircuitShape, ShapeBuilder};

  pub(crate) fn emit(
    b: &mut impl CircuitEmitter,
    nu: usize,
    capacity: usize,
  ) -> (BoundedBlake3, InputLayout, PublicLayout) {
    let mut b = LayoutEmitter::new(b);
    let hash = BoundedBlake3::declare(&mut b, nu, capacity).unwrap();
    let length = b.input();
    let words: Vec<_> = (0..hash.padded_words()).map(|_| b.input()).collect();
    for output in hash.hash(&mut b, length, &words) {
      b.publish(output);
    }
    let (inputs, public) = b.finish();
    (hash, inputs, public)
  }

  pub(crate) fn setup(
    nu: usize,
    capacity: usize,
  ) -> (BoundedBlake3, InputLayout, PublicLayout, CircuitShape) {
    let mut b = ShapeBuilder::new(nu);
    let (hash, inputs, public) = emit(&mut b, nu, capacity);
    (hash, inputs, public, b.finish().unwrap())
  }

  pub(crate) fn private_input(capacity: usize, message: &[u8]) -> Vec<F128> {
    assert!(message.len() <= capacity);
    let mut bytes = vec![0; capacity.div_ceil(64).max(1) * 64];
    bytes[..message.len()].copy_from_slice(message);
    let mut input = vec![F128::new(message.len() as u64, 0)];
    input.extend(bytes.as_chunks::<16>().0.iter().map(|word| pack_bytes(word)));
    input
  }

  pub(crate) fn expected(message: &[u8]) -> [F128; 2] {
    let digest = ::blake3::hash(message);
    [pack_bytes(&digest.as_bytes()[..16]), pack_bytes(&digest.as_bytes()[16..])]
  }

  #[test]
  fn every_small_length_and_odd_tree_boundary_match_native_under_fixed_setup() {
    for capacity in [0, 1, 63, 64, 65, 128, 1024, 1025, 3073, 7169] {
      let (hash, inputs, public, shape) = setup(8, capacity);
      let identity = shape.circuit.digest();
      let lengths: Vec<_> = if capacity <= 128 {
        (0..=capacity).collect()
      } else {
        vec![
          0, 1, 63, 64, 65, 1023, 1024, 1025, 2047, 2048, 2049, 3072, 3073,
          4096, 4097, 5120, 6144, 6145, 7168, capacity,
        ]
      };
      for length in lengths.into_iter().filter(|length| *length <= capacity) {
        let message: Vec<_> =
          (0..length).map(|i| (i * 31 + i / 256 + 7) as u8).collect();
        let witness = shape.run(
          &inputs.assign(&private_input(capacity, &message)).unwrap(),
          &[],
        );
        assert_eq!(
          witness.public,
          public.instantiate(&expected(&message)).unwrap(),
          "capacity {capacity}, length {length}"
        );
        assert_eq!(shape.circuit.digest(), identity);
        assert_eq!(
          witness.rows::<HashBlockGate>(hash.block_slot()).len(),
          capacity.div_ceil(64).max(1)
        );
      }
    }
  }

  #[test]
  fn census_and_compiled_topology_match_without_any_message_values() {
    for capacity in [0usize, 65, 1025, 3073, 7169] {
      let mut count = CountingEmitter::new();
      let (_, counted_input, counted_public) = emit(&mut count, 3, capacity);
      let nu = count.required_nu(3).unwrap();
      let (hash, input, public, shape) = setup(nu, capacity);
      count.ensure_matches(&shape).unwrap();
      assert_eq!(input, counted_input);
      assert_eq!(public, counted_public);
      let blocks = capacity.div_ceil(64).max(1);
      let chunks = blocks.div_ceil(16);
      assert_eq!(
        shape.counts[shape.registry_slot(hash.compression_slot())],
        blocks + chunks
      );
      assert_eq!(shape.counts[shape.registry_slot(hash.block_slot())], blocks);
      assert_eq!(
        shape.counts[shape.registry_slot(hash.select_slot())],
        blocks + chunks - 1
      );
      assert_eq!(shape.counts[shape.registry_slot(hash.root_slot())], 1);
      let (_, again_input, again_public, again) = setup(nu, capacity);
      assert_eq!(shape.circuit.digest(), again.circuit.digest());
      assert_eq!(input, again_input);
      assert_eq!(public, again_public);
    }
  }
}
