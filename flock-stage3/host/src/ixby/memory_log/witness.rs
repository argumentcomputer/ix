//! Untrusted streaming trace advice. Repeated accesses use a native overlay;
//! authentication paths are computed once per touched cell at batch commit.
//! Circuit consumers must supply their own address/flag/value wires to check.
use super::{MemoryLogSlots, PAD, READ, SEAL, SEED, WRITE};
use crate::ixby::auth_memory::{MemoryOpening, SparseMemory};
use anyhow::Result;
use flock_prover::field::F128;
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug)]
pub struct AccessAdvice {
  pub address: u64,
  pub write: bool,
  pub value: [F128; 2],
}
#[derive(Clone, Debug)]
pub struct BoundaryAdvice {
  pub opening: MemoryOpening,
  pub final_value: [F128; 2],
}
pub struct MemoryBatchAdvice {
  pub initial_root: [F128; 2],
  pub final_root: [F128; 2],
  pub accesses: Vec<AccessAdvice>,
  pub boundaries: Vec<BoundaryAdvice>,
  pub switches: Vec<F128>,
}
impl MemoryBatchAdvice {
  pub fn private_boundary_words(&self) -> Vec<F128> {
    let mut words = Vec::new();
    for boundary in &self.boundaries {
      words.extend(boundary.opening.words());
      words.extend(boundary.final_value);
    }
    words.extend(&self.switches);
    words
  }
}

pub struct MemoryBatch<'a> {
  memory: &'a mut SparseMemory,
  initial_root: [F128; 2],
  current: BTreeMap<u64, [F128; 2]>,
  accesses: Vec<AccessAdvice>,
}
impl<'a> MemoryBatch<'a> {
  pub fn new(memory: &'a mut SparseMemory) -> Self {
    let initial_root = memory.root();
    Self {
      memory,
      initial_root,
      current: BTreeMap::new(),
      accesses: Vec::new(),
    }
  }
  pub fn value(&self, address: u64) -> Result<[F128; 2]> {
    match self.current.get(&address) {
      Some(value) => Ok(*value),
      None => self.memory.value(address),
    }
  }
  pub fn read(&mut self, address: u64) -> Result<[F128; 2]> {
    let value = self.value(address)?;
    self.current.insert(address, value);
    self.accesses.push(AccessAdvice { address, write: false, value });
    Ok(value)
  }
  pub fn write(&mut self, address: u64, value: [F128; 2]) -> Result<()> {
    self.value(address)?; // Check the full address before changing the overlay.
    self.current.insert(address, value);
    self.accesses.push(AccessAdvice { address, write: true, value });
    Ok(())
  }
  pub fn finish(self) -> Result<MemoryBatchAdvice> {
    let plan = MemoryLogSlots::plan(self.accesses.len(), self.current.len())?;
    let mut records = self
      .accesses
      .iter()
      .enumerate()
      .map(|(i, a)| {
        [
          F128::new(a.address, 0),
          F128::new(i as u64 + 1, 0),
          F128::new(if a.write { WRITE } else { READ }, 0),
          a.value[0],
          a.value[1],
        ]
      })
      .collect::<Vec<_>>();
    let mut boundaries = Vec::with_capacity(self.current.len());
    for (address, final_value) in self.current {
      let opening = self.memory.replace(address, final_value)?;
      records.push([
        F128::new(address, 0),
        F128::ZERO,
        F128::new(SEED, 0),
        opening.value[0],
        opening.value[1],
      ]);
      records.push([
        F128::new(address, 0),
        F128::new(u64::MAX, 0),
        F128::new(SEAL, 0),
        final_value[0],
        final_value[1],
      ]);
      boundaries.push(BoundaryAdvice { opening, final_value });
    }
    records.resize(
      plan.lanes(),
      [F128::ZERO, F128::ZERO, F128::new(PAD, 0), F128::ZERO, F128::ZERO],
    );
    let mut order = (0..plan.lanes()).collect::<Vec<_>>();
    order.sort_by_key(|&i| {
      (records[i][2].lo == PAD, records[i][0].lo, records[i][1].lo)
    });
    let mut destination = vec![0; plan.lanes()];
    for (output, input) in order.into_iter().enumerate() {
      destination[input] = output;
    }
    Ok(MemoryBatchAdvice {
      initial_root: self.initial_root,
      final_root: self.memory.root(),
      accesses: self.accesses,
      boundaries,
      switches: plan.route(&destination)?,
    })
  }
}
