//! Untrusted streaming trace advice. Repeated accesses use a native overlay;
//! authentication paths are computed once per touched cell at batch commit.
//! Circuit consumers must supply their own address/flag/value wires to check.
use super::{MemoryLogSlots, PAD, READ, SEAL, SEED, WRITE};
use crate::ixby::auth_memory::{
  MemoryDepth, MemoryOpening, SparseMemory,
  multi::{MultiAdvice, MultiCapacity},
};
use anyhow::{Result, ensure};
use flock_prover::field::F128;
use std::collections::{BTreeMap, BTreeSet};

/// Exact parent count for the same smallest-unused-address padding used at
/// commit. Sorted neighboring leaves contribute one new parent at each level
/// below their first common ancestor. A dense padding prefix is counted by
/// its occupied nodes per level, without constructing every path.
fn shared_parent_count(
  depth: MemoryDepth,
  mut addresses: Vec<u64>,
  leaves: usize,
) -> Option<usize> {
  addresses.sort_unstable();
  addresses.dedup();
  if addresses.len() > leaves || addresses.iter().any(|&a| !depth.admits(a)) {
    return None;
  }
  let mut missing = u64::try_from(leaves - addresses.len()).ok()?;
  let mut padding_end = 0u64;
  for &address in &addresses {
    if missing == 0 {
      break;
    }
    let gap = address.checked_sub(padding_end)?;
    if gap >= missing {
      break;
    }
    missing -= gap;
    padding_end = address.checked_add(1)?;
  }
  padding_end = padding_end.checked_add(missing)?;
  if padding_end != 0 && !depth.admits(padding_end - 1) {
    return None;
  }
  let mut parents = 0usize;
  if padding_end != 0 {
    for level in 1..=depth.bits() {
      let count =
        (padding_end - 1).checked_shr(u32::try_from(level).ok()?).unwrap_or(0)
          + 1;
      parents = parents.checked_add(usize::try_from(count).ok()?)?;
    }
  }
  let mut previous = padding_end.checked_sub(1);
  for &address in addresses.iter().filter(|&&a| a >= padding_end) {
    let contribution = if let Some(before) = previous {
      usize::try_from((before ^ address).checked_ilog2()?).ok()?
    } else {
      depth.bits()
    };
    parents = parents.checked_add(contribution)?;
    previous = Some(address);
  }
  Some(parents)
}

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
  fn ordered_switches(&self) -> Result<Vec<F128>> {
    let order = (0..self.accesses.len())
      .map(|index| {
        // The general timed helper uses clock*32+ordinal+1. This packs the
        // fixed chronological sequence into those same exact integer times.
        Some((index, index as u64 / 32, (index % 32) as u8))
      })
      .collect::<Vec<_>>();
    self.timed_switches(&order)
  }
  pub fn boundary_words(&self) -> Vec<F128> {
    let mut words = Vec::new();
    for boundary in &self.boundaries {
      words.extend(boundary.opening.words());
      words.extend(boundary.final_value);
    }
    words
  }
  pub fn private_boundary_words(&self) -> Vec<F128> {
    let mut words = self.boundary_words();
    words.extend(&self.switches);
    words
  }
  /// Arrange chronological native accesses in a fixed class's grouped row
  /// order. `None` is an inactive request. The circuit independently derives
  /// each timestamp from the same clock used by its state transition.
  pub fn timed_switches(
    &self,
    order: &[Option<(usize, u64, u8)>],
  ) -> Result<Vec<F128>> {
    let mut seen = vec![false; self.accesses.len()];
    let padding =
      [F128::ZERO, F128::ZERO, F128::new(PAD, 0), F128::ZERO, F128::ZERO];
    let mut records =
      Vec::with_capacity(order.len() + self.boundaries.len() * 2);
    for request in order {
      if let Some((index, clock, ordinal)) = *request {
        ensure!(index < seen.len() && !seen[index], "timed access index");
        ensure!(clock < (1u64 << 59) - 1 && ordinal < 32, "timed access clock");
        seen[index] = true;
        let access = self.accesses[index];
        records.push([
          F128::new(access.address, 0),
          F128::new(clock * 32 + u64::from(ordinal) + 1, 0),
          F128::new(if access.write { WRITE } else { READ }, 0),
          access.value[0],
          access.value[1],
        ]);
      } else {
        records.push(padding);
      }
    }
    ensure!(seen.iter().all(|&v| v), "missing timed memory access");
    for boundary in &self.boundaries {
      records.push([
        F128::new(boundary.opening.address, 0),
        F128::ZERO,
        F128::new(SEED, 0),
        boundary.opening.value[0],
        boundary.opening.value[1],
      ]);
      records.push([
        F128::new(boundary.opening.address, 0),
        F128::new(u64::MAX, 0),
        F128::new(SEAL, 0),
        boundary.final_value[0],
        boundary.final_value[1],
      ]);
    }
    let plan = MemoryLogSlots::plan(order.len(), self.boundaries.len())?;
    records.resize(plan.lanes(), padding);
    let mut sorted = (0..plan.lanes()).collect::<Vec<_>>();
    sorted.sort_by_key(|&i| {
      (records[i][2].lo == PAD, records[i][0].lo, records[i][1].lo)
    });
    let mut destination = vec![0; plan.lanes()];
    for (to, from) in sorted.into_iter().enumerate() {
      destination[from] = to;
    }
    plan.route(&destination)
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
  /// Distinct cells after a proposed step, without modifying the trace.
  pub fn prospective_cells(&self, accesses: &[AccessAdvice]) -> usize {
    self.current.len()
      + accesses
        .iter()
        .map(|a| a.address)
        .filter(|a| !self.current.contains_key(a))
        .collect::<BTreeSet<_>>()
        .len()
  }
  /// Quotas are setup policy; this only decides when native advice should
  /// stop. Every parent and leaf is independently checked by the proof.
  pub fn fits_shared(
    &self,
    accesses: &[AccessAdvice],
    capacity: MultiCapacity,
  ) -> bool {
    let addresses = self
      .current
      .keys()
      .copied()
      .chain(accesses.iter().map(|a| a.address))
      .collect::<Vec<_>>();
    shared_parent_count(self.memory.depth(), addresses, capacity.leaves)
      .is_some_and(|parents| parents <= capacity.parents)
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
    self.finish_padded(0)
  }
  fn pad(&mut self, minimum_cells: usize) -> Result<()> {
    let mut candidate = 0;
    while self.current.len() < minimum_cells {
      if !self.current.contains_key(&candidate) {
        let value = self.memory.value(candidate)?;
        self.current.insert(candidate, value);
      }
      candidate += 1;
    }
    Ok(())
  }
  pub fn finish_shared(
    mut self,
    capacity: MultiCapacity,
  ) -> Result<(MemoryBatchAdvice, MultiAdvice)> {
    ensure!(self.fits_shared(&[], capacity), "shared memory batch quota");
    self.pad(capacity.leaves)?;
    // Check the fixed audit capacity before changing the backing memory.
    MemoryLogSlots::plan(self.accesses.len(), self.current.len())?;
    let update = self.memory.replace_many(self.current)?;
    let tree = MultiAdvice::new(capacity, &update)?;
    let mut memory = MemoryBatchAdvice {
      initial_root: update.initial_root,
      final_root: update.final_root,
      accesses: self.accesses,
      boundaries: update
        .leaves
        .iter()
        .map(|leaf| BoundaryAdvice {
          opening: MemoryOpening {
            address: leaf.address,
            value: leaf.old,
            siblings: Vec::new(),
          },
          final_value: leaf.new,
        })
        .collect(),
      switches: Vec::new(),
    };
    memory.switches = memory.ordered_switches()?;
    Ok((memory, tree))
  }
  /// Fixed factories may authenticate additional untouched cells to fill a
  /// public boundary quota. Their seed and seal values must still match.
  pub fn finish_padded(
    mut self,
    minimum_cells: usize,
  ) -> Result<MemoryBatchAdvice> {
    self.pad(minimum_cells)?;
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

#[cfg(test)]
mod quota_tests {
  use super::*;
  fn reference(
    depth: MemoryDepth,
    addresses: &[u64],
    leaves: usize,
  ) -> Option<usize> {
    let mut addresses = addresses.iter().copied().collect::<BTreeSet<_>>();
    if addresses.len() > leaves {
      return None;
    }
    let mut candidate = 0;
    while addresses.len() < leaves {
      if !depth.admits(candidate) {
        return None;
      }
      addresses.insert(candidate);
      candidate += 1;
    }
    let mut parents = BTreeSet::new();
    for address in addresses {
      if !depth.admits(address) {
        return None;
      }
      for level in 1..=depth.bits() {
        parents.insert((
          level,
          address.checked_shr(u32::try_from(level).unwrap()).unwrap_or(0),
        ));
      }
    }
    Some(parents.len())
  }
  #[test]
  fn sorted_parent_count_matches_exact_paths_and_low_address_padding() {
    for depth in 0..=4 {
      let d = MemoryDepth::new(depth).unwrap();
      let domain = 1usize << depth;
      for mask in 0usize..1usize << domain {
        let addresses = (0..domain)
          .filter(|i| mask & (1 << i) != 0)
          .map(|i| u64::try_from(i).unwrap())
          .collect::<Vec<_>>();
        for leaves in [
          addresses.len().saturating_sub(1),
          addresses.len(),
          (addresses.len() + domain) / 2,
          domain,
          domain + 1,
        ] {
          assert_eq!(
            shared_parent_count(d, addresses.clone(), leaves),
            reference(d, &addresses, leaves),
            "depth={depth} leaves={leaves} addresses={addresses:?}"
          );
        }
      }
    }
    for depth in [8, 16, 40, 63, 64] {
      let d = MemoryDepth::new(depth).unwrap();
      let last =
        u64::MAX.checked_shr(u32::try_from(64 - depth).unwrap()).unwrap();
      for seed in 0u64..128 {
        let mut addresses = vec![0, 1, last, last / 2];
        let mut state = seed + 1;
        for _ in 0..32 {
          state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
          addresses.push(state & last);
        }
        addresses.extend_from_within(..4);
        addresses.reverse();
        for leaves in [0, 4, 16, 32, 64, 256, 512] {
          assert_eq!(
            shared_parent_count(d, addresses.clone(), leaves),
            reference(d, &addresses, leaves),
            "depth={depth} leaves={leaves} seed={seed}"
          );
        }
      }
      if depth < 64 {
        assert!(shared_parent_count(d, vec![1 << depth], 2).is_none());
      }
    }
  }
}
