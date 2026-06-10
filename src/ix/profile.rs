//! Out-of-circuit kernel profile (`.ixesp`) — the cost + delta-graph hints
//! that drive the sharding strategy (see `plans/sharding.md`).
//!
//! A profile is computed by running the Rust kernel **out of circuit** over an
//! environment and recording, per *block*:
//!
//! - `heartbeats`: total recursive fuel consumed checking the block's members
//!   (the balance metric for partitioning),
//! - `serialized_size`: the block's serialized byte length (the ingress-cost
//!   metric — net weight in the partition hypergraph),
//! - `const_count`: number of constants in the block,
//! - the set of *other blocks whose definition bodies the block delta-unfolds*
//!   (the delta edges — the cost graph the partitioner cuts on).
//!
//! A "block" is the ingress unit: a `Muts` mutual block or a standalone
//! constant. Projection constants (`*Prj { block, .. }`) are attributed to
//! their `block` address; everything else is its own block.
//!
//! The delta graph is stored in compressed-sparse-row (CSR) form keyed by
//! stable block ids (assigned by sorting block addresses), and the on-disk
//! `.ixesp` format is an explicit little-endian binary so it does not depend
//! on the optional `serde`/`bincode` feature.

// Block ids and counts are `u32` (envs are far below the limit); the binary
// decoder maps decode failures to a single message. Both are intentional here.
#![allow(clippy::cast_possible_truncation, clippy::map_err_ignore)]

use rustc_hash::{FxHashMap, FxHashSet};

use crate::ix::address::Address;

/// Magic bytes at the head of every `.ixesp` file.
const MAGIC: &[u8; 8] = b"IXESP\0\0\0";
/// On-disk format version. Bump on any incompatible layout change.
const VERSION: u32 = 1;

/// Per-block recorded statistics.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockEntry {
  /// Content address of the block (a `Muts` block or a standalone constant).
  pub addr: Address,
  /// Total recursive fuel (heartbeats) consumed checking this block's members.
  pub heartbeats: u64,
  /// Serialized byte length of the block (ingress cost / net weight).
  pub serialized_size: u32,
  /// Number of constants in the block (1 for standalone constants).
  pub const_count: u32,
}

/// A recorded kernel profile over an environment.
///
/// Blocks are indexed by stable id `0..num_blocks`. The delta graph is stored
/// in CSR form: `producers(c)` are the block ids whose definition bodies block
/// `c` delta-unfolds (the "consumer → producer" direction). Self-edges are
/// dropped; producer lists are sorted and deduplicated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockProfile {
  blocks: Vec<BlockEntry>,
  /// CSR row offsets into `delta_col`, length `blocks.len() + 1`.
  delta_row: Vec<usize>,
  /// CSR column indices: producer block ids, grouped by consumer.
  delta_col: Vec<u32>,
}

impl BlockProfile {
  /// Number of blocks (vertices).
  pub fn num_blocks(&self) -> usize {
    self.blocks.len()
  }

  /// Number of delta edges (consumer → producer pairs).
  pub fn num_edges(&self) -> usize {
    self.delta_col.len()
  }

  /// The block entries, indexed by block id.
  pub fn blocks(&self) -> &[BlockEntry] {
    &self.blocks
  }

  /// The entry for block id `i`.
  pub fn block(&self, i: u32) -> &BlockEntry {
    &self.blocks[i as usize]
  }

  /// Producer block ids unfolded by consumer block `c` (sorted, deduped, no
  /// self-edges).
  pub fn producers(&self, c: u32) -> &[u32] {
    let lo = self.delta_row[c as usize];
    let hi = self.delta_row[c as usize + 1];
    &self.delta_col[lo..hi]
  }

  /// Build the reverse delta adjacency: for each producer block, the sorted set
  /// of consumer blocks that unfold it. This is the natural form for the
  /// partition hypergraph, where `net(p) = {p} ∪ consumers_of(p)`.
  pub fn consumers_csr(&self) -> (Vec<usize>, Vec<u32>) {
    let n = self.num_blocks();
    let mut counts = vec![0usize; n + 1];
    for &p in &self.delta_col {
      counts[p as usize + 1] += 1;
    }
    for i in 0..n {
      counts[i + 1] += counts[i];
    }
    let row = counts.clone();
    let mut col = vec![0u32; self.delta_col.len()];
    let mut cursor = counts;
    for c in 0..n as u32 {
      for &p in self.producers(c) {
        let slot = cursor[p as usize];
        col[slot] = c;
        cursor[p as usize] += 1;
      }
    }
    (row, col)
  }

  /// Total heartbeats across all blocks.
  pub fn total_heartbeats(&self) -> u128 {
    self.blocks.iter().map(|b| u128::from(b.heartbeats)).sum()
  }

  /// Serialize to the `.ixesp` binary format.
  pub fn to_bytes(&self) -> Vec<u8> {
    let n = self.blocks.len();
    let mut out = Vec::with_capacity(
      8 + 4 + 4 + n * 48 + 8 + (n + 1) * 8 + self.delta_col.len() * 4,
    );
    out.extend_from_slice(MAGIC);
    out.extend_from_slice(&VERSION.to_le_bytes());
    out.extend_from_slice(&(n as u32).to_le_bytes());
    for b in &self.blocks {
      out.extend_from_slice(b.addr.as_bytes());
      out.extend_from_slice(&b.heartbeats.to_le_bytes());
      out.extend_from_slice(&b.serialized_size.to_le_bytes());
      out.extend_from_slice(&b.const_count.to_le_bytes());
    }
    out.extend_from_slice(&(self.delta_col.len() as u64).to_le_bytes());
    // CSR row offsets (n+1 entries) as u64.
    for &off in &self.delta_row {
      out.extend_from_slice(&(off as u64).to_le_bytes());
    }
    for &p in &self.delta_col {
      out.extend_from_slice(&p.to_le_bytes());
    }
    out
  }

  /// Deserialize from the `.ixesp` binary format.
  pub fn from_bytes(bytes: &[u8]) -> Result<Self, ProfileError> {
    let mut r = Reader::new(bytes);
    let magic = r.take(8)?;
    if magic != MAGIC {
      return Err(ProfileError::BadMagic);
    }
    let version = r.u32()?;
    if version != VERSION {
      return Err(ProfileError::BadVersion(version));
    }
    let n = r.u32()? as usize;
    // Each block entry consumes exactly 48 bytes (32 addr + 8 + 4 + 4).
    let mut blocks = Vec::with_capacity(n.min(r.remaining() / 48));
    for _ in 0..n {
      let addr = Address::from_slice(r.take(32)?)
        .map_err(|_| ProfileError::Truncated)?;
      let heartbeats = r.u64()?;
      let serialized_size = r.u32()?;
      let const_count = r.u32()?;
      blocks.push(BlockEntry {
        addr,
        heartbeats,
        serialized_size,
        const_count,
      });
    }
    let num_edges = r.u64()? as usize;
    let mut delta_row = Vec::with_capacity((n + 1).min(r.remaining() / 8 + 1));
    for _ in 0..n + 1 {
      delta_row.push(r.u64()? as usize);
    }
    let mut delta_col = Vec::with_capacity(num_edges.min(r.remaining() / 4));
    for _ in 0..num_edges {
      delta_col.push(r.u32()?);
    }
    // Structural validation: monotone offsets bounded by edge count, in-range ids.
    if delta_row.len() != n + 1
      || delta_row.first() != Some(&0)
      || delta_row.last() != Some(&num_edges)
    {
      return Err(ProfileError::Corrupt);
    }
    for w in delta_row.windows(2) {
      if w[0] > w[1] {
        return Err(ProfileError::Corrupt);
      }
    }
    for &p in &delta_col {
      if p as usize >= n {
        return Err(ProfileError::Corrupt);
      }
    }
    Ok(BlockProfile { blocks, delta_row, delta_col })
  }
}

/// Errors from decoding a `.ixesp` file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProfileError {
  BadMagic,
  BadVersion(u32),
  Truncated,
  Corrupt,
}

impl std::fmt::Display for ProfileError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      ProfileError::BadMagic => write!(f, "not an .ixesp file (bad magic)"),
      ProfileError::BadVersion(v) => {
        write!(f, "unsupported .ixesp version {v}")
      },
      ProfileError::Truncated => write!(f, "truncated .ixesp file"),
      ProfileError::Corrupt => write!(f, "corrupt .ixesp file"),
    }
  }
}

impl std::error::Error for ProfileError {}

/// Minimal little-endian byte reader with bounds checking.
struct Reader<'a> {
  buf: &'a [u8],
  pos: usize,
}

impl<'a> Reader<'a> {
  fn new(buf: &'a [u8]) -> Self {
    Reader { buf, pos: 0 }
  }
  fn take(&mut self, n: usize) -> Result<&'a [u8], ProfileError> {
    let end = self.pos.checked_add(n).ok_or(ProfileError::Truncated)?;
    if end > self.buf.len() {
      return Err(ProfileError::Truncated);
    }
    let s = &self.buf[self.pos..end];
    self.pos = end;
    Ok(s)
  }
  /// Bytes left in the buffer. Used to cap `Vec` pre-allocations against
  /// untrusted counts: a count whose elements cannot fit in the remaining
  /// bytes is necessarily malformed, so allocating beyond it only serves
  /// an attacker.
  fn remaining(&self) -> usize {
    self.buf.len() - self.pos
  }
  fn u32(&mut self) -> Result<u32, ProfileError> {
    Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
  }
  fn u64(&mut self) -> Result<u64, ProfileError> {
    Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
  }
}

/// Accumulates block-level statistics and delta edges (keyed by address), then
/// freezes into a [`BlockProfile`] with stable, address-sorted block ids.
///
/// Phase A (the kernel recorder) feeds this with one `block(..)` per checked
/// block and one `delta_edge(consumer, producer)` per recorded cross-block
/// unfold. The builder is the merge point for per-worker accumulators: calling
/// `block`/`delta_edge` is commutative and idempotent w.r.t. edge sets, so
/// merge order does not affect the result.
#[derive(Default)]
pub struct ProfileBuilder {
  blocks: FxHashMap<Address, Accum>,
}

#[derive(Default)]
struct Accum {
  heartbeats: u64,
  serialized_size: u32,
  const_count: u32,
  producers: FxHashSet<Address>,
}

impl ProfileBuilder {
  pub fn new() -> Self {
    Self::default()
  }

  /// Record (or accumulate into) a block's statistics. Heartbeats and
  /// const_count accumulate additively; serialized_size is set (idempotent for
  /// a fixed block).
  pub fn block(
    &mut self,
    addr: Address,
    heartbeats: u64,
    serialized_size: u32,
    const_count: u32,
  ) {
    let e = self.blocks.entry(addr).or_default();
    e.heartbeats = e.heartbeats.saturating_add(heartbeats);
    e.serialized_size = serialized_size;
    e.const_count = e.const_count.saturating_add(const_count);
  }

  /// Record that `consumer` delta-unfolds the body of `producer`. Self-edges
  /// are ignored. Ensures both endpoints exist as blocks (with zeroed stats if
  /// not yet seen) so the graph is well-formed even if a producer is only ever
  /// referenced, never directly checked.
  pub fn delta_edge(&mut self, consumer: Address, producer: Address) {
    if consumer == producer {
      return;
    }
    self.blocks.entry(producer.clone()).or_default();
    self.blocks.entry(consumer).or_default().producers.insert(producer);
  }

  /// Freeze into an immutable [`BlockProfile`]. Block ids are assigned by
  /// sorting addresses, so the result is deterministic regardless of insertion
  /// order.
  pub fn finish(self) -> BlockProfile {
    let mut addrs: Vec<Address> = self.blocks.keys().cloned().collect();
    addrs.sort();
    let id_of: FxHashMap<Address, u32> =
      addrs.iter().enumerate().map(|(i, a)| (a.clone(), i as u32)).collect();

    let mut blocks = Vec::with_capacity(addrs.len());
    let mut delta_row = Vec::with_capacity(addrs.len() + 1);
    let mut delta_col = Vec::new();
    delta_row.push(0usize);

    for addr in &addrs {
      let a = &self.blocks[addr];
      blocks.push(BlockEntry {
        addr: addr.clone(),
        heartbeats: a.heartbeats,
        serialized_size: a.serialized_size,
        const_count: a.const_count,
      });
      let mut prods: Vec<u32> = a.producers.iter().map(|p| id_of[p]).collect();
      prods.sort_unstable();
      prods.dedup();
      delta_col.extend_from_slice(&prods);
      delta_row.push(delta_col.len());
    }

    BlockProfile { blocks, delta_row, delta_col }
  }
}

/// Per-worker raw accumulator filled by the out-of-circuit kernel recorder: for
/// each *constant* (by address) checked on this worker, its heartbeats and the
/// set of constant addresses whose definition bodies it delta-unfolded. The
/// env-aware layer later maps these constant addresses to their home blocks and
/// attaches serialized sizes to produce a [`BlockProfile`].
#[derive(Default, Debug)]
pub struct ProfileSink {
  /// When true, the kernel clears its reduction-memo caches between constants
  /// so recording is sound (no unfolds skipped by cross-constant cache hits)
  /// and heartbeats reflect the no-cross-constant-memo in-circuit cost.
  pub isolate: bool,
  /// Consumer constant address → record.
  pub records: FxHashMap<Address, ConstRecord>,
}

/// One constant's recorded statistics (pre block-aggregation).
#[derive(Default, Debug, Clone)]
pub struct ConstRecord {
  /// Recursive fuel (heartbeats) consumed checking this constant.
  pub fuel: u64,
  /// Constant addresses whose bodies were delta-unfolded during the check.
  pub producers: FxHashSet<Address>,
}

impl ProfileSink {
  pub fn new(isolate: bool) -> Self {
    ProfileSink { isolate, records: FxHashMap::default() }
  }

  /// Accumulate one constant's record (additive in fuel, set-union in
  /// producers) so repeated flushes for the same constant combine correctly.
  pub fn record(
    &mut self,
    consumer: Address,
    fuel: u64,
    producers: impl IntoIterator<Item = Address>,
  ) {
    let rec = self.records.entry(consumer).or_default();
    rec.fuel = rec.fuel.saturating_add(fuel);
    rec.producers.extend(producers);
  }

  /// Merge another worker's sink into this one (order-independent).
  pub fn merge(&mut self, other: ProfileSink) {
    for (addr, rec) in other.records {
      let e = self.records.entry(addr).or_default();
      e.fuel = e.fuel.saturating_add(rec.fuel);
      e.producers.extend(rec.producers);
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn addr(byte: u8) -> Address {
    Address::from_slice(&[byte; 32]).unwrap()
  }

  fn sample() -> BlockProfile {
    let mut b = ProfileBuilder::new();
    // Three blocks a<b<c by address ordering.
    b.block(addr(1), 100, 10, 1);
    b.block(addr(2), 200, 20, 3);
    b.block(addr(3), 300, 30, 1);
    // a unfolds b and c; c unfolds b; self-edge ignored.
    b.delta_edge(addr(1), addr(2));
    b.delta_edge(addr(1), addr(3));
    b.delta_edge(addr(3), addr(2));
    b.delta_edge(addr(2), addr(2));
    b.finish()
  }

  #[test]
  fn builder_assigns_sorted_ids_and_stats() {
    let p = sample();
    assert_eq!(p.num_blocks(), 3);
    assert_eq!(p.block(0).addr, addr(1));
    assert_eq!(p.block(0).heartbeats, 100);
    assert_eq!(p.block(1).heartbeats, 200);
    assert_eq!(p.block(1).const_count, 3);
    assert_eq!(p.total_heartbeats(), 600);
  }

  #[test]
  fn producers_sorted_and_self_edge_dropped() {
    let p = sample();
    // block 0 (addr 1) unfolds blocks 1 and 2.
    assert_eq!(p.producers(0), &[1, 2]);
    // block 1 (addr 2): self-edge dropped → no producers.
    assert_eq!(p.producers(1), &[]);
    // block 2 (addr 3) unfolds block 1.
    assert_eq!(p.producers(2), &[1]);
    assert_eq!(p.num_edges(), 3);
  }

  #[test]
  fn consumers_reverse_adjacency() {
    let p = sample();
    let (row, col) = p.consumers_csr();
    // block 1 (addr 2) is unfolded by blocks 0 and 2.
    let lo = row[1];
    let hi = row[2];
    let mut got: Vec<u32> = col[lo..hi].to_vec();
    got.sort_unstable();
    assert_eq!(got, vec![0, 2]);
  }

  #[test]
  fn roundtrip_serialization() {
    let p = sample();
    let bytes = p.to_bytes();
    let q = BlockProfile::from_bytes(&bytes).unwrap();
    assert_eq!(p, q);
  }

  #[test]
  fn rejects_bad_magic_and_truncation() {
    assert_eq!(
      BlockProfile::from_bytes(b"nope").unwrap_err(),
      ProfileError::Truncated
    );
    let mut bytes = sample().to_bytes();
    bytes[0] = b'X';
    assert_eq!(
      BlockProfile::from_bytes(&bytes).unwrap_err(),
      ProfileError::BadMagic
    );
  }

  #[test]
  fn merge_order_independent() {
    // Build the same logical profile with edges added in a different order and
    // via separate builders merged conceptually; result must be identical.
    let mut b = ProfileBuilder::new();
    b.delta_edge(addr(3), addr(2));
    b.block(addr(3), 300, 30, 1);
    b.delta_edge(addr(1), addr(3));
    b.block(addr(2), 200, 20, 3);
    b.delta_edge(addr(1), addr(2));
    b.block(addr(1), 100, 10, 1);
    b.delta_edge(addr(2), addr(2));
    assert_eq!(b.finish(), sample());
  }
}
