//! File-backed spilling of the compile accumulator's serialized bytes.
//!
//! Under `IX_COMPILE_SPILL=mmap`, `Env::store_const` appends each
//! constant's bytes to an **anonymous temp file** (`tempfile::tempfile_in`
//! — `O_TMPFILE` on Linux, so no pathname ever exists and the kernel
//! reclaims the space when the last fd/mapping drops, even on SIGKILL).
//! The file is sealed in fixed segments: when the unsealed region
//! exceeds the segment size, that range is mmapped read-only and every
//! entry in it is swapped from its heap `BytesSource` to a window into
//! the mapping (`LazyConstant::from_mmap_slice`). Sealed pages are clean
//! file-backed page cache — the kernel can evict them under memory
//! pressure with no swap configured — so the accumulator's resident
//! heap is bounded by one unsealed segment.
//!
//! The spill directory must be **disk-backed**: tmpfs (`/tmp` on most
//! distros) and `memfd_create` are shmem, whose pages are swap-backed
//! anonymous memory and cannot be evicted under `MemorySwapMax=0`,
//! silently defeating the spill. Hence the default is the current
//! working directory, overridable via `IX_COMPILE_SPILL_DIR`.
//!
//! Fixed sealed segments (rather than one growing mapping) keep every
//! window's lifetime trivially correct: remapping on growth would
//! invalidate outstanding windows.

use std::fs::File;
use std::io::Write;
use std::sync::Arc;

use memmap2::{Mmap, MmapOptions};

use ix_common::address::Address;

/// Segment start alignment. Mmap offsets must be page-aligned; 64 KiB
/// covers every Linux page size in use (4k / 16k / 64k).
const SEGMENT_ALIGN: usize = 64 * 1024;

/// Default sealed-segment size. Overridable via
/// `IX_COMPILE_SPILL_SEGMENT_MB` (minimum 1).
const DEFAULT_SEGMENT_SIZE: usize = 256 * 1024 * 1024;

/// Spill lifecycle slot held by `Env`. `Unopened` until the first
/// spill-mode `store_const`; `Disabled` after any I/O error (already
/// heap-backed entries remain valid, later stores stay heap-backed).
#[derive(Debug, Default)]
pub(crate) enum SpillSlot {
  #[default]
  Unopened,
  Active(SpillState),
  Disabled,
}

/// One sealed segment: the read-only mapping plus the entries it
/// contains as `(addr, offset_within_mapping, len)`.
pub(crate) type SealedSegment = (Arc<Mmap>, Vec<(Address, usize, usize)>);

/// Staged bytes are flushed to the file once this much accumulates, so
/// the caller's lock hold per append is a memcpy, not a syscall — the
/// store path is called from every scheduler worker and a per-append
/// `write` measurably convoys them.
const FLUSH_SIZE: usize = 8 * 1024 * 1024;

#[derive(Debug)]
pub(crate) struct SpillState {
  file: File,
  /// Appended but not yet written to the file.
  staging: Vec<u8>,
  /// Next virtual write offset (file bytes + staging bytes).
  offset: usize,
  /// Start of the unsealed segment; `SEGMENT_ALIGN`-aligned.
  segment_start: usize,
  /// `(addr, virtual_offset, len)` of entries in the unsealed segment.
  pending: Vec<(Address, usize, usize)>,
  segment_size: usize,
  pub(crate) segments_sealed: usize,
}

impl SpillState {
  pub(crate) fn create() -> std::io::Result<Self> {
    let dir =
      std::env::var("IX_COMPILE_SPILL_DIR").unwrap_or_else(|_| ".".to_string());
    let segment_size = std::env::var("IX_COMPILE_SPILL_SEGMENT_MB")
      .ok()
      .and_then(|s| s.parse::<usize>().ok())
      .filter(|&n| n > 0)
      .map(|n| n * 1024 * 1024)
      .unwrap_or(DEFAULT_SEGMENT_SIZE);
    Self::create_in(&dir, segment_size)
  }

  pub(crate) fn create_in(
    dir: &str,
    segment_size: usize,
  ) -> std::io::Result<Self> {
    let file = tempfile::tempfile_in(dir)?;
    Ok(SpillState {
      file,
      staging: Vec::with_capacity(FLUSH_SIZE),
      offset: 0,
      segment_start: 0,
      pending: Vec::new(),
      segment_size,
      segments_sealed: 0,
    })
  }

  /// Write staged bytes through to the file.
  fn flush(&mut self) -> std::io::Result<()> {
    if !self.staging.is_empty() {
      self.file.write_all(&self.staging)?;
      self.staging.clear();
    }
    Ok(())
  }

  /// Append one entry's bytes (a memcpy into staging; the file write is
  /// amortized to every `FLUSH_SIZE`). When this fills the segment,
  /// seal it: flush, pad so the next segment starts aligned, mmap the
  /// sealed range, and return it with its entries (offsets rebased to
  /// the mapping) for the caller to swap into the consts map.
  pub(crate) fn append(
    &mut self,
    addr: Address,
    bytes: &[u8],
  ) -> std::io::Result<Option<SealedSegment>> {
    self.staging.extend_from_slice(bytes);
    self.pending.push((addr, self.offset, bytes.len()));
    self.offset += bytes.len();

    if self.offset - self.segment_start < self.segment_size {
      if self.staging.len() >= FLUSH_SIZE {
        self.flush()?;
      }
      return Ok(None);
    }

    let data_end = self.offset;
    let next_start = data_end.div_ceil(SEGMENT_ALIGN) * SEGMENT_ALIGN;
    self.staging.resize(self.staging.len() + (next_start - data_end), 0);
    self.offset = next_start;
    self.flush()?;
    // Safety: the fd is a private anonymous temp file no other process
    // can open or truncate; write() and mmap go through the same page
    // cache on Linux, so the sealed range reads back what was written.
    let mmap = unsafe {
      MmapOptions::new()
        .offset(self.segment_start as u64)
        .len(data_end - self.segment_start)
        .map(&self.file)?
    };
    let seg_start = self.segment_start;
    self.segment_start = next_start;
    self.segments_sealed += 1;
    let entries = std::mem::take(&mut self.pending)
      .into_iter()
      .map(|(a, off, len)| (a, off - seg_start, len))
      .collect();
    Ok(Some((Arc::new(mmap), entries)))
  }

  /// Entries appended but not yet sealed into a mapping.
  pub(crate) fn pending_count(&self) -> usize {
    self.pending.len()
  }

  /// Virtual spill size: data plus alignment padding, including staged
  /// bytes not yet written through.
  pub(crate) fn file_len(&self) -> u64 {
    self.offset as u64
  }
}
