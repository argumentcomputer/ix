//! The callee rows and ROM cells each recorded row reads.
//!
//! Device population uploads, per trace shard, only the rows that shard's
//! device rows read. To find them without filling every row on the host,
//! execution records, for each row of a function whose rows may be
//! populated on the device, every query its calls resolve to (a memo hit or
//! a newly started row) and every ROM cell its stores and loads touch. A row
//! records its references while it runs and hands them to its table when it
//! finishes, so rows of a recursive function, which nest, do not interleave.
//!
//! [`QueryMap::compact_refs`](crate::query::QueryMap::compact_refs) then
//! regroups each table's references by blocks of [`BLOCK`] consecutive rows,
//! sorted and without repeats. Population needs only the set of references
//! of a range of rows, and a shard's slice of a circuit covers whole rows, so
//! blocks lose nothing but a partial block at each end of a slice.
//!
//! A reference is a `u32`: the reference's target among its function's
//! targets (callee functions and ROM widths) in the high bits, the callee row
//! or ROM address in the low [`FunctionRefs::row_bits`]. A value that does
//! not fit is kept apart, with its row and target index, as a wide reference.
//! A row number at or beyond `2^31` stops the table's recording, and its
//! rows are populated from the whole record instead.
use crate::bytecode::{CheckedProgram, Instruction};
use crate::field::FieldBackend;

/// Rows per block of compacted references.
pub const BLOCK: usize = 1 << BLOCK_SHIFT;
pub const BLOCK_SHIFT: u32 = 8;

/// Marks the first word of a finished row's references while recording.
const HEADER: u32 = 1 << 31;

/// What a reference points into.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Target {
  /// A row of this function's query table.
  Function(usize),
  /// A ROM cell of this many words, by address.
  Rom(usize),
}

/// The reference targets of a function's call, store and load sites.
#[derive(Clone, Debug)]
pub struct FunctionRefs {
  pub targets: Vec<Target>,
  /// Bits of a reference that hold the row or address.
  pub row_bits: u32,
  /// Each execution PC's target index, or [`NO_SITE`].
  sites: Vec<u16>,
  /// Per target: the functions a lookup of the key of one of its rows may
  /// also find. A depth slot looks its callee up in each function of the
  /// callee's circuit in turn, and an earlier one may hold the same key;
  /// gathering a shard image adds those rows ([`crate::refs`] records only
  /// the row the call resolved to).
  pub aliases: Vec<Vec<usize>>,
}

const NO_SITE: u16 = u16::MAX;

impl FunctionRefs {
  #[inline(always)]
  pub(crate) fn site(&self, pc: usize) -> u16 {
    self.sites.get(pc).copied().unwrap_or(NO_SITE)
  }

  /// The reference to `value` of the target at `site`, or `None` when it
  /// does not fit.
  #[inline(always)]
  pub(crate) fn encode(&self, site: u16, value: usize) -> Option<u32> {
    if site == NO_SITE || value >> self.row_bits != 0 {
      return None;
    }
    Some((u32::from(site) << self.row_bits) | value as u32)
  }

  /// A reference's target and row or address.
  #[inline(always)]
  pub fn decode(&self, reference: u32) -> (Target, usize) {
    let site = (reference >> self.row_bits) as usize;
    (self.targets[site], (reference & ((1 << self.row_bits) - 1)) as usize)
  }

  /// A reference's target index and row or address.
  #[inline(always)]
  pub fn split(&self, reference: u32) -> (usize, usize) {
    (
      (reference >> self.row_bits) as usize,
      (reference & ((1 << self.row_bits) - 1)) as usize,
    )
  }
}

/// Which functions record references, and their targets.
#[derive(Debug)]
pub struct RefPlan {
  pub functions: Vec<Option<FunctionRefs>>,
}

impl<B: FieldBackend> CheckedProgram<B> {
  /// Have execution record the references of the rows of the functions
  /// `record` admits (none for those without call, store or load sites).
  /// Calls to fixed
  /// tables are not references: their rows are part of the program. A
  /// reference to a row of function `g` also records the rows with the same
  /// key in each function of `aliases[g]` ([`FunctionRefs::aliases`]).
  pub fn record_refs(
    &mut self,
    record: impl Fn(usize) -> bool,
    aliases: &[Vec<usize>],
  ) {
    let functions = self.program.functions.len();
    let plan = (0..functions)
      .map(|f| {
        if !record(f) {
          return None;
        }
        let code = &self.execution_functions[f].code;
        let mut targets = vec![];
        let mut sites = vec![NO_SITE; code.len()];
        for (pc, instruction) in code.iter().enumerate() {
          let target = match instruction {
            Instruction::Call { function, .. } if *function < functions => {
              Target::Function(*function)
            },
            Instruction::Store { .. } | Instruction::Load { .. } => {
              let memory_type = self.steps[f][pc].memory_type;
              Target::Rom(self.memory_types.get(memory_type)?.1.width())
            },
            _ => continue,
          };
          let index = match targets.iter().position(|&t| t == target) {
            Some(i) => i,
            None => {
              targets.push(target);
              targets.len() - 1
            },
          };
          sites[pc] = u16::try_from(index).ok()?;
        }
        let probes = targets
          .iter()
          .map(|&target| match target {
            Target::Function(g) => aliases
              .get(g)
              .into_iter()
              .flatten()
              .copied()
              .filter(|&a| a != g && a < functions)
              .collect(),
            Target::Rom(_) => vec![],
          })
          .collect();
        let bits = usize::BITS - targets.len().saturating_sub(1).leading_zeros();
        Some(FunctionRefs { targets, row_bits: 31 - bits, sites, aliases: probes })
      })
      .collect();
    self.refs = Some(std::sync::Arc::new(RefPlan { functions: plan }));
  }

  /// Whether execution records row references ([`Self::record_refs`]).
  pub fn records_refs(&self) -> bool {
    self.refs.is_some()
  }

  pub fn ref_plan(&self) -> Option<&RefPlan> {
    self.refs.as_deref()
  }
}

/// One query table's references.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct TableRefs {
  /// While recording, each finished row's references after a header word
  /// (`HEADER | row`), in the order rows finish; once compact, the
  /// references of block `b` at `starts[b]..starts[b + 1]`.
  refs: Vec<u32>,
  starts: Vec<u64>,
  compact: bool,
  /// Set when a row number did not fit; nothing is kept.
  overflowed: bool,
  /// References whose value does not fit beside its target index: (row,
  /// target index, value), sorted by row once compact.
  wide: Vec<[u32; 3]>,
}

impl TableRefs {
  pub(crate) fn overflowed(&self) -> bool {
    self.overflowed
  }

  pub(crate) fn is_compact(&self) -> bool {
    self.compact && !self.overflowed
  }

  pub(crate) fn overflow(&mut self, budget: &crate::budget::Budget) {
    self.overflowed = true;
    let refs = std::mem::take(&mut self.refs);
    let starts = std::mem::take(&mut self.starts);
    let wide = std::mem::take(&mut self.wide);
    release(
      budget,
      refs.capacity() * 4 + starts.capacity() * 8 + wide.capacity() * 12,
    );
  }

  /// Keeps `row`'s reference to `value` of target `site` that
  /// [`FunctionRefs::encode`] could not encode.
  #[cold]
  #[inline(never)]
  pub(crate) fn wide(
    &mut self,
    row: usize,
    site: u16,
    value: usize,
    budget: &crate::budget::Budget,
  ) -> Result<(), crate::budget::BudgetError> {
    if self.overflowed {
      return Ok(());
    }
    match (u32::try_from(row), u32::try_from(value)) {
      (Ok(row), Ok(value)) if site != NO_SITE => {
        budget.vector(&mut self.wide, 1)?;
        self.wide.push([row, u32::from(site), value]);
      },
      _ => self.overflow(budget),
    }
    Ok(())
  }

  /// The wide references of rows `rows`, as (target index, value).
  pub(crate) fn wide_refs(
    &self,
    rows: std::ops::Range<usize>,
  ) -> impl Iterator<Item = (usize, usize)> + '_ {
    let start = self.wide.partition_point(|w| (w[0] as usize) < rows.start);
    self.wide[start..]
      .iter()
      .take_while(move |w| (w[0] as usize) < rows.end)
      .map(|w| (w[1] as usize, w[2] as usize))
  }

  /// Keeps finished `row`'s `references`.
  #[inline]
  pub(crate) fn finish(
    &mut self,
    row: usize,
    references: &[u32],
    budget: &crate::budget::Budget,
  ) -> Result<(), crate::budget::BudgetError> {
    if references.is_empty() || self.overflowed {
      return Ok(());
    }
    let Ok(header) = u32::try_from(row) else {
      self.overflow(budget);
      return Ok(());
    };
    if header & HEADER != 0 {
      self.overflow(budget);
      return Ok(());
    }
    budget.vector(&mut self.refs, references.len() + 1)?;
    self.refs.push(HEADER | header);
    self.refs.extend_from_slice(references);
    Ok(())
  }

  /// Regroups the references of a table of `rows` rows by block, sorted
  /// and without repeats.
  pub(crate) fn compact(
    &mut self,
    rows: usize,
    budget: &crate::budget::Budget,
  ) -> Result<(), crate::budget::BudgetError> {
    if self.compact || self.overflowed {
      return Ok(());
    }
    let blocks = rows.div_ceil(BLOCK);
    budget.reserve((blocks + 1) * 8)?;
    let mut starts = vec![0u64; blocks + 1];
    let mut block = 0usize;
    let mut total = 0usize;
    for &word in &self.refs {
      if word & HEADER != 0 {
        block = ((word & !HEADER) >> BLOCK_SHIFT) as usize;
      } else {
        starts[block + 1] += 1;
        total += 1;
      }
    }
    for b in 0..blocks {
      starts[b + 1] += starts[b];
    }
    budget.reserve(total * 4)?;
    let mut compact = vec![0u32; total];
    let mut cursor: Vec<u64> = starts[..blocks].to_vec();
    for &word in &self.refs {
      if word & HEADER != 0 {
        block = ((word & !HEADER) >> BLOCK_SHIFT) as usize;
      } else {
        compact[cursor[block] as usize] = word;
        cursor[block] += 1;
      }
    }
    drop(cursor);
    let recorded = std::mem::take(&mut self.refs);
    release(budget, recorded.capacity() * 4);
    drop(recorded);
    let mut kept = 0usize;
    let mut start = 0usize;
    for b in 0..blocks {
      let end = starts[b + 1] as usize;
      let refs = &mut compact[start..end];
      refs.sort_unstable();
      let mut last = None;
      let mut n = 0;
      for i in 0..refs.len() {
        if last != Some(refs[i]) {
          last = Some(refs[i]);
          refs[n] = refs[i];
          n += 1;
        }
      }
      compact.copy_within(start..start + n, kept);
      starts[b] = kept as u64;
      kept += n;
      start = end;
    }
    starts[blocks] = kept as u64;
    compact.truncate(kept);
    compact.shrink_to_fit();
    release(budget, (total - compact.capacity()) * 4);
    self.refs = compact;
    self.starts = starts;
    self.wide.sort_unstable();
    self.compact = true;
    Ok(())
  }

  /// Blocks of compacted references.
  pub(crate) fn blocks(&self) -> usize {
    self.starts.len().saturating_sub(1)
  }

  /// The compacted references of the rows of blocks `blocks`.
  pub(crate) fn block_refs(&self, blocks: std::ops::Range<usize>) -> &[u32] {
    if !self.is_compact() || blocks.is_empty() {
      return &[];
    }
    let end = blocks.end.min(self.blocks());
    let start = blocks.start.min(end);
    &self.refs[self.starts[start] as usize..self.starts[end] as usize]
  }

  /// Bytes held, as charged.
  pub(crate) fn bytes(&self) -> usize {
    self.refs.capacity() * 4 + self.starts.capacity() * 8 + self.wide.capacity() * 12
  }
}

fn release(budget: &crate::budget::Budget, bytes: usize) {
  if let Some(reservation) = &budget.0 {
    reservation.release(bytes);
  }
}

/// Pending references of the rows being executed, innermost last.
#[derive(Debug, Default)]
pub(crate) struct Pending {
  refs: Vec<u32>,
}

impl Pending {
  #[inline(always)]
  pub(crate) fn mark(&self) -> usize {
    self.refs.len()
  }

  #[inline(always)]
  pub(crate) fn push(&mut self, reference: u32) {
    self.refs.push(reference);
  }

  /// The references since `mark`, removed once `keep` has taken them.
  #[inline]
  pub(crate) fn take<R>(
    &mut self,
    mark: usize,
    keep: impl FnOnce(&[u32]) -> R,
  ) -> R {
    let result = keep(&self.refs[mark..]);
    self.refs.truncate(mark);
    result
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  /// Rows that finish out of order, repeated references and a wide one come
  /// back grouped by block, sorted and without repeats.
  #[test]
  fn compaction_groups_references_by_block() {
    let budget = crate::budget::Budget::default();
    let mut refs = TableRefs::default();
    refs.finish(BLOCK + 1, &[7, 3, 7], &budget).unwrap();
    refs.finish(0, &[9, 3], &budget).unwrap();
    refs.finish(1, &[], &budget).unwrap();
    refs.wide(BLOCK, 2, 1 << 30, &budget).unwrap();
    refs.finish(2, &[1], &budget).unwrap();
    refs.compact(BLOCK + 2, &budget).unwrap();
    assert!(refs.is_compact());
    assert_eq!(refs.blocks(), 2);
    assert_eq!(refs.block_refs(0..1), [1, 3, 9]);
    assert_eq!(refs.block_refs(1..2), [3, 7]);
    assert_eq!(refs.block_refs(0..2), [1, 3, 9, 3, 7]);
    assert_eq!(refs.wide_refs(0..BLOCK).count(), 0);
    assert_eq!(refs.wide_refs(BLOCK..2 * BLOCK).collect::<Vec<_>>(), [(2, 1 << 30)]);
  }

  #[test]
  fn references_encode_target_and_row() {
    let refs = FunctionRefs {
      targets: vec![Target::Function(4), Target::Rom(2), Target::Function(1)],
      row_bits: 29,
      sites: vec![NO_SITE, 2],
      aliases: vec![vec![]; 3],
    };
    let reference = refs.encode(refs.site(1), 12345).unwrap();
    assert_eq!(refs.decode(reference), (Target::Function(1), 12345));
    assert_eq!(refs.encode(2, 1 << 29), None);
    assert_eq!(refs.encode(refs.site(0), 1), None);
  }
}
