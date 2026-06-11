use multi_stark::p3_field::{PrimeCharacteristicRing, PrimeField64};
use rustc_hash::FxHashMap;
use std::collections::hash_map::Entry;

use crate::{
  FxIndexMap,
  aiur::{
    G,
    bytecode::{Block, Ctrl, FunIdx, Function, Op, Toplevel},
    gadgets::{
      AiurGadget,
      bytes1::{Bytes1, Bytes1Op, Bytes1Queries},
      bytes2::{Bytes2, Bytes2Op, Bytes2Queries},
    },
  },
};

/// Immutable view of one query entry.
#[derive(Clone, Copy)]
pub struct QueryRef<'a> {
  pub(crate) output: &'a [G],
  pub(crate) multiplicity: G,
}

/// Mutable view of one query entry: the output is fixed at insertion,
/// only the multiplicity is bumped on memo hits.
pub struct QueryRefMut<'a> {
  pub(crate) output: &'a [G],
  pub(crate) multiplicity: &'a mut G,
}

fn hash_g_slice(key: &[G]) -> u64 {
  use std::hash::Hasher;
  let mut h = rustc_hash::FxHasher::default();
  for g in key {
    h.write_u64(g.as_canonical_u64());
  }
  h.finish()
}

/// Append-only query store with a hash index.
///
/// Functionally the insertion-ordered map `args -> (output, multiplicity)`
/// it replaces (`FxIndexMap<Vec<G>, QueryResult>`) — but every circuit has
/// a FIXED key arity and output width, so keys and outputs live in flat
/// `Vec<G>` arenas addressed by entry index, and the hash table holds only
/// `u32` indices. This cuts per-entry overhead from ~130 B (two heap
/// `Vec`s + IndexMap bucket + allocator metadata) to the raw field
/// elements plus ~13 B of index. The record IS the proof witness, so
/// entries cannot be dropped — only stored compactly; on kernel-heavy
/// executions it is the dominant RAM consumer (billions of entries).
///
/// Entry index == insertion order; memory circuits use it as the pointer
/// value, mirroring the old `IndexMap::get_index_of` semantics.
pub struct QueryMap {
  key_stride: usize,
  /// Output width; inferred on first insert (not statically available in
  /// `FunctionLayout`).
  out_stride: usize,
  keys: Vec<G>,
  outs: Vec<G>,
  mults: Vec<G>,
  table: hashbrown::HashTable<u32>,
}

impl QueryMap {
  pub fn new(key_stride: usize) -> Self {
    Self {
      key_stride,
      out_stride: 0,
      keys: Vec::new(),
      outs: Vec::new(),
      mults: Vec::new(),
      table: hashbrown::HashTable::new(),
    }
  }

  #[inline]
  pub fn len(&self) -> usize {
    self.mults.len()
  }

  #[inline]
  pub fn is_empty(&self) -> bool {
    self.mults.is_empty()
  }

  /// Total retained field elements (keys + outputs); used by the
  /// `IX_AIUR_QUERY_STATS` RAM-attribution dump.
  pub fn retained_elems(&self) -> usize {
    self.keys.len() + self.outs.len()
  }

  #[inline]
  fn key_at(&self, i: usize) -> &[G] {
    &self.keys[i * self.key_stride..(i + 1) * self.key_stride]
  }

  #[inline]
  fn out_at(&self, i: usize) -> &[G] {
    &self.outs[i * self.out_stride..(i + 1) * self.out_stride]
  }

  pub fn get_index_of(&self, key: &[G]) -> Option<usize> {
    debug_assert_eq!(key.len(), self.key_stride);
    let hash = hash_g_slice(key);
    self
      .table
      .find(hash, |&i| self.key_at(i as usize) == key)
      .map(|&i| i as usize)
  }

  pub fn get(&self, key: &[G]) -> Option<QueryRef<'_>> {
    let i = self.get_index_of(key)?;
    Some(QueryRef { output: self.out_at(i), multiplicity: self.mults[i] })
  }

  pub fn get_mut(&mut self, key: &[G]) -> Option<QueryRefMut<'_>> {
    let i = self.get_index_of(key)?;
    let output = &self.outs[i * self.out_stride..(i + 1) * self.out_stride];
    Some(QueryRefMut { output, multiplicity: &mut self.mults[i] })
  }

  /// Append a new entry. The key must not already be present: call sites
  /// only insert on a confirmed miss, and a same-key re-entrant call
  /// would loop forever before reaching its own insert.
  pub fn insert(&mut self, key: &[G], output: &[G], multiplicity: G) {
    debug_assert_eq!(key.len(), self.key_stride);
    debug_assert!(self.get_index_of(key).is_none());
    if self.mults.is_empty() {
      self.out_stride = output.len();
    } else {
      debug_assert_eq!(output.len(), self.out_stride);
    }
    let hash = hash_g_slice(key);
    let i = u32::try_from(self.mults.len()).expect("query map overflow");
    self.keys.extend_from_slice(key);
    self.outs.extend_from_slice(output);
    self.mults.push(multiplicity);
    let keys = &self.keys;
    let stride = self.key_stride;
    self.table.insert_unique(hash, i, |&j| {
      let j = j as usize;
      hash_g_slice(&keys[j * stride..(j + 1) * stride])
    });
  }

  /// Entry at insertion index `i`: the key slice plus a mutable handle on
  /// the multiplicity (memory `Load` bumps the pointed-to row's count).
  pub fn get_index_mut(&mut self, i: usize) -> Option<(&[G], &mut G)> {
    if i >= self.mults.len() {
      return None;
    }
    let key = &self.keys[i * self.key_stride..(i + 1) * self.key_stride];
    Some((key, &mut self.mults[i]))
  }

  pub fn get_index(&self, i: usize) -> Option<(&[G], QueryRef<'_>)> {
    if i >= self.len() {
      return None;
    }
    Some((
      self.key_at(i),
      QueryRef { output: self.out_at(i), multiplicity: self.mults[i] },
    ))
  }

  pub fn iter(&self) -> impl Iterator<Item = (&[G], QueryRef<'_>)> {
    (0..self.len()).map(|i| {
      (
        self.key_at(i),
        QueryRef { output: self.out_at(i), multiplicity: self.mults[i] },
      )
    })
  }
}

pub struct QueryRecord {
  pub(crate) function_queries: Vec<QueryMap>,
  pub(crate) memory_queries: FxIndexMap<usize, QueryMap>,
  pub(crate) bytes1_queries: Bytes1Queries,
  pub(crate) bytes2_queries: Bytes2Queries,
}

impl QueryRecord {
  fn new(toplevel: &Toplevel) -> Self {
    let function_queries = toplevel
      .functions
      .iter()
      .map(|f| QueryMap::new(f.layout.input_size))
      .collect();
    let memory_queries = toplevel
      .memory_sizes
      .iter()
      .map(|width| (*width, QueryMap::new(*width)))
      .collect();
    let bytes1_queries = Bytes1Queries::new();
    let bytes2_queries = Bytes2Queries::new();
    Self { function_queries, memory_queries, bytes1_queries, bytes2_queries }
  }
}

pub(crate) struct IOKeyInfo {
  pub(crate) idx: usize,
  pub(crate) len: usize,
}

pub struct IOBuffer {
  /// Per-channel data arenas. `idx` slots into `data[&channel]`.
  pub(crate) data: FxHashMap<G, Vec<G>>,
  /// Channel-keyed info map; same `key` on different channels resolves
  /// to distinct `IOKeyInfo`.
  pub(crate) map: FxHashMap<(G, Vec<G>), IOKeyInfo>,
}

impl IOBuffer {
  #[inline]
  pub(crate) fn get_info(
    &self,
    channel: G,
    key: &[G],
  ) -> Result<&IOKeyInfo, ExecError> {
    self.map.get(&(channel, key.to_vec())).ok_or(ExecError::InvalidIOKey)
  }
  fn set_info(
    &mut self,
    channel: G,
    key: Vec<G>,
    idx: usize,
    len: usize,
  ) -> Result<(), ExecError> {
    let Entry::Vacant(e) = self.map.entry((channel, key)) else {
      return Err(ExecError::IOMappingAlreadySet);
    };
    e.insert(IOKeyInfo { idx, len });
    Ok(())
  }
  #[inline]
  pub(crate) fn read(
    &self,
    channel: G,
    idx: usize,
    len: usize,
  ) -> Result<&[G], ExecError> {
    let empty: &[G] = &[];
    let arena = self.data.get(&channel).map_or(empty, |v| v.as_slice());
    arena
      .get(idx..idx.saturating_add(len))
      .ok_or(ExecError::IOReadOutOfBounds { idx, len })
  }
  fn write(&mut self, channel: G, data: impl Iterator<Item = G>) {
    self.data.entry(channel).or_default().extend(data)
  }
}

/// Errors raised by Aiur bytecode execution. Mirrors the panic/assert sites
/// in `Function::execute` so callers (tests, kernel-arena runner) can
/// distinguish recoverable rejections (`AssertEq`, `MatchNoCase`) from
/// genuine bytecode bugs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExecError {
  NotEntryFunction(FunIdx),
  InvalidMemorySize(usize),
  UnboundPointer { ptr: u64, size: usize },
  PointerTooLarge(u64),
  IndexTooLarge(u64),
  U32OutOfRange(u64),
  U8RangeCheckFailed(u64),
  AssertEqLengthMismatch { lhs: usize, rhs: usize },
  AssertEqMismatch { lhs: u64, rhs: u64 },
  MatchNoCase(u64),
  NoContinuation,
  StackNotEmpty,
  InvalidIOKey,
  IOMappingAlreadySet,
  IOReadOutOfBounds { idx: usize, len: usize },
}

impl std::fmt::Display for ExecError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::NotEntryFunction(idx) => {
        write!(f, "cannot execute non-entry function {idx}")
      },
      Self::InvalidMemorySize(s) => write!(f, "invalid memory size {s}"),
      Self::UnboundPointer { ptr, size } => {
        write!(f, "unbound pointer {ptr} for memory size {size}")
      },
      Self::PointerTooLarge(p) => write!(f, "pointer {p} too large for usize"),
      Self::IndexTooLarge(i) => write!(f, "index {i} too large for usize"),
      Self::U32OutOfRange(v) => write!(f, "value {v} out of u32 range"),
      Self::U8RangeCheckFailed(v) => {
        write!(f, "value {v} out of u8 range [0, 256)")
      },
      Self::AssertEqLengthMismatch { lhs, rhs } => {
        write!(f, "assert_eq length mismatch: lhs={lhs}, rhs={rhs}")
      },
      Self::AssertEqMismatch { lhs, rhs } => {
        write!(f, "assert_eq mismatch: {lhs} != {rhs}")
      },
      Self::MatchNoCase(v) => write!(f, "no match case for value {v}"),
      Self::NoContinuation => write!(f, "yield without continuation"),
      Self::StackNotEmpty => {
        write!(f, "exec entries stack not empty at return")
      },
      Self::InvalidIOKey => write!(f, "invalid IO key"),
      Self::IOMappingAlreadySet => write!(f, "IO mapping already set for key"),
      Self::IOReadOutOfBounds { idx, len } => {
        write!(f, "IO read out of bounds: idx={idx}, len={len}")
      },
    }
  }
}

impl std::error::Error for ExecError {}

/// Gated by `IX_AIUR_QUERY_STATS=1`: dump per-function query-map sizes
/// during/after execution so RAM blowups can be attributed to specific
/// Aiur functions (indices resolve to names via the Lean
/// `CompiledToplevel`). Heaviest maps first, by retained G elements.
static QUERY_STATS: std::sync::LazyLock<bool> = std::sync::LazyLock::new(
  || std::env::var_os("IX_AIUR_QUERY_STATS").is_some(),
);

fn dump_query_stats(record: &QueryRecord, tag: &str) {
  let mut rows: Vec<(usize, usize, usize)> = record
    .function_queries
    .iter()
    .enumerate()
    .map(|(i, m)| (i, m.len(), m.retained_elems()))
    .filter(|(_, n, _)| *n > 0)
    .collect();
  rows.sort_by(|a, b| b.2.cmp(&a.2));
  let total_entries: usize = rows.iter().map(|r| r.1).sum();
  let total_elems: usize = rows.iter().map(|r| r.2).sum();
  eprintln!(
    "[aiur-stats {tag}] function_queries: {total_entries} entries, \
     {total_elems} G-elems; top maps:"
  );
  for (i, n, e) in rows.iter().take(30) {
    eprintln!("  fn{i:<4} entries={n:<12} g_elems={e}");
  }
  let mem: Vec<String> = record
    .memory_queries
    .iter()
    .map(|(w, m)| format!("w{w}={}", m.len()))
    .collect();
  eprintln!("[aiur-stats {tag}] memory entries: {}", mem.join(" "));
}

impl Toplevel {
  pub fn execute(
    &self,
    fun_idx: FunIdx,
    args: Vec<G>,
    io_buffer: &mut IOBuffer,
  ) -> Result<(QueryRecord, Vec<G>), ExecError> {
    if !self.functions[fun_idx].entry {
      return Err(ExecError::NotEntryFunction(fun_idx));
    }
    let mut record = QueryRecord::new(self);
    let function = &self.functions[fun_idx];
    let output =
      function.execute(fun_idx, args, self, &mut record, io_buffer)?;
    if *QUERY_STATS {
      dump_query_stats(&record, "final");
    }
    Ok((record, output))
  }
}

enum ExecEntry<'a> {
  Op(&'a Op),
  Ctrl(&'a Ctrl),
}

struct CallerState {
  fun_idx: FunIdx,
  map: Vec<G>,
  unconstrained: bool,
  continuation_depth: usize,
}

struct ContinuationState<'a> {
  block: &'a Block,
  map_len: usize,
}

impl Function {
  fn execute(
    &self,
    mut fun_idx: FunIdx,
    mut map: Vec<G>,
    toplevel: &Toplevel,
    record: &mut QueryRecord,
    io_buffer: &mut IOBuffer,
  ) -> Result<Vec<G>, ExecError> {
    let mut exec_entries_stack = vec![];
    let mut callers_states_stack = vec![];
    let mut continuation_stack: Vec<ContinuationState<'_>> = vec![];
    macro_rules! push_block_exec_entries {
      ($block:expr) => {
        exec_entries_stack.push(ExecEntry::Ctrl(&$block.ctrl));
        exec_entries_stack.extend($block.ops.iter().rev().map(ExecEntry::Op));
      };
    }
    push_block_exec_entries!(&self.body);
    let mut unconstrained = false;
    let mut stats_ops: u64 = 0;
    while let Some(exec_entry) = exec_entries_stack.pop() {
      if *QUERY_STATS {
        stats_ops += 1;
        if stats_ops.is_multiple_of(1 << 31) {
          dump_query_stats(record, &format!("ops={stats_ops}"));
        }
      }
      match exec_entry {
        ExecEntry::Op(Op::Const(c)) => map.push(*c),
        ExecEntry::Op(Op::Add(a, b)) => {
          let a = map[*a];
          let b = map[*b];
          map.push(a + b);
        },
        ExecEntry::Op(Op::Sub(a, b)) => {
          let a = map[*a];
          let b = map[*b];
          map.push(a - b);
        },
        ExecEntry::Op(Op::Mul(a, b)) => {
          let a = map[*a];
          let b = map[*b];
          map.push(a * b);
        },
        ExecEntry::Op(Op::EqZero(a)) => {
          let a = map[*a];
          map.push(G::from_bool(a == G::ZERO));
        },
        ExecEntry::Op(Op::Call(callee_idx, args, _, op_unconstrained)) => {
          let args: Vec<G> = args.iter().map(|i| map[*i]).collect();
          if let Some(result) =
            record.function_queries[*callee_idx].get_mut(&args)
          {
            if !unconstrained && !op_unconstrained {
              *result.multiplicity += G::ONE;
            }
            map.extend_from_slice(result.output);
          } else {
            let saved_map = std::mem::replace(&mut map, args);
            callers_states_stack.push(CallerState {
              fun_idx,
              map: saved_map,
              unconstrained,
              continuation_depth: continuation_stack.len(),
            });
            fun_idx = *callee_idx;
            unconstrained = unconstrained || *op_unconstrained;
            push_block_exec_entries!(&toplevel.functions[fun_idx].body);
          }
        },
        ExecEntry::Op(Op::Store(values)) => {
          let values = values.iter().map(|v| map[*v]).collect::<Vec<_>>();
          let size = values.len();
          let memory_queries = record
            .memory_queries
            .get_mut(&size)
            .ok_or(ExecError::InvalidMemorySize(size))?;
          if let Some(result) = memory_queries.get_mut(&values) {
            if !unconstrained {
              *result.multiplicity += G::ONE;
            }
            map.extend_from_slice(result.output);
          } else {
            let ptr = G::from_usize(memory_queries.len());
            memory_queries.insert(
              &values,
              &[ptr],
              G::from_bool(!unconstrained),
            );
            map.push(ptr);
          }
        },
        ExecEntry::Op(Op::Load(size, ptr)) => {
          let memory_queries = record
            .memory_queries
            .get_mut(size)
            .ok_or(ExecError::InvalidMemorySize(*size))?;
          let ptr = &map[*ptr];
          let ptr_u64 = ptr.as_canonical_u64();
          let ptr_usize = usize::try_from(ptr_u64)
            .ok()
            .ok_or(ExecError::PointerTooLarge(ptr_u64))?;
          let (args, multiplicity) = memory_queries
            .get_index_mut(ptr_usize)
            .ok_or(ExecError::UnboundPointer { ptr: ptr_u64, size: *size })?;
          if !unconstrained {
            *multiplicity += G::ONE;
          }
          map.extend_from_slice(args);
        },
        ExecEntry::Op(Op::AssertEq(xs, ys)) => {
          if xs.len() != ys.len() {
            return Err(ExecError::AssertEqLengthMismatch {
              lhs: xs.len(),
              rhs: ys.len(),
            });
          }
          for (x, y) in xs.iter().zip(ys) {
            let lhs = map[*x];
            let rhs = map[*y];
            if lhs != rhs {
              return Err(ExecError::AssertEqMismatch {
                lhs: lhs.as_canonical_u64(),
                rhs: rhs.as_canonical_u64(),
              });
            }
          }
        },
        ExecEntry::Op(Op::IOGetInfo(channel, key)) => {
          let channel = map[*channel];
          let key = key.iter().map(|v| map[*v]).collect::<Vec<_>>();
          let IOKeyInfo { idx, len } = io_buffer.get_info(channel, &key)?;
          map.push(G::from_usize(*idx));
          map.push(G::from_usize(*len));
        },
        ExecEntry::Op(Op::IOSetInfo(channel, key, idx, len)) => {
          let channel = map[*channel];
          let key = key.iter().map(|v| map[*v]).collect::<Vec<_>>();
          let get = |x: &usize| {
            let v = map[*x].as_canonical_u64();
            usize::try_from(v).ok().ok_or(ExecError::IndexTooLarge(v))
          };
          io_buffer.set_info(channel, key, get(idx)?, get(len)?)?;
        },
        ExecEntry::Op(Op::IORead(channel, idx, len)) => {
          let channel = map[*channel];
          let idx_val = map[*idx].as_canonical_u64();
          let idx = usize::try_from(idx_val)
            .ok()
            .ok_or(ExecError::IndexTooLarge(idx_val))?;
          let data = io_buffer.read(channel, idx, *len)?.to_vec();
          map.extend(data);
        },
        ExecEntry::Op(Op::IOWrite(channel, data)) => {
          let channel = map[*channel];
          io_buffer.write(channel, data.iter().map(|v| map[*v]))
        },
        ExecEntry::Op(Op::U8BitDecomposition(byte)) => {
          if unconstrained {
            map.extend(Bytes1::bit_decompose(&map[*byte]));
          } else {
            bytes1_execute(
              *byte,
              &Bytes1Op::BitDecomposition,
              &mut map,
              record,
            );
          }
        },
        ExecEntry::Op(Op::U8ShiftLeft(byte)) => {
          if unconstrained {
            map.push(Bytes1::shift_left(&map[*byte]));
          } else {
            bytes1_execute(*byte, &Bytes1Op::ShiftLeft, &mut map, record);
          }
        },
        ExecEntry::Op(Op::U8ShiftRight(byte)) => {
          if unconstrained {
            map.push(Bytes1::shift_right(&map[*byte]));
          } else {
            bytes1_execute(*byte, &Bytes1Op::ShiftRight, &mut map, record);
          }
        },
        ExecEntry::Op(Op::U8Xor(i, j)) => {
          if unconstrained {
            map.push(Bytes2::xor(&map[*i], &map[*j]));
          } else {
            bytes2_execute(*i, *j, &Bytes2Op::Xor, &mut map, record);
          }
        },
        ExecEntry::Op(Op::U8Add(i, j)) => {
          // The add gadget yields only the low byte; the carry is derived
          // and pushed separately so the op still produces `(low, carry)`.
          let (_r, o) = Bytes2::add(&map[*i], &map[*j]);
          if unconstrained {
            map.push(Bytes2::add(&map[*i], &map[*j]).0);
          } else {
            bytes2_execute(*i, *j, &Bytes2Op::Add, &mut map, record);
          }
          map.push(o);
        },
        ExecEntry::Op(Op::U8Mul(i, j)) => {
          if unconstrained {
            let (lo, hi) = Bytes2::mul(&map[*i], &map[*j]);
            map.extend([lo, hi]);
          } else {
            bytes2_execute(*i, *j, &Bytes2Op::Mul, &mut map, record);
          }
        },
        ExecEntry::Op(Op::U8Sub(i, j)) => {
          // The sub gadget yields only the low byte; the borrow is derived
          // and pushed separately so the op still produces `(low, borrow)`.
          let (_r, u) = Bytes2::sub(&map[*i], &map[*j]);
          if unconstrained {
            map.push(Bytes2::sub(&map[*i], &map[*j]).0);
          } else {
            bytes2_execute(*i, *j, &Bytes2Op::Sub, &mut map, record);
          }
          map.push(u);
        },
        ExecEntry::Op(Op::U8And(i, j)) => {
          if unconstrained {
            map.push(Bytes2::and(&map[*i], &map[*j]));
          } else {
            bytes2_execute(*i, *j, &Bytes2Op::And, &mut map, record);
          }
        },
        ExecEntry::Op(Op::U8Or(i, j)) => {
          if unconstrained {
            map.push(Bytes2::or(&map[*i], &map[*j]));
          } else {
            bytes2_execute(*i, *j, &Bytes2Op::Or, &mut map, record);
          }
        },
        ExecEntry::Op(Op::U8LessThan(i, j)) => {
          if unconstrained {
            map.push(Bytes2::less_than(&map[*i], &map[*j]));
          } else {
            bytes2_execute(*i, *j, &Bytes2Op::LessThan, &mut map, record);
          }
        },
        ExecEntry::Op(Op::U32LessThan(x_idx, y_idx)) => {
          let a_val = map[*x_idx].as_canonical_u64();
          let b_val = map[*y_idx].as_canonical_u64();
          let a_u32 =
            u32::try_from(a_val).ok().ok_or(ExecError::U32OutOfRange(a_val))?;
          let b_u32 =
            u32::try_from(b_val).ok().ok_or(ExecError::U32OutOfRange(b_val))?;
          let result = G::from_bool(a_u32 < b_u32);
          map.push(result);
          if !unconstrained {
            let x_bytes = a_u32.to_le_bytes();
            let z_bytes = b_u32.to_le_bytes();
            let c_u32 = b_u32.wrapping_sub(a_u32).wrapping_sub(1);
            let y_bytes = c_u32.to_le_bytes();
            // Bump range-check queries for byte pairs
            for (i, j) in [
              (x_bytes[0], x_bytes[1]),
              (x_bytes[2], x_bytes[3]),
              (y_bytes[0], y_bytes[1]),
              (y_bytes[2], y_bytes[3]),
              (z_bytes[0], z_bytes[1]),
              (z_bytes[2], z_bytes[3]),
            ] {
              record
                .bytes2_queries
                .bump_range_check(&G::from_u8(i), &G::from_u8(j));
            }
          }
        },
        ExecEntry::Op(Op::U8ChainRotr7(i, j)) => {
          if unconstrained {
            let (o0, o1, o2) = Bytes2::chain_rotr7(&map[*i], &map[*j]);
            map.extend([o0, o1, o2]);
          } else {
            bytes2_execute(*i, *j, &Bytes2Op::ChainRotr7, &mut map, record);
          }
        },
        ExecEntry::Op(Op::U8ChainRotr4(i, j)) => {
          if unconstrained {
            let (o0, o1, o2) = Bytes2::chain_rotr4(&map[*i], &map[*j]);
            map.extend([o0, o1, o2]);
          } else {
            bytes2_execute(*i, *j, &Bytes2Op::ChainRotr4, &mut map, record);
          }
        },
        ExecEntry::Op(Op::U8RangeCheck(i, j)) => {
          // No `map.push`: the two `u8` outputs alias the inputs `i`, `j`.
          // Records a range-check query so the byte-chip lookup is satisfied.
          if !unconstrained {
            let (vi, vj) = (map[*i], map[*j]);
            let (bi, bj) = (vi.as_canonical_u64(), vj.as_canonical_u64());
            if bi >= 256 {
              return Err(ExecError::U8RangeCheckFailed(bi));
            }
            if bj >= 256 {
              return Err(ExecError::U8RangeCheckFailed(bj));
            }
            record.bytes2_queries.bump_range_check(&vi, &vj);
          }
        },
        ExecEntry::Op(Op::Debug(label, idxs)) => match idxs {
          None => println!("{label}"),
          Some(idxs) => {
            let parts: Vec<_> =
              idxs.iter().map(|idx| map[*idx].to_string()).collect();
            let parts_joined = parts.join(", ");
            println!("{label}: {parts_joined}");
          },
        },
        ExecEntry::Ctrl(Ctrl::Match(val_idx, cases, default)) => {
          let val = &map[*val_idx];
          if let Some(block) = cases.get(val) {
            push_block_exec_entries!(block);
          } else {
            let default = default
              .as_ref()
              .ok_or_else(|| ExecError::MatchNoCase(val.as_canonical_u64()))?;
            push_block_exec_entries!(default);
          }
        },
        ExecEntry::Ctrl(Ctrl::MatchContinue(
          val_idx,
          cases,
          default,
          _output_size,
          _shared_aux,
          _shared_lookups,
          continuation,
        )) => {
          continuation_stack.push(ContinuationState {
            block: continuation,
            map_len: map.len(),
          });
          let val = &map[*val_idx];
          if let Some(block) = cases.get(val) {
            push_block_exec_entries!(block);
          } else {
            let default = default
              .as_ref()
              .ok_or_else(|| ExecError::MatchNoCase(val.as_canonical_u64()))?;
            push_block_exec_entries!(default);
          }
        },
        ExecEntry::Ctrl(Ctrl::Yield(_, output)) => {
          let cont =
            continuation_stack.pop().ok_or(ExecError::NoContinuation)?;
          let yielded: Vec<G> = output.iter().map(|&v| map[v]).collect();
          map.truncate(cont.map_len);
          map.extend(yielded);
          push_block_exec_entries!(cont.block);
        },
        ExecEntry::Ctrl(Ctrl::Return(_, output)) => {
          // Register the query.
          let input_size = toplevel.functions[fun_idx].layout.input_size;
          let output = output.iter().map(|i| map[*i]).collect::<Vec<_>>();
          record.function_queries[fun_idx].insert(
            &map[..input_size],
            &output,
            G::from_bool(!unconstrained),
          );
          if let Some(CallerState {
            fun_idx: caller_idx,
            map: caller_map,
            unconstrained: caller_unconstrained,
            continuation_depth,
          }) = callers_states_stack.pop()
          {
            continuation_stack.truncate(continuation_depth);
            fun_idx = caller_idx;
            map = caller_map;
            map.extend(output);
            unconstrained = caller_unconstrained;
          } else {
            continuation_stack.clear();
            if !exec_entries_stack.is_empty() {
              return Err(ExecError::StackNotEmpty);
            }
            map = output;
            break;
          }
        },
      }
    }
    Ok(map)
  }
}

fn bytes1_execute(
  byte: usize,
  op: &Bytes1Op,
  map: &mut Vec<G>,
  record: &mut QueryRecord,
) {
  map.extend(Bytes1.execute(op, &[map[byte]], record));
}

fn bytes2_execute(
  i: usize,
  j: usize,
  op: &Bytes2Op,
  map: &mut Vec<G>,
  record: &mut QueryRecord,
) {
  map.extend(Bytes2.execute(op, &[map[i], map[j]], record));
}
