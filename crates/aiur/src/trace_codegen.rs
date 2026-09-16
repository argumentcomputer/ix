//! Read-only seed preparation and canonical scalar rows for generated traces.
//!
//! Binding compares the complete bytecode library, including unconstrained
//! callees. Function numbers and widths alone do not identify a row writer.

pub mod contract;
#[cfg(feature = "cuda-trace-codegen")]
pub mod cuda;
#[cfg(feature = "cuda-trace-codegen")]
pub(crate) mod programs;

use std::fmt;

use multi_stark::p3_field::{PrimeCharacteristicRing, PrimeField64};

use crate::{
  G,
  bytecode::{Block, Ctrl, FunctionLayout, Toplevel},
  execute::{IOBuffer, QueryRecord, find_unconstrained_big_uint_div_mod},
};

#[derive(Debug, PartialEq, Eq)]
pub struct TraceError {
  pub function: usize,
  pub query: Option<usize>,
  pub operation: Option<usize>,
  pub detail: String,
}

impl fmt::Display for TraceError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "trace function {}", self.function)?;
    if let Some(query) = self.query {
      write!(f, " query {query}")?;
    }
    if let Some(operation) = self.operation {
      write!(f, " operation {operation}")?;
    }
    write!(f, ": {}", self.detail)
  }
}

impl std::error::Error for TraceError {}

pub type TraceResult<T> = Result<T, TraceError>;

pub fn error(
  function: usize,
  operation: Option<usize>,
  detail: impl Into<String>,
) -> TraceError {
  TraceError { function, query: None, operation, detail: detail.into() }
}

pub fn no_match(function: usize, value: G) -> TraceError {
  error(function, None, format!("no match for {}", value.as_canonical_u64()))
}

/// Borrows the finalized record and I/O for one row. No helper inserts a query
/// or changes its multiplicity. The owner must retain both across regeneration.
pub struct SeedContext<'a> {
  pub inputs: &'a [G],
  pub output: &'a [G],
  pub multiplicity: G,
  record: &'a QueryRecord,
  io: &'a IOBuffer,
  function: usize,
}

impl SeedContext<'_> {
  fn fail(&self, operation: usize, detail: impl Into<String>) -> TraceError {
    error(self.function, Some(operation), detail)
  }

  pub fn call<const N: usize>(
    &self,
    operation: usize,
    callee: usize,
    args: &[G],
  ) -> TraceResult<[G; N]> {
    let result = self
      .record
      .function_queries
      .get(callee)
      .and_then(|queries| queries.get(args))
      .ok_or_else(|| {
        self.fail(operation, format!("missing call to function {callee}"))
      })?;
    result
      .output
      .try_into()
      .map_err(|_| self.fail(operation, "call output arity mismatch"))
  }

  pub fn returned<const N: usize>(
    &self,
    operation: usize,
  ) -> TraceResult<[G; N]> {
    self
      .output
      .try_into()
      .map_err(|_| self.fail(operation, "returned-call arity mismatch"))
  }

  pub fn check_returned<const N: usize>(
    &self,
    operation: usize,
    callee: usize,
    args: &[G],
  ) -> TraceResult<[G; N]> {
    let output = self.returned(operation)?;
    if self.call::<N>(operation, callee, args)? != output {
      return Err(self.fail(
        operation,
        format!("returned-call alias disagrees with function {callee}"),
      ));
    }
    Ok(output)
  }

  pub fn store(&self, operation: usize, values: &[G]) -> TraceResult<[G; 1]> {
    let index = self
      .record
      .memory_queries
      .get(&values.len())
      .and_then(|table| table.get_index_of(values))
      .ok_or_else(|| self.fail(operation, "missing stored values"))?;
    let pointer = self
      .record
      .pointer_base
      .checked_add(index)
      .ok_or_else(|| self.fail(operation, "memory pointer overflow"))?;
    Ok([G::from_usize(pointer)])
  }

  pub fn load<const N: usize>(
    &self,
    operation: usize,
    pointer: G,
  ) -> TraceResult<[G; N]> {
    let index = usize::try_from(pointer.as_canonical_u64())
      .ok()
      .and_then(|pointer| pointer.checked_sub(self.record.pointer_base))
      .ok_or_else(|| {
        self.fail(operation, "pointer precedes this record's memory namespace")
      })?;
    let (values, _) = self
      .record
      .memory_queries
      .get(&N)
      .and_then(|table| table.get_index(index))
      .ok_or_else(|| self.fail(operation, "missing loaded values"))?;
    values.try_into().map_err(|_| self.fail(operation, "memory width mismatch"))
  }

  pub fn io_info(
    &self,
    operation: usize,
    channel: G,
    key: &[G],
  ) -> TraceResult<[G; 2]> {
    let info = self
      .io
      .get_info(channel, key)
      .map_err(|e| self.fail(operation, e.to_string()))?;
    Ok([G::from_usize(info.idx), G::from_usize(info.len)])
  }

  pub fn io_read<const N: usize>(
    &self,
    operation: usize,
    channel: G,
    index: G,
  ) -> TraceResult<[G; N]> {
    let index = usize::try_from(index.as_canonical_u64())
      .map_err(|_| self.fail(operation, "I/O index overflow"))?;
    self
      .io
      .read(channel, index, N)
      .map_err(|e| self.fail(operation, e.to_string()))?
      .try_into()
      .map_err(|_| self.fail(operation, "I/O length mismatch"))
  }

  pub fn big_uint(&self, operation: usize, a: G, b: G) -> TraceResult<[G; 2]> {
    let (q, r) = find_unconstrained_big_uint_div_mod(
      a,
      b,
      &self.record.memory_queries,
      self.record.pointer_base,
    )
    .map_err(|e| self.fail(operation, e))?;
    Ok([q, r])
  }
}

#[derive(Clone, Copy)]
pub struct RowOffsets {
  pub selectors: usize,
  pub auxiliaries: usize,
}

/// A guarded byte payload. Out-of-range words set the guard before their low
/// byte is written; callers must discard that payload and use canonical words.
pub struct PackedSeed<'a> {
  bytes: &'a mut [u8],
  high_bits: u64,
}

impl PackedSeed<'_> {
  #[inline]
  pub fn set(&mut self, index: usize, value: G) {
    assert!(index > 0, "multiplicity is a full-width word");
    let value = value.as_canonical_u64();
    self.high_bits |= value;
    self.bytes[index + 7] = value as u8;
  }
}

#[derive(Clone, Copy)]
pub struct FunctionWriter {
  pub layout: FunctionLayout,
  pub output_size: usize,
  pub seed_words: usize,
  pub pack: fn(&SeedContext<'_>, &mut [u64]) -> TraceResult<()>,
  pub pack_u8: fn(&SeedContext<'_>, &mut PackedSeed<'_>) -> TraceResult<()>,
  pub pack_checked: fn(&SeedContext<'_>, &mut [u64]) -> TraceResult<()>,
  pub write: fn(&[u64], RowOffsets, &mut [u64]) -> TraceResult<()>,
}

pub struct GeneratedProgram {
  pub fingerprint: [u8; 32],
  pub complete: bool,
  pub expected: fn() -> Toplevel,
  pub functions: &'static [Option<FunctionWriter>],
}

pub struct BoundProgram<'a> {
  generated: &'a GeneratedProgram,
  bytecode: &'a Toplevel,
}

pub struct BoundFunction<'a> {
  index: usize,
  writer: &'a FunctionWriter,
  bytecode: &'a Toplevel,
}

fn same_block(a: &Block, b: &Block) -> bool {
  let arms_equal = |a: &crate::FxIndexMap<G, Block>,
                    b: &crate::FxIndexMap<G, Block>| {
    // Default-arm inverse columns follow case order; map equality ignores it.
    a.len() == b.len()
      && a.iter().zip(b).all(|((ka, a), (kb, b))| ka == kb && same_block(a, b))
  };
  let fallback_equal =
    |a: &Option<Box<Block>>, b: &Option<Box<Block>>| match (a, b) {
      (None, None) => true,
      (Some(a), Some(b)) => same_block(a, b),
      _ => false,
    };
  a.ops == b.ops
    && match (&a.ctrl, &b.ctrl) {
      (Ctrl::Return(sa, va), Ctrl::Return(sb, vb))
      | (Ctrl::Yield(sa, va), Ctrl::Yield(sb, vb)) => sa == sb && va == vb,
      (Ctrl::Match(da, aa, fa), Ctrl::Match(db, ab, fb)) => {
        da == db && arms_equal(aa, ab) && fallback_equal(fa, fb)
      },
      (
        Ctrl::MatchContinue(da, aa, fa, na, ca, la, ba),
        Ctrl::MatchContinue(db, ab, fb, nb, cb, lb, bb),
      ) => {
        da == db
          && na == nb
          && ca == cb
          && la == lb
          && arms_equal(aa, ab)
          && fallback_equal(fa, fb)
          && same_block(ba, bb)
      },
      _ => false,
    }
}

impl GeneratedProgram {
  pub fn bind<'a>(
    &'a self,
    bytecode: &'a Toplevel,
  ) -> Result<BoundProgram<'a>, &'static str> {
    let expected = (self.expected)();
    if self.fingerprint != contract::fingerprint(bytecode)
      || !contract::validate_grouping(bytecode)
      || expected.memory_sizes != bytecode.memory_sizes
      || expected.functions.len() != bytecode.functions.len()
      || self.functions.len() != bytecode.functions.len()
      || expected.functions.iter().zip(&bytecode.functions).any(|(a, b)| {
        !same_block(&a.body, &b.body)
          || a.layout != b.layout
          || a.entry != b.entry
          || a.constrained != b.constrained
      })
    {
      return Err("generated trace library differs from the bytecode program");
    }
    for (function, writer) in bytecode.functions.iter().zip(self.functions) {
      if (self.complete && function.constrained && writer.is_none())
        || (!function.constrained && writer.is_some())
        || writer
          .as_ref()
          .is_some_and(|writer| writer.layout != function.layout)
      {
        return Err(
          "generated trace descriptors differ from the bytecode program",
        );
      }
    }
    Ok(BoundProgram { generated: self, bytecode })
  }
}

impl BoundProgram<'_> {
  pub fn function(&self, index: usize) -> Option<BoundFunction<'_>> {
    Some(BoundFunction {
      index,
      writer: self.generated.functions.get(index)?.as_ref()?,
      bytecode: self.bytecode,
    })
  }
}

impl BoundFunction<'_> {
  pub fn seed_words(&self) -> usize {
    self.writer.seed_words
  }

  pub fn pack_row(
    &self,
    record: &QueryRecord,
    io: &IOBuffer,
    query: usize,
    check_aliases: bool,
    seed: &mut [u64],
  ) -> TraceResult<()> {
    if seed.len() != self.seed_words() {
      return Err(error(self.index, None, "seed width mismatch"));
    }
    let (inputs, result) = record
      .function_queries
      .get(self.index)
      .and_then(|queries| queries.get_index(query))
      .ok_or_else(|| error(self.index, None, "missing row query"))?;
    if inputs.len() != self.writer.layout.input_size
      || result.output.len() != self.writer.output_size
    {
      return Err(error(self.index, None, "row query arity mismatch"));
    }
    if result.multiplicity == G::ZERO {
      return Err(error(
        self.index,
        None,
        "zero-multiplicity function query has no trace row",
      ));
    }
    seed.fill(0);
    seed[0] = result.multiplicity.as_canonical_u64();
    for (dst, value) in seed[1..].iter_mut().zip(inputs) {
      *dst = value.as_canonical_u64();
    }
    let context = SeedContext {
      inputs,
      output: result.output,
      multiplicity: result.multiplicity,
      record,
      io,
      function: self.index,
    };
    let pack =
      if check_aliases { self.writer.pack_checked } else { self.writer.pack };
    pack(&context, seed).map_err(|mut error| {
      error.query = Some(query);
      error
    })
  }

  pub fn pack_u8_row(
    &self,
    record: &QueryRecord,
    io: &IOBuffer,
    query: usize,
    bytes: &mut [u8],
  ) -> TraceResult<bool> {
    if SeedEncoding::U8Payload.stride(self.seed_words()) != Some(bytes.len()) {
      return Err(error(self.index, None, "packed seed width mismatch"));
    }
    let (inputs, result) = record
      .function_queries
      .get(self.index)
      .and_then(|queries| queries.get_index(query))
      .ok_or_else(|| error(self.index, None, "missing row query"))?;
    if inputs.len() != self.writer.layout.input_size
      || result.output.len() != self.writer.output_size
      || result.multiplicity == G::ZERO
    {
      return Err(error(
        self.index,
        None,
        "row arity or multiplicity mismatch",
      ));
    }
    bytes.fill(0);
    bytes[..8]
      .copy_from_slice(&result.multiplicity.as_canonical_u64().to_le_bytes());
    let mut seed = PackedSeed { bytes, high_bits: 0 };
    for (i, &input) in inputs.iter().enumerate() {
      seed.set(1 + i, input);
    }
    let context = SeedContext {
      inputs,
      output: result.output,
      multiplicity: result.multiplicity,
      record,
      io,
      function: self.index,
    };
    (self.writer.pack_u8)(&context, &mut seed).map_err(|mut error| {
      error.query = Some(query);
      error
    })?;
    Ok(seed.high_bits <= 255)
  }

  pub fn write_row(
    &self,
    seed: &[u64],
    circuit: usize,
    row: &mut [u64],
  ) -> TraceResult<()> {
    if seed.len() != self.seed_words()
      || seed.first() == Some(&0)
      || seed.iter().any(|&word| word >= G::ORDER_U64)
    {
      return Err(error(
        self.index,
        None,
        "seed width, multiplicity, or canonical form mismatch",
      ));
    }
    let circuit = self
      .bytecode
      .circuits
      .get(circuit)
      .ok_or_else(|| error(self.index, None, "missing circuit"))?;
    let member = circuit
      .members
      .iter()
      .position(|&member| member == self.index)
      .ok_or_else(|| {
        error(self.index, None, "function is not a member of this circuit")
      })?;
    if row.len() != circuit.layout.width() {
      return Err(error(self.index, None, "row width mismatch"));
    }
    let selector_offset: usize = circuit.members[..member]
      .iter()
      .map(|&index| self.bytecode.functions[index].layout.selectors)
      .sum();
    let offsets = RowOffsets {
      selectors: circuit.layout.input_size + selector_offset,
      auxiliaries: circuit.layout.input_size + circuit.layout.selectors,
    };
    row.fill(0);
    row[..self.writer.layout.input_size]
      .copy_from_slice(&seed[1..1 + self.writer.layout.input_size]);
    row[offsets.auxiliaries] = seed[0];
    (self.writer.write)(seed, offsets, row)
  }
}

/// Encoding is metadata for a row or a homogeneous batch, never inferred from
/// byte length. Multiplicities stay full-width, including negative field values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SeedEncoding {
  Canonical,
  U8Payload,
}

impl SeedEncoding {
  pub fn for_words(words: &[u64]) -> Result<Self, &'static str> {
    if words.is_empty() || words.iter().any(|&word| word >= G::ORDER_U64) {
      return Err("seed words must be nonempty and canonical");
    }
    Ok(if words[1..].iter().all(|&word| word <= 255) {
      Self::U8Payload
    } else {
      Self::Canonical
    })
  }

  pub fn stride(self, words: usize) -> Option<usize> {
    if words == 0 {
      return None;
    }
    match self {
      Self::Canonical => words.checked_mul(8),
      Self::U8Payload => words.checked_add(14).map(|size| (size / 8) * 8),
    }
  }

  pub fn encode(
    self,
    words: &[u64],
    bytes: &mut [u8],
  ) -> Result<(), &'static str> {
    let smallest = Self::for_words(words)?;
    if self.stride(words.len()) != Some(bytes.len())
      || (self == Self::U8Payload && smallest != self)
    {
      return Err("seed encoding width or byte guard mismatch");
    }
    bytes.fill(0);
    match self {
      Self::Canonical => {
        for (word, bytes) in words.iter().zip(bytes.chunks_exact_mut(8)) {
          bytes.copy_from_slice(&word.to_le_bytes());
        }
      },
      Self::U8Payload => {
        bytes[..8].copy_from_slice(&words[0].to_le_bytes());
        for (byte, &word) in bytes[8..].iter_mut().zip(&words[1..]) {
          *byte = u8::try_from(word).expect("byte guard checked");
        }
      },
    }
    Ok(())
  }

  pub fn decode(
    self,
    bytes: &[u8],
    words: &mut [u64],
  ) -> Result<(), &'static str> {
    if self.stride(words.len()) != Some(bytes.len()) {
      return Err("seed encoding width mismatch");
    }
    match self {
      Self::Canonical => {
        for (word, bytes) in words.iter_mut().zip(bytes.chunks_exact(8)) {
          *word = u64::from_le_bytes(bytes.try_into().expect("eight bytes"));
        }
      },
      Self::U8Payload => {
        words[0] =
          u64::from_le_bytes(bytes[..8].try_into().expect("eight bytes"));
        for (word, &byte) in words[1..].iter_mut().zip(&bytes[8..]) {
          *word = u64::from(byte);
        }
        if bytes[7 + words.len()..].iter().any(|&byte| byte != 0) {
          return Err("nonzero seed padding");
        }
      },
    }
    Self::for_words(words).map(|_| ())
  }
}

pub fn u32_word(bytes: [G; 4]) -> u64 {
  bytes
    .iter()
    .enumerate()
    .fold(0, |word, (i, byte)| word | (byte.as_canonical_u64() << (8 * i)))
}

pub fn u32_add(words: &[u64]) -> [G; 5] {
  let sum: u128 = words.iter().map(|&word| u128::from(word)).sum();
  let bytes = u32::try_from(sum & 0xffff_ffff)
    .expect("32 bits")
    .to_le_bytes()
    .map(G::from_u8);
  [
    bytes[0],
    bytes[1],
    bytes[2],
    bytes[3],
    G::from_u64(u64::try_from(sum >> 32).expect("carry fits")),
  ]
}

pub fn u32_less_than(a: G, b: G) -> (G, [G; 12]) {
  let a = u32::try_from(a.as_canonical_u64()).expect("u32 operand");
  let b = u32::try_from(b.as_canonical_u64()).expect("u32 operand");
  let c = b.wrapping_sub(a).wrapping_sub(1);
  let mut bytes = [G::ZERO; 12];
  for (dst, word) in bytes.chunks_exact_mut(4).zip([a, c, b]) {
    dst.copy_from_slice(&word.to_le_bytes().map(G::from_u8));
  }
  (G::from_bool(a < b), bytes)
}

#[cfg(test)]
pub(crate) mod tests;
