//! CUDA rows from owned, immutable, encoded seeds.

use std::sync::Arc;

use rayon::prelude::*;

use multi_stark::{
  cuda::DeviceTraceView,
  lookup::LookupValues,
  witness::{TraceGenerator, TraceSource},
};

use super::*;
use crate::trace::QueryPosition;

const MAX_ROWS: usize = 65537;
const MAX_SEED_BYTES: usize = 16 * 1024 * 1024 - 8;

type Kernel = unsafe extern "C" fn(
  i32,
  *const u8,
  u32,
  usize,
  usize,
  usize,
  usize,
  usize,
  *mut u64,
) -> i32;

pub struct CudaLibrary {
  fingerprint: [u8; 32],
  contract: unsafe extern "C" fn() -> *const u8,
  schema: unsafe extern "C" fn() -> *const u8,
  functions: &'static [Option<Kernel>],
  seed_words: &'static [usize],
  typed_bytes: &'static [usize],
}

/// The seed layouts the compiled unit was generated with, as the unit hashes
/// them: the same encoding `Aiur.TraceCuda` emits into `aiur_trace_*_schema`,
/// recomputed here from the Rust writers so the kernels' typed loads and the
/// packers' typed stores are proven to agree at bind, not assumed from a
/// shared generation run.
pub fn schema_contract(functions: &[Option<FunctionWriter>]) -> [u8; 32] {
  let mut hasher = blake3::Hasher::new();
  hasher.update(b"aiur-trace-schema-v1\0");
  for (index, writer) in functions.iter().enumerate() {
    let Some(writer) = writer else { continue };
    for word in [index, writer.seed_words, writer.schema.bytes] {
      hasher.update(&(word as u64).to_le_bytes());
    }
    for &width in writer.schema.widths {
      hasher.update(&[width.bytes() as u8]);
    }
    for &offset in writer.schema.offsets {
      hasher.update(&(offset as u64).to_le_bytes());
    }
  }
  *hasher.finalize().as_bytes()
}

impl CudaLibrary {
  /// # Safety
  /// The contract and schema functions must return 32 readable immutable
  /// bytes. Every kernel must implement the generated seed/writer ABI for its
  /// function index, validate output dimensions, and finish all accesses
  /// before returning.
  pub const unsafe fn new(
    fingerprint: [u8; 32],
    contract: unsafe extern "C" fn() -> *const u8,
    schema: unsafe extern "C" fn() -> *const u8,
    functions: &'static [Option<Kernel>],
    seed_words: &'static [usize],
    typed_bytes: &'static [usize],
  ) -> Self {
    Self { fingerprint, contract, schema, functions, seed_words, typed_bytes }
  }

  pub fn bind<'a>(
    &'static self,
    generated: &'static GeneratedProgram,
    bytecode: &'a Toplevel,
  ) -> Result<BoundCudaProgram<'a>, &'static str> {
    generated.bind(bytecode)?;
    let compiled = unsafe { std::slice::from_raw_parts((self.contract)(), 32) };
    if generated.fingerprint != self.fingerprint
      || compiled != self.fingerprint
      || self.functions.len() != generated.functions.len()
      || self.seed_words.len() != self.functions.len()
      || self.typed_bytes.len() != self.functions.len()
    {
      return Err("CUDA unit differs from the generated seed/writer contract");
    }
    let schemas = unsafe { std::slice::from_raw_parts((self.schema)(), 32) };
    if schemas != schema_contract(generated.functions) {
      return Err("CUDA unit was compiled for different seed layouts");
    }
    for (((kernel, writer), &words), &typed) in self
      .functions
      .iter()
      .zip(generated.functions)
      .zip(self.seed_words)
      .zip(self.typed_bytes)
    {
      if kernel.is_some()
        && writer.as_ref().is_none_or(|writer| {
          writer.seed_words != words || writer.schema.bytes != typed
        })
      {
        return Err("CUDA kernel has no matching seed writer");
      }
    }
    Ok(BoundCudaProgram { library: self, generated, bytecode })
  }

  pub(crate) fn register(
    &'static self,
    generated: &'static GeneratedProgram,
    bytecode: Arc<Toplevel>,
  ) -> Result<RegisteredCudaProgram, &'static str> {
    self.bind(generated, &bytecode)?;
    Ok(RegisteredCudaProgram { library: self, generated, bytecode })
  }
}

/// A validated library and its immutable bytecode travel together across GPUs.
pub(crate) struct RegisteredCudaProgram {
  library: &'static CudaLibrary,
  generated: &'static GeneratedProgram,
  bytecode: Arc<Toplevel>,
}

impl RegisteredCudaProgram {
  pub(crate) fn bound(&self) -> BoundCudaProgram<'_> {
    BoundCudaProgram {
      library: self.library,
      generated: self.generated,
      bytecode: &self.bytecode,
    }
  }
}

pub struct BoundCudaProgram<'a> {
  library: &'static CudaLibrary,
  generated: &'static GeneratedProgram,
  bytecode: &'a Toplevel,
}

impl BoundCudaProgram<'_> {
  pub fn supports(&self, circuit: usize) -> bool {
    self.bytecode.circuits.get(circuit).is_some_and(|c| {
      c.members.iter().all(|&f| self.library.functions[f].is_some())
    })
  }

  /// The finalized record and I/O stay borrowed until packing finishes. The
  /// returned source owns its seeds; dropping or regenerating another batch
  /// cannot change these rows.
  pub fn prepare(
    &self,
    circuit: usize,
    record: &QueryRecord,
    io: &IOBuffer,
    slots: &[usize],
    start: QueryPosition,
    end: QueryPosition,
    row_count: usize,
    check_aliases: bool,
  ) -> TraceResult<(TraceSource<G>, LookupValues<G>)> {
    let _span =
      tracing::info_span!("aiur/codegen_seeds", circuit, rows = row_count)
        .entered();
    if !self.supports(circuit) || row_count == 0 {
      return Err(error(
        0,
        None,
        "missing CUDA circuit coverage or empty span",
      ));
    }
    let c = &self.bytecode.circuits[circuit];
    let mut spans: Vec<SeedSpan> = Vec::new();
    let mut count = 0usize;
    let mut selectors = c.layout.input_size;
    for (member, &function) in c.members.iter().enumerate() {
      let writer = self.generated.functions[function].as_ref().unwrap();
      let offsets = RowOffsets {
        selectors,
        auxiliaries: c.layout.input_size + c.layout.selectors,
      };
      selectors += writer.layout.selectors;
      if member < start.0 || member > end.0 {
        continue;
      }
      let bound = BoundFunction::new(function, writer, self.bytecode);
      let queries = record
        .function_queries
        .get(function)
        .ok_or_else(|| error(function, None, "record has no function table"))?;
      let lo = if member == start.0 { start.1 } else { 0 };
      let hi = if member == end.0 { end.1 } else { queries.len() };
      if lo > hi || hi > queries.len() {
        return Err(error(function, None, "invalid query span"));
      }
      let schema = writer.schema;
      if SeedEncoding::Canonical.stride(schema) > MAX_SEED_BYTES {
        return Err(error(function, None, "seed exceeds the upload limit"));
      }
      let live: Vec<usize> = (lo..hi)
        .filter(|&query| {
          queries.get_index(query).unwrap().1.multiplicity != G::ZERO
        })
        .collect();
      if live.is_empty() {
        continue;
      }
      // Chunks pack in parallel. A chunk is typed while every narrowed word
      // fits and turns full width at its first wide row, re-encoding its
      // earlier rows from their typed bytes. A member run then takes one
      // codec: if any chunk turned, the others are widened the same way, so
      // no row is ever packed twice and no span mixes encodings.
      let typed_first = !check_aliases && !schema.is_canonical();
      let mut chunks = live
        .par_chunks(CHUNK_ROWS)
        .map(|rows| {
          pack_chunk(&bound, record, io, rows, typed_first, check_aliases)
        })
        .collect::<TraceResult<Vec<_>>>()?;
      if typed_first
        && chunks.iter().any(|chunk| chunk.encoding == SeedEncoding::Canonical)
      {
        chunks.par_iter_mut().for_each(|chunk| chunk.widen(schema));
      }
      // Every chunk of the run now shares one encoding, so a span's final
      // size is known when it opens: the rest of the run, within the tile and
      // staging limits.
      let mut run_remaining: usize =
        chunks.iter().map(|chunk| chunk.rows).sum();
      for chunk in chunks {
        let stride = chunk.encoding.stride(schema);
        let mut offset = 0;
        let mut remaining = chunk.rows;
        while remaining > 0 {
          let open = spans.last().is_some_and(|s| {
            s.function == function
              && s.encoding == chunk.encoding
              && s.rows < MAX_ROWS
              && s.bytes.len() + stride <= MAX_SEED_BYTES
          });
          if !open {
            spans.push(SeedSpan {
              first: count,
              rows: 0,
              function,
              writer,
              kernel: self.library.functions[function].unwrap(),
              offsets,
              encoding: chunk.encoding,
              stride,
              bytes: Vec::with_capacity(
                run_remaining.min(MAX_ROWS).min(MAX_SEED_BYTES / stride)
                  * stride,
              ),
            });
          }
          let span = spans.last_mut().unwrap();
          let take = remaining
            .min(MAX_ROWS - span.rows)
            .min((MAX_SEED_BYTES - span.bytes.len()) / stride);
          span
            .bytes
            .extend_from_slice(&chunk.bytes[offset..offset + take * stride]);
          span.rows += take;
          count += take;
          offset += take * stride;
          remaining -= take;
          run_remaining -= take;
        }
      }
    }
    if count != row_count {
      return Err(error(0, None, "packed row count differs from query span"));
    }
    let height = count
      .checked_next_power_of_two()
      .ok_or_else(|| error(0, None, "trace height overflow"))?;
    let source =
      CudaTrace { spans, height, real: count, width: c.layout.width() };
    tracing::debug!(
      circuit,
      rows = count,
      width = source.width,
      seed_bytes =
        source.spans.iter().map(|span| span.bytes.len()).sum::<usize>(),
      seed_spans = source.spans.len(),
      "prepared generated CUDA trace"
    );
    Ok((
      TraceSource::Generated(Arc::new(source)),
      LookupValues::shape_only(height, slots),
    ))
  }
}

struct SeedSpan {
  first: usize,
  rows: usize,
  function: usize,
  writer: &'static FunctionWriter,
  kernel: Kernel,
  offsets: RowOffsets,
  encoding: SeedEncoding,
  stride: usize,
  bytes: Vec<u8>,
}

/// Rows packed together by one worker; see `prepare`.
const CHUNK_ROWS: usize = 4096;

struct PackedChunk {
  rows: usize,
  encoding: SeedEncoding,
  bytes: Vec<u8>,
}

impl PackedChunk {
  /// Typed bytes decode exactly, so widening never packs a row again.
  fn widen(&mut self, schema: &SeedSchema) {
    if self.encoding == SeedEncoding::Typed {
      self.bytes = widen_bytes(&self.bytes, schema);
      self.encoding = SeedEncoding::Canonical;
    }
  }
}

fn widen_bytes(typed: &[u8], schema: &SeedSchema) -> Vec<u8> {
  let typed_stride = schema.bytes;
  let canonical_stride = SeedEncoding::Canonical.stride(schema);
  let rows = typed.len() / typed_stride;
  let mut words = vec![0; schema.widths.len()];
  let mut canonical = vec![0; rows * canonical_stride];
  for row in 0..rows {
    schema
      .decode(&typed[row * typed_stride..(row + 1) * typed_stride], &mut words)
      .expect("typed rows were validated");
    SeedEncoding::Canonical
      .encode(
        schema,
        &words,
        &mut canonical[row * canonical_stride..(row + 1) * canonical_stride],
      )
      .expect("decoded words are canonical");
  }
  canonical
}

fn pack_chunk(
  bound: &BoundFunction<'_>,
  record: &QueryRecord,
  io: &IOBuffer,
  rows: &[usize],
  typed_first: bool,
  check_aliases: bool,
) -> TraceResult<PackedChunk> {
  let schema = bound.schema();
  let typed_stride = schema.bytes;
  let canonical_stride = SeedEncoding::Canonical.stride(schema);
  let mut encoding =
    if typed_first { SeedEncoding::Typed } else { SeedEncoding::Canonical };
  let mut bytes = Vec::with_capacity(rows.len() * encoding.stride(schema));
  let mut seed = vec![0; bound.seed_words()];
  for &query in rows {
    if encoding == SeedEncoding::Typed {
      let offset = bytes.len();
      bytes.resize(offset + typed_stride, 0);
      if bound.pack_typed_row(record, io, query, &mut bytes[offset..])? {
        continue;
      }
      bytes.truncate(offset);
      bytes = widen_bytes(&bytes, schema);
      encoding = SeedEncoding::Canonical;
    }
    bound.pack_row(record, io, query, check_aliases, &mut seed)?;
    let offset = bytes.len();
    bytes.resize(offset + canonical_stride, 0);
    SeedEncoding::Canonical
      .encode(schema, &seed, &mut bytes[offset..])
      .map_err(|e| error(bound.index, None, e))?;
  }
  Ok(PackedChunk { rows: rows.len(), encoding, bytes })
}

pub struct CudaTrace {
  spans: Vec<SeedSpan>,
  height: usize,
  real: usize,
  width: usize,
}

impl CudaTrace {
  fn span(&self, row: usize) -> &SeedSpan {
    let index =
      self.spans.partition_point(|s| s.first <= row).saturating_sub(1);
    &self.spans[index]
  }
}

impl TraceGenerator<G> for CudaTrace {
  fn height(&self) -> usize {
    self.height
  }
  fn width(&self) -> usize {
    self.width
  }
  fn host_bytes(&self) -> usize {
    self.spans.capacity() * size_of::<SeedSpan>()
      + self.spans.iter().map(|s| s.bytes.capacity()).sum::<usize>()
  }
  fn write_rows(&self, first: usize, output: &mut [G]) {
    assert_eq!(output.len() % self.width, 0);
    let mut seed = Vec::new();
    let mut canonical = vec![0; self.width];
    let mut index = first % self.height;
    for row in output.chunks_exact_mut(self.width) {
      row.fill(G::ZERO);
      if index < self.real {
        let span = self.span(index);
        seed.resize(span.writer.seed_words, 0);
        let offset = (index - span.first) * span.stride;
        span
          .encoding
          .decode(
            span.writer.schema,
            &span.bytes[offset..offset + span.stride],
            &mut seed,
          )
          .expect("validated seed");
        canonical.fill(0);
        canonical[..span.writer.layout.input_size]
          .copy_from_slice(&seed[1..1 + span.writer.layout.input_size]);
        canonical[span.offsets.auxiliaries] = seed[0];
        (span.writer.write)(&seed, span.offsets, &mut canonical)
          .expect("valid generated row");
        for (dst, &word) in row.iter_mut().zip(&canonical) {
          *dst = G::from_u64(word);
        }
      }
      index = (index + 1) % self.height;
    }
  }
  fn write_device_rows(
    &self,
    output: DeviceTraceView<'_>,
  ) -> Result<(), String> {
    let _span = tracing::info_span!(
      "aiur/codegen_device_rows",
      device = output.device_id(),
      first = output.first_row(),
      rows = output.rows(),
      width = self.width
    )
    .entered();
    if output.width() != self.width {
      return Err("CUDA trace width mismatch".into());
    }
    let mut done = 0;
    let mut first = output.first_row() % self.height;
    while done < output.rows() {
      let span = self.span(first.min(self.real - 1));
      let remaining =
        (output.rows() - done).min(self.height - first).min(MAX_ROWS);
      let (rows, real, seeds) = if first >= self.real {
        (remaining, 0, std::ptr::null())
      } else {
        let rows = remaining.min(span.first + span.rows - first);
        let offset = (first - span.first) * span.stride;
        (rows, rows, span.bytes[offset..].as_ptr())
      };
      let encoding = match span.encoding {
        SeedEncoding::Canonical => 0,
        SeedEncoding::Typed => 1,
      };
      let status = unsafe {
        (span.kernel)(
          output.device_id(),
          seeds,
          encoding,
          real,
          rows,
          self.width,
          span.offsets.selectors,
          span.offsets.auxiliaries,
          output.as_mut_ptr().add(done * self.width),
        )
      };
      if status != 0 {
        return Err(format!(
          "generated CUDA function {}, row {first}: status {status}",
          span.function
        ));
      }
      done += rows;
      first = (first + rows) % self.height;
    }
    Ok(())
  }
}

unsafe extern "C" {
  fn aiur_trace_memory(
    device: i32,
    seeds: *const u8,
    values: usize,
    real: usize,
    rows: usize,
    output: *mut u64,
  ) -> i32;
}

/// One memory table range as `[multiplicity, 1, pointer, values]` rows, built
/// on the device from `[multiplicity, pointer, values]` seeds. The seeds are
/// canonical words copied out of the record, so no packer runs; every table
/// row is real, zero multiplicities included, exactly as the CPU builder
/// emits them.
pub struct MemoryTrace {
  values: usize,
  spans: Vec<MemorySpan>,
  height: usize,
  real: usize,
}

struct MemorySpan {
  first: usize,
  rows: usize,
  bytes: Vec<u8>,
}

impl MemoryTrace {
  fn stride(&self) -> usize {
    8 * (self.values + 2)
  }

  fn span(&self, row: usize) -> &MemorySpan {
    let index =
      self.spans.partition_point(|s| s.first <= row).saturating_sub(1);
    &self.spans[index]
  }
}

/// The width-`size` table's rows at table indices `range`, row `i` carrying
/// pointer `record.pointer_base + range.start + i`. An empty range is the CPU
/// builder's case: it yields an empty trace that the prover deactivates.
pub fn prepare_memory(
  record: &QueryRecord,
  size: usize,
  slots: &[usize],
  range: std::ops::Range<usize>,
) -> TraceResult<(TraceSource<G>, LookupValues<G>)> {
  let _span =
    tracing::info_span!("aiur/codegen_memory_seeds", size, rows = range.len())
      .entered();
  let queries = record.memory_queries.get(&size).ok_or_else(|| {
    error(0, None, "record has no memory table of this width")
  })?;
  if range.is_empty() || range.end > queries.len() {
    return Err(error(0, None, "invalid memory table range"));
  }
  let stride = 8 * (size + 2);
  if stride > MAX_SEED_BYTES {
    return Err(error(0, None, "memory seed exceeds the upload limit"));
  }
  let per_span = MAX_ROWS.min(MAX_SEED_BYTES / stride);
  let count = range.len();
  let spans: Vec<MemorySpan> = (0..count)
    .step_by(per_span)
    .collect::<Vec<_>>()
    .into_par_iter()
    .map(|first| {
      let rows = per_span.min(count - first);
      let mut bytes = vec![0; rows * stride];
      for (i, seed) in bytes.chunks_exact_mut(stride).enumerate() {
        let index = range.start + first + i;
        let (values, result) =
          queries.get_index(index).expect("table index in range");
        let pointer = G::from_usize(record.pointer_base + index);
        seed[..8].copy_from_slice(
          &result.multiplicity.as_canonical_u64().to_le_bytes(),
        );
        seed[8..16].copy_from_slice(&pointer.as_canonical_u64().to_le_bytes());
        for (dst, value) in seed[16..].chunks_exact_mut(8).zip(values) {
          dst.copy_from_slice(&value.as_canonical_u64().to_le_bytes());
        }
      }
      MemorySpan { first, rows, bytes }
    })
    .collect();
  let height = count
    .checked_next_power_of_two()
    .ok_or_else(|| error(0, None, "trace height overflow"))?;
  tracing::debug!(
    size,
    rows = count,
    seed_bytes = count * stride,
    seed_spans = spans.len(),
    "prepared generated memory trace"
  );
  Ok((
    TraceSource::Generated(Arc::new(MemoryTrace {
      values: size,
      spans,
      height,
      real: count,
    })),
    LookupValues::shape_only(height, slots),
  ))
}

impl TraceGenerator<G> for MemoryTrace {
  fn height(&self) -> usize {
    self.height
  }
  fn width(&self) -> usize {
    self.values + 3
  }
  fn host_bytes(&self) -> usize {
    self.spans.capacity() * size_of::<MemorySpan>()
      + self.spans.iter().map(|s| s.bytes.capacity()).sum::<usize>()
  }
  fn write_rows(&self, first: usize, output: &mut [G]) {
    let width = self.width();
    assert_eq!(output.len() % width, 0);
    let stride = self.stride();
    let mut index = first % self.height;
    for row in output.chunks_exact_mut(width) {
      row.fill(G::ZERO);
      if index < self.real {
        let span = self.span(index);
        let offset = (index - span.first) * stride;
        let seed = &span.bytes[offset..offset + stride];
        let word = |i: usize| {
          G::from_u64(u64::from_le_bytes(
            seed[8 * i..8 * i + 8].try_into().expect("eight bytes"),
          ))
        };
        row[0] = word(0);
        row[1] = G::ONE;
        row[2] = word(1);
        for (i, cell) in row[3..].iter_mut().enumerate() {
          *cell = word(2 + i);
        }
      }
      index = (index + 1) % self.height;
    }
  }
  fn write_device_rows(
    &self,
    output: DeviceTraceView<'_>,
  ) -> Result<(), String> {
    let _span = tracing::info_span!(
      "aiur/codegen_memory_rows",
      device = output.device_id(),
      first = output.first_row(),
      rows = output.rows(),
      width = self.width()
    )
    .entered();
    if output.width() != self.width() {
      return Err("memory trace width mismatch".into());
    }
    let stride = self.stride();
    let mut done = 0;
    let mut first = output.first_row() % self.height;
    while done < output.rows() {
      let span = self.span(first.min(self.real - 1));
      let remaining =
        (output.rows() - done).min(self.height - first).min(MAX_ROWS);
      let (rows, real, seeds) = if first >= self.real {
        (remaining, 0, std::ptr::null())
      } else {
        let rows = remaining.min(span.first + span.rows - first);
        let offset = (first - span.first) * stride;
        (rows, rows, span.bytes[offset..].as_ptr())
      };
      let status = unsafe {
        aiur_trace_memory(
          output.device_id(),
          seeds,
          self.values,
          real,
          rows,
          output.as_mut_ptr().add(done * self.width()),
        )
      };
      if status != 0 {
        return Err(format!(
          "generated memory table of width {}, row {first}: status {status}",
          self.values
        ));
      }
      done += rows;
      first = (first + rows) % self.height;
    }
    Ok(())
  }
}
