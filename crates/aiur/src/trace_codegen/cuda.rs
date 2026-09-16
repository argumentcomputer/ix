//! CUDA rows from owned, immutable, encoded seeds.

use std::sync::Arc;

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
  functions: &'static [Option<Kernel>],
  seed_words: &'static [usize],
}

impl CudaLibrary {
  /// # Safety
  /// The contract must return 32 readable immutable bytes. Every kernel must
  /// implement the generated seed/writer ABI for its function index, validate
  /// output dimensions, and finish all accesses before returning.
  pub const unsafe fn new(
    fingerprint: [u8; 32],
    contract: unsafe extern "C" fn() -> *const u8,
    functions: &'static [Option<Kernel>],
    seed_words: &'static [usize],
  ) -> Self {
    Self { fingerprint, contract, functions, seed_words }
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
    {
      return Err("CUDA unit differs from the generated seed/writer contract");
    }
    for ((kernel, writer), &words) in
      self.functions.iter().zip(generated.functions).zip(self.seed_words)
    {
      if kernel.is_some()
        && writer.as_ref().is_none_or(|writer| writer.seed_words != words)
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
      let bound =
        BoundFunction { index: function, writer, bytecode: self.bytecode };
      let queries = record
        .function_queries
        .get(function)
        .ok_or_else(|| error(function, None, "record has no function table"))?;
      let lo = if member == start.0 { start.1 } else { 0 };
      let hi = if member == end.0 { end.1 } else { queries.len() };
      if lo > hi || hi > queries.len() {
        return Err(error(function, None, "invalid query span"));
      }
      let mut seed = vec![0; writer.seed_words];
      let mut packed =
        vec![
          0;
          SeedEncoding::U8Payload
            .stride(writer.seed_words)
            .ok_or_else(|| error(function, None, "seed width overflow"))?
        ];
      for query in lo..hi {
        if queries.get_index(query).unwrap().1.multiplicity == G::ZERO {
          continue;
        }
        let compact = !check_aliases
          && bound.pack_u8_row(record, io, query, &mut packed)?;
        let encoding = if compact {
          SeedEncoding::U8Payload
        } else {
          bound.pack_row(record, io, query, check_aliases, &mut seed)?;
          SeedEncoding::for_words(&seed)
            .map_err(|e| error(function, None, e))?
        };
        let stride = encoding
          .stride(writer.seed_words)
          .filter(|&n| n <= MAX_SEED_BYTES)
          .ok_or_else(|| {
            error(function, None, "seed exceeds the upload limit")
          })?;
        let continues = spans.last().is_some_and(|s| {
          s.function == function
            && s.encoding == encoding
            && s.rows < MAX_ROWS
            && s.bytes.len() <= MAX_SEED_BYTES - stride
        });
        if !continues {
          let changed_encoding = spans
            .last()
            .is_some_and(|s| s.function == function && s.encoding != encoding);
          // Finished spans retain at most twice their encoded size; only the
          // current span may reserve up to one tile ahead of its actual rows.
          if let Some(previous) = spans.last_mut() {
            if previous.bytes.capacity()
              > previous.bytes.len().saturating_mul(2)
            {
              previous.bytes.shrink_to_fit();
            }
          }
          let reserve_rows = if changed_encoding { 1 } else { hi - query };
          spans.push(SeedSpan {
            first: count,
            rows: 0,
            function,
            writer,
            kernel: self.library.functions[function].unwrap(),
            offsets,
            encoding,
            stride,
            bytes: Vec::with_capacity(
              reserve_rows
                .min(row_count - count)
                .min(MAX_ROWS)
                .min(MAX_SEED_BYTES / stride)
                * stride,
            ),
          });
        }
        let span = spans.last_mut().unwrap();
        let offset = span.bytes.len();
        span.bytes.resize(offset + stride, 0);
        if compact {
          span.bytes[offset..].copy_from_slice(&packed);
        } else {
          encoding
            .encode(&seed, &mut span.bytes[offset..])
            .map_err(|e| error(function, None, e))?;
        }
        span.rows += 1;
        count += 1;
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
          .decode(&span.bytes[offset..offset + span.stride], &mut seed)
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
        SeedEncoding::U8Payload => 1,
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
