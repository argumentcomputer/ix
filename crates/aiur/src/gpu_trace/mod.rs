//! Opt-in BLAKE3 main traces from immutable query inputs and results.

mod blake3_body;

use std::sync::Arc;

use multi_stark::{
  lookup::LookupValues,
  p3_field::{Field, PrimeCharacteristicRing, PrimeField64},
  witness::{TraceGenerator, TraceSource},
};

use crate::{
  G,
  bytecode::{FunctionLayout, Toplevel},
  execute::QueryRecord,
  trace::QueryPosition,
};

pub const WIDTH: usize = 533;

#[derive(Clone)]
#[repr(C)]
struct Blake3Seed {
  multiplicity: u64,
  stage: u8,
  input: [u8; 128],
  output: [u8; 32],
  // Explicit padding keeps every byte initialized when the seed is uploaded.
  padding: [u8; 7],
}

const _: () = {
  assert!(size_of::<Blake3Seed>() == 176);
  assert!(align_of::<Blake3Seed>() == 8);
  assert!(std::mem::offset_of!(Blake3Seed, multiplicity) == 0);
  assert!(std::mem::offset_of!(Blake3Seed, stage) == 8);
  assert!(std::mem::offset_of!(Blake3Seed, input) == 9);
  assert!(std::mem::offset_of!(Blake3Seed, output) == 137);
  assert!(std::mem::offset_of!(Blake3Seed, padding) == 169);
};

const LAYOUT: FunctionLayout = FunctionLayout {
  input_size: 129,
  selectors: 2,
  auxiliaries: 402,
  lookups: 194,
};

pub(crate) fn enabled() -> bool {
  match std::env::var("AIUR_GPU_TRACE").as_deref() {
    Err(_) | Ok("cpu") => false,
    Ok("blake3") => {
      assert!(
        crate::trace::trace_only_lookups(),
        "AIUR_GPU_TRACE=blake3 requires AIUR_TRACE_ONLY_LOOKUPS=1"
      );
      true
    },
    Ok(value) => {
      panic!("unsupported AIUR_GPU_TRACE={value}; use cpu or blake3")
    },
  }
}

pub(crate) fn supported(top: &Toplevel, circuit: usize) -> bool {
  let circuit = &top.circuits[circuit];
  if circuit.members.len() != 1 || circuit.layout != LAYOUT {
    return false;
  }
  let member = circuit.members[0];
  let function = &top.functions[member];
  function.constrained
    && function.layout == LAYOUT
    && function.body == blake3_body::body(member)
}

pub(crate) fn prepare(
  top: &Toplevel,
  circuit: usize,
  record: &QueryRecord,
  slots: &[usize],
  start: QueryPosition,
  end: QueryPosition,
  row_count: usize,
) -> Option<(TraceSource<G>, LookupValues<G>)> {
  if !supported(top, circuit) || row_count == 0 {
    return None;
  }
  let member = top.circuits[circuit].members[0];
  let queries = &record.function_queries[member];
  let _g = tracing::info_span!("aiur/blake3_seeds", circuit, rows = row_count)
    .entered();
  let lo = if start.0 == 0 { start.1 } else { queries.len() };
  let hi = if end.0 == 0 { end.1 } else { queries.len() };
  let mut seeds = Vec::with_capacity(row_count);
  for (input, result) in queries.iter().skip(lo).take(hi.saturating_sub(lo)) {
    if result.multiplicity.is_zero() {
      continue;
    }
    if input.len() != 129
      || result.output.len() != 32
      || input[0].as_canonical_u64() > 7
      || input[1..]
        .iter()
        .chain(result.output)
        .any(|g| g.as_canonical_u64() > 255)
    {
      tracing::debug!(
        circuit,
        "BLAKE3 seeds require the reference trace builder"
      );
      return None;
    }
    seeds.push(Blake3Seed {
      multiplicity: result.multiplicity.as_canonical_u64(),
      stage: input[0].as_canonical_u64() as u8,
      input: std::array::from_fn(|i| input[i + 1].as_canonical_u64() as u8),
      output: std::array::from_fn(|i| {
        result.output[i].as_canonical_u64() as u8
      }),
      padding: [0; 7],
    });
  }
  assert_eq!(seeds.len(), row_count, "BLAKE3 query span row count");
  let height = row_count.next_power_of_two();
  tracing::debug!(
    circuit,
    row_count,
    height,
    seed_bytes = row_count * size_of::<Blake3Seed>(),
    main_bytes = height * WIDTH * 8,
    "prepared GPU BLAKE3 trace"
  );
  Some((
    TraceSource::Generated(Arc::new(Blake3Trace { seeds, height })),
    LookupValues::shape_only(height, slots),
  ))
}

pub struct Blake3Trace {
  seeds: Vec<Blake3Seed>,
  height: usize,
}

impl TraceGenerator<G> for Blake3Trace {
  fn height(&self) -> usize {
    self.height
  }
  fn width(&self) -> usize {
    WIDTH
  }
  fn host_bytes(&self) -> usize {
    self.seeds.capacity() * size_of::<Blake3Seed>()
  }

  fn write_rows(&self, first: usize, output: &mut [G]) {
    assert_eq!(output.len() % WIDTH, 0);
    for (offset, row) in output.chunks_exact_mut(WIDTH).enumerate() {
      row.fill(G::ZERO);
      if let Some(seed) = self.seeds.get((first + offset) % self.height) {
        write_row(seed, row);
      }
    }
  }

  fn write_device_rows(
    &self,
    output: multi_stark::cuda::DeviceTraceView<'_>,
  ) -> Result<(), String> {
    let _g =
      tracing::info_span!("aiur/blake3_device_rows", rows = output.rows())
        .entered();
    assert_eq!(output.width(), WIDTH);
    let mut done = 0;
    while done < output.rows() {
      let first = (output.first_row() + done) % self.height;
      let rows = (output.rows() - done).min(self.height - first);
      let real = rows.min(self.seeds.len().saturating_sub(first));
      let seeds =
        if real == 0 { std::ptr::null() } else { self.seeds[first..].as_ptr() };
      let status = unsafe {
        aiur_blake3_trace(
          output.device_id(),
          seeds,
          real,
          rows,
          output.as_mut_ptr().add(done * WIDTH),
        )
      };
      if status != 0 {
        return Err(format!("BLAKE3 CUDA status {status}"));
      }
      done += rows;
    }
    Ok(())
  }
}

unsafe extern "C" {
  fn aiur_blake3_trace(
    device: i32,
    seeds: *const Blake3Seed,
    real: usize,
    rows: usize,
    output: *mut u64,
  ) -> i32;
}

fn write_row(seed: &Blake3Seed, row: &mut [G]) {
  row[0] = G::from_u8(seed.stage);
  for (to, &from) in row[1..129].iter_mut().zip(&seed.input) {
    *to = G::from_u8(from);
  }
  row[131] = G::from_u64(seed.multiplicity);
  let mut at = 132;
  let mut emit = |v: u64| {
    row[at] = G::from_u64(v);
    at += 1;
  };
  let mut state = [0u32; 32];
  for (i, word) in state.iter_mut().enumerate() {
    *word =
      u32::from_le_bytes(seed.input[i * 4..i * 4 + 4].try_into().unwrap());
  }
  if seed.stage == 7 {
    for i in 0..8 {
      emit_word(&mut emit, state[i] ^ state[i + 8]);
    }
    row[129] = G::ONE;
  } else {
    emit((G::from_u8(seed.stage) - G::from_u8(7)).inverse().as_canonical_u64());
    for [a, b, c, d, x, y] in [
      [0, 4, 8, 12, 16, 17],
      [1, 5, 9, 13, 18, 19],
      [2, 6, 10, 14, 20, 21],
      [3, 7, 11, 15, 22, 23],
      [0, 5, 10, 15, 24, 25],
      [1, 6, 11, 12, 26, 27],
      [2, 7, 8, 13, 28, 29],
      [3, 4, 9, 14, 30, 31],
    ] {
      state[a] = add3(&mut emit, state[a], state[b], state[x]);
      let xor = state[d] ^ state[a];
      emit_word(&mut emit, xor);
      state[d] = xor.rotate_right(16);
      state[c] = add2(&mut emit, state[c], state[d]);
      state[b] = xor_rotate(&mut emit, state[b], state[c], 12);
      state[a] = add3(&mut emit, state[a], state[b], state[y]);
      let xor = state[d] ^ state[a];
      emit_word(&mut emit, xor);
      state[d] = xor.rotate_right(8);
      state[c] = add2(&mut emit, state[c], state[d]);
      state[b] = xor_rotate(&mut emit, state[b], state[c], 7);
    }
    for &v in &seed.output {
      emit(u64::from(v));
    }
    assert_eq!(at, WIDTH);
    row[130] = G::ONE;
  }
}

fn emit_word(emit: &mut impl FnMut(u64), word: u32) {
  for byte in word.to_le_bytes() {
    emit(u64::from(byte));
  }
}

fn add3(emit: &mut impl FnMut(u64), a: u32, b: u32, c: u32) -> u32 {
  let sum = u64::from(a) + u64::from(b) + u64::from(c);
  emit_word(emit, sum as u32);
  // The compiled product evaluates (carry - 1) * (carry - 2) first.
  emit(if sum >> 32 == 0 { 2 } else { 0 });
  emit(0);
  sum as u32
}

fn add2(emit: &mut impl FnMut(u64), a: u32, b: u32) -> u32 {
  let sum = u64::from(a) + u64::from(b);
  emit_word(emit, sum as u32);
  emit(sum >> 32);
  sum as u32
}

fn xor_rotate(emit: &mut impl FnMut(u64), a: u32, b: u32, rotate: u32) -> u32 {
  let xor = a ^ b;
  let split = if rotate == 12 { 4 } else { 7 };
  for byte in xor.to_le_bytes() {
    emit(u64::from(byte >> split));
    emit(u64::from(byte.wrapping_shl(8 - split)));
  }
  xor.rotate_right(rotate)
}

#[cfg(test)]
pub(crate) mod tests;
