use multi_stark::{
  lookup::{LookupRowMut, LookupValues},
  p3_field::{Field, PrimeCharacteristicRing, PrimeField64},
  p3_matrix::dense::RowMajorMatrix,
};
use rayon::{
  iter::{
    IndexedParallelIterator, IntoParallelRefIterator,
    IntoParallelRefMutIterator, ParallelIterator,
  },
  slice::ParallelSliceMut,
};
use std::sync::atomic::{AtomicU64, Ordering};

use crate::{
  FxIndexMap, G,
  bytecode::{Block, Ctrl, Function, Op, Toplevel},
  execute::{
    IOBuffer, IOKeyInfo, QueryRecord, find_unconstrained_big_uint_div_mod,
    g_inverse_value,
  },
  function_channel, memory_channel,
  gadgets::{bytes1::Bytes1, bytes2::Bytes2},
  memory::Memory,
  u8_add_channel, u8_and_channel, u8_bit_decomposition_channel,
  u8_less_than_channel, u8_mul_channel, u8_or_channel, u8_range_check_channel,
  u8_shift_left_channel, u8_shift_right_channel, u8_sub_channel,
  u8_xor_channel, u8_xor_split4_channel, u8_xor_split7_channel,
};

struct ColumnIndex {
  auxiliary: usize,
  lookup: usize,
}

struct ColumnMutSlice<'a, 'b> {
  inputs: &'a mut [G],
  selectors: &'a mut [G],
  auxiliaries: &'a mut [G],
  lookups: &'a mut LookupRowMut<'b, G>,
}

type Degree = u8;

fn u32_value(map: &[(G, Degree)], bytes: &[usize]) -> u64 {
  assert_eq!(bytes.len(), 4, "u32 operation requires four bytes");
  bytes.iter().enumerate().fold(0, |word, (i, idx)| {
    word | (map[*idx].0.as_canonical_u64() << (8 * i))
  })
}

fn u32_sum(values: &[u64]) -> ([G; 4], G) {
  let sum: u128 = values.iter().map(|x| u128::from(*x)).sum();
  let word = u32::try_from(sum & 0xFFFF_FFFF).expect("masked to 32 bits");
  let carry = u64::try_from(sum >> 32).expect("sum of u32 words fits in u64");
  (word.to_le_bytes().map(|b| G::from_u64(b.into())), G::from_u64(carry))
}

impl<'a, 'b> ColumnMutSlice<'a, 'b> {
  fn from_slice(
    function: &Function,
    slice: &'a mut [G],
    lookups: &'a mut LookupRowMut<'b, G>,
  ) -> Self {
    let (inputs, slice) = slice.split_at_mut(function.layout.input_size);
    let (selectors, slice) = slice.split_at_mut(function.layout.selectors);
    let (auxiliaries, slice) = slice.split_at_mut(function.layout.auxiliaries);
    assert!(slice.is_empty());
    Self { inputs, selectors, auxiliaries, lookups }
  }
}

/// What a row walk does with the values it computes. `populate_row` is
/// generic over this: the WITNESS sink ([`ColumnMutSlice`]) writes trace
/// columns and lookup rows; the COUNT sink ([`CountSink`]) tallies only
/// the consumption events (pushes) to DERIVE multiplicities from the
/// unique-query set. One walker, two consumers — the counter counts
/// exactly the pushes the witness emits, by construction, so the two
/// can never drift. `ColumnIndex` threads through both so branch-region
/// index arithmetic (`MatchContinue`) stays identical.
trait RowSink {
  fn input(&mut self, i: usize, v: G);
  fn selector(&mut self, s: usize);
  fn auxiliary(&mut self, index: &mut ColumnIndex, v: G);
  fn pull(&mut self, slot: usize, mult: G, args: &[G]);
  fn push(&mut self, index: &mut ColumnIndex, args: &[G]);
}

impl RowSink for ColumnMutSlice<'_, '_> {
  fn input(&mut self, i: usize, v: G) {
    self.inputs[i] = v;
  }

  fn selector(&mut self, s: usize) {
    self.selectors[s] = G::ONE;
  }

  fn auxiliary(&mut self, index: &mut ColumnIndex, v: G) {
    self.auxiliaries[index.auxiliary] = v;
    index.auxiliary += 1;
  }

  fn pull(&mut self, slot: usize, mult: G, args: &[G]) {
    self.lookups.pull(slot, mult, args);
  }

  // Every push in the row walk has multiplicity ONE (call sites,
  // memory ops, gadget ops each consume exactly once per row).
  fn push(&mut self, index: &mut ColumnIndex, args: &[G]) {
    self.lookups.push(index.lookup, G::ONE, args);
    index.lookup += 1;
  }
}

#[derive(Clone, Copy)]
struct TraceContext<'a> {
  function_index: G,
  multiplicity: G,
  inputs: &'a [G],
  output: &'a [G],
  query_record: &'a QueryRecord,
}

/// Reusable per-worker buffers for the row replay (witness generation
/// and multiplicity derivation both walk rows through the same code):
/// value collections and lookup-argument tuples are built in place so
/// the walk allocates nothing per row or per op.
#[derive(Default)]
struct ReplayBufs {
  /// Value collections (call inputs, stored values, io keys).
  key: Vec<G>,
  /// Lookup argument tuples (function/memory/gadget channels).
  args: Vec<G>,
}

impl Toplevel {
  pub fn witness_data(
    &self,
    function_index: usize,
    query_record: &QueryRecord,
    io_buffer: &IOBuffer,
    slot_arg_widths: &[usize],
  ) -> (RowMajorMatrix<G>, LookupValues<G>) {
    let func = &self.functions[function_index];
    let width = func.width();
    let unfiltered_queries = &query_record.function_queries[function_index];
    // Live rows (multiplicity != 0) as u32 indices — 4 bytes per row
    // instead of a 40-byte entry-reference tuple — and no vector at
    // all in the common sealed case where every entry is live.
    let n = unfiltered_queries.len();
    let live_count =
      (0..n).filter(|&i| !unfiltered_queries.mult_is_zero(i)).count();
    let live: Option<Vec<u32>> = if live_count == n {
      None
    } else {
      Some(
        (0..n)
          .filter(|&i| !unfiltered_queries.mult_is_zero(i))
          .map(|i| u32::try_from(i).expect("row index fits u32"))
          .collect(),
      )
    };
    let height_no_padding = live_count;
    // An unqueried circuit yields an EMPTY trace (not a padded height-1 one):
    // the prover deactivates it, so it is neither committed nor opened.
    let height = if height_no_padding == 0 {
      0
    } else {
      height_no_padding.next_power_of_two()
    };
    let mut rows = vec![G::ZERO; height * width];
    let rows_no_padding = &mut rows[0..height_no_padding * width];
    // Builder rows start zeroed (`Lookup::empty()` in every slot), so padding
    // rows need no writes at all.
    let mut builder = LookupValues::builder(height, slot_arg_widths);
    let mut row_writers = builder.rows_mut();
    rows_no_padding
      .par_chunks_mut(width)
      .zip(row_writers[..height_no_padding].par_iter_mut())
      .enumerate()
      .for_each_init(
        || (Vec::new(), ReplayBufs::default()),
        |(map, bufs), (i, (row, lookups))| {
          let qi = live.as_ref().map_or(i, |v| v[i] as usize);
          let (inputs, result) =
            unfiltered_queries.get_index(qi).expect("live row in range");
          let index = &mut ColumnIndex {
            auxiliary: 0,
            // we skip the first lookup, which is reserved for return
            lookup: 1,
          };
          let slice = &mut ColumnMutSlice::from_slice(func, row, lookups);
          let context = TraceContext {
            function_index: G::from_usize(function_index),
            inputs,
            multiplicity: result.multiplicity,
            output: result.output,
            query_record,
          };
          func.populate_row(index, slice, context, io_buffer, map, bufs);
        },
      );
    drop(row_writers);
    let trace = RowMajorMatrix::new(rows, width);
    (trace, builder.finish())
  }
}

impl Function {
  pub fn width(&self) -> usize {
    self.layout.input_size + self.layout.auxiliaries + self.layout.selectors
  }

  fn populate_row<S: RowSink>(
    &self,
    index: &mut ColumnIndex,
    sink: &mut S,
    context: TraceContext<'_>,
    io_buffer: &IOBuffer,
    map: &mut Vec<(G, Degree)>,
    bufs: &mut ReplayBufs,
  ) {
    debug_assert_eq!(
      self.layout.input_size,
      context.inputs.len(),
      "Argument mismatch"
    );
    // Variable to value map (caller-owned scratch, reused across rows).
    map.clear();
    map.extend(context.inputs.iter().map(|arg| (*arg, 1)));
    // One column per input
    context
      .inputs
      .iter()
      .enumerate()
      .for_each(|(i, arg)| sink.input(i, *arg));
    // Push the multiplicity
    sink.auxiliary(index, context.multiplicity);
    let _ = self.body.populate_row(map, index, sink, context, io_buffer, bufs);
  }
}

/// `Some(values)` means the block ended with `Yield` (values for the merge).
/// `None` means the block ended with `Return` (function exited).
type PopulateResult = Option<Vec<G>>;

impl Block {
  fn populate_row<S: RowSink>(
    &self,
    map: &mut Vec<(G, Degree)>,
    index: &mut ColumnIndex,
    sink: &mut S,
    context: TraceContext<'_>,
    io_buffer: &IOBuffer,
    bufs: &mut ReplayBufs,
  ) -> PopulateResult {
    self.ops.iter().for_each(|op| {
      op.populate_row(map, index, sink, context, io_buffer, bufs)
    });
    self.ctrl.populate_row(map, index, sink, context, io_buffer, bufs)
  }
}

/// Dispatch a match: look up the value in the cases map, or fall through to the
/// default (pushing inverse witnesses for each case to prove inequality).
fn dispatch_branch<'a, S: RowSink>(
  val: G,
  cases: &'a FxIndexMap<G, Block>,
  def: &'a Option<Box<Block>>,
  index: &mut ColumnIndex,
  sink: &mut S,
) -> &'a Block {
  cases
    .get(&val)
    .or_else(|| {
      for &case in cases.keys() {
        let witness = (val - case).inverse();
        sink.auxiliary(index, witness);
      }
      def.as_deref()
    })
    .expect("No match")
}

impl Ctrl {
  fn populate_row<S: RowSink>(
    &self,
    map: &mut Vec<(G, Degree)>,
    index: &mut ColumnIndex,
    sink: &mut S,
    context: TraceContext<'_>,
    io_buffer: &IOBuffer,
    bufs: &mut ReplayBufs,
  ) -> PopulateResult {
    match self {
      Ctrl::Return(sel, _) => {
        sink.selector(*sel);
        function_lookup_args_into(
          &mut bufs.args,
          context.function_index,
          context.inputs,
          context.output,
        );
        // The first lookup slot is reserved for the function return, which
        // pulls the query claim with the query's multiplicity.
        sink.pull(0, context.multiplicity, &bufs.args);
        None
      },
      Ctrl::Yield(sel, vals) => {
        sink.selector(*sel);
        Some(vals.iter().map(|&v| map[v].0).collect())
      },
      Ctrl::Match(var, cases, def) => {
        let branch = dispatch_branch(map[*var].0, cases, def, index, sink);
        branch.populate_row(map, index, sink, context, io_buffer, bufs)
      },
      Ctrl::MatchContinue(
        var,
        cases,
        def,
        _output_size,
        shared_aux,
        shared_lookups,
        continuation,
      ) => {
        let map_len = map.len();
        let init_aux = index.auxiliary;
        let init_lookup = index.lookup;

        let branch = dispatch_branch(map[*var].0, cases, def, index, sink);
        let result =
          branch.populate_row(map, index, sink, context, io_buffer, bufs);
        match result {
          Some(yielded) => {
            // Advance past the shared branch region. The taken branch may
            // use fewer auxiliaries/lookups than the max across all branches.
            index.auxiliary = init_aux + shared_aux;
            index.lookup = init_lookup + shared_lookups;

            map.truncate(map_len);
            for &val in &yielded {
              sink.auxiliary(index, val);
              map.push((val, 1));
            }
            continuation.populate_row(map, index, sink, context, io_buffer, bufs)
          },
          None => None,
        }
      },
    }
  }
}

impl Op {
  fn populate_row<S: RowSink>(
    &self,
    map: &mut Vec<(G, Degree)>,
    index: &mut ColumnIndex,
    sink: &mut S,
    context: TraceContext<'_>,
    io_buffer: &IOBuffer,
    bufs: &mut ReplayBufs,
  ) {
    match self {
      Op::Const(f) => map.push((*f, 0)),
      Op::Add(a, b) => {
        let (a, a_deg) = map[*a];
        let (b, b_deg) = map[*b];
        let deg = a_deg.max(b_deg);
        map.push((a + b, deg));
      },
      Op::Sub(a, b) => {
        let (a, a_deg) = map[*a];
        let (b, b_deg) = map[*b];
        let deg = a_deg.max(b_deg);
        map.push((a - b, deg));
      },
      Op::Mul(a, b) => {
        let (a, a_deg) = map[*a];
        let (b, b_deg) = map[*b];
        let deg = a_deg + b_deg;
        let f = a * b;
        if deg < 2 {
          map.push((f, deg));
        } else {
          map.push((f, 1));
          sink.auxiliary(index, f);
        }
      },
      Op::EqZero(a) => {
        let (a, deg) = map[*a];
        let is_zero = a == G::ZERO;
        let is_zero_g = G::from_bool(is_zero);
        if deg == 0 {
          map.push((is_zero_g, 0));
        } else {
          let (d, x) =
            if is_zero { (G::ZERO, G::ONE) } else { (a.inverse(), G::ZERO) };
          sink.auxiliary(index, d);
          sink.auxiliary(index, x);
          map.push((is_zero_g, 1));
        }
      },
      Op::Call(function_index, inputs, _, op_unconstrained) => {
        bufs.key.clear();
        bufs.key.extend(inputs.iter().map(|a| map[*a].0));
        let queries = &context.query_record.function_queries[*function_index];
        let result = queries.get(&bufs.key).expect("Cannot find query result");
        for f in result.output.iter() {
          map.push((*f, 1));
          sink.auxiliary(index, *f);
        }
        if !op_unconstrained {
          function_lookup_args_into(
            &mut bufs.args,
            G::from_usize(*function_index),
            &bufs.key,
            result.output,
          );
          sink.push(index, &bufs.args);
        }
      },
      Op::Store(values) => {
        let size = values.len();
        let memory_queries = context
          .query_record
          .memory_queries
          .get(&size)
          .expect("Invalid memory size");
        bufs.key.clear();
        bufs.key.extend(values.iter().map(|a| map[*a].0));
        let ptr = G::from_usize(
          memory_queries.get_index_of(&bufs.key).expect("Unbound pointer"),
        );
        map.push((ptr, 1));
        sink.auxiliary(index, ptr);
        Memory::lookup_args_into(
          &mut bufs.args,
          G::from_usize(size),
          ptr,
          &bufs.key,
        );
        sink.push(index, &bufs.args);
      },
      Op::Load(size, ptr) => {
        let memory_queries = context
          .query_record
          .memory_queries
          .get(size)
          .expect("Invalid memory size");
        let (ptr, _) = map[*ptr];
        let ptr_u64 = ptr.as_canonical_u64();
        let ptr_usize = usize::try_from(ptr_u64).expect("Pointer is too big");
        let (values, _) =
          memory_queries.get_index(ptr_usize).expect("Unbound pointer");
        for f in values.iter() {
          map.push((*f, 1));
          sink.auxiliary(index, *f);
        }
        Memory::lookup_args_into(
          &mut bufs.args,
          G::from_usize(*size),
          ptr,
          values,
        );
        sink.push(index, &bufs.args);
      },
      Op::IOGetInfo(channel, key) => {
        let channel = map[*channel].0;
        bufs.key.clear();
        bufs.key.extend(key.iter().map(|a| map[*a].0));
        let IOKeyInfo { idx, len } = io_buffer
          .get_info_frozen(channel, &bufs.key)
          .expect("Invalid IO key");
        for f in [G::from_usize(idx), G::from_usize(len)] {
          map.push((f, 1));
          sink.auxiliary(index, f);
        }
      },
      Op::IORead(channel, idx, len) => {
        let channel = map[*channel].0;
        let idx = map[*idx]
          .0
          .as_canonical_u64()
          .try_into()
          .expect("Index is too big for an usize");
        // Borrowed read: the returned slice lives in the io buffer,
        // disjoint from the map/sink this loop writes.
        let data =
          io_buffer.read(channel, idx, *len).expect("IO read out of bounds");
        for &f in data {
          map.push((f, 1));
          sink.auxiliary(index, f);
        }
      },
      Op::U8BitDecomposition(byte) => {
        let (byte, _) = map[*byte];
        let bits = Bytes1::bit_decompose(&byte);
        for &b in &bits {
          map.push((b, 1));
          sink.auxiliary(index, b);
        }
        bufs.args.clear();
        bufs.args.extend([u8_bit_decomposition_channel(), byte]);
        bufs.args.extend(bits);
        sink.push(index, &bufs.args);
      },
      Op::U8ShiftLeft(byte) => {
        let (byte, _) = map[*byte];
        let byte_shifted = Bytes1::shift_left(&byte);
        map.push((byte_shifted, 1));
        sink.auxiliary(index, byte_shifted);
        sink.push(index, &[u8_shift_left_channel(), byte, byte_shifted],
        );
      },
      Op::U8ShiftRight(byte) => {
        let (byte, _) = map[*byte];
        let byte_shifted = Bytes1::shift_right(&byte);
        map.push((byte_shifted, 1));
        sink.auxiliary(index, byte_shifted);
        sink.push(index, &[u8_shift_right_channel(), byte, byte_shifted],
        );
      },
      Op::U8Xor(i, j) => {
        let (i, _) = map[*i];
        let (j, _) = map[*j];
        let xor = Bytes2::xor(&i, &j);
        map.push((xor, 1));
        sink.auxiliary(index, xor);
        sink.push(index, &[u8_xor_channel(), i, j, xor]);
      },
      Op::U8Add(i, j) => {
        let (i, _) = map[*i];
        let (j, _) = map[*j];
        // Only the low byte `r` is witnessed (one auxiliary + the add lookup).
        // The carry `o` is a derived value, pushed to the map for downstream
        // ops but not materialized as a column.
        let (r, o) = Bytes2::add(&i, &j);
        map.push((r, 1));
        map.push((o, 1));
        sink.auxiliary(index, r);
        sink.push(index, &[u8_add_channel(), i, j, r]);
      },
      Op::UnconstrainedU32Add(a, b) => {
        let (bytes, carry) = u32_sum(&[u32_value(map, a), u32_value(map, b)]);
        for byte in bytes {
          map.push((byte, 1));
          sink.auxiliary(index, byte);
        }
        map.push((carry, 1));
      },
      Op::UnconstrainedU32Add3(a, b, c) => {
        let (bytes, carry) =
          u32_sum(&[u32_value(map, a), u32_value(map, b), u32_value(map, c)]);
        for byte in bytes {
          map.push((byte, 1));
          sink.auxiliary(index, byte);
        }
        map.push((carry, 1));
      },
      Op::U32ToField(bytes) => {
        let word = u32_value(map, bytes);
        let degree = bytes.iter().map(|idx| map[*idx].1).max().unwrap_or(0);
        map.push((G::from_u64(word), degree));
      },
      Op::U8Mul(i, j) => {
        let (i, _) = map[*i];
        let (j, _) = map[*j];
        let (lo, hi) = Bytes2::mul(&i, &j);
        map.push((lo, 1));
        map.push((hi, 1));
        sink.auxiliary(index, lo);
        sink.auxiliary(index, hi);
        sink.push(index, &[u8_mul_channel(), i, j, lo, hi]);
      },
      Op::U8Sub(i, j) => {
        let (i, _) = map[*i];
        let (j, _) = map[*j];
        // Only the low byte `r` is witnessed (one auxiliary + the sub lookup).
        // The borrow `u` is derived, pushed to the map for downstream ops but
        // not materialized as a column.
        let (r, u) = Bytes2::sub(&i, &j);
        map.push((r, 1));
        map.push((u, 1));
        sink.auxiliary(index, r);
        sink.push(index, &[u8_sub_channel(), i, j, r]);
      },
      Op::U8And(i, j) => {
        let (i, _) = map[*i];
        let (j, _) = map[*j];
        let and = Bytes2::and(&i, &j);
        map.push((and, 1));
        sink.auxiliary(index, and);
        sink.push(index, &[u8_and_channel(), i, j, and]);
      },
      Op::U8Or(i, j) => {
        let (i, _) = map[*i];
        let (j, _) = map[*j];
        let or = Bytes2::or(&i, &j);
        map.push((or, 1));
        sink.auxiliary(index, or);
        sink.push(index, &[u8_or_channel(), i, j, or]);
      },
      Op::U8LessThan(i, j) => {
        let (i, _) = map[*i];
        let (j, _) = map[*j];
        let less_than = Bytes2::less_than(&i, &j);
        map.push((less_than, 1));
        sink.auxiliary(index, less_than);
        sink.push(index, &[u8_less_than_channel(), i, j, less_than],
        );
      },
      Op::U8XorSplit7(i, j) => {
        let (i, _) = map[*i];
        let (j, _) = map[*j];
        let (hi, lo) = Bytes2::xor_split7(&i, &j);
        map.extend([(hi, 1), (lo, 1)]);
        sink.auxiliary(index, hi);
        sink.auxiliary(index, lo);
        sink.push(index, &[u8_xor_split7_channel(), i, j, hi, lo],
        );
      },
      Op::U8XorSplit4(i, j) => {
        let (i, _) = map[*i];
        let (j, _) = map[*j];
        let (hi, lo) = Bytes2::xor_split4(&i, &j);
        map.extend([(hi, 1), (lo, 1)]);
        sink.auxiliary(index, hi);
        sink.auxiliary(index, lo);
        sink.push(index, &[u8_xor_split4_channel(), i, j, hi, lo],
        );
      },
      Op::U32LessThan(x_idx, y_idx) => {
        let (a, _) = map[*x_idx];
        let (b, _) = map[*y_idx];
        let a_u32 = u32::try_from(a.as_canonical_u64()).unwrap();
        let b_u32 = u32::try_from(b.as_canonical_u64()).unwrap();
        let x_bytes: [u8; 4] = a_u32.to_le_bytes();
        let z_bytes: [u8; 4] = b_u32.to_le_bytes();
        // Witness: c = if a < b then b - a - 1 else 2^32 + b - a - 1
        let c_u32 = b_u32.wrapping_sub(a_u32).wrapping_sub(1);
        let y_bytes: [u8; 4] = c_u32.to_le_bytes();

        // Push 12 byte auxiliaries: x (a bytes), y (c bytes), z (b bytes)
        for &byte in x_bytes.iter().chain(y_bytes.iter()).chain(z_bytes.iter())
        {
          sink.auxiliary(index, G::from_u8(byte));
        }

        // Range-check byte pairs via Bytes2 lookups
        let rc_channel = u8_range_check_channel();
        for (i, j) in [
          (x_bytes[0], x_bytes[1]),
          (x_bytes[2], x_bytes[3]),
          (y_bytes[0], y_bytes[1]),
          (y_bytes[2], y_bytes[3]),
          (z_bytes[0], z_bytes[1]),
          (z_bytes[2], z_bytes[3]),
        ] {
          sink.push(index, &[rc_channel, G::from_u8(i), G::from_u8(j)],
          );
        }

        let result = G::from_bool(a_u32 < b_u32);
        map.push((result, 1));
      },
      Op::U8RangeCheck(i, j) => {
        // No `map.push`: the `u8` outputs alias the inputs. Just require the
        // `(i, j)` pair from the byte-chip range-check table.
        sink.push(index, &[u8_range_check_channel(), map[*i].0, map[*j].0],
        );
      },
      Op::UnconstrainedBigUintDivMod(tag, a, b) => {
        // Mirrors the execute arm and the two auxiliary columns the
        // constraints allocate: recompute `(q, r)` and resolve the head
        // pointers execution recorded in the type-tagged list memory.
        // Skipping the two map pushes would shift every later `ValIdx`
        // (and witness column) in the block.
        let (q_ptr, r_ptr) = find_unconstrained_big_uint_div_mod(
          map[*tag].0,
          map[*a].0,
          map[*b].0,
          &context.query_record.memory_queries,
        )
        .expect("BigUint div-mod result not recorded");
        for f in [q_ptr, r_ptr] {
          map.push((f, 1));
          sink.auxiliary(index, f);
        }
      },
      Op::UnconstrainedGToBytes(a) => {
        // Recompute the deterministic hint (canonical LE bytes) and fill
        // the 8 auxiliary columns the constraints allocate.
        let bytes = map[*a].0.as_canonical_u64().to_le_bytes();
        for b in bytes {
          let f = G::from_u8(b);
          map.push((f, 1));
          sink.auxiliary(index, f);
        }
      },
      Op::UnconstrainedGInverse(a) => {
        let f = g_inverse_value(map[*a].0);
        map.push((f, 1));
        sink.auxiliary(index, f);
      },
      Op::AssertEq(..)
      | Op::IOSetInfo(..)
      | Op::IOWrite(..)
      | Op::Debug(..) => {},
    }
  }
}

/// Function-channel lookup tuple into a reusable buffer — the row
/// replay is allocation-free.
fn function_lookup_args_into(
  buf: &mut Vec<G>,
  function_index: G,
  inputs: &[G],
  output: &[G],
) {
  buf.clear();
  buf.extend([function_channel(), function_index]);
  buf.extend_from_slice(inputs);
  buf.extend_from_slice(output);
}

/// Derived multiplicity tallies for one record: everything the logUp
/// balance consumes, computed FROM the unique-query set instead of
/// accumulated during execution. Multiplicities are a function of the
/// set — each live row consumes its callees/memory/gadget lookups once
/// per call site, claims consume their entries once — so they can be
/// derived exactly at seal by walking live rows with a counting sink.
/// This is what makes duplicate speculative execution sound: execution
/// only has to produce the SET (insert-once, confluent under races);
/// nothing accumulated at runtime enters the witness.
pub struct MultTally {
  /// Per function, per entry index (parallel to
  /// `record.function_queries`).
  pub fn_mults: Vec<Vec<AtomicU64>>,
  /// Memory widths in `record.memory_queries` iteration order, and the
  /// per-entry tallies parallel to them.
  pub mem_widths: Vec<usize>,
  pub mem_mults: Vec<Vec<AtomicU64>>,
  /// Bytes1 gadget counters, row-major `[byte][col]`, cols as in
  /// `Bytes1Queries` (0 = bit_decomposition, 1 = shift_left,
  /// 2 = shift_right).
  pub bytes1: Vec<AtomicU64>,
  /// Bytes2 gadget counters, row-major `[256*i + j][col]`, cols as in
  /// `Bytes2Queries` (0 = xor, 1 = add, 2 = sub, 3 = and, 4 = or,
  /// 5 = less_than, 6 = range_check, 7 = mul, 8 = xor_split7,
  /// 9 = xor_split4).
  pub bytes2: Vec<AtomicU64>,
}

const BYTES1_COLS: usize = 3;
const BYTES2_COLS: usize = 10;

fn atomic_zeros(n: usize) -> Vec<AtomicU64> {
  let mut v = Vec::with_capacity(n);
  v.resize_with(n, || AtomicU64::new(0));
  v
}

impl MultTally {
  fn new(record: &QueryRecord) -> Self {
    let fn_mults =
      record.function_queries.iter().map(|m| atomic_zeros(m.len())).collect();
    let mut mem_widths = Vec::new();
    let mut mem_mults = Vec::new();
    for (w, m) in &record.memory_queries {
      mem_widths.push(*w);
      mem_mults.push(atomic_zeros(m.len()));
    }
    Self {
      fn_mults,
      mem_widths,
      mem_mults,
      bytes1: atomic_zeros(256 * BYTES1_COLS),
      bytes2: atomic_zeros(256 * 256 * BYTES2_COLS),
    }
  }

  /// Add one consumption of function `f` entry `idx`; returns the
  /// PREVIOUS count (0 means this bump made the entry live — the
  /// caller enqueues its row exactly once).
  fn fn_add(&self, f: usize, idx: usize) -> u64 {
    self.fn_mults[f][idx].fetch_add(1, Ordering::Relaxed)
  }
}

/// Dense width -> slot table for the memory pushes of a derivation
/// walk (widths are few and small, so a direct-indexed array replaces
/// the per-push linear scan).
fn width_slots(record: &QueryRecord) -> Vec<u32> {
  let max = record.memory_queries.iter().map(|(w, _)| *w).max().unwrap_or(0);
  let mut slots = vec![u32::MAX; max + 1];
  for (i, (w, _)) in record.memory_queries.iter().enumerate() {
    slots[*w] = u32::try_from(i).expect("memory slot fits u32");
  }
  slots
}

/// Where a derivation walk's counts land. Two stores share the walk:
/// the standalone [`MultTally`] (differential tests against
/// accumulated counts) and the record's own multiplicity cells
/// (production seal — sound because generated execution is set-only,
/// so every cell is zero until derivation writes it, and no shadow
/// arrays or copy-back pass exist).
trait MultStore: Sync {
  /// Previous count of function `f` entry `idx` (0 = this bump made
  /// the entry live).
  fn fn_add(&self, f: usize, idx: usize) -> u64;
  fn mem_add(&self, width: usize, ptr: usize);
  fn bytes1_add(&self, byte: usize, col: usize);
  fn bytes2_add(&self, cell: usize, col: usize);
}

struct TallyStore<'a> {
  tally: &'a MultTally,
  width_slot: Vec<u32>,
}

impl MultStore for TallyStore<'_> {
  fn fn_add(&self, f: usize, idx: usize) -> u64 {
    self.tally.fn_add(f, idx)
  }
  fn mem_add(&self, width: usize, ptr: usize) {
    let slot = self.width_slot[width] as usize;
    self.tally.mem_mults[slot][ptr].fetch_add(1, Ordering::Relaxed);
  }
  fn bytes1_add(&self, byte: usize, col: usize) {
    self.tally.bytes1[byte * BYTES1_COLS + col]
      .fetch_add(1, Ordering::Relaxed);
  }
  fn bytes2_add(&self, cell: usize, col: usize) {
    self.tally.bytes2[cell * BYTES2_COLS + col]
      .fetch_add(1, Ordering::Relaxed);
  }
}

struct RecordStore<'a> {
  record: &'a QueryRecord,
  /// Memory maps in `width_slot` order (borrowed once, so pushes skip
  /// the per-push map lookup entirely).
  mems: Vec<&'a crate::querymap::QueryMap>,
  width_slot: Vec<u32>,
}

impl MultStore for RecordStore<'_> {
  fn fn_add(&self, f: usize, idx: usize) -> u64 {
    self.record.function_queries[f].mult_add(idx)
  }
  fn mem_add(&self, width: usize, ptr: usize) {
    let slot = self.width_slot[width] as usize;
    self.mems[slot].mult_add(ptr);
  }
  fn bytes1_add(&self, byte: usize, col: usize) {
    self.record.bytes1_queries.add_count(byte, col);
  }
  fn bytes2_add(&self, cell: usize, col: usize) {
    self.record.bytes2_queries.add_count(cell, col);
  }
}

/// Counting sink: tallies exactly the pushes the witness sink would
/// emit for the same row, classified by lookup channel. Newly-live
/// function entries land in `frontier` for the wave loop to walk.
struct CountSink<'a, S: MultStore> {
  toplevel: &'a Toplevel,
  record: &'a QueryRecord,
  store: &'a S,
  frontier: &'a mut Vec<(u32, u32)>,
}

impl<S: MultStore> RowSink for CountSink<'_, S> {
  fn input(&mut self, _i: usize, _v: G) {}

  fn selector(&mut self, _s: usize) {}

  fn auxiliary(&mut self, _index: &mut ColumnIndex, _v: G) {}

  fn pull(&mut self, _slot: usize, _mult: G, _args: &[G]) {}

  fn push(&mut self, _index: &mut ColumnIndex, args: &[G]) {
    let ch = args[0];
    if ch == function_channel() {
      let f = usize::try_from(args[1].as_canonical_u64())
        .expect("function index fits usize");
      let input_size = self.toplevel.functions[f].layout.input_size;
      let key = &args[2..2 + input_size];
      let idx = self.record.function_queries[f]
        .get_index_of(key)
        .expect("pushed function query must exist in the record");
      if self.store.fn_add(f, idx) == 0 {
        // Unconstrained functions have no circuit, hence no rows to
        // walk (the compiler only emits constrained pushes to
        // constrained callees; tallying is still harmless).
        if self.toplevel.functions[f].constrained {
          self.frontier.push((
            u32::try_from(f).expect("fn idx fits u32"),
            u32::try_from(idx).expect("entry idx fits u32"),
          ));
        }
      }
    } else if ch == memory_channel() {
      let width = usize::try_from(args[1].as_canonical_u64())
        .expect("memory width fits usize");
      let ptr = usize::try_from(args[2].as_canonical_u64())
        .expect("memory pointer fits usize");
      self.store.mem_add(width, ptr);
    } else {
      // Byte-gadget channels: cell + column mirror the Queries tables.
      let (table2, col) = if ch == u8_xor_channel() {
        (true, 0)
      } else if ch == u8_add_channel() {
        (true, 1)
      } else if ch == u8_sub_channel() {
        (true, 2)
      } else if ch == u8_and_channel() {
        (true, 3)
      } else if ch == u8_or_channel() {
        (true, 4)
      } else if ch == u8_less_than_channel() {
        (true, 5)
      } else if ch == u8_range_check_channel() {
        (true, 6)
      } else if ch == u8_mul_channel() {
        (true, 7)
      } else if ch == u8_xor_split7_channel() {
        (true, 8)
      } else if ch == u8_xor_split4_channel() {
        (true, 9)
      } else if ch == u8_bit_decomposition_channel() {
        (false, 0)
      } else if ch == u8_shift_left_channel() {
        (false, 1)
      } else if ch == u8_shift_right_channel() {
        (false, 2)
      } else {
        panic!("unknown lookup channel {}", ch.as_canonical_u64())
      };
      let i = usize::try_from(args[1].as_canonical_u64()).expect("byte");
      if table2 {
        let j = usize::try_from(args[2].as_canonical_u64()).expect("byte");
        self.store.bytes2_add(256 * i + j, col);
      } else {
        self.store.bytes1_add(i, col);
      }
    }
  }
}

/// Walk one live row with the counting sink, appending newly-live
/// entries to `out`.
fn count_row<S: MultStore>(
  toplevel: &Toplevel,
  record: &QueryRecord,
  io_buffer: &IOBuffer,
  store: &S,
  f: usize,
  idx: usize,
  out: &mut Vec<(u32, u32)>,
  map: &mut Vec<(G, Degree)>,
  bufs: &mut ReplayBufs,
) {
  let func = &toplevel.functions[f];
  let (inputs, res) = record.function_queries[f]
    .get_index(idx)
    .expect("live entry index in range");
  let mut sink = CountSink { toplevel, record, store, frontier: out };
  let context = TraceContext {
    function_index: G::from_usize(f),
    multiplicity: G::ZERO,
    inputs,
    output: res.output,
    query_record: record,
  };
  let index = &mut ColumnIndex { auxiliary: 0, lookup: 1 };
  func.populate_row(index, &mut sink, context, io_buffer, map, bufs);
}

/// The shared derivation walk: seed each claim's entry with one
/// consumption, then walk newly-live rows in parallel waves — each
/// live row is walked exactly once (the 0→1 transition enqueues it),
/// counting every push the witness for that row would emit into
/// `store`. Terminates because liveness only grows.
fn derive_into<S: MultStore>(
  toplevel: &Toplevel,
  record: &QueryRecord,
  io_buffer: &IOBuffer,
  claims: &[(usize, Vec<G>)],
  store: &S,
) {
  let mut frontier: Vec<(u32, u32)> = Vec::new();
  for (f, input) in claims {
    let idx = record.function_queries[*f]
      .get_index_of(input)
      .expect("claimed query must exist in the record");
    if store.fn_add(*f, idx) == 0 && toplevel.functions[*f].constrained {
      frontier.push((
        u32::try_from(*f).expect("fn idx fits u32"),
        u32::try_from(idx).expect("entry idx fits u32"),
      ));
    }
  }
  while !frontier.is_empty() {
    frontier = frontier
      .par_iter()
      .fold(
        || (Vec::new(), Vec::new(), ReplayBufs::default()),
        |(mut acc, mut map, mut bufs), &(f, idx)| {
          count_row(
            toplevel,
            record,
            io_buffer,
            store,
            f as usize,
            idx as usize,
            &mut acc,
            &mut map,
            &mut bufs,
          );
          (acc, map, bufs)
        },
      )
      .map(|(acc, _, _)| acc)
      .reduce(Vec::new, |mut a, mut b| {
        a.append(&mut b);
        a
      });
  }
}

/// Derive every multiplicity of `record` into a standalone
/// [`MultTally`]. This is the DIFFERENTIAL-TEST path (compare against
/// accumulated counts via [`diff_multiplicities`]); the production
/// seal uses [`derive_multiplicities_into`], which needs no shadow
/// arrays.
pub fn derive_multiplicities(
  toplevel: &Toplevel,
  record: &QueryRecord,
  io_buffer: &IOBuffer,
  claims: &[(usize, Vec<G>)],
) -> MultTally {
  let tally = MultTally::new(record);
  let store = TallyStore { tally: &tally, width_slot: width_slots(record) };
  derive_into(toplevel, record, io_buffer, claims, &store);
  tally
}

/// Derive every multiplicity of `record` DIRECTLY into its own
/// multiplicity cells and gadget counters — the production seal.
/// Sound because generated execution is set-only (the codegen
/// invariant: emitted inserts never bump): every cell is zero until
/// this walk bumps it, so counting in place yields exactly the counts
/// a standalone tally would, with no shadow arrays and no copy-back
/// pass. Additive, NOT idempotent: call exactly once, on a
/// freshly executed record (debug builds assert the zero state).
pub fn derive_multiplicities_into(
  toplevel: &Toplevel,
  record: &QueryRecord,
  io_buffer: &IOBuffer,
  claims: &[(usize, Vec<G>)],
) {
  debug_assert_record_counts_zero(record);
  let mems: Vec<&crate::querymap::QueryMap> =
    record.memory_queries.iter().map(|(_, m)| m).collect();
  let store = RecordStore { record, mems, width_slot: width_slots(record) };
  derive_into(toplevel, record, io_buffer, claims, &store);
}

/// Debug-build gate for [`derive_multiplicities_into`]'s exactly-once
/// contract: every multiplicity cell and gadget counter must still be
/// zero (set-only execution, no prior derivation).
fn debug_assert_record_counts_zero(record: &QueryRecord) {
  if !cfg!(debug_assertions) {
    return;
  }
  for (f, m) in record.function_queries.iter().enumerate() {
    for i in 0..m.len() {
      assert!(
        m.get_index(i).expect("in range").1.multiplicity.is_zero(),
        "derive_into on a non-zero record (fn {f} entry {i})"
      );
    }
  }
  for (w, m) in &record.memory_queries {
    for i in 0..m.len() {
      assert!(
        m.get_index(i).expect("in range").1.multiplicity.is_zero(),
        "derive_into on a non-zero record (mem {w} entry {i})"
      );
    }
  }
  for i in 0..256 {
    for col in 0..BYTES1_COLS {
      assert_eq!(record.bytes1_queries.count(i, col), 0, "bytes1 not zero");
    }
  }
  for cell in 0..256 * 256 {
    for col in 0..BYTES2_COLS {
      assert_eq!(record.bytes2_queries.count(cell, col), 0, "bytes2 not zero");
    }
  }
}

/// Differential check: derived tallies vs the record's accumulated
/// multiplicities and gadget counters. The gate for replacing runtime
/// accumulation with derivation — any single-threaded execution must
/// produce identical numbers, bit for bit. Returns the first few
/// mismatches on failure.
pub fn diff_multiplicities(
  record: &QueryRecord,
  tally: &MultTally,
) -> Result<(), String> {
  let mut errs: Vec<String> = Vec::new();
  for (f, (m, t)) in
    record.function_queries.iter().zip(&tally.fn_mults).enumerate()
  {
    for i in 0..m.len() {
      let acc = m.get_index(i).expect("in range").1.multiplicity;
      let der = G::from_u64(t[i].load(Ordering::Relaxed));
      if acc != der {
        errs.push(format!(
          "fn {f} entry {i}: accumulated {} derived {}",
          acc.as_canonical_u64(),
          der.as_canonical_u64()
        ));
      }
    }
  }
  for (pos, width) in tally.mem_widths.iter().enumerate() {
    let m = record.memory_queries.get(width).expect("width present");
    for i in 0..m.len() {
      let acc = m.get_index(i).expect("in range").1.multiplicity;
      let der = G::from_u64(tally.mem_mults[pos][i].load(Ordering::Relaxed));
      if acc != der {
        errs.push(format!(
          "mem {width} ptr {i}: accumulated {} derived {}",
          acc.as_canonical_u64(),
          der.as_canonical_u64()
        ));
      }
    }
  }
  for i in 0..256 {
    for col in 0..BYTES1_COLS {
      let acc = record.bytes1_queries.count(i, col);
      let der = tally.bytes1[i * BYTES1_COLS + col].load(Ordering::Relaxed);
      if acc != der {
        errs.push(format!("bytes1[{i}][{col}]: accumulated {acc} derived {der}"));
      }
    }
  }
  for cell in 0..256 * 256 {
    for col in 0..BYTES2_COLS {
      let acc = record.bytes2_queries.count(cell, col);
      let der = tally.bytes2[cell * BYTES2_COLS + col].load(Ordering::Relaxed);
      if acc != der {
        errs.push(format!("bytes2[{cell}][{col}]: accumulated {acc} derived {der}"));
      }
    }
  }
  if errs.is_empty() {
    Ok(())
  } else {
    let n = errs.len();
    errs.truncate(8);
    Err(format!("{n} multiplicity mismatch(es):\n{}", errs.join("\n")))
  }
}
