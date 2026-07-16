use multi_stark::{
  lookup::Lookup,
  p3_field::{Field, PrimeCharacteristicRing, PrimeField64},
  p3_matrix::dense::RowMajorMatrix,
};
use rayon::{
  iter::{
    IndexedParallelIterator, IntoParallelRefMutIterator, ParallelIterator,
  },
  slice::ParallelSliceMut,
};

use crate::{
  FxIndexMap, G,
  bytecode::{Block, Ctrl, Function, FunctionLayout, Op, Toplevel},
  execute::{
    IOBuffer, IOKeyInfo, QueryRecord, find_unconstrained_big_uint_div_mod,
  },
  function_channel,
  gadgets::{bytes1::Bytes1, bytes2::Bytes2},
  memory::Memory,
  querymap::QueryRef,
  u8_add_channel, u8_and_channel, u8_bit_decomposition_channel,
  u8_chain_rotr4_channel, u8_chain_rotr7_channel, u8_less_than_channel,
  u8_mul_channel, u8_or_channel, u8_range_check_channel, u8_shift_left_channel,
  u8_shift_right_channel, u8_sub_channel, u8_xor_channel,
};

struct ColumnIndex {
  auxiliary: usize,
  lookup: usize,
}

struct ColumnMutSlice<'a> {
  inputs: &'a mut [G],
  selectors: &'a mut [G],
  auxiliaries: &'a mut [G],
  lookups: &'a mut [Lookup<G>],
}

type Degree = u8;

impl<'a> ColumnMutSlice<'a> {
  /// Slice a circuit row into the regions of one member function: the
  /// member's inputs are a prefix of the circuit's input block, its selectors
  /// a sub-range of the circuit's selector block at `sel_offset`, and the
  /// auxiliary block is shared by all members.
  fn from_slice(
    function: &Function,
    circuit_layout: &FunctionLayout,
    sel_offset: usize,
    slice: &'a mut [G],
    lookups: &'a mut [Lookup<G>],
  ) -> Self {
    let (inputs, slice) = slice.split_at_mut(circuit_layout.input_size);
    let (selectors, auxiliaries) = slice.split_at_mut(circuit_layout.selectors);
    assert_eq!(auxiliaries.len(), circuit_layout.auxiliaries);
    let inputs = &mut inputs[..function.layout.input_size];
    let selectors =
      &mut selectors[sel_offset..sel_offset + function.layout.selectors];
    Self { inputs, selectors, auxiliaries, lookups }
  }

  fn push_auxiliary(&mut self, index: &mut ColumnIndex, t: G) {
    self.auxiliaries[index.auxiliary] = t;
    index.auxiliary += 1;
  }

  fn push_lookup(&mut self, index: &mut ColumnIndex, t: Lookup<G>) {
    self.lookups[index.lookup] = t;
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

/// One row of a circuit trace: the member function it belongs to, the
/// member's selector offset within the circuit, its function index, and the
/// recorded query.
struct RowMeta<'a> {
  function: &'a Function,
  sel_offset: usize,
  function_index: G,
  inputs: &'a [G],
  result: QueryRef<'a>,
}

impl Toplevel {
  pub fn witness_data(
    &self,
    circuit_index: usize,
    query_record: &QueryRecord,
    io_buffer: &IOBuffer,
  ) -> (RowMajorMatrix<G>, Vec<Vec<Lookup<G>>>) {
    let circuit = &self.circuits[circuit_index];
    let layout = &circuit.layout;
    let width = layout.width();
    // Concatenate the members' queried rows, in member order.
    let mut rows_meta = Vec::new();
    let mut sel_offset = 0;
    for &member in &circuit.members {
      let function = &self.functions[member];
      let function_index = G::from_usize(member);
      rows_meta.extend(
        query_record.function_queries[member]
          .iter()
          .filter(|(_, res)| !res.multiplicity.is_zero())
          .map(|(inputs, result)| RowMeta {
            function,
            sel_offset,
            function_index,
            inputs,
            result,
          }),
      );
      sel_offset += function.layout.selectors;
    }
    let height_no_padding = rows_meta.len();
    let height = height_no_padding.next_power_of_two();
    let mut rows = vec![G::ZERO; height * width];
    let rows_no_padding = &mut rows[0..height_no_padding * width];
    let empty_lookup = Lookup::empty();
    let mut lookups = vec![vec![empty_lookup; layout.lookups]; height];
    let lookups_no_padding = &mut lookups[0..height_no_padding];
    rows_no_padding
      .par_chunks_mut(width)
      .zip(lookups_no_padding.par_iter_mut())
      .enumerate()
      .for_each(|(i, (row, lookups))| {
        let meta = &rows_meta[i];
        let index = &mut ColumnIndex {
          auxiliary: 0,
          // we skip the first lookup, which is reserved for return
          lookup: 1,
        };
        let slice = &mut ColumnMutSlice::from_slice(
          meta.function,
          layout,
          meta.sel_offset,
          row,
          lookups,
        );
        let context = TraceContext {
          function_index: meta.function_index,
          inputs: meta.inputs,
          multiplicity: meta.result.multiplicity,
          output: meta.result.output,
          query_record,
        };
        meta.function.populate_row(index, slice, context, io_buffer);
      });
    let trace = RowMajorMatrix::new(rows, width);
    (trace, lookups)
  }
}

impl Function {
  pub fn width(&self) -> usize {
    self.layout.input_size + self.layout.auxiliaries + self.layout.selectors
  }

  fn populate_row(
    &self,
    index: &mut ColumnIndex,
    slice: &mut ColumnMutSlice<'_>,
    context: TraceContext<'_>,
    io_buffer: &IOBuffer,
  ) {
    debug_assert_eq!(
      self.layout.input_size,
      context.inputs.len(),
      "Argument mismatch"
    );
    // Variable to value map
    let map = &mut context.inputs.iter().map(|arg| (*arg, 1)).collect();
    // One column per input
    context
      .inputs
      .iter()
      .enumerate()
      .for_each(|(i, arg)| slice.inputs[i] = *arg);
    // Push the multiplicity
    slice.push_auxiliary(index, context.multiplicity);
    let _ = self.body.populate_row(map, index, slice, context, io_buffer);
  }
}

/// `Some(values)` means the block ended with `Yield` (values for the merge).
/// `None` means the block ended with `Return` (function exited).
type PopulateResult = Option<Vec<G>>;

impl Block {
  fn populate_row(
    &self,
    map: &mut Vec<(G, Degree)>,
    index: &mut ColumnIndex,
    slice: &mut ColumnMutSlice<'_>,
    context: TraceContext<'_>,
    io_buffer: &IOBuffer,
  ) -> PopulateResult {
    self
      .ops
      .iter()
      .for_each(|op| op.populate_row(map, index, slice, context, io_buffer));
    self.ctrl.populate_row(map, index, slice, context, io_buffer)
  }
}

/// Dispatch a match: look up the value in the cases map, or fall through to the
/// default (pushing inverse witnesses for each case to prove inequality).
fn dispatch_branch<'a>(
  val: G,
  cases: &'a FxIndexMap<G, Block>,
  def: &'a Option<Box<Block>>,
  index: &mut ColumnIndex,
  slice: &mut ColumnMutSlice<'_>,
) -> &'a Block {
  cases
    .get(&val)
    .or_else(|| {
      for &case in cases.keys() {
        let witness = (val - case).inverse();
        slice.push_auxiliary(index, witness);
      }
      def.as_deref()
    })
    .expect("No match")
}

impl Ctrl {
  fn populate_row(
    &self,
    map: &mut Vec<(G, Degree)>,
    index: &mut ColumnIndex,
    slice: &mut ColumnMutSlice<'_>,
    context: TraceContext<'_>,
    io_buffer: &IOBuffer,
  ) -> PopulateResult {
    match self {
      Ctrl::Return(sel, _) => {
        slice.selectors[*sel] = G::ONE;
        let lookup = function_lookup(
          -context.multiplicity,
          context.function_index,
          context.inputs,
          context.output,
        );
        slice.lookups[0] = lookup;
        None
      },
      Ctrl::Yield(sel, vals) => {
        slice.selectors[*sel] = G::ONE;
        Some(vals.iter().map(|&v| map[v].0).collect())
      },
      Ctrl::Match(var, cases, def) => {
        let branch = dispatch_branch(map[*var].0, cases, def, index, slice);
        branch.populate_row(map, index, slice, context, io_buffer)
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

        let branch = dispatch_branch(map[*var].0, cases, def, index, slice);
        let result = branch.populate_row(map, index, slice, context, io_buffer);
        match result {
          Some(yielded) => {
            // Advance past the shared branch region. The taken branch may
            // use fewer auxiliaries/lookups than the max across all branches.
            index.auxiliary = init_aux + shared_aux;
            index.lookup = init_lookup + shared_lookups;

            map.truncate(map_len);
            for &val in &yielded {
              slice.push_auxiliary(index, val);
              map.push((val, 1));
            }
            continuation.populate_row(map, index, slice, context, io_buffer)
          },
          None => None,
        }
      },
    }
  }
}

impl Op {
  fn populate_row(
    &self,
    map: &mut Vec<(G, Degree)>,
    index: &mut ColumnIndex,
    slice: &mut ColumnMutSlice<'_>,
    context: TraceContext<'_>,
    io_buffer: &IOBuffer,
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
          slice.push_auxiliary(index, f);
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
          slice.push_auxiliary(index, d);
          slice.push_auxiliary(index, x);
          map.push((is_zero_g, 1));
        }
      },
      Op::Call(function_index, inputs, _, op_unconstrained) => {
        let inputs = inputs.iter().map(|a| map[*a].0).collect::<Vec<_>>();
        let queries = &context.query_record.function_queries[*function_index];
        let result = queries.get(&inputs).expect("Cannot find query result");
        for f in result.output.iter() {
          map.push((*f, 1));
          slice.push_auxiliary(index, *f);
        }
        if !op_unconstrained {
          let lookup = function_lookup(
            G::ONE,
            G::from_usize(*function_index),
            &inputs,
            result.output,
          );
          slice.push_lookup(index, lookup);
        }
      },
      Op::Store(values) => {
        let size = values.len();
        let memory_queries = context
          .query_record
          .memory_queries
          .get(&size)
          .expect("Invalid memory size");
        let values = values.iter().map(|a| map[*a].0).collect::<Vec<_>>();
        let ptr = G::from_usize(
          memory_queries.get_index_of(&values).expect("Unbound pointer"),
        );
        map.push((ptr, 1));
        slice.push_auxiliary(index, ptr);
        let lookup = Memory::lookup(G::ONE, G::from_usize(size), ptr, &values);
        slice.push_lookup(index, lookup);
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
          slice.push_auxiliary(index, *f);
        }
        let lookup = Memory::lookup(G::ONE, G::from_usize(*size), ptr, values);
        slice.push_lookup(index, lookup);
      },
      Op::IOGetInfo(channel, key) => {
        let channel = map[*channel].0;
        let key = key.iter().map(|a| map[*a].0).collect::<Vec<_>>();
        let IOKeyInfo { idx, len } =
          io_buffer.get_info(channel, &key).expect("Invalid IO key");
        for f in [G::from_usize(*idx), G::from_usize(*len)] {
          map.push((f, 1));
          slice.push_auxiliary(index, f);
        }
      },
      Op::IORead(channel, idx, len) => {
        let channel = map[*channel].0;
        let idx = map[*idx]
          .0
          .as_canonical_u64()
          .try_into()
          .expect("Index is too big for an usize");
        let data = io_buffer
          .read(channel, idx, *len)
          .expect("IO read out of bounds")
          .to_vec();
        for f in data {
          map.push((f, 1));
          slice.push_auxiliary(index, f);
        }
      },
      Op::U8BitDecomposition(byte) => {
        let (byte, _) = map[*byte];
        let bits = Bytes1::bit_decompose(&byte);
        for &b in &bits {
          map.push((b, 1));
          slice.push_auxiliary(index, b);
        }
        let mut lookup_args = vec![u8_bit_decomposition_channel(), byte];
        lookup_args.extend(bits);
        slice.push_lookup(index, Lookup::push(G::ONE, lookup_args));
      },
      Op::U8ShiftLeft(byte) => {
        let (byte, _) = map[*byte];
        let byte_shifted = Bytes1::shift_left(&byte);
        map.push((byte_shifted, 1));
        slice.push_auxiliary(index, byte_shifted);
        let lookup_args = vec![u8_shift_left_channel(), byte, byte_shifted];
        slice.push_lookup(index, Lookup::push(G::ONE, lookup_args));
      },
      Op::U8ShiftRight(byte) => {
        let (byte, _) = map[*byte];
        let byte_shifted = Bytes1::shift_right(&byte);
        map.push((byte_shifted, 1));
        slice.push_auxiliary(index, byte_shifted);
        let lookup_args = vec![u8_shift_right_channel(), byte, byte_shifted];
        slice.push_lookup(index, Lookup::push(G::ONE, lookup_args));
      },
      Op::U8Xor(i, j) => {
        let (i, _) = map[*i];
        let (j, _) = map[*j];
        let xor = Bytes2::xor(&i, &j);
        map.push((xor, 1));
        slice.push_auxiliary(index, xor);
        let lookup_args = vec![u8_xor_channel(), i, j, xor];
        slice.push_lookup(index, Lookup::push(G::ONE, lookup_args));
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
        slice.push_auxiliary(index, r);
        let lookup_args = vec![u8_add_channel(), i, j, r];
        slice.push_lookup(index, Lookup::push(G::ONE, lookup_args));
      },
      Op::U8Mul(i, j) => {
        let (i, _) = map[*i];
        let (j, _) = map[*j];
        let (lo, hi) = Bytes2::mul(&i, &j);
        map.push((lo, 1));
        map.push((hi, 1));
        slice.push_auxiliary(index, lo);
        slice.push_auxiliary(index, hi);
        let lookup_args = vec![u8_mul_channel(), i, j, lo, hi];
        slice.push_lookup(index, Lookup::push(G::ONE, lookup_args));
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
        slice.push_auxiliary(index, r);
        let lookup_args = vec![u8_sub_channel(), i, j, r];
        slice.push_lookup(index, Lookup::push(G::ONE, lookup_args));
      },
      Op::U8And(i, j) => {
        let (i, _) = map[*i];
        let (j, _) = map[*j];
        let and = Bytes2::and(&i, &j);
        map.push((and, 1));
        slice.push_auxiliary(index, and);
        let lookup_args = vec![u8_and_channel(), i, j, and];
        slice.push_lookup(index, Lookup::push(G::ONE, lookup_args));
      },
      Op::U8Or(i, j) => {
        let (i, _) = map[*i];
        let (j, _) = map[*j];
        let or = Bytes2::or(&i, &j);
        map.push((or, 1));
        slice.push_auxiliary(index, or);
        let lookup_args = vec![u8_or_channel(), i, j, or];
        slice.push_lookup(index, Lookup::push(G::ONE, lookup_args));
      },
      Op::U8LessThan(i, j) => {
        let (i, _) = map[*i];
        let (j, _) = map[*j];
        let less_than = Bytes2::less_than(&i, &j);
        map.push((less_than, 1));
        slice.push_auxiliary(index, less_than);
        let lookup_args = vec![u8_less_than_channel(), i, j, less_than];
        slice.push_lookup(index, Lookup::push(G::ONE, lookup_args));
      },
      Op::U8ChainRotr7(i, j) => {
        let (i, _) = map[*i];
        let (j, _) = map[*j];
        let (o0, o1, o2) = Bytes2::chain_rotr7(&i, &j);
        map.push((o0, 1));
        map.push((o1, 1));
        map.push((o2, 1));
        slice.push_auxiliary(index, o0);
        slice.push_auxiliary(index, o1);
        slice.push_auxiliary(index, o2);
        let lookup_args = vec![u8_chain_rotr7_channel(), i, j, o0, o1, o2];
        slice.push_lookup(index, Lookup::push(G::ONE, lookup_args));
      },
      Op::U8ChainRotr4(i, j) => {
        let (i, _) = map[*i];
        let (j, _) = map[*j];
        let (o0, o1, o2) = Bytes2::chain_rotr4(&i, &j);
        map.push((o0, 1));
        map.push((o1, 1));
        map.push((o2, 1));
        slice.push_auxiliary(index, o0);
        slice.push_auxiliary(index, o1);
        slice.push_auxiliary(index, o2);
        let lookup_args = vec![u8_chain_rotr4_channel(), i, j, o0, o1, o2];
        slice.push_lookup(index, Lookup::push(G::ONE, lookup_args));
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
          slice.push_auxiliary(index, G::from_u8(byte));
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
          slice.push_lookup(
            index,
            Lookup::push(
              G::ONE,
              vec![rc_channel, G::from_u8(i), G::from_u8(j)],
            ),
          );
        }

        let result = G::from_bool(a_u32 < b_u32);
        map.push((result, 1));
      },
      Op::U8RangeCheck(i, j) => {
        // No `map.push`: the `u8` outputs alias the inputs. Just require the
        // `(i, j)` pair from the byte-chip range-check table.
        slice.push_lookup(
          index,
          Lookup::push(
            G::ONE,
            vec![u8_range_check_channel(), map[*i].0, map[*j].0],
          ),
        );
      },
      Op::UnconstrainedBigUintDivMod(a, b) => {
        // Mirrors the execute arm and the two auxiliary columns the
        // constraints allocate: recompute `(q, r)` and resolve the head
        // pointers execution recorded in memory[10]. Skipping the two map
        // pushes would shift every later `ValIdx` (and witness column) in
        // the block.
        let (q_ptr, r_ptr) = find_unconstrained_big_uint_div_mod(
          map[*a].0,
          map[*b].0,
          &context.query_record.memory_queries,
        )
        .expect("BigUint div-mod result not recorded");
        for f in [q_ptr, r_ptr] {
          map.push((f, 1));
          slice.push_auxiliary(index, f);
        }
      },
      Op::AssertEq(..)
      | Op::IOSetInfo(..)
      | Op::IOWrite(..)
      | Op::Debug(..) => {},
    }
  }
}

fn function_lookup(
  multiplicity: G,
  function_index: G,
  inputs: &[G],
  output: &[G],
) -> Lookup<G> {
  let mut args = vec![function_channel(), function_index];
  args.extend(inputs);
  args.extend(output);
  Lookup { multiplicity, args }
}
