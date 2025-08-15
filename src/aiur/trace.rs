use multi_stark::{
    lookup::Lookup,
    p3_field::{Field, PrimeCharacteristicRing, PrimeField64},
    p3_matrix::dense::RowMajorMatrix,
};
use rayon::{
    iter::{IndexedParallelIterator, IntoParallelRefMutIterator, ParallelIterator},
    slice::ParallelSliceMut,
};

use super::{
    G,
    bytecode::{Block, Ctrl, Function, Op, Toplevel},
    execute::{IOBuffer, IOKeyInfo, QueryRecord},
    memory::Memory,
};

pub enum Channel {
    Function,
    Memory,
}

impl Channel {
    pub fn to_field(&self) -> G {
        match self {
            Channel::Function => G::ZERO,
            Channel::Memory => G::ONE,
        }
    }
}

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
    fn from_slice(function: &Function, slice: &'a mut [G], lookups: &'a mut [Lookup<G>]) -> Self {
        let (inputs, slice) = slice.split_at_mut(function.layout.input_size);
        let (selectors, slice) = slice.split_at_mut(function.layout.selectors);
        let (auxiliaries, slice) = slice.split_at_mut(function.layout.auxiliaries);
        assert!(slice.is_empty());
        Self {
            inputs,
            selectors,
            auxiliaries,
            lookups,
        }
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

impl Toplevel {
    pub fn generate_trace(
        &self,
        function_index: usize,
        query_record: &QueryRecord,
        io_buffer: &IOBuffer,
    ) -> (RowMajorMatrix<G>, Vec<Vec<Lookup<G>>>) {
        let func = &self.functions[function_index];
        let width = func.width();
        let queries = &query_record.function_queries[function_index];
        let height_no_padding = queries.len();
        let height = height_no_padding.next_power_of_two();
        let mut rows = vec![G::ZERO; height * width];
        let rows_no_padding = &mut rows[0..height_no_padding * width];
        let empty_lookup = Lookup {
            multiplicity: G::ZERO,
            args: vec![],
        };
        let mut lookups = vec![vec![empty_lookup; func.layout.lookups]; height];
        let lookups_no_padding = &mut lookups[0..height_no_padding];
        rows_no_padding
            .par_chunks_mut(width)
            .zip(lookups_no_padding.par_iter_mut())
            .enumerate()
            .for_each(|(i, (row, lookups))| {
                let (inputs, result) = queries.get_index(i).unwrap();
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
                    output: &result.output,
                    query_record,
                };
                func.populate_row(index, slice, context, io_buffer);
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
        self.body
            .populate_row(map, index, slice, context, io_buffer);
    }
}

impl Block {
    fn populate_row(
        &self,
        map: &mut Vec<(G, Degree)>,
        index: &mut ColumnIndex,
        slice: &mut ColumnMutSlice<'_>,
        context: TraceContext<'_>,
        io_buffer: &IOBuffer,
    ) {
        self.ops
            .iter()
            .for_each(|op| op.populate_row(map, index, slice, context, io_buffer));
        self.ctrl
            .populate_row(map, index, slice, context, io_buffer);
    }
}

impl Ctrl {
    fn populate_row(
        &self,
        map: &mut Vec<(G, Degree)>,
        index: &mut ColumnIndex,
        slice: &mut ColumnMutSlice<'_>,
        context: TraceContext<'_>,
        io_buffer: &IOBuffer,
    ) {
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
            }
            Ctrl::Match(var, cases, def) => {
                let val = map[*var].0;
                let branch = cases
                    .get(&val)
                    .or_else(|| {
                        for &case in cases.keys() {
                            // the witness shows that val is different from case
                            let witness = (val - case).inverse();
                            slice.push_auxiliary(index, witness);
                        }
                        def.as_deref()
                    })
                    .expect("No match");
                branch.populate_row(map, index, slice, context, io_buffer);
            }
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
            }
            Op::Sub(a, b) => {
                let (a, a_deg) = map[*a];
                let (b, b_deg) = map[*b];
                let deg = a_deg.max(b_deg);
                map.push((a - b, deg));
            }
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
            }
            Op::Call(function_index, inputs, _) => {
                let inputs = inputs.iter().map(|a| map[*a].0).collect::<Vec<_>>();
                let queries = &context.query_record.function_queries[*function_index];
                let result = queries.get(&inputs).expect("Cannot find query result");
                for f in result.output.iter() {
                    map.push((*f, 1));
                    slice.push_auxiliary(index, *f);
                }
                let lookup = function_lookup(
                    G::ONE,
                    G::from_usize(*function_index),
                    &inputs,
                    &result.output,
                );
                slice.push_lookup(index, lookup);
            }
            Op::Store(values) => {
                let size = values.len();
                let memory_queries = context
                    .query_record
                    .memory_queries
                    .get(&size)
                    .expect("Invalid memory size");
                let values = values.iter().map(|a| map[*a].0).collect::<Vec<_>>();
                let ptr = G::from_usize(
                    memory_queries
                        .get_index_of(&values)
                        .expect("Unbound pointer"),
                );
                map.push((ptr, 1));
                slice.push_auxiliary(index, ptr);
                let lookup = Memory::lookup(G::ONE, G::from_usize(size), ptr, &values);
                slice.push_lookup(index, lookup);
            }
            Op::Load(size, ptr) => {
                let memory_queries = context
                    .query_record
                    .memory_queries
                    .get(size)
                    .expect("Invalid memory size");
                let (ptr, _) = map[*ptr];
                let ptr_u64 = ptr.as_canonical_u64();
                let ptr_usize = usize::try_from(ptr_u64).expect("Pointer is too big");
                let (values, _) = memory_queries
                    .get_index(ptr_usize)
                    .expect("Unbound pointer");
                for f in values.iter() {
                    map.push((*f, 1));
                    slice.push_auxiliary(index, *f);
                }
                let lookup = Memory::lookup(G::ONE, G::from_usize(*size), ptr, values);
                slice.push_lookup(index, lookup);
            }
            Op::IOGetInfo(key) => {
                let key = key.iter().map(|a| map[*a].0).collect::<Vec<_>>();
                let IOKeyInfo { idx, len } = io_buffer.get_info(&key);
                for f in [G::from_usize(*idx), G::from_usize(*len)] {
                    map.push((f, 1));
                    slice.push_auxiliary(index, f);
                }
            }
            Op::IORead(idx, len) => {
                let idx = map[*idx]
                    .0
                    .as_canonical_u64()
                    .try_into()
                    .expect("Index is too big for an usize");
                for &f in io_buffer.read(idx, *len) {
                    map.push((f, 1));
                    slice.push_auxiliary(index, f);
                }
            }
            Op::IOSetInfo(..) | Op::IOWrite(_) => (),
        }
    }
}

fn function_lookup(multiplicity: G, function_index: G, inputs: &[G], output: &[G]) -> Lookup<G> {
    let mut args = vec![Channel::Function.to_field(), function_index];
    args.extend(inputs);
    args.extend(output);
    Lookup { multiplicity, args }
}
