use binius_field::underlier::{U1, WithUnderlier};
use binius_field::{BinaryField, Field};

use super::execute::{FxIndexMap, QueryRecord, QueryResult, load_u64};
use super::ir::{Block, Ctrl, FuncIdx, Function, Op, Prim, SelIdx, Toplevel};
use super::layout::{AiurByteField, Layout, MultiplicityField};

pub const MULT_GEN: MultiplicityField = MultiplicityField::MULTIPLICATIVE_GENERATOR;

#[derive(Clone, Default, Debug)]
pub struct Trace {
    pub num_queries: u64,
    pub inputs: Vec<Vec<u8>>,
    pub outputs: Vec<Vec<u8>>,
    pub auxiliaries: Vec<Vec<u8>>,
    pub multiplicity: Vec<MultiplicityField>,
    pub require_hints: Vec<Vec<MultiplicityField>>,
    pub selectors: Vec<Vec<U1>>,
}

#[derive(Clone, Copy, Default, Debug)]
struct ColumnIndex {
    auxiliary: usize,
    require_hint: usize,
}

impl Trace {
    fn blank_trace_with_io(
        shape: &Layout,
        num_queries: usize,
        multiplicity: Vec<MultiplicityField>,
        inputs: Vec<Vec<u8>>,
        outputs: Vec<Vec<u8>>,
    ) -> Self {
        let height = num_queries.next_power_of_two();
        let blank_column = vec![0; height];
        let auxiliaries = vec![blank_column; shape.auxiliaries as usize];
        let blank_column = vec![U1::new(0); height];
        let selectors = vec![blank_column; shape.selectors as usize];
        let blank_column = vec![MultiplicityField::ZERO; height];
        let require_hints = vec![blank_column; shape.require_hints as usize];
        Self {
            inputs,
            outputs,
            auxiliaries,
            multiplicity,
            require_hints,
            selectors,
            num_queries: num_queries as u64,
        }
    }

    fn push(&mut self, row: usize, col: &mut ColumnIndex, val: u8) {
        self.auxiliaries[col.auxiliary][row] = val;
        col.auxiliary += 1;
    }

    fn require(&mut self, row: usize, col: &mut ColumnIndex, val: MultiplicityField) {
        self.require_hints[col.require_hint][row] = val;
        col.require_hint += 1;
    }

    fn set_selector(&mut self, row: usize, sel: SelIdx) {
        self.selectors[sel.0 as usize][row] = U1::new(1);
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
enum Query {
    Func(FuncIdx, Vec<u8>),
    Mem(u32, Vec<u8>),
}

impl Toplevel {
    pub fn generate_trace(&self, record: &QueryRecord) -> Vec<Trace> {
        let mut traces = Vec::with_capacity(self.functions.len());
        let prev_counts = &mut FxIndexMap::default();
        for (func_idx, func) in self.functions.iter().enumerate() {
            let func_map = &record.func_queries[func_idx];
            let layout = &self.layouts[func_idx];
            let trace = generate_func_trace(func, func_map, layout, record, prev_counts);
            traces.push(trace);
        }
        traces
    }
}

fn generate_func_trace(
    func: &Function,
    func_map: &FxIndexMap<Vec<u8>, QueryResult>,
    shape: &Layout,
    record: &QueryRecord,
    prev_counts: &mut FxIndexMap<Query, MultiplicityField>,
) -> Trace {
    let num_queries = func_map.len();
    let (multiplicity, inputs, outputs) = extract_io(func_map, shape);
    let mut trace = Trace::blank_trace_with_io(shape, num_queries, multiplicity, inputs, outputs);
    for row in 0..num_queries {
        let mut col = ColumnIndex::default();
        let mut map = trace.inputs.iter().map(|col| col[row]).collect::<Vec<_>>();
        populate_block_trace(
            &func.body,
            &mut trace,
            &mut map,
            row,
            &mut col,
            record,
            prev_counts,
        );
    }
    trace
}

fn populate_block_trace(
    block: &Block,
    trace: &mut Trace,
    map: &mut Vec<u8>,
    row: usize,
    col: &mut ColumnIndex,
    record: &QueryRecord,
    prev_counts: &mut FxIndexMap<Query, MultiplicityField>,
) {
    block
        .ops
        .iter()
        .for_each(|op| populate_op_trace(op, trace, map, row, col, record, prev_counts));
    match block.ctrl.as_ref() {
        Ctrl::If(b, t, f) => {
            let val = map[b.to_usize()];
            if val != 0 {
                let inv = AiurByteField::new(val).invert().unwrap().to_underlier();
                trace.push(row, col, inv);
                populate_block_trace(t, trace, map, row, col, record, prev_counts);
            } else {
                populate_block_trace(f, trace, map, row, col, record, prev_counts);
            }
        }
        Ctrl::If64(b, t, f) => {
            let val = &map[b.to_usize()..b.to_usize() + 8];
            if let Some(pos) = val.iter().position(|&byte| byte != 0) {
                let inv = AiurByteField::new(val[pos])
                    .invert()
                    .unwrap()
                    .to_underlier();
                let mut coeffs = vec![0; 8];
                coeffs[pos] = inv;
                coeffs
                    .into_iter()
                    .for_each(|coeff| trace.push(row, col, coeff));
                populate_block_trace(t, trace, map, row, col, record, prev_counts);
            } else {
                populate_block_trace(f, trace, map, row, col, record, prev_counts);
            }
        }
        Ctrl::Return(sel, _) => trace.set_selector(row, *sel),
    }
}

fn populate_op_trace(
    op: &Op,
    trace: &mut Trace,
    map: &mut Vec<u8>,
    row: usize,
    col: &mut ColumnIndex,
    record: &QueryRecord,
    prev_counts: &mut FxIndexMap<Query, MultiplicityField>,
) {
    match op {
        Op::Prim(Prim::U64(a)) => {
            map.extend(a.to_le_bytes());
        }
        Op::Prim(Prim::Bool(a)) => {
            map.push(*a as u8);
        }
        Op::Xor(a, b) => {
            let a = map[a.to_usize()];
            let b = map[b.to_usize()];
            map.push(a ^ b);
        }
        Op::And(a, b) => {
            let a = map[a.to_usize()];
            let b = map[b.to_usize()];
            // NOTE: this operation only works when `a` and `b` are both bits
            let c = a & b;
            trace.push(row, col, c);
            map.push(c);
        }
        Op::Add(a, b) => {
            let a = load_u64(a, map);
            let b = load_u64(b, map);
            let (c, overflow) = a.overflowing_add(b);
            for byte in c.to_le_bytes() {
                trace.push(row, col, byte);
                map.push(byte);
            }
            trace.push(row, col, overflow as u8);
        }
        Op::Sub(a, b) => {
            let a = load_u64(a, map);
            let b = load_u64(b, map);
            let (c, overflow) = a.overflowing_sub(b);
            for byte in c.to_le_bytes() {
                trace.push(row, col, byte);
                map.push(byte);
            }
            trace.push(row, col, overflow as u8);
        }
        Op::Lt(a, b) => {
            let a = load_u64(a, map);
            let b = load_u64(b, map);
            let (c, overflow) = a.overflowing_sub(b);
            for byte in c.to_le_bytes() {
                trace.push(row, col, byte);
            }
            trace.push(row, col, overflow as u8);
            map.push(overflow as u8);
        }
        Op::Mul(a, b) => {
            let a = load_u64(a, map);
            let b = load_u64(b, map);
            let c = a.wrapping_mul(b);
            for byte in c.to_le_bytes() {
                trace.push(row, col, byte);
                map.push(byte);
            }
        }
        Op::Store(values) => {
            let len = values
                .len()
                .try_into()
                .expect("Error: too many arguments to store");
            let mem_map = load_mem_map(&record.mem_queries, len);
            let values = values
                .iter()
                .map(|value| map[value.to_usize()])
                .collect::<Vec<_>>();
            let query_result = mem_map
                .get(&values)
                .unwrap_or_else(|| panic!("Value {values:?} not in memory"));
            for value in query_result.result.iter() {
                trace.push(row, col, *value);
                map.push(*value);
            }
            let count = prev_counts
                .entry(Query::Mem(len, values.clone()))
                .or_insert(MultiplicityField::ONE);
            trace.require(row, col, *count);
            *count *= MULT_GEN;
        }
        Op::Load(len, ptr) => {
            let ptr: usize = load_u64(ptr, map)
                .try_into()
                .expect("Pointer too large for current architecture");
            let mem_map = load_mem_map(&record.mem_queries, *len);
            let (values, _) = mem_map
                .get_index(ptr)
                .unwrap_or_else(|| panic!("Unbound {len}-wide pointer {ptr}"));
            for value in values.iter() {
                trace.push(row, col, *value);
                map.push(*value);
            }
            let count = prev_counts
                .entry(Query::Mem(*len, values.clone()))
                .or_insert(MultiplicityField::ONE);
            trace.require(row, col, *count);
            *count *= MULT_GEN;
        }
        Op::Call(func_idx, args, _) => {
            let args = args.iter().map(|a| map[a.to_usize()]).collect::<Vec<_>>();
            let output = &record.get_from_u8(*func_idx, &args).unwrap().result;
            for byte in output {
                trace.push(row, col, *byte);
                map.push(*byte);
            }
            let count = prev_counts
                .entry(Query::Func(*func_idx, args))
                .or_insert(MultiplicityField::ONE);
            trace.require(row, col, *count);
            *count *= MULT_GEN;
        }
    }
}

fn extract_io(
    func_map: &FxIndexMap<Vec<u8>, QueryResult>,
    shape: &Layout,
) -> (Vec<MultiplicityField>, Vec<Vec<u8>>, Vec<Vec<u8>>) {
    let height = func_map.len().next_power_of_two();
    let blank_column = vec![0; height];
    let mut inputs = vec![blank_column.clone(); shape.inputs as usize];
    let mut outputs = vec![blank_column; shape.outputs as usize];
    let mut multiplicity = vec![MultiplicityField::ONE; height];
    func_map
        .iter()
        .enumerate()
        .for_each(|(i, (input_bytes, result))| {
            multiplicity[i] = MULT_GEN.pow([result.multiplicity as u64]);
            assert_eq!(input_bytes.len(), inputs.len());
            input_bytes
                .iter()
                .zip(inputs.iter_mut())
                .for_each(|(byte, inp)| inp[i] = *byte);
            let output_bytes = &result.result;
            assert_eq!(output_bytes.len(), outputs.len());
            output_bytes
                .iter()
                .zip(outputs.iter_mut())
                .for_each(|(byte, out)| out[i] = *byte);
        });
    (multiplicity, inputs, outputs)
}

pub(crate) fn load_mem_map(
    mem_queries: &[(u32, FxIndexMap<Vec<u8>, QueryResult>)],
    len: u32,
) -> &FxIndexMap<Vec<u8>, QueryResult> {
    mem_queries.iter().find(|(k, _)| *k == len).map_or_else(
        || panic!("Internal error: no memory map of size {len}"),
        |(_, v)| v,
    )
}
