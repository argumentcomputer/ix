use binius_field::underlier::{U1, WithUnderlier};
use binius_field::{BinaryField, Field};

use super::execute::{FxIndexMap, QueryRecord, QueryResult};
use super::ir::{Block, Ctrl, FuncIdx, Function, Op, Prim, SelIdx, Toplevel};
use super::layout::{B64, Layout};

pub const MULT_GEN: B64 = B64::MULTIPLICATIVE_GENERATOR;

#[derive(Clone, Default, Debug)]
pub struct Trace {
    pub num_queries: u64,
    pub inputs: Vec<Vec<u64>>,
    pub outputs: Vec<Vec<u64>>,
    pub u1_auxiliaries: Vec<Vec<U1>>,
    pub u8_auxiliaries: Vec<Vec<u8>>,
    pub u64_auxiliaries: Vec<Vec<u64>>,
    pub multiplicity: Vec<u64>,
    pub selectors: Vec<Vec<U1>>,
}

#[derive(Clone, Copy, Default, Debug)]
struct ColumnIndex {
    u1_auxiliary: usize,
    u8_auxiliary: usize,
    u64_auxiliary: usize,
}

impl Trace {
    fn blank_trace_with_io(
        shape: &Layout,
        num_queries: usize,
        multiplicity: Vec<u64>,
        inputs: Vec<Vec<u64>>,
        outputs: Vec<Vec<u64>>,
    ) -> Self {
        let height = num_queries.next_power_of_two();
        let blank_column = vec![U1::new(0); height];
        let u1_auxiliaries = vec![blank_column.clone(); shape.u1_auxiliaries as usize];
        let selectors = vec![blank_column; shape.selectors as usize];
        let blank_column = vec![0; height];
        let u8_auxiliaries = vec![blank_column; shape.u8_auxiliaries as usize];
        let blank_column = vec![0; height];
        let u64_auxiliaries = vec![blank_column; shape.u64_auxiliaries as usize];
        Self {
            inputs,
            outputs,
            u1_auxiliaries,
            u8_auxiliaries,
            u64_auxiliaries,
            multiplicity,
            selectors,
            num_queries: num_queries as u64,
        }
    }

    fn push_u1(&mut self, row: usize, col: &mut ColumnIndex, val: U1) {
        self.u1_auxiliaries[col.u1_auxiliary][row] = val;
        col.u1_auxiliary += 1;
    }

    #[allow(dead_code)]
    fn push_u8(&mut self, row: usize, col: &mut ColumnIndex, val: u8) {
        self.u8_auxiliaries[col.u8_auxiliary][row] = val;
        col.u8_auxiliary += 1;
    }

    fn push_u64(&mut self, row: usize, col: &mut ColumnIndex, val: u64) {
        self.u64_auxiliaries[col.u64_auxiliary][row] = val;
        col.u64_auxiliary += 1;
    }

    fn set_selector(&mut self, row: usize, sel: SelIdx) {
        self.selectors[sel.0 as usize][row] = U1::new(1);
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
enum Query {
    Func(FuncIdx, Vec<u64>),
    Mem(u32, Vec<u64>),
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
    func_map: &FxIndexMap<Vec<u64>, QueryResult>,
    shape: &Layout,
    record: &QueryRecord,
    prev_counts: &mut FxIndexMap<Query, B64>,
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
    map: &mut Vec<u64>,
    row: usize,
    col: &mut ColumnIndex,
    record: &QueryRecord,
    prev_counts: &mut FxIndexMap<Query, B64>,
) {
    block
        .ops
        .iter()
        .for_each(|op| populate_op_trace(op, trace, map, row, col, record, prev_counts));
    match block.ctrl.as_ref() {
        Ctrl::If(b, t, f) => {
            let val = map[b.to_usize()];
            if val != 0 {
                let inv = B64::new(val).invert().unwrap().to_underlier();
                trace.push_u64(row, col, inv);
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
    map: &mut Vec<u64>,
    row: usize,
    col: &mut ColumnIndex,
    record: &QueryRecord,
    prev_counts: &mut FxIndexMap<Query, B64>,
) {
    match op {
        Op::Prim(Prim::U64(a)) => {
            map.push(*a);
        }
        Op::Prim(Prim::Bool(a)) => {
            map.push(*a as u64);
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
            trace.push_u1(
                row,
                col,
                U1::new(c.try_into().expect("Result exceed 1 bit")),
            );
            map.push(c);
        }
        Op::Add(a, b) => {
            let a = map[a.to_usize()];
            let b = map[b.to_usize()];
            let (c, overflow) = a.overflowing_add(b);
            trace.push_u64(row, col, c);
            map.push(c);
            trace.push_u1(row, col, U1::new(overflow as u8));
        }
        Op::Sub(c, b) => {
            let c = map[c.to_usize()];
            let b = map[b.to_usize()];
            let (a, overflow) = c.overflowing_sub(b);
            trace.push_u64(row, col, a);
            map.push(a);
            trace.push_u1(row, col, U1::new(overflow as u8));
        }
        Op::Lt(c, b) => {
            let c = map[c.to_usize()];
            let b = map[b.to_usize()];
            let (a, overflow) = c.overflowing_sub(b);
            trace.push_u64(row, col, a);
            trace.push_u1(row, col, U1::new(overflow as u8));
            map.push(overflow as u64);
        }
        Op::Mul(a, b) => {
            let a = map[a.to_usize()];
            let b = map[b.to_usize()];
            let c = a.wrapping_mul(b);
            trace.push_u64(row, col, c);
            map.push(c);
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
                trace.push_u64(row, col, *value);
                map.push(*value);
            }
            let count = prev_counts
                .entry(Query::Mem(len, values.clone()))
                .or_insert(B64::ONE);
            trace.push_u64(row, col, count.to_underlier());
            *count *= MULT_GEN;
        }
        Op::Load(len, ptr) => {
            let ptr = map[ptr.to_usize()]
                .try_into()
                .expect("Value too big for current architecture");
            let mem_map = load_mem_map(&record.mem_queries, *len);
            let (values, _) = mem_map
                .get_index(ptr)
                .unwrap_or_else(|| panic!("Unbound {len}-wide pointer {ptr}"));
            for value in values.iter() {
                trace.push_u64(row, col, *value);
                map.push(*value);
            }
            let count = prev_counts
                .entry(Query::Mem(*len, values.clone()))
                .or_insert(B64::ONE);
            trace.push_u64(row, col, count.to_underlier());
            *count *= MULT_GEN;
        }
        Op::Call(func_idx, args, _) => {
            let args = args.iter().map(|a| map[a.to_usize()]).collect::<Vec<_>>();
            let output = &record.get_from_u64(*func_idx, &args).unwrap().result;
            for byte in output {
                trace.push_u64(row, col, *byte);
                map.push(*byte);
            }
            let count = prev_counts
                .entry(Query::Func(*func_idx, args))
                .or_insert(B64::ONE);
            trace.push_u64(row, col, count.to_underlier());
            *count *= MULT_GEN;
        }
    }
}

fn extract_io(
    func_map: &FxIndexMap<Vec<u64>, QueryResult>,
    shape: &Layout,
) -> (Vec<u64>, Vec<Vec<u64>>, Vec<Vec<u64>>) {
    let height = func_map.len().next_power_of_two();
    let blank_column = vec![0; height];
    let mut inputs = vec![blank_column.clone(); shape.inputs as usize];
    let mut outputs = vec![blank_column; shape.outputs as usize];
    let mut multiplicity = vec![1; height];
    func_map
        .iter()
        .enumerate()
        .for_each(|(i, (input_bytes, result))| {
            multiplicity[i] = MULT_GEN.pow([result.multiplicity]).to_underlier();
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
    mem_queries: &[(u32, FxIndexMap<Vec<u64>, QueryResult>)],
    len: u32,
) -> &FxIndexMap<Vec<u64>, QueryResult> {
    mem_queries.iter().find(|(k, _)| *k == len).map_or_else(
        || panic!("Internal error: no memory map of size {len}"),
        |(_, v)| v,
    )
}
