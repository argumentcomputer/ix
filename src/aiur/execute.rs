use indexmap::IndexMap;
use rustc_hash::FxBuildHasher;

pub type FxIndexMap<K, V> = IndexMap<K, V, FxBuildHasher>;

use super::ir::{Ctrl, FuncIdx, Op, Prim, Toplevel, ValIdx};

/// `QueryResult` is an output of the particular function. The `TopLevel` may contain multiply
/// functions, and for each one executed, it generates one `QueryResult` objects that contains
/// output for a given function
#[derive(PartialEq, Eq, Debug)]
pub struct QueryResult {
    pub result: Vec<u8>,
    pub multiplicity: u32,
}

/// `QueryRecord` is a collection of `QueryResult` objects that can be referenced by the input tuple
/// used while invoking `TopLevel` execution algorithm
#[derive(Debug)]
pub struct QueryRecord {
    pub func_queries: Vec<FxIndexMap<Vec<u8>, QueryResult>>,
    pub mem_queries: Vec<(u32, FxIndexMap<Vec<u8>, QueryResult>)>,
}

impl QueryRecord {
    pub fn new(toplevel: &Toplevel) -> Self {
        let len = toplevel.functions.len();
        let func_queries = (0..len).map(|_| Default::default()).collect();
        let mem_queries = Vec::new();
        QueryRecord {
            func_queries,
            mem_queries,
        }
    }

    pub fn get_func_map(&self, func_idx: FuncIdx) -> &FxIndexMap<Vec<u8>, QueryResult> {
        &self.func_queries[func_idx.to_usize()]
    }

    pub fn get_from_u8(&self, func_idx: FuncIdx, input: &[u8]) -> Option<&QueryResult> {
        self.func_queries[func_idx.to_usize()].get(input)
    }

    pub fn get(&self, func_idx: FuncIdx, input: &[u8]) -> Option<&QueryResult> {
        self.func_queries[func_idx.to_usize()].get(input)
    }

    pub fn get_mut(&mut self, func_idx: FuncIdx, input: &[u8]) -> Option<&mut QueryResult> {
        self.func_queries[func_idx.to_usize()].get_mut(input)
    }

    pub fn insert(
        &mut self,
        func_idx: FuncIdx,
        input: Vec<u8>,
        output: QueryResult,
    ) -> Option<QueryResult> {
        self.func_queries[func_idx.to_usize()].insert(input, output)
    }
}

enum ExecEntry<'a> {
    Op(&'a Op),
    Ctrl(&'a Ctrl),
}

struct CallerState {
    func_idx: FuncIdx,
    map: Vec<u8>,
}

impl Toplevel {
    /// Implementation of the execution algorithm
    ///
    /// 1) The values from the input are the very first values in the inner stack of the execution
    ///     algorithm
    /// 2) You can write additional input values (for example if you need some constants) into the
    ///     stack while implementing particular block of the program
    pub fn execute(&self, mut func_idx: FuncIdx, input: Vec<u8>) -> QueryRecord {
        let func = &self.functions[func_idx.to_usize()];
        assert_eq!(input.len(), func.input_size as usize);

        let mut record = QueryRecord::new(self);
        let mut exec_entries_stack = vec![];
        let mut callers_states_stack = vec![];
        let mut map = input;

        macro_rules! stack_block_exec_entries {
            ($block:expr) => {
                exec_entries_stack.push(ExecEntry::Ctrl(&$block.ctrl));
                exec_entries_stack.extend($block.ops.iter().rev().map(ExecEntry::Op));
            };
        }

        stack_block_exec_entries!(&func.body);

        while let Some(exec_entry) = exec_entries_stack.pop() {
            match exec_entry {
                ExecEntry::Op(Op::Prim(Prim::Bool(x))) => map.push(*x as u8),
                ExecEntry::Op(Op::Prim(Prim::U64(x))) => {
                    x.to_le_bytes().into_iter().for_each(|b| map.push(b))
                }
                ExecEntry::Op(Op::Add(a, b)) => {
                    let a = load_u64(a, &map);
                    let b = load_u64(b, &map);
                    let c = a.wrapping_add(b);
                    for byte in c.to_le_bytes() {
                        map.push(byte);
                    }
                }
                ExecEntry::Op(Op::Sub(a, b)) => {
                    let a = load_u64(a, &map);
                    let b = load_u64(b, &map);
                    let c = a.wrapping_sub(b);
                    for byte in c.to_le_bytes() {
                        map.push(byte);
                    }
                }
                ExecEntry::Op(Op::Mul(a, b)) => {
                    let a = load_u64(a, &map);
                    let b = load_u64(b, &map);
                    let c = a.wrapping_mul(b);
                    for byte in c.to_le_bytes() {
                        map.push(byte);
                    }
                }
                ExecEntry::Op(Op::Lt(a, b)) => {
                    let a = load_u64(a, &map);
                    let b = load_u64(b, &map);
                    let c = a < b;
                    map.push(c as u8);
                }
                ExecEntry::Op(Op::And(a, b)) => {
                    let a = map[a.to_usize()];
                    let b = map[b.to_usize()];
                    let c = a & b;
                    map.push(c);
                }
                ExecEntry::Op(Op::Xor(a, b)) => {
                    let a = map[a.to_usize()];
                    let b = map[b.to_usize()];
                    let c = a ^ b;
                    map.push(c);
                }
                ExecEntry::Op(Op::Store(values)) => {
                    let len = values
                        .len()
                        .try_into()
                        .expect("Error: too many arguments to store");
                    let mem_map = load_mem_map_mut(&mut record.mem_queries, len);
                    let values = values
                        .iter()
                        .map(|value| map[value.to_usize()])
                        .collect::<Vec<_>>();
                    if let Some(query_result) = mem_map.get_mut(&values) {
                        query_result.multiplicity += 1;
                        map.extend(&query_result.result);
                    } else {
                        let ptr = (mem_map.len() as u64).to_le_bytes().to_vec();
                        let query_result = QueryResult {
                            result: ptr,
                            multiplicity: 1,
                        };
                        map.extend(&query_result.result);
                        mem_map.insert(values, query_result);
                    }
                }
                ExecEntry::Op(Op::Load(len, ptr)) => {
                    let ptr = load_u64(ptr, &map)
                        .try_into()
                        .expect("Pointer too large for current architecture");
                    let mem_map = load_mem_map_mut(&mut record.mem_queries, *len);
                    let (values, query_result) = mem_map
                        .get_index_mut(ptr)
                        .unwrap_or_else(|| panic!("Unbound {len}-wide pointer {ptr}"));
                    query_result.multiplicity += 1;
                    map.extend(values);
                }
                ExecEntry::Op(Op::Call(called_func_idx, args, _)) => {
                    let args = args
                        .iter()
                        .map(|ValIdx(v)| map[*v as usize])
                        .collect::<Vec<_>>();
                    if let Some(query_result) = record.get_mut(*called_func_idx, &args) {
                        query_result.multiplicity += 1;
                        map.extend(query_result.result.clone());
                    } else {
                        let input_len = args.len();
                        // `map_buffer` will become the map for the called function
                        let mut map_buffer = args;
                        // Swap so we can save the old map in `map_buffer` and move on
                        // with `map` already set.
                        std::mem::swap(&mut map_buffer, &mut map);
                        callers_states_stack.push(CallerState {
                            func_idx,
                            map: map_buffer,
                        });
                        // Prepare outer variables to go into the new func scope.
                        func_idx = *called_func_idx;
                        let func = &self.functions[func_idx.to_usize()];
                        assert_eq!(input_len, func.input_size as usize);
                        stack_block_exec_entries!(&func.body);
                    }
                }
                ExecEntry::Ctrl(Ctrl::Return(_, out)) => {
                    let out = out
                        .iter()
                        .map(|ValIdx(v)| map[*v as usize])
                        .collect::<Vec<_>>();

                    // Register the result for the current function index.
                    let query_result = QueryResult {
                        result: out.clone(),
                        multiplicity: 1,
                    };
                    let num_inp = self.functions[func_idx.to_usize()].input_size as usize;
                    let args = map[..num_inp].to_vec();
                    record.insert(func_idx, args, query_result);

                    // Recover the state of the caller
                    if let Some(CallerState {
                        func_idx: caller_func_idx,
                        map: caller_map,
                    }) = callers_states_stack.pop()
                    {
                        func_idx = caller_func_idx;
                        map = caller_map;
                        map.extend(out);
                    } else {
                        // No outer caller... about to exit!
                        assert!(exec_entries_stack.is_empty());
                        assert!(callers_states_stack.is_empty());
                        break;
                    }
                }
                ExecEntry::Ctrl(Ctrl::If(v, tt, ff)) => {
                    let cond = map[v.to_usize()];
                    if cond != 0 {
                        stack_block_exec_entries!(tt);
                    } else {
                        stack_block_exec_entries!(ff);
                    }
                }
                ExecEntry::Ctrl(Ctrl::If64(v, tt, ff)) => {
                    let cond = load_u64(v, &map);
                    if cond != 0 {
                        stack_block_exec_entries!(tt);
                    } else {
                        stack_block_exec_entries!(ff);
                    }
                }
            }
        }
        record
    }
}

fn load_mem_map_mut(
    mem_queries: &mut Vec<(u32, FxIndexMap<Vec<u8>, QueryResult>)>,
    len: u32,
) -> &mut FxIndexMap<Vec<u8>, QueryResult> {
    if let Some(pos) = mem_queries.iter_mut().position(|(k, _)| *k == len) {
        &mut mem_queries[pos].1
    } else {
        mem_queries.push((len, FxIndexMap::default()));
        let last = mem_queries.last_mut().unwrap();
        &mut last.1
    }
}

pub(crate) fn load_u64(a: &ValIdx, map: &[u8]) -> u64 {
    let mut a_buffer = [0; 8];
    for i in 0..8 {
        a_buffer[i] = map[a.to_usize() + i];
    }
    u64::from_le_bytes(a_buffer)
}

#[cfg(test)]
pub(crate) mod tests {
    use crate::{
        aiur::{
            execute::QueryResult,
            frontend::expr::toplevel_from_funcs,
            ir::{FuncIdx, Toplevel},
        },
        func,
    };

    pub(crate) fn factorial_toplevel() -> Toplevel {
        let func = func!(
        fn factorial(n): [8] {
            let one = 1;
            if n {
                let pred = sub(n, one);
                let m = call(factorial, pred);
                let res = mul(n, m);
                return res
            }
            return one
        });
        toplevel_from_funcs(&[func])
    }

    fn square_toplevel() -> Toplevel {
        let func = func!(
        fn square(n): [8] {
            let m = mul(n, n);
            return m
        });
        toplevel_from_funcs(&[func])
    }

    fn cube_toplevel() -> Toplevel {
        let func = func!(
        fn cube(n): [8] {
            let tmp = mul(n, n);
            let m = mul(tmp, n);
            return m
        });
        toplevel_from_funcs(&[func])
    }

    fn double_toplevel() -> Toplevel {
        let func = func!(
        fn double(n): [8] {
            let two = 2;
            let m = mul(two, n);
            return m
        });
        toplevel_from_funcs(&[func])
    }

    fn addition_toplevel() -> Toplevel {
        let func = func!(
        fn addition(n): [8] {
            let m = add(n, n);
            return m
        });
        toplevel_from_funcs(&[func])
    }

    #[test]
    fn test_addition() {
        // Regular computation
        let val_in = 100u64;
        let val_out = val_in + val_in;

        // Euir-rs program
        let func_idx = FuncIdx(0);
        let input = val_in.to_le_bytes();
        let toplevel = addition_toplevel();

        let result = toplevel.execute(func_idx, input.to_vec());
        let out = result.get(func_idx, &input).unwrap();
        assert_eq!(out.result.len(), 8);
        assert_eq!(&out.result, &val_out.to_le_bytes());
    }

    #[test]
    fn test_double() {
        // Regular computation
        let val_in = 50u64;
        let val_out = val_in * 2;

        // Euir-rs program
        let toplevel = double_toplevel();

        let func_idx = FuncIdx(0);
        let input = val_in.to_le_bytes();
        let result = toplevel.execute(func_idx, input.to_vec());
        let out = result
            .get(func_idx, &input)
            .expect("requested item is unavailable");
        assert_eq!(out.result.len(), 8);
        assert_eq!(&out.result, &val_out.to_le_bytes());
    }

    #[test]
    fn test_cube() {
        // Regular program
        let val_in = 3u64;
        let val_out = val_in * val_in * val_in;

        // Aiur-rs program
        let top_level = cube_toplevel();

        let func_idx = FuncIdx(0);
        let input = val_in.to_le_bytes();
        let record = top_level.execute(func_idx, input.to_vec());
        let out = record
            .get(func_idx, &input)
            .expect("output of Lair / Aiur program is unavailable");

        assert_eq!(out.result.len(), 8);
        assert_eq!(&out.result, &val_out.to_le_bytes());
    }

    #[test]
    fn test_square() {
        // Regular computation
        let value_in = 6u64;
        let value_out = value_in * value_in;

        // Aiur-rs program
        let top_level = square_toplevel();

        let func_idx = FuncIdx(0);
        let input = value_in.to_le_bytes();
        let record = top_level.execute(func_idx, input.to_vec());

        let out = record.get(func_idx, &input).expect("no out available");

        assert_eq!(out.result.len(), 8);
        assert_eq!(&out.result, &value_out.to_le_bytes());
    }

    #[test]
    fn test_factorial() {
        let toplevel = factorial_toplevel();

        let record = toplevel.execute(FuncIdx(0), 5u64.to_le_bytes().to_vec());
        let pairs: [(u64, u64); 6] = [(0, 1), (1, 1), (2, 2), (3, 6), (4, 24), (5, 120)];
        for (i, o) in pairs {
            let query_result = QueryResult {
                result: o.to_le_bytes().to_vec(),
                multiplicity: 1,
            };
            assert_eq!(
                record.get(FuncIdx(0), &i.to_le_bytes()),
                Some(&query_result)
            );
        }
    }
}
