use multi_stark::p3_field::{PrimeCharacteristicRing, PrimeField64};

use super::{
    G,
    bytecode::{Ctrl, FunIdx, Function, FxIndexMap, Op, Toplevel},
};

pub struct QueryResult {
    pub(crate) output: Vec<G>,
    pub(crate) multiplicity: G,
}

pub type QueryMap = FxIndexMap<Vec<G>, QueryResult>;

pub struct QueryRecord {
    pub(crate) function_queries: Vec<QueryMap>,
    pub(crate) memory_queries: FxIndexMap<usize, QueryMap>,
}

impl QueryRecord {
    fn new(toplevel: &Toplevel) -> Self {
        let function_queries = toplevel
            .functions
            .iter()
            .map(|_| QueryMap::default())
            .collect();
        let memory_queries = toplevel
            .memory_widths
            .iter()
            .map(|width| (*width, QueryMap::default()))
            .collect();
        Self {
            function_queries,
            memory_queries,
        }
    }
}

impl Toplevel {
    pub fn execute(&self, fun_idx: FunIdx, args: Vec<G>) -> (QueryRecord, Vec<G>) {
        let mut record = QueryRecord::new(self);
        let function = &self.functions[fun_idx];
        let output = function.execute(fun_idx, args, self, &mut record);
        (record, output)
    }
}

enum ExecEntry<'a> {
    Op(&'a Op),
    Ctrl(&'a Ctrl),
}

struct CallerState {
    fun_idx: FunIdx,
    map: Vec<G>,
}

impl Function {
    fn execute(
        &self,
        mut fun_idx: FunIdx,
        mut map: Vec<G>,
        toplevel: &Toplevel,
        record: &mut QueryRecord,
    ) -> Vec<G> {
        let mut exec_entries_stack = vec![];
        let mut callers_states_stack = vec![];
        macro_rules! push_block_exec_entries {
            ($block:expr) => {
                exec_entries_stack.push(ExecEntry::Ctrl(&$block.ctrl));
                exec_entries_stack.extend($block.ops.iter().rev().map(ExecEntry::Op));
            };
        }
        push_block_exec_entries!(&self.body);
        while let Some(exec_entry) = exec_entries_stack.pop() {
            match exec_entry {
                ExecEntry::Op(Op::Const(c)) => map.push(*c),
                ExecEntry::Op(Op::Add(a, b)) => {
                    let a = map[*a];
                    let b = map[*b];
                    map.push(a + b);
                }
                ExecEntry::Op(Op::Sub(a, b)) => {
                    let a = map[*a];
                    let b = map[*b];
                    map.push(a - b);
                }
                ExecEntry::Op(Op::Mul(a, b)) => {
                    let a = map[*a];
                    let b = map[*b];
                    map.push(a * b);
                }
                ExecEntry::Op(Op::Call(callee_idx, args, _)) => {
                    let args = args.iter().map(|i| map[*i]).collect();
                    if let Some(result) = record.function_queries[*callee_idx].get_mut(&args) {
                        result.multiplicity += G::ONE;
                        map.extend(result.output.clone());
                    } else {
                        let saved_map = std::mem::replace(&mut map, args);
                        // Save the current caller state.
                        callers_states_stack.push(CallerState {
                            fun_idx,
                            map: saved_map,
                        });
                        // Prepare outer variables to go into the new func scope.
                        fun_idx = *callee_idx;
                        let function = &toplevel.functions[fun_idx];
                        push_block_exec_entries!(&function.body);
                    }
                }
                ExecEntry::Op(Op::Store(values)) => {
                    let values = values.iter().map(|v| map[*v]).collect::<Vec<_>>();
                    let width = values.len();
                    let memory_queries = record
                        .memory_queries
                        .get_mut(&width)
                        .expect("Invalid memory width");
                    if let Some(result) = memory_queries.get_mut(&values) {
                        result.multiplicity += G::ONE;
                        map.extend(&result.output);
                    } else {
                        let ptr = G::from_usize(memory_queries.len());
                        let result = QueryResult {
                            output: vec![ptr],
                            multiplicity: G::ONE,
                        };
                        memory_queries.insert(values, result);
                        map.push(ptr);
                    }
                }
                ExecEntry::Op(Op::Load(width, ptr)) => {
                    let memory_queries = record
                        .memory_queries
                        .get_mut(width)
                        .expect("Invalid memory width");
                    let ptr = &map[*ptr];
                    let ptr_u64 = ptr.as_canonical_u64();
                    let ptr_usize = usize::try_from(ptr_u64).expect("Pointer is too big");
                    let (args, result) = memory_queries
                        .get_index_mut(ptr_usize)
                        .expect("Unbound pointer");
                    result.multiplicity += G::ONE;
                    map.extend(args);
                }
                ExecEntry::Ctrl(Ctrl::Match(val_idx, cases, default)) => {
                    let val = &map[*val_idx];
                    if let Some(block) = cases.get(val) {
                        push_block_exec_entries!(block);
                    } else {
                        let default = default.as_ref().expect("No match");
                        push_block_exec_entries!(default);
                    }
                }
                ExecEntry::Ctrl(Ctrl::Return(_, output)) => {
                    // Register the query.
                    let input_size = toplevel.functions[fun_idx].layout.input_size;
                    let args = map[..input_size].to_vec();
                    let output = output.iter().map(|i| map[*i]).collect::<Vec<_>>();
                    let result = QueryResult {
                        output: output.clone(),
                        multiplicity: G::ONE,
                    };
                    record.function_queries[fun_idx].insert(args, result);
                    if let Some(CallerState {
                        fun_idx: caller_idx,
                        map: caller_map,
                    }) = callers_states_stack.pop()
                    {
                        // Recover the state of the caller.
                        fun_idx = caller_idx;
                        map = caller_map;
                        map.extend(output);
                    } else {
                        // No outer caller. About to exit.
                        assert!(exec_entries_stack.is_empty());
                        map = output;
                        break;
                    }
                }
            }
        }
        map
    }
}
