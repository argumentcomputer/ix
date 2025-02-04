use rustc_hash::FxHashMap;

use super::ir::{Ctrl, FuncIdx, Op, Prim, Toplevel, ValIdx};

/// `Value` defines actual primitive types supported by Eiur-rs
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub enum Value {
    U64(u64),
    Bool(bool),
}

/// `QueryResult` is an output of the particular function. The `TopLevel` may contain multiply
/// functions, and for each one executed, it generates one `QueryResult` objects that contains
/// output for a given function
#[derive(PartialEq, Debug)]
pub struct QueryResult {
    pub values: Vec<Value>,
    pub multiplicity: u32,
}

/// `QueryRecord` is a collection of `QueryResult` objects that can be referenced by the input tuple
/// used while invoking `TopLevel` execution algorithm
#[derive(Default)]
pub struct QueryRecord {
    pub queries: FxHashMap<(FuncIdx, Vec<Value>), QueryResult>,
    // pub queries_inv: FxHashMap<(FuncIdx, Vec<Value>), Vec<Value>>,
}

enum ExecEntry<'a> {
    Op(&'a Op),
    Ctrl(&'a Ctrl),
}

struct CallerState {
    func_idx: FuncIdx,
    map: Vec<Value>,
}

impl Toplevel {
    /// Implementation of the execution algorithm
    ///
    /// 1) The values from the input are the very first values in the inner stack of the execution
    ///     algorithm
    /// 2) You can write additional input values (for example if you need some constants) into the
    ///     stack while implementing particular block of the program
    pub fn execute(&self, input: (FuncIdx, Vec<Value>)) -> QueryRecord {
        let mut record = QueryRecord::default();
        let mut exec_entries_stack = vec![];
        let mut callers_states_stack = vec![];
        let (mut func_idx, mut map) = input;

        macro_rules! stack_block_exec_entries {
            ($block:expr) => {
                exec_entries_stack.push(ExecEntry::Ctrl(&$block.ctrl));
                exec_entries_stack.extend($block.ops.iter().rev().map(ExecEntry::Op));
            };
        }

        stack_block_exec_entries!(&self.functions[func_idx.to_usize()].body);

        while let Some(exec_entry) = exec_entries_stack.pop() {
            match exec_entry {
                ExecEntry::Op(Op::Prim(Prim::Bool(x))) => map.push(Value::Bool(*x)),
                ExecEntry::Op(Op::Prim(Prim::U64(x))) => map.push(Value::U64(*x)),
                ExecEntry::Op(Op::Add(ValIdx(a), ValIdx(b))) => {
                    match (&map[*a as usize], &map[*b as usize]) {
                        (Value::U64(a), Value::U64(b)) => map.push(Value::U64(*a + *b)),
                        _ => panic!(),
                    }
                }
                ExecEntry::Op(Op::Sub(ValIdx(a), ValIdx(b))) => {
                    match (&map[*a as usize], &map[*b as usize]) {
                        (Value::U64(a), Value::U64(b)) => map.push(Value::U64(*a - *b)),
                        _ => panic!(),
                    }
                }
                ExecEntry::Op(Op::Mul(ValIdx(a), ValIdx(b))) => {
                    match (&map[*a as usize], &map[*b as usize]) {
                        (Value::U64(a), Value::U64(b)) => map.push(Value::U64(*a * *b)),
                        _ => panic!(),
                    }
                }
                ExecEntry::Op(Op::And(ValIdx(a), ValIdx(b))) => {
                    match (&map[*a as usize], &map[*b as usize]) {
                        (Value::U64(a), Value::U64(b)) => map.push(Value::U64(*a & *b)),
                        (Value::Bool(a), Value::Bool(b)) => map.push(Value::Bool(*a & *b)),
                        _ => panic!(),
                    }
                }
                ExecEntry::Op(Op::Lt(ValIdx(a), ValIdx(b))) => {
                    match (&map[*a as usize], &map[*b as usize]) {
                        (Value::U64(a), Value::U64(b)) => map.push(Value::Bool(*a < *b)),
                        _ => panic!(),
                    }
                }
                ExecEntry::Op(Op::Xor(ValIdx(a), ValIdx(b))) => {
                    match (&map[*a as usize], &map[*b as usize]) {
                        (Value::U64(a), Value::U64(b)) => map.push(Value::U64(*a ^ *b)),
                        (Value::Bool(a), Value::Bool(b)) => map.push(Value::Bool(*a ^ *b)),
                        _ => panic!(),
                    }
                }
                ExecEntry::Op(Op::Call(called_func_idx, args)) => {
                    let args = args.iter().map(|ValIdx(v)| map[*v as usize]).collect();
                    let query_input = (*called_func_idx, args);
                    if let Some(query_result) = record.queries.get_mut(&query_input) {
                        query_result.multiplicity += 1;
                        map.extend(query_result.values.clone());
                    } else {
                        // `map_buffer` will become the map for the called function
                        let (called_func_idx, mut map_buffer) = query_input;
                        // Swap so we can save the old map in `map_buffer` and move on
                        // with `map` already set.
                        std::mem::swap(&mut map_buffer, &mut map);
                        callers_states_stack.push(CallerState {
                            func_idx,
                            map: map_buffer,
                        });
                        // Prepare outer variables to go into the new func scope.
                        func_idx = called_func_idx;
                        stack_block_exec_entries!(&self.functions[func_idx.to_usize()].body);
                    }
                }
                ExecEntry::Ctrl(Ctrl::Return(_, out)) => {
                    let out = out
                        .iter()
                        .map(|ValIdx(v)| map[*v as usize])
                        .collect::<Vec<_>>();

                    // Register the result for the current function index.
                    let query_result = QueryResult {
                        values: out.clone(),
                        multiplicity: 1,
                    };
                    let num_inp = self.functions[func_idx.to_usize()].input_size as usize;
                    let args = map[..num_inp].to_vec();
                    record.queries.insert((func_idx, args), query_result);

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
                ExecEntry::Ctrl(Ctrl::If(ValIdx(v), tt, ff)) => {
                    let cond = match &map[*v as usize] {
                        Value::Bool(b) => *b,
                        Value::U64(u) => u != &0,
                    };
                    if cond {
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

#[cfg(test)]
mod tests {
    use crate::eiur::execute::Value::U64;
    use crate::eiur::{
        execute::{QueryResult, Value},
        ir::{Block, Ctrl, FuncIdx, Function, Op, Prim, SelIdx, Toplevel, ValIdx},
    };

    fn factorial_function() -> Function {
        let inp_val_idx = ValIdx(0); // the input is at index 0
        let one_val_idx = ValIdx(1); // a constant `1` value
        let pre_val_idx = ValIdx(2); // inp - one
        let rec_val_idx = ValIdx(3); // factorial(pre)
        let res_val_idx = ValIdx(4); // inp * rec

        let true_block = Block {
            ops: vec![
                Op::Sub(inp_val_idx, one_val_idx),
                Op::Call(FuncIdx(0), vec![pre_val_idx]),
                Op::Mul(inp_val_idx, rec_val_idx),
            ],
            ctrl: Box::new(Ctrl::Return(SelIdx(0), vec![res_val_idx])), // Recursive return
        };

        let false_block = Block {
            ops: vec![],
            ctrl: Box::new(Ctrl::Return(SelIdx(1), vec![one_val_idx])),
        };

        let main_block = Block {
            ops: vec![Op::Prim(Prim::U64(1))],
            ctrl: Box::new(Ctrl::If(inp_val_idx, true_block, false_block)),
        };

        Function {
            input_size: 1,
            output_size: 1,
            body: main_block,
        }
    }

    fn square_function() -> Function {
        let input = ValIdx(0);
        let output = ValIdx(1);

        let main_block = Block {
            ops: vec![Op::Mul(input, input)],
            ctrl: Box::new(Ctrl::Return(SelIdx(0), vec![output])),
        };

        Function {
            input_size: 1,
            output_size: 1,
            body: main_block,
        }
    }

    fn cube_function() -> Function {
        let input = ValIdx(0);
        let tmp = ValIdx(1);
        let output = ValIdx(2);

        let main_block = Block {
            ops: vec![Op::Mul(input, input), Op::Mul(tmp, input)],
            ctrl: Box::new(Ctrl::Return(SelIdx(0), vec![output])),
        };

        Function {
            input_size: 1,
            output_size: 1,
            body: main_block,
        }
    }

    fn double_function() -> Function {
        let input = ValIdx(0);
        let two = ValIdx(1); // constant = 2
        let output = ValIdx(2);

        let main_block = Block {
            ops: vec![Op::Prim(Prim::U64(2)), Op::Mul(input, two)],
            ctrl: Box::new(Ctrl::Return(SelIdx(0), vec![output])),
        };

        Function {
            input_size: 1,
            output_size: 1,
            body: main_block,
        }
    }

    fn addition_function() -> Function {
        let input = ValIdx(0);
        let output = ValIdx(1);

        let main_block = Block {
            ops: vec![Op::Add(input, input)],
            ctrl: Box::new(Ctrl::Return(SelIdx(0), vec![output])),
        };

        Function {
            input_size: 1,
            output_size: 1,
            body: main_block,
        }
    }

    #[test]
    fn test_addition() {
        // Regular computation
        let val_in = 100u64;
        let val_out = val_in + val_in;

        // Euir-rs program
        let input = (FuncIdx(0), vec![U64(val_in)]);
        let toplevel = Toplevel {
            functions: vec![addition_function()],
        };

        let result = toplevel.execute(input.clone());
        let out = result.queries.get(&input).unwrap();
        assert_eq!(out.values.len(), 1);
        assert_eq!(out.values[0], U64(val_out));
    }

    #[test]
    fn test_double() {
        // Regular computation
        let val_in = 50u64;
        let val_out = val_in * 2;

        // Euir-rs program
        let toplevel = Toplevel {
            functions: vec![double_function()],
        };

        let input = (FuncIdx(0), vec![U64(val_in)]);
        let result = toplevel.execute(input.clone());
        let out = result
            .queries
            .get(&input)
            .expect("requested item is unavailable");
        assert_eq!(out.values.len(), 1);
        assert_eq!(out.values[0], U64(val_out));
    }

    #[test]
    fn test_cube() {
        // Regular program
        let val_in = 3u64;
        let val_out = val_in * val_in * val_in;

        // Eiur-rs program
        let top_level = Toplevel {
            functions: vec![cube_function()],
        };

        let input = (FuncIdx(0), vec![U64(val_in)]);
        let record = top_level.execute(input.clone());
        let out = record
            .queries
            .get(&input)
            .expect("output of Lair / Eiur program is unavailable");

        assert_eq!(out.values.len(), 1);
        assert_eq!(out.values[0], U64(val_out));
    }

    #[test]
    fn test_square() {
        // Regular computation
        let value_in = 6u64;
        let value_out = value_in * value_in;

        // Eiur-rs program
        let top_level = Toplevel {
            functions: vec![square_function()],
        };

        let input = (FuncIdx(0), vec![Value::U64(value_in)]);
        let record = top_level.execute(input.clone());

        let out = record.queries.get(&input).expect("no out available");

        assert_eq!(out.values.len(), 1);
        assert_eq!(out.values[0], Value::U64(value_out));
    }

    #[test]
    fn test_factorial() {
        let toplevel = Toplevel {
            functions: vec![factorial_function()],
        };

        let record = toplevel.execute((FuncIdx(0), vec![U64(5)]));
        let pairs = [(0, 1), (1, 1), (2, 2), (3, 6), (4, 24), (5, 120)];
        for (i, o) in pairs {
            let query_result = QueryResult {
                values: vec![U64(o)],
                multiplicity: 1,
            };
            assert_eq!(
                record.queries.get(&(FuncIdx(0), vec![U64(i)])),
                Some(&query_result)
            );
        }
    }
}
