use super::*;
use crate::bytecode::FunctionLayout;

fn empty_record() -> QueryRecord {
  QueryRecord::new(&Toplevel {
    functions: vec![],
    memory_sizes: vec![],
    circuits: vec![],
  })
}

fn empty_io() -> IOBuffer {
  IOBuffer { data: FxHashMap::default(), map: FxHashMap::default() }
}

fn trace1(record: &QueryRecord) -> Vec<G> {
  let widths: Vec<_> = Bytes1.lookups().iter().map(|l| l.args.len()).collect();
  Bytes1.witness_data(record, &widths).0.values
}

fn trace2(record: &QueryRecord) -> Vec<G> {
  let widths: Vec<_> = Bytes2.lookups().iter().map(|l| l.args.len()).collect();
  Bytes2.witness_data(record, &widths).0.values
}

#[test]
fn bad_byte_queries_reject_before_mutation_including_second_digit_alias() {
  let mut record = empty_record();
  record.bytes1_queries.bump_bit_decomposition(&G::ONE).unwrap();
  record.bytes2_queries.bump_range_check(&G::ONE, &G::ZERO).unwrap();
  let before1 = trace1(&record);
  let before2 = trace2(&record);
  for value in [G::from_u16(256), G::from_u64(1 << 40), G::NEG_ONE] {
    let error = ExecError::U8RangeCheckFailed(value.as_canonical_u64());
    for op in
      [Bytes1Op::BitDecomposition, Bytes1Op::ShiftLeft, Bytes1Op::ShiftRight]
    {
      assert_eq!(
        Bytes1.execute(&op, &[value], &mut record),
        Err(error.clone())
      );
    }
    for (a, b) in [(value, G::ZERO), (G::ZERO, value)] {
      for op in [
        Bytes2Op::Xor,
        Bytes2Op::Add,
        Bytes2Op::Sub,
        Bytes2Op::Mul,
        Bytes2Op::And,
        Bytes2Op::Or,
        Bytes2Op::LessThan,
        Bytes2Op::XorSplit7,
        Bytes2Op::XorSplit4,
      ] {
        assert_eq!(
          Bytes2.execute(&op, &[a, b], &mut record),
          Err(error.clone())
        );
      }
      assert_eq!(
        record.bytes2_queries.bump_range_check(&a, &b),
        Err(error.clone())
      );
    }
  }
  assert_eq!(trace1(&record), before1);
  assert_eq!(trace2(&record), before2);
}

type UnaryHelper = fn(G, &mut QueryRecord) -> Result<Vec<G>, ExecError>;
type BinaryHelper = fn(G, G, &mut QueryRecord) -> Result<Vec<G>, ExecError>;

#[test]
fn generated_byte_helpers_match_gadget_outputs_queries_and_typed_errors() {
  let unary: [(Bytes1Op, UnaryHelper); 3] = [
    (Bytes1Op::BitDecomposition, |a, r| {
      bytes1_bit_decompose_value(a, r).map(Vec::from)
    }),
    (Bytes1Op::ShiftLeft, |a, r| {
      bytes1_shift_left_value(a, r).map(|v| vec![v])
    }),
    (Bytes1Op::ShiftRight, |a, r| {
      bytes1_shift_right_value(a, r).map(|v| vec![v])
    }),
  ];
  let binary: [(Bytes2Op, BinaryHelper); 9] = [
    (Bytes2Op::Xor, |a, b, r| bytes2_xor_value(a, b, r).map(|v| vec![v])),
    (Bytes2Op::And, |a, b, r| bytes2_and_value(a, b, r).map(|v| vec![v])),
    (Bytes2Op::Or, |a, b, r| bytes2_or_value(a, b, r).map(|v| vec![v])),
    (Bytes2Op::LessThan, |a, b, r| {
      bytes2_less_than_value(a, b, r).map(|v| vec![v])
    }),
    // The gadget returns just the low byte for add/sub; their generated
    // helpers additionally return the derived carry/borrow.
    (Bytes2Op::Add, |a, b, r| bytes2_add_value(a, b, r).map(|(v, _)| vec![v])),
    (Bytes2Op::Sub, |a, b, r| bytes2_sub_value(a, b, r).map(|(v, _)| vec![v])),
    (Bytes2Op::Mul, |a, b, r| {
      bytes2_mul_value(a, b, r).map(|(a, b)| vec![a, b])
    }),
    (Bytes2Op::XorSplit7, |a, b, r| {
      bytes2_xor_split7_value(a, b, r).map(|(a, b)| vec![a, b])
    }),
    (Bytes2Op::XorSplit4, |a, b, r| {
      bytes2_xor_split4_value(a, b, r).map(|(a, b)| vec![a, b])
    }),
  ];
  let (mut native, mut interpreted) = (empty_record(), empty_record());
  let inputs = [
    G::ZERO,
    G::ONE,
    G::from_u8(255),
    G::new(G::ORDER_U64 + 7),
    G::from_u16(256),
    G::new(G::ORDER_U64 + 256),
    G::NEG_ONE,
  ];
  for (op, helper) in unary {
    for a in inputs {
      assert_eq!(
        helper(a, &mut native),
        Bytes1.execute(&op, &[a], &mut interpreted)
      );
    }
  }
  for (op, helper) in binary {
    for a in inputs {
      for b in inputs {
        assert_eq!(
          helper(a, b, &mut native),
          Bytes2.execute(&op, &[a, b], &mut interpreted)
        );
      }
    }
  }
  assert_eq!(trace1(&native), trace1(&interpreted));
  assert_eq!(trace2(&native), trace2(&interpreted));
}

fn call_toplevel(
  op: Op,
  inputs: usize,
  outputs: usize,
  hint: bool,
) -> Toplevel {
  let make = |ops, entry| Function {
    body: Block {
      ops,
      ctrl: Ctrl::Return(0, (inputs..inputs + outputs).collect()),
    },
    // Only execution is used here, not synthesis of these fixture layouts.
    layout: FunctionLayout {
      input_size: inputs,
      selectors: 1,
      auxiliaries: 1,
      lookups: 1,
    },
    entry,
    constrained: true,
  };
  Toplevel {
    functions: vec![
      make(vec![Op::Call(1, (0..inputs).collect(), outputs, hint)], true),
      make(vec![op], false),
    ],
    memory_sizes: vec![],
    // This fixture tests execution/rejection, not a proving-system layout.
    circuits: vec![],
  }
}

#[test]
fn bytecode_rejects_every_bad_binary_operand_in_checked_and_hint_calls() {
  type BinaryOp = fn(usize, usize) -> Op;
  let ops: [(BinaryOp, usize); 9] = [
    (Op::U8Xor, 1),
    (Op::U8Add, 2),
    (Op::U8Sub, 2),
    (Op::U8Mul, 2),
    (Op::U8And, 1),
    (Op::U8Or, 1),
    (Op::U8LessThan, 1),
    (Op::U8XorSplit7, 2),
    (Op::U8XorSplit4, 2),
  ];
  for (op, outputs) in ops {
    for hint in [false, true] {
      let tl = call_toplevel(op(0, 1), 2, outputs, hint);
      for bad in [G::from_u16(256), G::from_u64(1 << 40), G::NEG_ONE] {
        for input in [vec![bad, G::ZERO], vec![G::ZERO, bad]] {
          assert_eq!(
            tl.execute(0, input, &mut empty_io()).err(),
            Some(ExecError::U8RangeCheckFailed(bad.as_canonical_u64()))
          );
        }
      }
      assert!(
        tl.execute(0, vec![G::from_u8(255), G::ONE], &mut empty_io()).is_ok()
      );
    }
  }
}

#[test]
fn bytecode_unary_rejection_and_unconstrained_range_check_boundary() {
  let ops: [(fn(usize) -> Op, usize); 3] =
    [(Op::U8BitDecomposition, 8), (Op::U8ShiftLeft, 1), (Op::U8ShiftRight, 1)];
  for (op, outputs) in ops {
    let tl = call_toplevel(op(0), 1, outputs, false);
    assert_eq!(
      tl.execute(0, vec![G::from_u16(256)], &mut empty_io()).err(),
      Some(ExecError::U8RangeCheckFailed(256))
    );
    assert!(tl.execute(0, vec![G::from_u8(255)], &mut empty_io()).is_ok());
  }
  for hint in [false, true] {
    let tl = call_toplevel(Op::U8RangeCheck(0, 1), 2, 0, hint);
    let result =
      tl.execute(0, vec![G::ZERO, G::from_u16(256)], &mut empty_io());
    if hint {
      assert!(result.is_ok(), "unconstrained range checks remain advisory");
    } else {
      assert_eq!(result.err(), Some(ExecError::U8RangeCheckFailed(256)));
    }
  }
}
