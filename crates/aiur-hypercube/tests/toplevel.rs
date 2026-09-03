//! End-to-end: an Aiur `Toplevel` over KoalaBear, executed by Aiur's
//! interpreter and proved with the Hypercube backend.

use aiur::{
  bytecode::{Block, Ctrl, Function, FunctionLayout, Op, Toplevel},
  execute::IOBuffer,
  function_channel,
};
use aiur_hypercube::{ProverParams, ShardingParams, ToplevelMachine, verify};
use multi_stark::p3_field::PrimeCharacteristicRing;
use p3_koala_bear::KoalaBear as FF;
use slop_algebra::AbstractField;

/// `f(a, b) = (a + 1) * b`, calling itself nowhere: one branchless function.
fn mul_toplevel() -> Toplevel<FF> {
  let body = Block {
    ops: vec![Op::Const(FF::ONE), Op::Add(0, 2), Op::Mul(3, 1)],
    ctrl: Ctrl::Return(0, vec![4]),
  };
  let function = Function {
    body,
    layout: FunctionLayout {
      input_size: 2,
      selectors: 1,
      auxiliaries: 4,
      lookups: 1,
    },
    entry: true,
    constrained: true,
  };
  Toplevel { functions: vec![function], memory_sizes: vec![] }
}

fn params() -> ProverParams {
  // The byte gadgets carry a 65536-row preprocessed table.
  ProverParams { log_blowup: 1, log_stacking_height: 18, max_log_row_count: 17 }
}

fn io_buffer() -> IOBuffer<FF> {
  IOBuffer { data: Default::default(), map: Default::default() }
}

#[test]
fn proves_and_verifies_a_toplevel_call() {
  let toplevel = mul_toplevel();
  let machine = ToplevelMachine::build(&toplevel, 0).unwrap();
  let (a, b) = (FF::from_u32(3), FF::from_u32(5));
  let (claim, vk, proof) = machine
    .execute_and_prove(
      &toplevel,
      &[a, b],
      &mut io_buffer(),
      params(),
      ShardingParams::default(),
    )
    .unwrap();
  assert_eq!(
    claim,
    vec![function_channel(), FF::ZERO, a, b, (a + FF::ONE) * b]
  );
  verify(machine.machine(), params(), &vk, &proof).unwrap();
}

#[test]
fn rejects_a_tampered_claim() {
  let toplevel = mul_toplevel();
  let machine = ToplevelMachine::build(&toplevel, 0).unwrap();
  let (a, b) = (FF::from_u32(3), FF::from_u32(5));
  let mut io = io_buffer();
  let (query_record, output) =
    toplevel.execute(0, vec![a, b], &mut io).unwrap();
  let mut claim = machine.claim(&[a, b], &output);
  *claim.last_mut().unwrap() += FF::ONE;
  let record = machine.record(&toplevel, &query_record, &io, &claim).unwrap();
  let (vk, proof) =
    aiur_hypercube::prove(machine.machine(), vec![record], params());
  assert!(verify(machine.machine(), params(), &vk, &proof).is_err());
}

/// `f(a, b) = g(a) * b` with `g(a) = a + 1`, where `g(a)` round-trips through
/// a width-1 memory table (store, then load).
fn call_and_memory_toplevel() -> Toplevel<FF> {
  let f = Function {
    body: Block {
      ops: vec![
        Op::Call(1, vec![0], 1, false),
        Op::Store(vec![1]),
        Op::Load(1, 3),
        Op::Mul(2, 4),
      ],
      ctrl: Ctrl::Return(0, vec![5]),
    },
    layout: FunctionLayout {
      input_size: 2,
      selectors: 1,
      auxiliaries: 5,
      lookups: 4,
    },
    entry: true,
    constrained: true,
  };
  let g = Function {
    body: Block {
      ops: vec![Op::Const(FF::ONE), Op::Add(0, 1)],
      ctrl: Ctrl::Return(0, vec![2]),
    },
    layout: FunctionLayout {
      input_size: 1,
      selectors: 1,
      auxiliaries: 1,
      lookups: 1,
    },
    entry: false,
    constrained: true,
  };
  Toplevel { functions: vec![f, g], memory_sizes: vec![1] }
}

#[test]
fn proves_calls_and_memory() {
  let toplevel = call_and_memory_toplevel();
  let machine = ToplevelMachine::build(&toplevel, 0).unwrap();
  let (a, b) = (FF::from_u32(3), FF::from_u32(5));
  let (claim, vk, proof) = machine
    .execute_and_prove(
      &toplevel,
      &[a, b],
      &mut io_buffer(),
      params(),
      ShardingParams::default(),
    )
    .unwrap();
  assert_eq!(
    claim,
    vec![function_channel(), FF::ZERO, a, b, (a + FF::ONE) * b]
  );
  verify(machine.machine(), params(), &vk, &proof).unwrap();
}

#[test]
fn rejects_a_forged_memory_pointer() {
  // A second memory row claiming pointer 0 with a different value. Its
  // multiplicity is zero, so the memory lookups still balance; only the
  // pointer allocation chain can reject the aliasing.
  let toplevel = call_and_memory_toplevel();
  let machine = ToplevelMachine::build(&toplevel, 0).unwrap();
  let (a, b) = (FF::from_u32(3), FF::from_u32(5));
  let mut io = io_buffer();
  let (query_record, output) =
    toplevel.execute(0, vec![a, b], &mut io).unwrap();
  let claim = machine.claim(&[a, b], &output);
  let mut record =
    machine.record(&toplevel, &query_record, &io, &claim).unwrap();
  // The memory table is the third circuit (f, g, memory, bytes1, bytes2,
  // boundary); duplicate its single real row into the next padding row.
  let trace = record.traces[2].as_mut().unwrap();
  let width = trace.width;
  let mut row: Vec<_> = trace.values[..width].to_vec();
  row[0] = aiur_hypercube::F::from_canonical_u32(0); // multiplicity
  row[3] += aiur_hypercube::F::from_canonical_u32(1); // stored value
  trace.values[width..2 * width].copy_from_slice(&row);
  let (vk, proof) =
    aiur_hypercube::prove(machine.machine(), vec![record], params());
  assert!(verify(machine.machine(), params(), &vk, &proof).is_err());
}

#[test]
fn prints_vk_size() {
  // The vk is machine-independent in size (commitments + constants), so the
  // toy machine's number is the kernel's too.
  let toplevel = mul_toplevel();
  let machine = ToplevelMachine::build(&toplevel, 0).unwrap();
  let (_claim, vk, proof) = machine
    .execute_and_prove(
      &toplevel,
      &[FF::from_u32(3), FF::from_u32(5)],
      &mut io_buffer(),
      params(),
      ShardingParams::default(),
    )
    .unwrap();
  let vk_bytes = bincode::serialize(&vk).unwrap();
  let proof_bytes = bincode::serialize(&proof).unwrap();
  println!(
    "hypercube vk: {} bytes; proof alone: {} bytes",
    vk_bytes.len(),
    proof_bytes.len()
  );
}
