//! Differential test for `Instruction::PtrEq` (opcode 14): the generated
//! native executor must match the interpreter on both equal and unequal
//! pointers, and `PtrEq` operands must enter `native_fingerprint`.
use aiur::bytecode::{Instruction, Program};
use aiur::field::{FieldBackend, NativeField};
use aiur::native::record_diff;
use multi_stark::p3_goldilocks::Goldilocks;

#[allow(warnings, clippy::all, clippy::pedantic)]
mod generated {
  include!(concat!(env!("OUT_DIR"), "/ptreq.rs"));
}
use generated::PtrEq;

fn program() -> Program {
  serde_json::from_slice(include_bytes!("fixtures/ptreq.json")).unwrap()
}

fn check<B: FieldBackend>(
  program: &aiur::bytecode::CheckedProgram<B>,
  field: B,
) {
  let prepared = program.prepare_hints(&[]).unwrap();
  let native = prepared.bind_native::<PtrEq>().unwrap();
  let pairs = [
    (0u64, 0u64, 1u64),
    (7, 7, 1),
    (7, 8, 0),
    (0, 1, 0),
    (42, 99, 0),
    (99, 99, 1),
  ];
  for entry in ["ptreq_rom", "ptreq_direct"] {
    for (a, b, expected) in pairs {
      let args = vec![field.from_u64(a), field.from_u64(b)];
      let interp = prepared.execute(entry, args.clone()).unwrap();
      let generated = native.execute(entry, args).unwrap();
      assert_eq!(interp.output, vec![field.from_u64(expected)]);
      record_diff(&interp, &generated)
        .unwrap_or_else(|e| panic!("{entry}({a}, {b}): {e}"));
    }
  }
}

#[test]
fn ptreq_native_matches_interpreter_over_prime_field() {
  let program = program().check().unwrap();
  check(&program, program.field());
}

#[test]
fn ptreq_native_matches_interpreter_over_goldilocks() {
  let program = program().check_field::<Goldilocks>().unwrap();
  check(&program, NativeField::<Goldilocks>::new());
}

#[test]
fn ptreq_operand_changes_native_fingerprint() {
  let base = program().check().unwrap();
  let mut modified = program();
  modified.functions[1].code[0] =
    Instruction::PtrEq { dest: 2, left: 0, right: 0 };
  let modified = modified.check().unwrap();
  assert_ne!(base.native_fingerprint(), modified.native_fingerprint());
}
