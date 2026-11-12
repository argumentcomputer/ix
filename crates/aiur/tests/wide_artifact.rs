//! Wide artifact transport and cross-language fixtures. No test executes or
//! proves a BN254 program; the arithmetic backend remains a separate milestone.
use aiur::{
  FieldWord,
  artifact::{
    ExecutionPackage, Package, WidePackage, decode_cases, decode_groups,
    encode_cases, encode_groups,
  },
  bytecode::Instruction,
  ixon::Writer,
  library::io::Invocation,
  trace::Polynomial,
};
use std::ops::Range;

const FR: [u64; 4] = [
  0x43e1_f593_f000_0001,
  0x2833_e848_79b9_7091,
  0xb850_45b6_8181_585d,
  0x3064_4e72_e131_a029,
];
const MINUS_ONE: [u64; 4] = [FR[0] - 1, FR[1], FR[2], FR[3]];
const BIG: [u64; 4] = [5, 1, 1, 0];
const LEAN_FIXTURE: &[u8] = include_bytes!("fixtures/bn254-wide.ixa");

fn constants(polynomial: &Polynomial<FieldWord>, output: &mut Vec<FieldWord>) {
  match polynomial {
    Polynomial::Const(value) => output.push(*value),
    Polynomial::Var(_) => {},
    Polynomial::Add(operands)
    | Polynomial::Sub(operands)
    | Polynomial::Mul(operands) => {
      for operand in operands.iter() {
        constants(operand, output);
      }
    },
  }
}

#[test]
fn lean_bn254_transport_fixture_roundtrips_every_field_bit() {
  assert_eq!(&LEAN_FIXTURE[..9], b"IXAIURP\0\x03");
  let package = WidePackage::decode(LEAN_FIXTURE).unwrap();
  assert_eq!(package.program.modulus, FieldWord::from_limbs_le(FR));
  assert_eq!(package.encode().unwrap(), LEAN_FIXTURE);
  assert!(Package::decode(LEAN_FIXTURE).is_err());

  let instructions = package.program.functions.iter().flat_map(|f| &f.code);
  let mut literal = false;
  let mut guard = false;
  let mut branch = false;
  for instruction in instructions {
    match instruction {
      Instruction::Literal { value, .. } => literal |= value.to_u64().is_err(),
      Instruction::Guard { tests, .. } => {
        guard |= tests.iter().any(|(_, value)| value.to_u64().is_err());
      },
      Instruction::Branch { tests, .. } => {
        branch |= tests.iter().any(|(_, value)| value.to_u64().is_err());
      },
      _ => {},
    }
  }
  assert!(literal && guard && branch);
  let table_values: Vec<_> = package
    .program
    .tables
    .iter()
    .flat_map(|table| table.rows.iter().flatten())
    .copied()
    .collect();
  assert!(table_values.contains(&FieldWord::from_limbs_le(MINUS_ONE)));
  assert!(table_values.contains(&FieldWord::from_limbs_le(BIG)));
  assert!(table_values.contains(&FieldWord::ZERO));

  let trace = package.trace.as_ref().expect("Lean fixture includes a trace");
  assert_eq!(trace.modulus, package.program.modulus);
  let mut trace_constants = Vec::new();
  for chip in &trace.chips {
    for polynomial in chip.output.iter().chain(&chip.constraints) {
      constants(polynomial, &mut trace_constants);
    }
    for send in &chip.sends {
      for polynomial in send.args.iter().chain(std::iter::once(&send.enable)) {
        constants(polynomial, &mut trace_constants);
      }
    }
  }
  assert!(trace_constants.iter().any(|value| value.to_u64().is_err()));
  assert!(trace_constants.iter().all(|value| *value < package.program.modulus));
}

#[test]
fn legacy_goldilocks_fixtures_keep_their_exact_version_two_encoding() {
  for (v1, v2) in [
    (
      &include_bytes!("fixtures/grouping.v1.ixa")[..],
      &include_bytes!("fixtures/grouping.ixa")[..],
    ),
    (
      &include_bytes!("fixtures/depth.v1.ixa")[..],
      &include_bytes!("fixtures/depth.ixa")[..],
    ),
  ] {
    let narrow = Package::decode(v1).unwrap();
    assert_eq!(narrow.program.modulus, 0xffff_ffff_0000_0001);
    assert_eq!(narrow.encode(), v2);
    assert_eq!(Package::decode(v2).unwrap(), narrow);
    assert_eq!(Package::decode(v2).unwrap().encode(), v2);
    let wide = WidePackage::decode(v1).unwrap();
    assert_eq!(wide, WidePackage::decode(v2).unwrap());
    assert_eq!(wide.program.modulus.to_u64().unwrap(), narrow.program.modulus);
    let v3 = wide.encode().unwrap();
    assert_eq!(v3[8], 3);
    assert_eq!(WidePackage::decode(&v3).unwrap(), wide);
  }
}

#[derive(Default)]
struct Wire {
  bytes: Vec<u8>,
}

impl Wire {
  fn nat(&mut self, value: u64) {
    let mut writer = Writer::new();
    writer.nat(value);
    self.bytes.extend(writer.into_bytes());
  }

  fn string(&mut self, value: &str) {
    self.nat(value.len() as u64);
    self.bytes.extend(value.as_bytes());
  }

  fn nats(&mut self, values: &[u64]) {
    self.nat(values.len() as u64);
    for &value in values {
      self.nat(value);
    }
  }

  // Field framing is intentionally independent of FieldWord::write.
  fn field(&mut self, limbs: &[u64]) -> Range<usize> {
    let start = self.bytes.len();
    self.nats(limbs);
    start..self.bytes.len()
  }

  fn byte(&mut self, byte: u8) {
    self.bytes.push(byte);
  }
}

struct Encoded {
  bytes: Vec<u8>,
  modulus: Range<usize>,
  literal: Range<usize>,
  guard: Range<usize>,
  branch: Range<usize>,
  table: Range<usize>,
  trace_modulus: Range<usize>,
  trace_constant: Range<usize>,
  backref: Range<usize>,
}

/// A small wire-level package for locating adversarial edits. It exercises
/// codec framing; the trace is not an execution certificate.
fn encoded() -> Encoded {
  let mut w = Wire::default();
  w.bytes.extend(b"IXAIURP\0");
  w.nat(3);
  w.nat(2);
  let modulus = w.field(&FR);
  w.nat(1);
  w.string("Wide::entry");
  w.nat(1);
  w.byte(0);
  w.byte(0);
  w.nat(2);
  w.nat(4);
  w.byte(0);
  w.nat(1);
  let literal = w.field(&BIG[..3]);
  w.byte(4);
  w.nat(1);
  w.nat(0);
  let guard = w.field(&MINUS_ONE);
  w.string("wide guard");
  w.byte(5);
  w.nat(1);
  w.nat(0);
  let branch = w.field(&BIG[..3]);
  w.nat(3);
  w.byte(12);
  w.nats(&[1]);
  w.nat(0);
  w.nat(2);
  w.nat(1);
  let table = w.field(&MINUS_ONE);
  w.nat(1);
  w.field(&[]);
  w.nat(1);
  w.string("Wide::values");
  w.byte(0);
  w.nats(&[0, 1]);
  w.nat(0);
  w.nat(1);
  w.string("Wide::entry");
  w.nat(0);
  w.nat(1);
  w.byte(0);
  w.byte(1);
  w.byte(0);
  w.byte(1);
  w.nat(3);
  let trace_modulus = w.field(&FR);
  w.nats(&[16, 8]);
  w.nat(3);
  w.byte(0);
  let trace_constant = w.field(&MINUS_ONE);
  w.byte(1);
  w.nat(0);
  w.byte(2);
  let backref_start = w.bytes.len();
  w.nat(2);
  let backref = backref_start..w.bytes.len();
  w.nat(1);
  w.nat(0);
  w.nat(1);
  w.string("wide");
  w.nat(1);
  w.nat(0);
  w.nats(&[0]);
  w.nats(&[0]);
  w.nats(&[2]);
  w.nat(0);
  w.nat(0);
  w.byte(0);
  w.nat(0);
  w.nat(0);
  w.nat(0);
  Encoded {
    bytes: w.bytes,
    modulus,
    literal,
    guard,
    branch,
    table,
    trace_modulus,
    trace_constant,
    backref,
  }
}

fn word_bytes(limbs: &[u64]) -> Vec<u8> {
  let mut w = Wire::default();
  w.field(limbs);
  w.bytes
}

fn replaced(bytes: &[u8], range: Range<usize>, replacement: &[u8]) -> Vec<u8> {
  let mut result = bytes.to_vec();
  result.splice(range, replacement.iter().copied());
  result
}

#[test]
fn independent_wire_fixture_roundtrips_canonically() {
  let fixture = encoded();
  let package = WidePackage::decode(&fixture.bytes).unwrap();
  assert_eq!(package.encode().unwrap(), fixture.bytes);
  assert_eq!(package.program.modulus, FieldWord::from_limbs_le(FR));
}

#[test]
fn every_field_position_rejects_noncanonical_representatives() {
  let f = encoded();
  for position in [&f.literal, &f.guard, &f.branch, &f.table, &f.trace_constant]
  {
    for invalid in [FR, [u64::MAX; 4]] {
      let bytes = replaced(&f.bytes, position.clone(), &word_bytes(&invalid));
      assert!(WidePackage::decode(&bytes).is_err(), "field at {position:?}");
    }
  }
}

#[test]
fn malformed_limb_counts_zero_aliases_and_truncations_are_rejected() {
  let f = encoded();
  for position in [
    &f.modulus,
    &f.literal,
    &f.guard,
    &f.table,
    &f.trace_modulus,
    &f.trace_constant,
  ] {
    for invalid in [word_bytes(&[1, 0]), word_bytes(&[0]), vec![5]] {
      let bytes = replaced(&f.bytes, position.clone(), &invalid);
      assert!(WidePackage::decode(&bytes).is_err(), "field at {position:?}");
    }
    for end in position.clone() {
      assert!(WidePackage::decode(&f.bytes[..end]).is_err());
    }
  }
  for end in 0..LEAN_FIXTURE.len() {
    assert!(WidePackage::decode(&LEAN_FIXTURE[..end]).is_err(), "prefix {end}");
  }
}

#[test]
fn modulus_identity_backreferences_and_trailing_bytes_are_checked() {
  for prefix in
    [&b"IXAIURP\0\x03\x02\x00"[..], &b"IXAIURP\0\x03\x02\x01\x01"[..]]
  {
    assert!(WidePackage::decode(prefix).unwrap_err().contains("modulus"));
  }
  let f = encoded();
  for invalid in [word_bytes(&[]), word_bytes(&[1])] {
    assert!(
      WidePackage::decode(&replaced(&f.bytes, f.modulus.clone(), &invalid))
        .is_err()
    );
  }
  let different_modulus = [FR[0] + 1, FR[1], FR[2], FR[3]];
  let changed = replaced(
    &f.bytes,
    f.trace_modulus.clone(),
    &word_bytes(&different_modulus),
  );
  assert!(WidePackage::decode(&changed).unwrap_err().contains("moduli differ"));
  for backref in [0, 3, u64::MAX] {
    let mut writer = Writer::new();
    writer.nat(backref);
    assert!(
      WidePackage::decode(&replaced(
        &f.bytes,
        f.backref.clone(),
        &writer.into_bytes()
      ))
      .is_err()
    );
  }
  let mut trailing = f.bytes;
  trailing.push(0);
  assert!(WidePackage::decode(&trailing).unwrap_err().contains("trailing"));
}

#[test]
fn wide_writer_rejects_invalid_in_memory_packages() {
  let base = WidePackage::decode(LEAN_FIXTURE).unwrap();
  let mut invalid = base.clone();
  invalid.program.modulus = FieldWord::ONE;
  assert!(invalid.encode().is_err());
  let mut invalid = base.clone();
  invalid.trace.as_mut().unwrap().modulus = FieldWord::from(97);
  assert!(invalid.encode().is_err());
  let mut invalid = base.clone();
  invalid.program.tables[0].rows[0][0] = base.program.modulus;
  assert!(invalid.encode().is_err());
  let mut invalid = base;
  invalid.trace.as_mut().unwrap().chips[0]
    .constraints
    .push(Polynomial::Const(invalid.program.modulus));
  assert!(invalid.encode().is_err());
}

#[test]
fn version_three_is_not_accepted_as_an_execution_or_other_legacy_envelope() {
  let mut groups = encode_groups(&[]);
  groups[8] = 3;
  assert!(decode_groups(&groups).is_err());
  let mut cases = encode_cases(&[]);
  cases[8] = 3;
  assert!(decode_cases(&cases).is_err());
  let invocation = Invocation {
    entry: "Wide::entry".into(),
    args: vec![0],
    streams: Default::default(),
  };
  let mut invocation = invocation.encode();
  invocation[8] = 3;
  assert!(Invocation::decode(&invocation).is_err());
  let mut execution = LEAN_FIXTURE.to_vec();
  execution[..8].copy_from_slice(b"IXAIURX\0");
  assert!(ExecutionPackage::decode(&execution).is_err());
  let mut unknown = LEAN_FIXTURE.to_vec();
  unknown[8] = 4;
  assert!(WidePackage::decode(&unknown).is_err());
}
