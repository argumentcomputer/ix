//! Opt-in differentials against independently generated, retained artifacts.
//! These validate codec component relations, not whole-image circuit admission.
use super::*;
use crate::{
  ixby::{bits::read_words, ixbf},
  sizing::CountedGate,
};
use flock_prover::{field::F128, r1cs::BlockR1cs};
use num_bigint::BigUint;
use std::{
  ffi::OsStr,
  fs::File,
  io::Read,
  path::{Path, PathBuf},
};

pub(super) fn path(name: &str) -> PathBuf {
  std::env::var_os(name).map(PathBuf::from).unwrap_or_else(|| {
    panic!("{name} must explicitly name an external fixture")
  })
}

pub(super) fn read(path: &Path) -> Vec<u8> {
  let limit = ixbf::DecodeLimits::default().bytes;
  let mut bytes = Vec::new();
  File::open(path)
    .unwrap()
    .take(limit as u64 + 1)
    .read_to_end(&mut bytes)
    .unwrap();
  assert!(bytes.len() <= limit, "external codec fixture byte limit");
  bytes
}

pub(super) fn word(value: &BigUint) -> F128 {
  assert!(
    value.bits() <= 128,
    "external metadata exceeds the explicit codec class"
  );
  let mut bytes = value.to_bytes_le();
  bytes.resize(16, 0);
  crate::hash::pack_bytes(&bytes)
}

pub(super) fn expected_header(artifact: &ixbf::Artifact<'_>) -> Vec<F128> {
  let limits = artifact.limits();
  let entry = BigUint::from(artifact.entry());
  let constructors = BigUint::from(artifact.constructors().len());
  let fields = [
    &limits.functions,
    &limits.constructors,
    &limits.blocks,
    &limits.locals,
    &limits.operands,
    &limits.continuations,
    &limits.input_nodes,
    &limits.nat_bits,
    &limits.string_bytes,
    &limits.byte_array_bytes,
    artifact.max_steps(),
    &entry,
    &constructors,
  ];
  let cursor = 12
    + fields
      .iter()
      .map(|value| tests::natural_bytes(value).len())
      .sum::<usize>();
  let mut output: Vec<_> = fields.into_iter().map(word).collect();
  output.push(F128::new(cursor as u64, 0));
  output
}

fn visit<'a>(
  instruction: &ixbf::Instruction<'a>,
  f: &mut impl FnMut(&ixbf::Operand<'a>),
) {
  use ixbf::{Instruction as I, Operation as O};
  let args = match instruction {
    I::Let(op, _) => match op {
      O::Copy(value) | O::Project(value, _) => {
        f(value);
        return;
      },
      O::Primitive(_, args)
      | O::Construct(_, args)
      | O::Closure(_, args)
      | O::Call(_, args)
      | O::CallSelf(args) => args,
      O::Apply(value, args) => {
        f(value);
        args
      },
    },
    I::Return(value)
    | I::CaseConstructor(value, _)
    | I::CaseNat(value, _, _)
    | I::Branch(value, _, _) => {
      f(value);
      return;
    },
    I::TailCall(_, args) | I::TailCallSelf(args) => args,
    I::TailApply(value, args) => {
      f(value);
      args
    },
  };
  for arg in args {
    f(arg);
  }
}

/// Untrusted fixture preparation: locate a borrowed literal in the original
/// buffer and check its canonical prefix. This is not a circuit source lookup.
pub(super) fn span_input(
  source: &[u8],
  payload: &[u8],
  limit: &BigUint,
) -> [F128; 4] {
  let start = (payload.as_ptr() as usize)
    .checked_sub(source.as_ptr() as usize)
    .expect("borrowed scalar payload source");
  assert_eq!(
    source.get(start..start.checked_add(payload.len()).unwrap()),
    Some(payload)
  );
  let length = tests::natural_bytes(&BigUint::from(payload.len()));
  let scalar = start.checked_sub(length.len() + 1).unwrap();
  assert_eq!(source[scalar], 6);
  assert_eq!(&source[scalar + 1..start], length);
  byte_span_tests::input(source, scalar, word(limit))
}

pub(super) fn check_span(
  gate: &ByteArraySpanGate,
  r1cs: &BlockR1cs,
  source: &[u8],
  payload: &[u8],
  limit: &BigUint,
) -> ([F128; 4], [F128; 2]) {
  let input = span_input(source, payload, limit);
  let start = (payload.as_ptr() as usize) - (source.as_ptr() as usize);
  let expected = [
    F128::new(start as u64, payload.len() as u64),
    F128::new((start + payload.len()) as u64, source.len() as u64),
  ];
  let row = byte_span_tests::bits(gate, &input);
  assert!(tests::satisfies(r1cs, &row));
  let output = read_words(&row, 4, 3);
  assert_eq!(output[..2], expected);
  assert_eq!(output[2], F128::ZERO);
  (input, expected)
}

fn check(
  bytes: &[u8],
  header: &HeaderDecodeGate,
  header_r1cs: &BlockR1cs,
  nat: &NaturalDecodeGate,
  nat_r1cs: &BlockR1cs,
) -> usize {
  let artifact =
    ixbf::decode_program(bytes, ixbf::DecodeLimits::default()).unwrap();
  let input = header_tests::input(bytes, bytes.len() as u64);
  let row = header_tests::bits(header, &input);
  assert!(tests::satisfies(header_r1cs, &row));
  let output = read_words(&row, header.input_count(), header.output_count());
  assert_eq!(output.last(), Some(&F128::ZERO));
  assert_eq!(output[..output.len() - 1], expected_header(&artifact));
  let mut naturals = 0;
  for function in artifact.functions() {
    for block in &function.blocks {
      visit(&block.instruction, &mut |operand| {
        if let ixbf::Operand::Literal(ixbf::Scalar::Nat(value)) = operand {
          // Re-encoding the admitted literal is uniquely canonical. This
          // differential does not claim a constrained source-span lookup.
          let input = tests::input(nat, &tests::natural_bytes(value), true);
          let row = tests::bits(nat, &input);
          assert!(tests::satisfies(nat_r1cs, &row));
          let output = read_words(&row, nat.input_count(), nat.output_count());
          assert_eq!(output.last(), Some(&F128::ZERO));
          let magnitude: Vec<_> = output[..output.len() - 1]
            .iter()
            .flat_map(|word| {
              word.lo.to_le_bytes().into_iter().chain(word.hi.to_le_bytes())
            })
            .collect();
          assert_eq!(BigUint::from_bytes_le(&magnitude), *value);
          naturals += 1;
        }
      });
    }
  }
  assert_eq!(naturals, artifact.inventory().scalars[0].literals);
  naturals
}

#[test]
#[ignore = "requires the independent compiler corpus and exact retained Init Stage 2 image"]
fn independent_corpus_and_real_init_headers_and_nat_literals_match_constraints()
{
  let header = HeaderDecodeGate::new(3).unwrap();
  let header_r1cs = header.r1cs();
  let nat =
    NaturalDecodeGate::new(3, NaturalCapacity::new(4096).unwrap()).unwrap();
  let nat_r1cs = nat.r1cs();
  let directory = path("IXBY_IXBF_CORPUS");
  let mut files: Vec<_> = std::fs::read_dir(directory)
    .unwrap()
    .map(|entry| entry.unwrap())
    .filter(|entry| {
      entry.file_type().unwrap().is_file()
        && entry.path().extension() == Some(OsStr::new("ixby"))
    })
    .map(|entry| entry.path())
    .collect();
  files.sort();
  assert!(files.len() >= 81, "incomplete external corpus");
  let mut naturals = 0;
  for file in &files {
    naturals += check(&read(file), &header, &header_r1cs, &nat, &nat_r1cs);
  }
  let bytes = read(&path("IXBY_IXBF_STAGE2_IMAGE"));
  assert_eq!(
    blake3::hash(&bytes).to_hex().as_str(),
    "a661dfede7c18bfb915d031393ffb258e65c21940d48039cdf44ab16428fe301"
  );
  assert_eq!(check(&bytes, &header, &header_r1cs, &nat, &nat_r1cs), 608);
  eprintln!(
    "constrained codecs: {} independent corpus headers, {naturals} corpus Nat literals; exact Init header and 608 Init Nat literals; no full-image admission",
    files.len()
  );
}

#[test]
#[ignore = "requires exact retained Init program, input and output for original ByteArray ranges"]
fn original_init_literal_input_and_output_byte_ranges_match_constraints() {
  let program = read(&path("IXBY_IXBF_STAGE2_IMAGE"));
  let input = read(&path("IXBY_IXBF_INIT_INPUT"));
  let output = read(&path("IXBY_IXBF_INIT_OUTPUT"));
  for (bytes, hash) in [
    (
      &program,
      "a661dfede7c18bfb915d031393ffb258e65c21940d48039cdf44ab16428fe301",
    ),
    (
      &input,
      "713a6a0b72dbaad673192c38c6e10115b1386482394cc22a945837c1a03f11c8",
    ),
    (
      &output,
      "3e6cb8264cfb6d253c41f22aa05221805a58f857d73877305adfed0781115a28",
    ),
  ] {
    assert_eq!(blake3::hash(bytes).to_hex().as_str(), hash);
  }
  let artifact =
    ixbf::decode_program(&program, ixbf::DecodeLimits::default()).unwrap();
  let input_model =
    ixbf::decode_input(&artifact, &input, ixbf::DecodeLimits::default())
      .unwrap();
  let output_model =
    ixbf::decode_output(&artifact, &output, ixbf::DecodeLimits::default())
      .unwrap();
  let gate = ByteArraySpanGate::new(3).unwrap();
  let r1cs = gate.r1cs();
  let limit = &artifact.limits().byte_array_bytes;
  let mut literals = 0;
  for function in artifact.functions() {
    for block in &function.blocks {
      visit(&block.instruction, &mut |operand| {
        if let ixbf::Operand::Literal(ixbf::Scalar::Bytes(payload)) = operand {
          check_span(&gate, &r1cs, &program, payload, limit);
          literals += 1;
        }
      });
    }
  }
  assert_eq!(literals, 6);
  for (source, values) in
    [(&input, input_model.values()), (&output, output_model.values())]
  {
    for node in values.nodes() {
      let ixbf::ValueKind::Scalar(ixbf::Scalar::Bytes(payload)) = node.kind
      else {
        panic!("expected exact Init scalar bytes")
      };
      let (_, expected) = check_span(&gate, &r1cs, source, payload, limit);
      eprintln!(
        "original Init byte span: file_bytes={}, payload_start={}, payload_bytes={}",
        source.len(),
        expected[0].lo,
        expected[0].hi
      );
    }
  }
  eprintln!(
    "constrained ranges passed for 6 program literals, 2 input values and 1 output value; payload read authentication remains separate"
  );
}
